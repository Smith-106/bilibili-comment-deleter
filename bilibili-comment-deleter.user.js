// ==UserScript==
// @name         B站评论批量删除 v2.2（全面优化版）
// @namespace    bilibili-comment-deleter
// @version      2.2.13
// @description  三源枚举（AICU / 官方历史 / 离线JSON导入）+ 官方接口删除 + 单条官方回查（不信 code=0，影子失败自动重试）+ 全区/整楼兜底 + 分阶段进度反馈 + 统一请求层 + 处理日志持久化
// @author       Smith-106 v2.0 / WorkBuddy v1.2 / SXM v1.1 + naaammme bilibili-tools 经验合并增强
// @license      MIT
// @match        *://*.bilibili.com/*
// @grant        GM_xmlhttpRequest
// @connect      api.aicu.cc
// @connect      apibackup2.aicu.cc
// @connect      api.bilibili.com
// @run-at       document-idle
// ==/UserScript==

(function () {
  'use strict';

  /* ═══════════ 常量 ═══════════ */
  const VERSION = '2.2.13';
  const P = 'bcd22';                  // DOM 前缀
  const DELAY_DEFAULT = 400;          // 删除间隔默认 ms
  const AICU_PS = 500;                // AICU 每页条数
  const AICU_DELAY = 3000;            // AICU 翻页延迟（防风控）
  const AICU_APIS = [
    'https://api.aicu.cc/api/v3/search/getreply',
    'https://apibackup2.aicu.cc:88/api/v3/search/getreply',
  ];
  const DELETE_MAX_RETRY = 4;         // -509 限流重试上限（含首次）
  const HISTORY_PS = 20;              // 官方历史每页条数
  const HISTORY_VIDEO_CAP = 200;      // 官方历史扫描视频数上限
  const HISTORY_VIDEO_DELAY = 1000;   // 逐视频扫描间隔
  const VIDEO_SCAN_PAGES_DEFAULT = 2; // 每视频扫描评论页数（时间序）
  const RENDER_CHUNK = 150;           // 列表增量渲染块大小
  const JOURNAL_CAP = 2000;           // 本地处理日志上限
  const TYPE_TEXT = { 1: '视频', 11: '番剧', 12: '专栏', 17: '动态', 21: '直播' };
  const ERR_TEXT = {
    '-101': '未登录',
    '-111': 'CSRF 校验失败（刷新页面）',
    '-404': '评论不存在或 oid/type 不匹配',
    '-412': '被风控拦截（换网络/降速）',
    '-509': '频率限制',
    '12022': '评论原本就不存在',
    '12006': '评论不存在（官方单条）',
  };
  const SHADOW_RETRY = 2;            // 接口回 0 但评论仍在时的自动重试次数
  const SHADOW_WAIT = 2500;          // 影子重试间隔（比正常删除更慢，避开风控假成功）
  const SRC_TEXT = { aicu: 'aicu', history: '官方历史', import: '导入', manual: '回查' };

  /* ═══════════ 状态 ═══════════ */
  let comments = [];                  // {rpid, oid, type, message, ctime, root, src}
  const rpidSet = new Set();          // O(1) 去重索引
  let datasetUid = '';                // 枚举时所属 UID（防换号误解）
  let selected = new Set();
  let anchorRpid = 0;
  let filterKw = '';                  // 关键词
  let filtSrc = 'all';
  let filtType = 'all';
  let filtState = 'all';          // all | ok | fail | uncertain | none
  let sortMode = 'default';           // default | tasc | tdesc
  let fetching = false;
  let logOnlyBad = false;
  let lastListPaint = 0;
  let deleting = false;
  let aborted = false;
  let batchResults = null;            // Map(rpid → 'ok'|'uncertain'|'fail')，最近一次批次
  let recheckCache = null;            // Map('oid:type' → {map, complete})  区域全量walk缓存（批次内）
  let threadCache = null;             // Map('oid:type:root' → {set, complete}) 楼层全量walk缓存（批次内）
  const bvidCache = {};

  /* ═══════════ 基础工具 ═══════════ */
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

  function getCookie(name) {
    // 某些特殊文档（about: 等）对 cookie 属性直接抛 SecurityError（冒烟测试实测），必须兜住
    let raw = '';
    try { raw = document.cookie; } catch (e) { return ''; }
    const m = raw.match(new RegExp('(?:^|;\\s*)' + name + '=([^;]*)'));
    if (!m) return '';
    try { return decodeURIComponent(m[1]); } catch (e) { return m[1]; }
  }

  function fmtEta(ms) {
    const s = Math.max(0, Math.round(ms / 1000));
    if (s < 60) return `约 ${s} 秒`;
    const m = Math.floor(s / 60);
    const r = s % 60;
    return r ? `约 ${m} 分 ${r} 秒` : `约 ${m} 分`;
  }

  function fmtTime(t) {
    if (!t) return '';
    const d = new Date(Number(t) * 1000);
    const p = (n) => String(n).padStart(2, '0');
    return `${d.getFullYear()}-${p(d.getMonth() + 1)}-${p(d.getDate())} ${p(d.getHours())}:${p(d.getMinutes())}`;
  }

  function typeText(t) { return TYPE_TEXT[t] || ('类型' + t); }

  /* ═══════════ 统一请求层 ═══════════
   * - 按 host 串行化（杜绝并发打同一接口）
   * - GET 自动重试：网络错误 / 5xx / 412 / 429 → 指数退避 + 抖动
   * - B站响应 code=-412 视为风控抛错
   */
  const hostChains = new Map();

  function hostOf(u) { try { return new URL(u).host; } catch (e) { return 'default'; } }

  function serialized(host, fn) {
    const prev = hostChains.get(host) || Promise.resolve();
    const p = prev.then(fn);
    hostChains.set(host, p.catch(() => {})); // 断链保护：错误不阻塞后续
    return p;
  }

  function gmXhr(opts) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest(Object.assign({}, opts, {
        onload: (r) => resolve(r),
        onerror: () => reject(new Error('网络错误')),
        ontimeout: () => reject(new Error('请求超时')),
        onabort: () => reject(new Error('请求中止')),
      }));
    });
  }

  function parseJsonRes(r) {
    let j = r.response;
    if (j == null || typeof j === 'string') {
      try { j = JSON.parse(r.responseText); }
      catch (e) { throw new Error('非 JSON 响应 (HTTP ' + r.status + ')'); }
    }
    return j;
  }

  const RETRYABLE_HTTP = (s) => s === 412 || s === 429 || (s >= 500 && s < 600 && s !== 509);

  async function gmGetJSON(url, { timeoutMs = 20000, retries = 2 } = {}) {
    for (let i = 0; ; i++) {
      let r;
      try {
        r = await serialized(hostOf(url), () => gmXhr({ method: 'GET', url, timeout: timeoutMs }));
        if (RETRYABLE_HTTP(r.status)) {
          if (i >= retries) throw new Error(`HTTP ${r.status}（重试 ${retries} 次后仍失败）`);
          await sleep(700 * Math.pow(2, i) + Math.random() * 400);
          continue;
        }
        const j = parseJsonRes(r);
        if (j && typeof j === 'object' && j.code === -412 && hostOf(url).includes('bilibili.com')) {
          throw new Error('B站风控(-412)，请降速或换网络');
        }
        return j;
      } catch (e) {
        if (i >= retries) throw e;
        await sleep(700 * Math.pow(2, i) + Math.random() * 400);
      }
    }
  }

  async function gmPostForm(url, body, timeoutMs = 15000) {
    const r = await serialized(hostOf(url), () => gmXhr({
      method: 'POST',
      url,
      data: body,
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      timeout: timeoutMs,
    }));
    let j;
    try { j = parseJsonRes(r); }
    catch (e) { j = { code: -1, message: ((r && r.responseText) || '空响应').slice(0, 120) }; }
    return j;
  }

  /* ═══════════ 处理日志（localStorage 持久化） ═══════════ */
  const JKEY = `${P}_journal`;
  let journalMapCache = null;

  function journalLoad() {
    try { return JSON.parse(localStorage.getItem(JKEY) || '[]'); } catch (e) { return []; }
  }
  function journalMap() {
    if (journalMapCache) return journalMapCache;
    journalMapCache = new Map(journalLoad().map((e) => [Number(e.rpid), e.state]));
    return journalMapCache;
  }
  function journalAdd(rpid, state) {
    try {
      let j = journalLoad();
      j.unshift({ rpid: Number(rpid), state, t: Date.now() });
      localStorage.setItem(JKEY, JSON.stringify(j.slice(0, JOURNAL_CAP)));
      journalMapCache = null;
      paintMark(rpid, state);
    } catch (e) { /* 容量满等原因，忽略 */ }
  }

  /** 已渲染行即时改徽标，不必等整批结束再重绘列表 */
  function paintMark(rpid, state) {
    const row = document.querySelector(`#${P}-list .${P}-item[data-rpid="${rpid}"]`);
    if (!row) return;
    const meta = row.querySelector('.meta');
    if (!meta) return;
    let b = meta.querySelector(`.${P}-mark`);
    if (!b) {
      b = document.createElement('span');
      b.className = `${P}-mark`;
      meta.appendChild(b);
    }
    b.textContent = state === 'ok' ? ' ·已确认删除✓' : state === 'fail' ? ' ·未生效' : ' ·待确认';
  }

  /** 标出正在处理的行，并只在列表内部滚动，不带动整页 */
  function markActive(rpid) {
    const list = document.getElementById(`${P}-list`);
    if (!list) return;
    const prev = list.querySelector(`.${P}-item.${P}-hot`);
    if (prev) prev.classList.remove(`${P}-hot`);
    if (rpid == null) return;
    const row = list.querySelector(`.${P}-item[data-rpid="${rpid}"]`);
    if (!row) return;
    row.classList.add(`${P}-hot`);
    const lr = list.getBoundingClientRect();
    const rr = row.getBoundingClientRect();
    if (rr.top < lr.top) list.scrollTop -= (lr.top - rr.top + 8);
    else if (rr.bottom > lr.bottom) list.scrollTop += (rr.bottom - lr.bottom + 8);
  }

  /* ═══════════ 数据层 ═══════════ */
  function addIfAbsent(item) {
    if (!item) return false;
    if (rpidSet.has(item.rpid)) return false;
    if (!item.rpid || !item.oid || !item.type) return false;
    comments.push(item);
    rpidSet.add(item.rpid);
    return true;
  }

  function resetDataset() {
    comments = [];
    rpidSet.clear();
    selected.clear();
    datasetUid = '';
    batchResults = null;
    filterKw = ''; filtSrc = 'all'; filtType = 'all'; filtState = 'all'; sortMode = 'default';
    const stSel = document.getElementById(`${P}-statesel`);
    if (stSel) stSel.value = 'all';
    const rb = document.getElementById(`${P}-retry`);
    if (rb) rb.style.display = 'none';
    renderList(); updCount();
  }

  /** aicu 导出条目 / 单页原始 JSON 条目 → 规范对象 */
  function mapAicuReply(it) {
    const rpid = Number(it && it.rpid);
    const dyn = (it && it.dyn) || {};
    const oid = Number(dyn.oid);
    const type = Number(dyn.type);
    if (!rpid || !oid || !type) return null;
    return {
      rpid,
      oid,
      type,
      message: (it.message || '').slice(0, 200),
      ctime: it.time || 0,
      root: (it.parent && it.parent.rootid) ? Number(it.parent.rootid) : 0,
      src: 'aicu',
    };
  }

  /* ═══════════ 枚举一：AICU 自动拉取 ═══════════ */
  async function fetchAicuComments(uid) {
    let page = 1;
    let aicuUrl = AICU_APIS[0];
    let total = 0;

    while (true) {
      if (aborted) break;
      const url = `${aicuUrl}?uid=${encodeURIComponent(uid)}&pn=${page}&ps=${AICU_PS}&mode=0`;
      let data;
      try {
        data = await gmGetJSON(url, { timeoutMs: 20000, retries: 1 });
      } catch (e) {
        if (aicuUrl === AICU_APIS[0]) {
          log(`主接口失败（${e.message}），切换备用…`, 'warn');
          aicuUrl = AICU_APIS[1];
          continue;
        }
        throw e;
      }

      if (data.code !== 0) {
        if (aicuUrl === AICU_APIS[0]) {
          log(`主接口返回 code=${data.code}，切换备用…`, 'warn');
          aicuUrl = AICU_APIS[1];
          continue;
        }
        log(`AICU 错误: ${data.message || data.code}`, 'err');
        break;
      }

      if (page === 1) {
        total = (data.data && data.data.cursor && data.data.cursor.all_count) || 0;
        log(total ? `AICU 索引共 ${total} 条，开始拉取` : 'AICU 未给出总数，开始拉取');
      }

      const replies = (data.data && data.data.replies) || [];
      if (!replies.length) { log('AICU 数据已全部获取'); break; }

      let added = 0;
      for (const it of replies) {
        if (addIfAbsent(mapAicuReply(it))) added++;
      }
      log(`第 ${page} 页: +${added} 条（累计 ${comments.length}${total ? '/' + total : ''}）`, 'info');
      setStatus(`枚举第 ${page} 页 · 累计 ${comments.length}${total ? '/' + total : ''} · 本页 +${added}`);
      touchList(true);
      if (total) setProg(Math.min(comments.length, total), total, '枚举');

      if (data.data && data.data.cursor && data.data.cursor.is_end) break;
      page++;
      await sleep(AICU_DELAY);
    }
  }

  /* ═══════════ 枚举二：官方观看历史兜底（纯官方，仅视频评论） ═══════════ */
  async function fetchHistoryComments(myUid, scanPages) {
    const mid = Number(myUid);
    const aids = [];
    let cursorMax = 0;
    let viewAt = 0;
    const seenAids = new Set();
    let guard = 0;

    while (seenAids.size < HISTORY_VIDEO_CAP && guard < 400) {
      guard++;
      if (aborted) break;
      const url = `https://api.bilibili.com/x/web-interface/history/cursor?type=archive&ps=${HISTORY_PS}&max=${cursorMax}&view_at=${viewAt}`;
      let data;
      try { data = await gmGetJSON(url); }
      catch (e) { log(`历史翻页失败: ${e.message}`, 'err'); break; }
      if (data.code !== 0) { log(`历史接口错误: ${data.message || data.code}`, 'err'); break; }

      const list = (data.data && data.data.list) || [];
      if (!list.length) break;
      for (const it of list) {
        const h = (it.history || {});
        if (h.aid && !seenAids.has(h.aid)) { seenAids.add(h.aid); aids.push(h.aid); }
      }
      const c = (data.data && data.data.cursor) || {};
      if (typeof c.max !== 'number' || typeof c.view_at !== 'number') break;
      cursorMax = c.max; viewAt = c.view_at;
      await sleep(800);
    }

    log(`观看历史共 ${seenAids.size} 个视频，逐个扫描（每视频 ${scanPages} 页，时间序）…`);
    for (let hi = 0; hi < aids.length; hi++) {
      if (aborted) break;
      const aid = aids[hi];
      setStatus(`扫描视频 ${hi + 1}/${aids.length} · 已找到 ${comments.length} 条`);
      touchList(false);
      setProg(hi, aids.length, '扫描');
      try { await fetchOwnRepliesFromVideo(aid, mid, scanPages); }
      catch (e) { log(`视频 ${aid} 扫描失败: ${e.message}`, 'warn'); }
      await sleep(HISTORY_VIDEO_DELAY);
    }
    log(`官方历史扫描结束，本来源新增 ${comments.filter((c) => c.src === 'history').length} 条`, 'ok');
  }

  async function fetchOwnRepliesFromVideo(aid, mid, scanPages) {
    let nextPage = 0;
    let guard = 0;
    while (guard < scanPages) {
      guard++;
      if (aborted) return;
      const d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/main?type=1&oid=${aid}&mode=2&next=${nextPage}`);
      if (d.code !== 0) return;
      let added = 0;
      const tops = (d.data && d.data.replies) || [];
      for (const top of tops) {
        const pool = [{ r: top, root: 0 }].concat(
          (Array.isArray(top.replies) ? top.replies : []).map((s) => ({ r: s, root: Number(top.rpid) || 0 }))
        );
        for (const entry of pool) {
          const r = entry.r;
          if (Number(r.mid) === mid) {
            const item = {
              rpid: Number(r.rpid),
              oid: aid,
              type: 1,
              message: ((r.content && r.content.message) || '').slice(0, 200),
              ctime: r.ctime || 0,
              root: entry.root,
              src: 'history',
            };
            if (addIfAbsent(item)) added++;
          }
        }
      }
      log(`  aid=${aid} 第${guard}页 +${added}`, 'info');
      const c = (d.data && d.data.cursor) || {};
      if (c.is_end) break;
      if (typeof c.next !== 'number' || c.next === nextPage) break;
      nextPage = c.next;
      await sleep(500);
    }
  }

  /* ═══════════ 枚举三：离线 JSON 导入 ═══════════ */
  function importJson(raw) {
    let data;
    try { data = JSON.parse(raw); }
    catch (e) { return { ok: false, msg: 'JSON 解析失败：' + e.message }; }

    let replies = null;
    if (Array.isArray(data)) replies = data;
    else if (Array.isArray(data.replies)) replies = data.replies;
    else if (data.data && Array.isArray(data.data.replies)) replies = data.data.replies;
    if (!replies) return { ok: false, msg: '未识别的结构：需要 replies 数组（aicu 导出 / 原始单页 JSON / 裸数组）' };

    let added = 0, skipped = 0;
    for (const it of replies) {
      const item = mapAicuReply(it);
      if (item) item.src = 'import';   // 与 aicu 枚举区分来源（冒烟测试抓到的标注 bug）
      if (item && addIfAbsent(item)) added++; else skipped++;
    }
    return { ok: true, msg: `导入完成：新增 ${added}，跳过 ${skipped}（无效/重复）` };
  }

  /* ═══════════ 删除 + 回查 ═══════════ */
  async function doDelete(c, csrf) {
    const attempt = async (withRoot) => {
      let url = 'https://api.bilibili.com/x/v2/reply/del';
      let body = `oid=${c.oid}&type=${c.type}&rpid=${c.rpid}`;
      // 番剧区（type=11）csrf 需走 query（naaammme/bilibili-tools 佐证的官方遗留行为）
      if (c.type === 11) url += `?csrf=${encodeURIComponent(csrf)}`;
      else body += `&csrf=${encodeURIComponent(csrf)}`;
      if (withRoot && c.root) body += `&root=${encodeURIComponent(c.root)}`;
      return gmPostForm(url, body);
    };
    let j = await attempt(!!c.root);
    if (j.code === -404 && c.root) {
      log(`↳ 带 root 报 -404，去掉 root 重试 rpid=${c.rpid}`, 'warn');
      j = await attempt(false);
    }
    return j;
  }

  /* ═══════════ 回查（v2.2.2：单条官方接口优先） ═══════════
   * 实测：删除接口 code=0 只表示「已受理」，风控下会假成功（评论仍在）。
   * 优先 GET /x/v2/reply/detail?type&oid&root&rpid：
   *   12006 / -404 = 不存在（终判已删）；code=0 = 仍可见（未生效）。
   * 单条接口不可用时才退回 v2.2.1 的全区/整楼 walk（巨区翻页不现实）。
   * walk 结果按批次缓存，删除只会移除条目，缓存不失效。 */
  const RECHECK_TOP_MAX = 200;      // 区域顶评 walk 页数上限（游标制）
  const RECHECK_SUB_PS = 49;        // 楼内每页条数（官方页面大小）
  const RECHECK_SUB_MAX = 60;       // 楼内最多翻页数
  const RECHECK_WALK_DELAY = 250;   // walk 翻页间隔

  /** 全量走完一个评论区：{map: Map(rpid→rootStr|''), complete, pages} */
  async function walkArea(oid, type) {
    const key = `${oid}:${type}`;
    if (recheckCache.has(key)) return recheckCache.get(key);
    const map = new Map();
    let complete = false, pages = 0, next = 0;
    for (let guard = 0; guard < RECHECK_TOP_MAX && !aborted; guard++) {
      let d;
      try {
        d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/main?type=${type}&oid=${oid}&mode=2&next=${next}`, { retries: 1 });
      } catch (e) { log(`回查 walk 失败 oid=${oid}: ${e.message}`, 'warn'); break; }
      if (d.code !== 0) { log(`回查 walk code=${d.code} oid=${oid} type=${type}`, 'warn'); break; }
      pages++;
      for (const top of ((d.data && d.data.replies) || [])) {
        map.set(String(top.rpid), '');
        if (Array.isArray(top.replies)) for (const s of top.replies) map.set(String(s.rpid), String(top.rpid));
      }
      const c = (d.data && d.data.cursor) || {};
      if (c.is_end || typeof c.next !== 'number' || c.next === next) { complete = true; break; }
      next = c.next;
      await sleep(RECHECK_WALK_DELAY);
    }
    const res = { map, complete, pages };
    recheckCache.set(key, res);
    return res;
  }

  /** 全量走完楼中楼根楼层下的全部子回复：{set:Set(rpidStr), complete} */
  async function walkThread(oid, type, root) {
    const key = `${oid}:${type}:${root}`;
    if (threadCache.has(key)) return threadCache.get(key);
    const set = new Set();
    let complete = false;
    for (let pn = 1; pn <= RECHECK_SUB_MAX && !aborted; pn++) {
      let d;
      try {
        d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/reply?type=${type}&oid=${oid}&root=${root}&pn=${pn}&ps=${RECHECK_SUB_PS}`, { retries: 1 });
      } catch (e) { log(`楼层 walk 失败 root=${root}: ${e.message}`, 'warn'); break; }
      if (d.code !== 0) { log(`楼层 walk code=${d.code} root=${root}`, 'warn'); break; }
      const rs = (d.data && d.data.replies) || [];
      for (const r of rs) set.add(String(r.rpid));
      const count = d.data && d.data.page && d.data.page.count;
      if ((typeof count === 'number' && pn * RECHECK_SUB_PS >= count) || rs.length < RECHECK_SUB_PS) { complete = true; break; }
      await sleep(RECHECK_WALK_DELAY);
    }
    const res = { set, complete };
    threadCache.set(key, res);
    return res;
  }

  /** 官方单条 oracle。顶评 root 用自身 rpid。不可判定返回 null，交给 walk。 */
  async function oracleCheck(c) {
    const root = c.root || c.rpid;
    let d;
    try {
      d = await gmGetJSON(
        `https://api.bilibili.com/x/v2/reply/detail?type=${c.type}&oid=${c.oid}&root=${root}&rpid=${c.rpid}`,
        { retries: 1 }
      );
    } catch (e) { return null; }
    if (!d || typeof d.code !== 'number') return null;
    if (d.code === 12006 || d.code === -404) return { state: 'ok', why: `官方单条确认不存在(${d.code})` };
    if (d.code === 0) return { state: 'fail', why: '官方单条仍可见（删除接口可能假成功）' };
    return null;
  }

  /** 可判定回查：{state:'ok'|'fail'|'uncertain', why}；接口不可用返回 null（按待确认处理） */
  async function recheckDefinitive(c) {
    const quick = await oracleCheck(c);
    if (quick) return quick;
    const area = await walkArea(c.oid, c.type);
    if (area.map.has(String(c.rpid))) {
      return { state: 'fail', why: area.map.get(String(c.rpid)) ? '楼中楼内联预览仍在' : '顶评仍在' };
    }
    if (c.root) {
      if (!area.map.has(String(c.root))) return { state: 'ok', why: '根楼层已不存在，子评必然已删' };
      const th = await walkThread(c.oid, c.type, c.root);
      if (th.set.has(String(c.rpid))) return { state: 'fail', why: '楼内仍在' };
      if (!th.complete) return { state: 'uncertain', why: `楼内翻页未走完(≤${RECHECK_SUB_MAX}页)` };
      return { state: 'ok', why: `整楼未发现(根=${c.root})` };
    }
    if (!area.complete) return { state: 'uncertain', why: `区域翻页未走完(≤${RECHECK_TOP_MAX}页)` };
    return { state: 'ok', why: `全区未发现(${area.pages}页)` };
  }

  /* ═══════════ 跳转定位 ═══════════ */
  async function aidToBvid(aid) {
    if (bvidCache[aid]) return bvidCache[aid];
    try {
      const d = await gmGetJSON(`https://api.bilibili.com/x/web-interface/view?aid=${encodeURIComponent(aid)}`);
      const bv = d && d.data && d.data.bvid ? d.data.bvid : null;
      bvidCache[aid] = bv;
      return bv;
    } catch (e) { return null; }
  }

  async function jumpTo(c) {
    if (!c.oid) { setStatus('该评论缺少 oid，无法跳转。'); return; }
    let url = null;
    if (c.type === 1) {
      const bv = await aidToBvid(c.oid);
      url = bv ? `https://www.bilibili.com/video/${bv}#reply${c.rpid}`
               : `https://www.bilibili.com/video/av${c.oid}#reply${c.rpid}`;
    } else if (c.type === 17) {
      url = `https://t.bilibili.com/${c.oid}#reply${c.rpid}`;
    } else if (c.type === 12) {
      url = `https://www.bilibili.com/read/cv${c.oid}#reply${c.rpid}`;
    } else if (c.type === 11) {
      url = `https://www.bilibili.com/bangumi/play/ep${c.oid}#reply${c.rpid}`;
    }
    if (url) window.open(url, '_blank');
    else setStatus(`暂不支持 ${typeText(c.type)} 的跳转（oid=${c.oid}）。`);
  }

  /* ═══════════ 导出备份 ═══════════ */
  function csvCell(s) {
    s = String(s == null ? '' : s);
    return '"' + s.replace(/"/g, '""') + '"';
  }

  function stateLabel(rpid) {
    const st = journalMap().get(Number(rpid));
    return st === 'ok' ? '已删除' : st === 'fail' ? '未生效' : st === 'uncertain' ? '待确认' : '';
  }

  function doExport(kind) {
    const list = visibleComments();
    if (!list.length) { setStatus('当前筛选下没有数据可导出。'); return; }
    const stamped = list.map((c) => Object.assign({}, c, { state: stateLabel(c.rpid) }));
    let blob, name;
    if (kind === 'json') {
      blob = new Blob([JSON.stringify(stamped, null, 2)], { type: 'application/json' });
      name = `bili-comments-${Date.now()}.json`;
    } else {
      const head = 'rpid,oid,type,typeText,message,ctime,ctimeText,root,src,state';
      const rows = stamped.map((c) =>
        [c.rpid, c.oid, c.type, typeText(c.type), c.message, c.ctime, fmtTime(c.ctime), c.root, SRC_TEXT[c.src] || c.src, c.state].map(csvCell).join(',')
      ).join('\r\n');
      blob = new Blob(['\ufeff' + head + '\r\n' + rows], { type: 'text/csv;charset=utf-8' });
      name = `bili-comments-${Date.now()}.csv`;
    }
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 3000);
    setStatus(`已导出 ${list.length} 条（${kind.toUpperCase()}，含处理结果列）。`);
    log(`已导出 ${list.length} 条（${kind.toUpperCase()}）`, 'ok');
  }

  /* ═══════════ 样式（明暗双主题，CSS 变量） ═══════════ */
  function injectCSS() {
    const s = document.createElement('style');
    s.textContent = `
      #${P}-toggle{position:fixed;bottom:80px;right:24px;z-index:999999;width:48px;height:48px;
        border-radius:50%;border:none;background:#00a1d6;color:#fff;font-size:22px;cursor:pointer;
        box-shadow:0 2px 14px rgba(0,0,0,.35);display:flex;align-items:center;justify-content:center;
        user-select:none;transition:transform .2s}
      #${P}-toggle:hover{transform:scale(1.12)}

      #${P}-panel{position:fixed;top:50%;right:24px;transform:translateY(-50%);width:480px;max-height:84vh;
        z-index:999998;background:var(--c-bg);border-radius:14px;box-shadow:0 10px 40px rgba(0,0,0,.55);
        color:var(--c-tx);font:13px/1.55 -apple-system,BlinkMacSystemFont,'Segoe UI','Microsoft YaHei',sans-serif;
        display:flex;flex-direction:column;overflow:hidden;
        --c-bg:#1e1e2e;--c-hdbg:#252540;--c-hdtx:#e0e0e0;--c-secbd:#2c2c48;--c-rowbd:#262642;
        --c-strip:#20203a;--c-tx:#e0e0e0;--c-sub:#9499a0;--c-sub2:#5a5a7a;--c-hover:#252540;
        --c-logbg:#141428;--c-inputbg:#2a2a3e;--c-inputbd:#454560;--c-btnbg:#2a2a3e;--c-btnbd:#454560;
        --c-btnhov:#3a3a5e;--c-mark:#ffa502}
      #${P}-panel[data-theme=light]{
        --c-bg:#ffffff;--c-hdbg:#00a1d6;--c-hdtx:#ffffff;--c-secbd:#e8e8f0;--c-rowbd:#ececf2;
        --c-strip:#f4f4f8;--c-tx:#333b4d;--c-sub:#6a7383;--c-sub2:#98a0ad;--c-hover:#f2f6fa;
        --c-logbg:#f7f8fc;--c-inputbg:#ffffff;--c-inputbd:#ccd2dc;--c-btnbg:#eef1f6;--c-btnbd:#ccd2dc;
        --c-btnhov:#e2e8f0;--c-mark:#ff9a12}
      #${P}-panel *{box-sizing:border-box}

      .${P}-hd{display:flex;align-items:center;justify-content:space-between;padding:12px 18px;
        background:var(--c-hdbg);color:var(--c-hdtx);font-size:15px;font-weight:600;cursor:move;user-select:none}
      .${P}-hd .v{color:rgba(255,255,255,.6);font-size:11px;font-weight:400;margin-left:6px}
      #${P}-panel[data-theme=light] .${P}-hd .v{color:rgba(255,255,255,.75)}
      .${P}-hd .hbtns{display:flex;gap:2px}
      .${P}-hd button{background:none;border:none;color:inherit;font-size:16px;cursor:pointer;
        line-height:1;padding:2px 6px;opacity:.85}
      .${P}-hd button:hover{opacity:1}

      .${P}-sec{padding:9px 18px;border-bottom:1px solid var(--c-secbd)}
      .${P}-row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}

      .${P}-btn{padding:6px 13px;border-radius:7px;border:1px solid var(--c-btnbd);background:var(--c-btnbg);
        color:var(--c-tx);cursor:pointer;font-size:12px;white-space:nowrap;transition:background .15s}
      .${P}-btn:hover:not(:disabled){background:var(--c-btnhov)}
      .${P}-btn:disabled{opacity:.4;cursor:not-allowed}
      .${P}-btn-p{background:#00a1d6;border-color:#00a1d6;color:#fff}
      .${P}-btn-p:hover:not(:disabled){background:#00b5e5}
      .${P}-btn-d{background:#ff4757;border-color:#ff4757;color:#fff}
      .${P}-btn-d:hover:not(:disabled){background:#ff6b7a}

      .${P}-input{width:72px;padding:5px 8px;border-radius:5px;border:1px solid var(--c-inputbd);
        background:var(--c-inputbg);color:var(--c-tx);font-size:12px;text-align:center}
      .${P}-input.w{width:170px}
      .${P}-input:focus{outline:none;border-color:#00a1d6}
      .${P}-sel{padding:5px 6px;border-radius:5px;border:1px solid var(--c-inputbd);background:var(--c-inputbg);
        color:var(--c-tx);font-size:12px;cursor:pointer}
      .${P}-ta{width:100%;height:66px;border-radius:6px;border:1px solid var(--c-inputbd);
        background:var(--c-inputbg);color:var(--c-tx);font-size:12px;padding:6px;resize:vertical}
      .${P}-hint{color:var(--c-sub);font-size:11px}
      #${P}-cfg label,.${P}-lab{cursor:pointer;display:flex;align-items:center;gap:5px;font-size:12px;
        color:var(--c-sub);margin-top:6px}
      #${P}-cfg input{accent-color:#00a1d6}
      .${P}-retry{display:none;background:#7a5cff !important;border-color:#7a5cff !important;color:#fff !important}

      .${P}-strip{padding:7px 18px;background:var(--c-strip);font-size:12px;color:var(--c-sub);
        display:flex;flex-direction:column;gap:5px}
      .${P}-strip .r{display:flex;align-items:center;gap:6px;flex-wrap:wrap}
      .${P}-cnt{margin-left:auto;color:var(--c-sub);white-space:nowrap}
      .${P}-strip label{display:flex;align-items:center;gap:4px;cursor:pointer}

      .${P}-list{flex:1;min-height:90px;max-height:290px;overflow-y:auto}
      .${P}-list::-webkit-scrollbar{width:6px}
      .${P}-list::-webkit-scrollbar-thumb{background:rgba(128,128,128,.4);border-radius:3px}
      .${P}-empty{padding:28px 18px;text-align:center;color:var(--c-sub2);font-size:13px}
      .${P}-item{display:flex;align-items:flex-start;gap:8px;padding:8px 18px;border-bottom:1px solid var(--c-rowbd);
        font-size:12px;transition:background .12s;cursor:pointer}
      .${P}-item:hover{background:var(--c-hover)}
      .${P}-item.${P}-hot{background:rgba(0,161,214,.18);box-shadow:inset 0 0 0 1px rgba(0,161,214,.55)}
      @media (prefers-reduced-motion: reduce){ .${P}-item{transition:none} }
      .${P}-item input{accent-color:#00a1d6;cursor:pointer;margin-top:3px;flex-shrink:0}
      .${P}-item .m{flex:1;min-width:0;word-break:break-all;color:var(--c-tx)}
      .${P}-item .meta{color:var(--c-sub2);font-size:11px;margin-top:2px}
      .${P}-nop{color:#ff6b6b}
      .${P}-mark{color:var(--c-mark)}
      .${P}-jump{background:var(--c-btnbg);color:var(--c-sub);border:1px solid var(--c-btnbd);border-radius:5px;
        padding:3px 8px;font-size:11px;cursor:pointer;white-space:nowrap;flex-shrink:0}
      .${P}-jump:hover{color:var(--c-tx)}
      .${P}-sent{padding:10px 18px;text-align:center;color:var(--c-sub2);font-size:11px;cursor:pointer}

      .${P}-barwrap{padding:9px 18px;display:flex;align-items:center;gap:12px}
      .${P}-bar{flex:1;height:8px;background:rgba(128,128,128,.3);border-radius:4px;overflow:hidden}
      .${P}-fill{height:100%;width:0%;background:linear-gradient(90deg,#00a1d6,#23e5a0);border-radius:4px;
        transition:width .3s}
      .${P}-pct{font-size:12px;color:var(--c-sub);min-width:100px;text-align:right;white-space:nowrap}
      .${P}-status{padding:6px 18px;color:var(--c-sub);font-size:12px;min-height:18px;white-space:pre-wrap}
      .${P}-log{max-height:140px;overflow-y:auto;padding:7px 18px;font-size:11px;
        font-family:'Cascadia Code',Consolas,'Courier New',monospace;background:var(--c-logbg);
        border-top:1px solid var(--c-secbd)}
      .${P}-log-line{padding:2px 0;word-break:break-all}
      .${P}-log-hide{display:none}
      .${P}-logbar{display:flex;justify-content:flex-end;padding:2px 14px 0}
      .${P}-ask{position:absolute;inset:0;z-index:6;background:rgba(0,0,0,.5);display:flex;align-items:center;justify-content:center;padding:16px}
      .${P}-askbox{width:100%;background:var(--c-bg);color:var(--c-tx);border:1px solid var(--c-inputbd);border-radius:10px;padding:14px;white-space:pre-wrap;font-size:13px;line-height:1.45}
      .${P}-askbox .${P}-row{margin-top:12px;justify-content:flex-end}
      .${P}-ok{color:#2ed573} .${P}-err{color:#ff4757} .${P}-warn{color:#ffa502} .${P}-info{color:#70a1ff}
    `;
    document.head.appendChild(s);
  }

  /* ═══════════ UI 构建 ═══════════ */
  function buildUI() {
    const toggle = document.createElement('button');
    toggle.id = `${P}-toggle`;
    toggle.innerHTML = '\u{1F5D1}\uFE0F';
    toggle.title = `B站评论批量删除 v${VERSION}`;
    document.body.appendChild(toggle);

    const panel = document.createElement('div');
    panel.id = `${P}-panel`;
    panel.style.display = 'none';

    panel.innerHTML = `
      <div class="${P}-hd" id="${P}-hdr">
        <span>B站评论批量删除<span class="v">v${VERSION}</span></span>
        <span class="hbtns">
          <button id="${P}-theme" title="切换明/暗主题">🌓</button>
          <button id="${P}-close" title="隐藏面板">×</button>
        </span>
      </div>
      <div class="${P}-sec">
        <div class="${P}-row">
          <button class="${P}-btn ${P}-btn-p" id="${P}-load" title="通过第三方 aicu 索引拉取全部评论（推荐首选）">📥 AICU 获取</button>
          <button class="${P}-btn" id="${P}-hist" title="翻观看历史→逐视频扫自己的评论（纯官方接口，仅视频评论）">🏛️ 官方历史</button>
          <button class="${P}-btn" id="${P}-stop" style="display:none">⏹ 停止</button>
        </div>
        <div class="${P}-row" style="margin-top:7px">
          <textarea class="${P}-ta" id="${P}-ta" placeholder="离线兜底：粘贴 aicu 导出的 JSON（含 replies 数组均可）"></textarea>
        </div>
        <div class="${P}-row" style="margin-top:4px">
          <button class="${P}-btn" id="${P}-import">📋 导入 JSON</button>
          <span class="${P}-hint">aicu 不可用时：在其网页导出后手动粘贴</span>
        </div>
      </div>
      <div class="${P}-sec" id="${P}-cfg">
        <div class="${P}-row">
          <button class="${P}-btn ${P}-btn-d" id="${P}-dsel" disabled>🔥 删除选中</button>
          <button class="${P}-btn ${P}-btn-d" id="${P}-dall" disabled>💣 删除全部</button>
          <button class="${P}-btn ${P}-retry" id="${P}-retry">↻ 重试未成功</button>
          <button class="${P}-btn ${P}-retry" id="${P}-copybad" type="button">复制未成功</button>
          <span style="color:var(--c-sub);font-size:12px">间隔</span>
          <input class="${P}-input" type="number" id="${P}-delay" value="${DELAY_DEFAULT}" min="200" max="5000" step="50">
          <span style="color:var(--c-sub);font-size:12px">ms</span>
        </div>
        <label><input type="checkbox" id="${P}-recheck" checked> 删除后官方单条确认（不信 code=0；仍在则自动降速重试）</label>
        <label><input type="checkbox" id="${P}-skipok" checked> 跳过日志里已确认删除的（重跑枚举时不再打这些接口）</label>
      </div>
      <div class="${P}-strip">
        <div class="r">
          <input class="${P}-input w" type="text" id="${P}-kw" placeholder="关键词筛选">
          <button class="${P}-btn" id="${P}-filter" style="padding:4px 10px">筛选</button>
          <button class="${P}-btn" id="${P}-clearf" style="padding:4px 10px">清除</button>
          <span class="${P}-cnt" id="${P}-cnt">0 条</span>
        </div>
        <div class="r">
          <label>来源 <select class="${P}-sel" id="${P}-srcsel">
            <option value="all">全部</option><option value="aicu">aicu</option>
            <option value="history">官方历史</option><option value="import">导入</option>
          </select></label>
          <label>类型 <select class="${P}-sel" id="${P}-typesel">
            <option value="all">全部</option><option value="1">视频</option><option value="11">番剧</option>
            <option value="12">专栏</option><option value="17">动态</option><option value="21">直播</option>
          </select></label>
          <label>结果 <select class="${P}-sel" id="${P}-statesel" title="按处理结果筛选">
             <option value="all">全部</option><option value="ok">已删除</option>
             <option value="fail">未生效</option><option value="uncertain">待确认</option>
             <option value="none">未处理</option>
           </select></label>
           <label>排序 <select class="${P}-sel" id="${P}-sortsel">
            <option value="default">默认</option><option value="tasc">时间↑</option><option value="tdesc">时间↓</option>
          </select></label>
          <button class="${P}-btn" id="${P}-selall" style="padding:4px 10px" title="勾选当前筛选。按住 Shift 再点两行，会连选中间">全选</button>
          <button class="${P}-btn" id="${P}-selnone" style="padding:4px 10px">全不选</button>
          <button class="${P}-btn" id="${P}-expj" title="导出当前筛选下列表为 JSON（删除前备份）">💾JSON</button>
          <button class="${P}-btn" id="${P}-expc" title="导出当前筛选下列表为 CSV">💾CSV</button>
          <button class="${P}-btn" id="${P}-reset" title="清空当前列表与勾选">🧹清空</button>
        </div>
      </div>
      <div class="${P}-list" id="${P}-list">
        <div class="${P}-empty">三选一：AICU 全量获取 / 官方历史扫描 / 粘贴 JSON 导入</div>
      </div>
      <div class="${P}-barwrap" id="${P}-prog" style="display:none">
        <div class="${P}-bar"><div class="${P}-fill" id="${P}-fill"></div></div>
        <span class="${P}-pct" id="${P}-pct">0%</span>
      </div>
      <div class="${P}-status" id="${P}-status"></div>
      <div class="${P}-logbar"><button type="button" class="${P}-btn" id="${P}-logbad" style="padding:2px 8px">只看问题</button></div>
      <div class="${P}-log" id="${P}-log"></div>
      <div class="${P}-ask" id="${P}-ask" style="display:none" role="dialog" aria-modal="true">
        <div class="${P}-askbox">
          <div id="${P}-askmsg"></div>
          <div class="${P}-row">
            <button type="button" class="${P}-btn" id="${P}-askno">取消</button>
            <button type="button" class="${P}-btn ${P}-btn-d" id="${P}-askok">确认</button>
          </div>
        </div>
      </div>
    `;
    document.body.appendChild(panel);

    const $el = (id) => document.getElementById(id);

    /* —— 顶部 —— */
    toggle.onclick = () => {
      panel.style.display = panel.style.display === 'none' ? 'flex' : 'none';
    };
    $el(`${P}-close`).onclick = () => { panel.style.display = 'none'; };
    $el(`${P}-logbad`).onclick = () => {
      logOnlyBad = !logOnlyBad;
      $el(`${P}-logbad`).textContent = logOnlyBad ? '显示全部' : '只看问题';
      const box = $el(`${P}-log`);
      for (const line of box.children) {
        const bad = line.classList.contains(`${P}-err`) || line.classList.contains(`${P}-warn`);
        line.classList.toggle(`${P}-log-hide`, logOnlyBad && !bad);
      }
    };
    $el(`${P}-stop`).onclick = () => {
      aborted = true;
      $el(`${P}-stop`).disabled = true;
      setStatus('正在停止，等当前这一次请求结束…');
      log('正在停止…（当前请求结束后退出）', 'warn');
    };
    $el(`${P}-theme`).onclick = () => {
      const t = panel.getAttribute('data-theme') === 'light' ? 'dark' : 'light';
      panel.setAttribute('data-theme', t);
      saveSettings();
    };

    /* —— 枚举 —— */
    $el(`${P}-load`).onclick = loadAicu;
    $el(`${P}-hist`).onclick = loadHistory;
    $el(`${P}-import`).onclick = onImport;

    /* —— 筛选/选择/导出 —— */
    $el(`${P}-filter`).onclick = onFilter;
    $el(`${P}-clearf`).onclick = () => { $el(`${P}-kw`).value = ''; onFilter(); };
    $el(`${P}-kw`).addEventListener('keydown', (e) => { if (e.key === 'Enter') onFilter(); });
    $el(`${P}-srcsel`).onchange = () => { filtSrc = $el(`${P}-srcsel`).value; renderList(); updCount(); };
    $el(`${P}-typesel`).onchange = () => { filtType = $el(`${P}-typesel`).value; renderList(); updCount(); };
    $el(`${P}-statesel`).onchange = () => { filtState = $el(`${P}-statesel`).value; renderList(); updCount(); };
    $el(`${P}-kw`).addEventListener('input', () => {
      clearTimeout(kwTimer);
      kwTimer = setTimeout(() => onFilter(true), 250);
    });
    $el(`${P}-sortsel`).onchange = () => { sortMode = $el(`${P}-sortsel`).value; renderList(); updCount(); };
    $el(`${P}-selall`).onclick = () => {
      visibleComments().forEach((c) => { if (c.oid && c.type) selected.add(c.rpid); });
      renderList(); updCount();
    };
    $el(`${P}-selnone`).onclick = () => { selected.clear(); renderList(); updCount(); };
    $el(`${P}-expj`).onclick = () => doExport('json');
    $el(`${P}-expc`).onclick = () => doExport('csv');
    $el(`${P}-reset`).onclick = async () => {
      if (!(await ask('清空当前列表与勾选？\n已删除记录不受影响。', '清空'))) return;
      resetDataset();
      setStatus('列表已清空。');
      log('🧹 列表已清空', 'warn');
    };

    /* —— 删除 —— */
    $el(`${P}-dsel`).onclick = () => runDelete('selected');
    $el(`${P}-dall`).onclick = () => runDelete('all');
    $el(`${P}-retry`).onclick = () => {
      const rp = [...(batchResults || [])].filter(([, s]) => s !== 'ok').map(([r]) => r);
      const targets = comments.filter((c) => rp.includes(c.rpid) && c.oid && c.type);
      if (!targets.length) { setStatus('没有需要重试的条目。'); return; }
      runDelete('explicit', targets, '重试未成功');
    };
    $el(`${P}-retry`).style.display = 'none';
    $el(`${P}-copybad`).onclick = async () => {
      const jm = journalMap();
      const ids = comments.filter((c) => {
        const st = jm.get(Number(c.rpid));
        return st === 'fail' || st === 'uncertain';
      }).map((c) => c.rpid);
      if (!ids.length) { setStatus('没有未成功的 rpid 可复制。'); return; }
      const text = ids.join('\n');
      try {
        await navigator.clipboard.writeText(text);
        setStatus(`已复制 ${ids.length} 个未成功 rpid。`);
      } catch (e) {
        setStatus('复制失败。请允许剪贴板，或从日志里复制。');
        log(`未成功 rpid：${ids.join(',')}`, 'warn');
      }
    };

    /* —— 列表事件委托（万级数据不挂） —— */
    const listEl = $el(`${P}-list`);
    listEl.addEventListener('change', (e) => {
      if (!e.target.matches('input[type="checkbox"]')) return;
      if (e.target.dataset.skip === '1') { e.target.dataset.skip = ''; return; }
      const rpid = Number(e.target.dataset.rpid);
      e.target.checked ? selected.add(rpid) : selected.delete(rpid);
      updCount();
    });
    listEl.addEventListener('click', (e) => {
      const jb = e.target.closest('button[data-act="jump"]');
      if (jb) {
        const c = comments.find((x) => x.rpid === Number(jb.dataset.rpid));
        if (c) jumpTo(c);
        return;
      }
      if (e.target.closest('a')) return;
      const row = e.target.closest(`.${P}-item`);
      if (!row) return;
      const rpid = Number(row.dataset.rpid);
      if (!rpid) return;
      const rowItem = comments.find((x) => x.rpid === rpid);
      if (rowItem && (!rowItem.oid || !rowItem.type)) {
        setStatus(`rpid=${rpid} 缺少 oid 或 type，不能删除。`);
        return;
      }
      const textSel = window.getSelection && String(window.getSelection());
      if (textSel) return;
      if (e.shiftKey && anchorRpid) {
        if (e.target.matches('input[type="checkbox"]')) {
          e.preventDefault();
          e.target.dataset.skip = '1';
          setTimeout(() => { e.target.dataset.skip = ''; }, 0);
        }
        selectRange(anchorRpid, rpid);
        return;
      }
      if (e.target.matches('input[type="checkbox"]')) { anchorRpid = rpid; return; }
      const box = row.querySelector('input[type="checkbox"]');
      const on = !(box ? box.checked : selected.has(rpid));
      if (box) box.checked = on;
      on ? selected.add(rpid) : selected.delete(rpid);
      anchorRpid = rpid;
      updCount();
    });

    /* —— 面板拖拽（位置记忆 + 越界复位） —— */
    const hdr = $el(`${P}-hdr`);
    let drag = null;
    hdr.addEventListener('mousedown', (e) => {
      if (e.target.closest('button')) return;
      const rect = panel.getBoundingClientRect();
      drag = { ox: e.clientX - rect.left, oy: e.clientY - rect.top };
      panel.style.right = 'auto';
      panel.style.top = rect.top + 'px';
      panel.style.left = rect.left + 'px';
      panel.style.transform = 'none';
      e.preventDefault();
    });
    window.addEventListener('mousemove', (e) => {
      if (!drag) return;
      const x = Math.min(Math.max(8, e.clientX - drag.ox), window.innerWidth - 120);
      const y = Math.min(Math.max(8, e.clientY - drag.oy), window.innerHeight - 60);
      panel.style.left = x + 'px';
      panel.style.top = y + 'px';
    });
    window.addEventListener('mouseup', () => {
      if (drag) { drag = null; saveSettings(); }
    });

    /* —— 恢复设置 —— */
    try {
      const saved = JSON.parse(localStorage.getItem(P) || '{}');
      if (saved.delay) $el(`${P}-delay`).value = saved.delay;
      if (saved.recheck === false) $el(`${P}-recheck`).checked = false;
      if (saved.skipOk === false) $el(`${P}-skipok`).checked = false;
      if (saved.theme === 'light') panel.setAttribute('data-theme', 'light');
      if (saved.left && saved.top && Number(saved.left) > 0 && Number(saved.left) < window.innerWidth - 100
          && Number(saved.top) > 0 && Number(saved.top) < window.innerHeight - 60) {
        panel.style.right = 'auto';
        panel.style.left = saved.left + 'px';
        panel.style.top = saved.top + 'px';
        panel.style.transform = 'none';
      }
    } catch (e) { /* noop */ }
    $el(`${P}-delay`).addEventListener('change', saveSettings);
    $el(`${P}-recheck`).addEventListener('change', saveSettings);
    $el(`${P}-skipok`).addEventListener('change', saveSettings);
    document.addEventListener('keydown', (e) => {
      if (e.key !== 'Escape' || !(deleting || fetching)) return;
      const tag = e.target && e.target.tagName;
      if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return;
      aborted = true;
      const stop = $el(`${P}-stop`);
      if (stop) stop.disabled = true;
      setStatus('正在停止（Esc），等当前这一次请求结束…');
      log('Esc 停止…（当前请求结束后退出）', 'warn');
    });

    /* —— 初始状态 —— */
    const csrf = getCookie('bili_jct');
    const uid = getCookie('DedeUserID');
    if (csrf && uid) setStatus(`已登录 UID=${uid}，bili_jct 就绪。删除不可逆，请谨慎。`);
    else setStatus('⚠️ 未检测到登录态（请先在 bilibili.com 登录后刷新）。可先导入/浏览，删除需登录。');
    renderList(); updCount();
  }

  function saveSettings() {
    try {
      const panel = document.getElementById(`${P}-panel`);
      localStorage.setItem(P, JSON.stringify({
        delay: parseInt(document.getElementById(`${P}-delay`).value, 10) || DELAY_DEFAULT,
        recheck: document.getElementById(`${P}-recheck`).checked,
        skipOk: document.getElementById(`${P}-skipok`).checked,
        theme: panel && panel.getAttribute('data-theme') || 'dark',
        left: panel && panel.style.left ? parseInt(panel.style.left, 10) : 0,
        top: panel && panel.style.top ? parseInt(panel.style.top, 10) : 0,
      }));
    } catch (e) { /* noop */ }
  }

  /* ═══════════ 视图/筛选 ═══════════ */
  function selectRange(a, b) {
    const list = (viewSnap && viewSnap.length) ? viewSnap : visibleComments();
    const ia = list.findIndex((c) => c.rpid === a);
    const ib = list.findIndex((c) => c.rpid === b);
    if (ia < 0 || ib < 0) return;
    const lo = Math.min(ia, ib);
    const hi = Math.max(ia, ib);
    let n = 0;
    for (let i = lo; i <= hi; i++) {
      const c = list[i];
      if (!c.oid || !c.type) continue;
      selected.add(c.rpid);
      n++;
    }
    anchorRpid = b;
    renderList();
    setStatus(`已连选 ${n} 条（当前筛选内，含两端）。`);
  }

  function filtersOn() {
    return !!(filterKw || filtSrc !== 'all' || filtType !== 'all' || filtState !== 'all');
  }

  function visibleComments() {
    let list = comments;
    if (filterKw) list = list.filter((c) => (c.message || '').toLowerCase().includes(filterKw.toLowerCase()));
    if (filtSrc !== 'all') list = list.filter((c) => c.src === filtSrc);
    if (filtType !== 'all') list = list.filter((c) => String(c.type) === filtType);
    if (filtState !== 'all') {
      const jm = journalMap();
      list = list.filter((c) => {
        const st = jm.get(c.rpid);
        return filtState === 'none' ? !st : st === filtState;
      });
    }
    if (sortMode === 'tasc') list = [...list].sort((a, b) => (a.ctime || 0) - (b.ctime || 0));
    else if (sortMode === 'tdesc') list = [...list].sort((a, b) => (b.ctime || 0) - (a.ctime || 0));
    return list;
  }

  let viewSnap = [];      // 当前渲染快照
  let viewOffset = 0;     // 已渲染条数
  let ro = null;          // IntersectionObserver
  let kwTimer = null;

  function buildRow(c) {
    const row = document.createElement('div');
    row.className = `${P}-item`;
    row.dataset.rpid = String(c.rpid);

    const can = !!(c.oid && c.type);
    if (!can) selected.delete(c.rpid);
    const cb = document.createElement('input');
    cb.type = 'checkbox';
    cb.checked = can && selected.has(c.rpid);
    cb.disabled = !can;
    cb.title = can ? '' : '缺少 oid 或 type，不能删除';
    cb.dataset.rpid = String(c.rpid);
    row.appendChild(cb);

    const main = document.createElement('div');
    main.className = 'm';
    const msgDiv = document.createElement('div');
    msgDiv.textContent = c.message || '(空评论)';   // 安全：永远 textContent
    main.appendChild(msgDiv);

    const meta = document.createElement('div');
    meta.className = 'meta';
    meta.appendChild(document.createTextNode(`${typeText(c.type)} · ${fmtTime(c.ctime)} · rpid:${c.rpid} · ${SRC_TEXT[c.src] || c.src}`));
    const jm = journalMap();
    if (jm.has(c.rpid)) {
      const st = jm.get(c.rpid);
      const b = document.createElement('span');
      b.className = `${P}-mark`;
      b.textContent = st === 'ok' ? ' ·上次已删除✓' : st === 'fail' ? ' ·上次失败' : ' ·上次待确认';
      meta.appendChild(b);
    }
    if (!c.oid || !c.type) {
      const bad = document.createElement('span');
      bad.className = `${P}-nop`;
      bad.textContent = ' ·[缺 oid/type，无法操作]';
      meta.appendChild(bad);
    }
    main.appendChild(meta);
    row.appendChild(main);

    if (c.oid && c.type) {
      const jb = document.createElement('button');
      jb.className = `${P}-jump`;
      jb.textContent = '↗';
      jb.title = '新标签页打开评论所在页面';
      jb.dataset.act = 'jump';
      jb.dataset.rpid = String(c.rpid);
      row.appendChild(jb);
    }
    return row;
  }

  function appendChunk() {
    const listEl = document.getElementById(`${P}-list`);
    if (!listEl || viewOffset >= viewSnap.length) return;
    const slice = viewSnap.slice(viewOffset, viewOffset + RENDER_CHUNK);
    const frag = document.createDocumentFragment();
    for (const c of slice) frag.appendChild(buildRow(c));
    const sent = listEl.querySelector(`#${P}-sentinel`);
    listEl.insertBefore(frag, sent);
    viewOffset += slice.length;
    updateSentinel();
  }

  function updateSentinel() {
    const sent = document.getElementById(`${P}-sentinel`);
    if (!sent) return;
    if (viewOffset >= viewSnap.length) {
      if (ro) { ro.disconnect(); ro = null; }
      if (sent.parentNode) sent.parentNode.removeChild(sent);
    } else {
      sent.textContent = `下滑加载更多（${viewOffset}/${viewSnap.length} 已渲染）…`;
    }
  }

  function renderList() {
    const listEl = document.getElementById(`${P}-list`);
    if (!listEl) return;
    const keep = listEl.scrollTop;
    if (ro) { ro.disconnect(); ro = null; }
    viewSnap = visibleComments();
    viewOffset = 0;
    listEl.innerHTML = '';

    if (!viewSnap.length) {
      const d = document.createElement('div');
      d.className = `${P}-empty`;
      d.textContent = comments.length && (filterKw || filtSrc !== 'all' || filtType !== 'all' || filtState !== 'all')
        ? '当前筛选无匹配。' : '暂无评论数据。';
      listEl.appendChild(d);
      updCount();
      return;
    }

    const sent = document.createElement('div');
    sent.id = `${P}-sentinel`;
    sent.className = `${P}-sent`;
    sent.addEventListener('click', appendChunk);
    listEl.appendChild(sent);

    if ('IntersectionObserver' in window) {
      ro = new IntersectionObserver((es) => {
        if (es.some((e) => e.isIntersecting)) appendChunk();
      }, { root: listEl, rootMargin: '140px' });
      ro.observe(sent);
    }
    appendChunk();
    while (keep > 0 && viewOffset < viewSnap.length && listEl.scrollHeight <= keep + listEl.clientHeight) appendChunk();
    updCount();
    listEl.scrollTop = keep;
  }

  function updCount() {
    const shown = visibleComments();
    const vis = shown.filter((c) => c.oid && c.type);
    const nSel = shown.filter((c) => selected.has(c.rpid)).length;
    const jm = journalMap();
    let okN = 0, failN = 0, uncN = 0;
    for (const c of vis) {
      const st = jm.get(c.rpid);
      if (st === 'ok') okN++;
      else if (st === 'fail') failN++;
      else if (st === 'uncertain') uncN++;
    }
    const nDel = shown.filter((c) => c.oid && c.type && selected.has(c.rpid)).length;
    const dsel = document.getElementById(`${P}-dsel`);
    const dall = document.getElementById(`${P}-dall`);
    if (dsel) { dsel.disabled = !nDel || deleting || fetching; dsel.textContent = `🔥 删除选中 (${nDel})`; }
    if (dall) {
      dall.disabled = !vis.length || deleting || fetching;
      dall.textContent = `${filtersOn() ? '💣 删除当前' : '💣 删除全部'} (${vis.length})`;
      dall.title = filtersOn() ? '只删除当前筛选里能删的评论，不会动被筛掉的' : '删除列表里能删的全部评论';
    }
    const copyBtn = document.getElementById(`${P}-copybad`);
    if (copyBtn) {
      let bad = 0;
      for (const c of comments) {
        const st = jm.get(Number(c.rpid));
        if (st === 'fail' || st === 'uncertain') bad++;
      }
      copyBtn.style.display = bad && !deleting ? 'inline-block' : 'none';
      copyBtn.textContent = `复制未成功 (${bad})`;
    }
    const cnt = document.getElementById(`${P}-cnt`);
    if (cnt) cnt.textContent = `${nSel}/${vis.length} · 已删${okN} 失败${failN} 待确认${uncN}`;
  }

  function onFilter(live) {
    const next = document.getElementById(`${P}-kw`).value.trim();
    if (live && next === filterKw) return;
    filterKw = next;
    renderList();
    if (!live) setStatus(filterKw ? `已按「${filterKw}」筛选。` : '已清除关键词。');
  }

  function armStop(on) {
    const el = document.getElementById(`${P}-stop`);
    if (!el) return;
    el.style.display = on ? 'inline-block' : 'none';
    el.disabled = !on;
  }

  /* ═══════════ 控制器：枚举 ═══════════ */
  function requireLogin() {
    const uid = getCookie('DedeUserID');
    const csrf = getCookie('bili_jct');
    return (uid && csrf) ? uid : null;
  }

  async function loadAicu() {
    const myUid = requireLogin();
    if (!myUid) { setStatus('❌ 未检测到登录态，无法枚举。请先登录 bilibili.com 并刷新。'); return; }
    const btn = document.getElementById(`${P}-load`);
    btn.disabled = true; fetching = true; aborted = false;
    document.getElementById(`${P}-hist`).disabled = true;
    armStop(true);
    setStatus('AICU 枚举中…（每页 500 条，间隔 3s 防风控）');
    showProg(true);
    try {
      log(`开始 AICU 枚举 UID=${myUid}`);
      datasetUid = myUid;
      await fetchAicuComments(myUid);
      renderList(); updCount();
      setStatus(`✅ AICU 枚举完成：累计 ${comments.length} 条（去重）。${digestLine()}`);
      log(`✅ AICU 枚举完成，累计 ${comments.length} 条`, 'ok');
    } catch (e) {
      setStatus(`❌ 枚举失败：${e.message}`);
      log(`枚举失败: ${e.message}`, 'err');
    } finally {
      btn.disabled = false; fetching = false;
      document.getElementById(`${P}-hist`).disabled = false;
      armStop(false);
      showProg(false);
      updCount();
    }
  }

  async function loadHistory() {
    const myUid = requireLogin();
    if (!myUid) { setStatus('❌ 未登录，官方历史扫描需要登录态。'); return; }
    const btn = document.getElementById(`${P}-hist`);
    btn.disabled = true; fetching = true; aborted = false;
    document.getElementById(`${P}-load`).disabled = true;
    armStop(true);
    setStatus('官方历史扫描：翻历史 → 逐视频扫评论（仅视频，aicu 的兜底）…');
    showProg(true);
    try {
      if (datasetUid && datasetUid !== myUid) log(`⚠️ 列表属于 UID=${datasetUid}，本次扫描账号 UID=${myUid}`, 'warn');
      else if (!datasetUid) datasetUid = myUid;
      const scanPages = Number(localStorage.getItem(`${P}_scanpages`)) || VIDEO_SCAN_PAGES_DEFAULT;
      log(`开始官方历史扫描 UID=${myUid}（每视频 ${scanPages} 页）`);
      await fetchHistoryComments(myUid, scanPages);
      renderList(); updCount();
      setStatus(`✅ 官方扫描完成：累计 ${comments.length} 条。${digestLine()}`);
      log(`✅ 官方历史扫描完成`, 'ok');
    } catch (e) {
      setStatus(`❌ 官方扫描失败：${e.message}`);
      log(`官方扫描失败: ${e.message}`, 'err');
    } finally {
      btn.disabled = false; fetching = false;
      document.getElementById(`${P}-load`).disabled = false;
      armStop(false);
      showProg(false);
      updCount();
    }
  }

  function onImport() {
    const raw = document.getElementById(`${P}-ta`).value.trim();
    if (!raw) { setStatus('请先粘贴 JSON 内容。'); return; }
    const r = importJson(raw);
    renderList();
    setStatus(r.ok ? `✅ ${r.msg}（来源标记：导入）。${digestLine()}` : `❌ ${r.msg}`);
    log(r.ok ? `导入: ${r.msg}` : `导入失败: ${r.msg}`, r.ok ? 'ok' : 'err');
  }

  function lockWhileDeleting(locked) {
    ['dsel', 'dall', 'retry', 'copybad', 'load', 'hist', 'import', 'reset'].forEach((k) => {
      const el = document.getElementById(`${P}-${k}`);
      if (el) el.disabled = locked;
    });
  }

  /* ═══════════ 控制器：删除 ═══════════ */
  async function runDelete(mode, explicitTargets, scopeLabel) {
    let targets, scope;
    if (mode === 'explicit' && explicitTargets) {
      targets = explicitTargets; scope = scopeLabel || '重试';
    } else if (mode === 'all') {
      targets = visibleComments().filter((c) => c.oid && c.type);
      scope = filtersOn() ? '当前筛选' : '全部列表';
    } else {
      targets = visibleComments().filter((c) => c.oid && c.type && selected.has(c.rpid));
      scope = '筛选下选中';
    }
    let skippedOk = 0;
    const skipBox = document.getElementById(`${P}-skipok`);
    if (skipBox && skipBox.checked) {
      const jm = journalMap();
      const kept = [];
      for (const c of targets) {
        if (jm.get(Number(c.rpid)) === 'ok') skippedOk++;
        else kept.push(c);
      }
      targets = kept;
    }
    if (!targets.length) {
      setStatus(skippedOk ? `没有待删除项。已跳过 ${skippedOk} 条日志里已确认删除的。` : '没有可删除的评论。');
      return;
    }

    const csrf = getCookie('bili_jct');
    if (!csrf) { setStatus('❌ 未检测到 bili_jct（登录态），请先登录并刷新页面。'); return; }

    // 换号防护：列表枚举账号与当前登录账号不一致时，明确提醒
    const curUid = getCookie('DedeUserID');
    if (datasetUid && curUid && datasetUid !== curUid) {
      if (!(await ask(`列表来自 UID=${datasetUid}，当前登录 UID=${curUid}。\n删除只会作用于当前登录账号自己的评论。\n继续这 ${targets.length} 条？`, '继续'))) return;
    }
    const recheckOn = document.getElementById(`${P}-recheck`).checked;
    const delay = Math.max(200, parseInt(document.getElementById(`${P}-delay`).value, 10) || DELAY_DEFAULT);
    const per = delay + (recheckOn ? 600 : 0);
    const sample = String(targets[0].message || '(空评论)').replace(/\s+/g, ' ').slice(0, 36);
    const skipNote = skippedOk ? `\n已跳过 ${skippedOk} 条已确认删除。` : '';
    if (!(await ask(`即将删除 ${targets.length} 条（${scope}）。\n间隔 ${delay}ms，回查${recheckOn ? '开' : '关'}，预计 ${fmtEta(targets.length * per)}。${skipNote}\n首条：${sample}\n\n不可撤销。`, '删除'))) return;

    deleting = true; aborted = false;
    batchResults = new Map();
    recheckCache = new Map(); threadCache = new Map();   // 回查缓存仅批次内有效
    const retryBtn = document.getElementById(`${P}-retry`);
    if (retryBtn) { retryBtn.style.display = 'none'; }

    lockWhileDeleting(true);
    armStop(true);
    showProg(true);
    const t0 = Date.now();
    log(`🔥 开始删除 ${targets.length} 条（${scope}），间隔 ${delay}ms，回查${recheckOn ? '开' : '关'}`, 'warn');

    let ok = 0, fail = 0, uncertain = 0, shadowFixed = 0;
    const pending = [];           // 已提交删除、留待统一回查的条目
    for (let i = 0; i < targets.length; i++) {
      if (aborted) { log('⏹ 已停止', 'warn'); break; }
      const c = targets[i];
      markActive(c.rpid);
      setProg(i, targets.length, '①删除');
      const leftDel = (targets.length - i) * delay + (recheckOn ? targets.length * 600 : 0);
      setStatus(`①删除 ${i + 1}/${targets.length} · ${String(c.message || '(空)').replace(/\s+/g, ' ').slice(0, 22)} · 剩余 ${fmtEta(leftDel)}`);

      let result = null;          // 'ok' | 'uncertain' | 'fail'
      let submittedPending = false;
      let attempt = 0;
      while (attempt < DELETE_MAX_RETRY) {
        if (aborted) break;
        let j = null;
        try { j = await doDelete(c, csrf); }
        catch (e) { result = 'fail'; log(`✗ 请求异常 rpid=${c.rpid} ${e.message}`, 'err'); break; }
        const codeStr = String(j.code);
        if (j.code === 0 || j.code === 12022 || j.code === -404) {
          if (!recheckOn) {
            result = 'ok';
            log(j.code === 0 ? `✓ 已提交删除 rpid=${c.rpid}` : `• ${j.code}：评论已不存在 rpid=${c.rpid}`);
          } else {
            submittedPending = true;
            log(`${j.code === 0 ? '✓' : '•'} ${j.code === 0 ? '接口已受理（不等于已删）' : `接口${j.code}（视为已不存在）`}，待官方确认 rpid=${c.rpid}`);
          }
          break;
        }
        if (j.code === -509) {
          const wait = 2000 * (attempt + 1);
          setStatus(`限流 -509，${Math.round(wait / 1000)}s 后重试 ${attempt + 1}/${DELETE_MAX_RETRY - 1} · rpid=${c.rpid}`);
          log(`⏳ 限流 -509，${wait}ms 后重试（${attempt + 1}/${DELETE_MAX_RETRY - 1}）…`, 'warn');
          await sleep(wait); attempt++;
          continue;
        }
        result = 'fail';
        log(`✗ rpid=${c.rpid} code=${j.code} ${j.message || ERR_TEXT[codeStr] || ''}`, 'err');
        break;
      }
      if (!result && !submittedPending) {   // 限流耗尽 / 中途停止 → 显式记录（不是静默漏计）
        result = aborted ? 'uncertain' : 'fail';
        log(aborted ? `⏹ 停止于 rpid=${c.rpid}（按待确认处理，可重试）`
                    : `✗ rpid=${c.rpid} 连续 ${DELETE_MAX_RETRY - 1} 次限流后放弃（可用「重试未成功」）`, 'err');
      }
      if (result) {
        batchResults.set(c.rpid, result);
        journalAdd(c.rpid, result);
        if (result === 'ok') ok++; else if (result === 'uncertain') uncertain++; else fail++;
      } else {
        pending.push(c);
      }
      await sleep(delay);
    }

    // ── 统一回查（v2.2.2：单条官方接口；仍在则降速重删；walk 仅兜底） ──
    if (pending.length) {
      setStatus(`②回查 0/${pending.length} · 官方单条确认中…`);
      log(`🔍 统一回查 ${pending.length} 条（先 /reply/detail 单条；不可用才全区/整楼翻页）`);
      for (let i = 0; i < pending.length; i++) {
        if (aborted) break;
        const c = pending[i];
        markActive(c.rpid);
        setProg(i, pending.length, '②回查');
        setStatus(`②回查 ${i + 1}/${pending.length} · ${String(c.message || '(空)').replace(/\s+/g, ' ').slice(0, 22)} · 已确认 ${ok} · 剩余 ${fmtEta((pending.length - i) * 600)}`);
        let v = null;
        try { v = await recheckDefinitive(c); } catch (e) { v = null; }
        if (v && v.state === 'fail' && !aborted) {
          for (let s = 0; s < SHADOW_RETRY; s++) {
            setStatus(`↻ 影子重试 ${s + 1}/${SHADOW_RETRY} · rpid=${c.rpid}（接口回成功但评论仍在）`);
            log(`↻ 评论仍在，降速重试 ${s + 1}/${SHADOW_RETRY} rpid=${c.rpid}`, 'warn');
            await sleep(SHADOW_WAIT);
            try { await doDelete(c, csrf); } catch (e) { break; }
            await sleep(800);
            let again = null;
            try { again = await oracleCheck(c); } catch (e) { again = null; }
            if (again && again.state === 'ok') {
              v = { state: 'ok', why: `影子失败后第${s + 1}次重试已确认删除` };
              shadowFixed++;
              break;
            }
            if (again && again.state === 'fail') v = again;
          }
        }
        let state, msg;
        if (!v || !v.state) { state = 'uncertain'; msg = `回查不可用（区/楼接口异常），↗跳转复核`; }
        else if (v.state === 'ok') { state = 'ok'; msg = `已确认删除（${v.why}）`; }
        else if (v.state === 'fail') { state = 'fail'; msg = `未生效（${v.why}）`; }
        else { state = 'uncertain'; msg = v.why; }
        batchResults.set(c.rpid, state);
        journalAdd(c.rpid, state);
        if (state === 'ok') ok++; else if (state === 'uncertain') uncertain++; else fail++;
        log(`${state === 'ok' ? '✓' : state === 'fail' ? '✗' : '～'} rpid=${c.rpid} ${msg}`,
            state === 'ok' ? 'ok' : state === 'fail' ? 'err' : 'warn');
        await sleep(150);
      }
    }

    markActive(null);
    setProg(targets.length, targets.length, aborted ? '已停止' : '完成');
    const sec = Math.max(1, Math.round((Date.now() - t0) / 1000));
    let focusNote = '';
    if (fail > 0) {
      filtState = 'fail';
      const sel = document.getElementById(`${P}-statesel`);
      if (sel) sel.value = 'fail';
      focusNote = ' 列表已切到「未生效」。';
    } else if (uncertain > 0) {
      filtState = 'uncertain';
      const sel = document.getElementById(`${P}-statesel`);
      if (sel) sel.value = 'uncertain';
      focusNote = ' 列表已切到「待确认」。';
    }
    const sum = `${aborted ? '已停止。' : '完成：'}确认删除 ${ok}，未生效 ${fail}，待确认 ${uncertain}${shadowFixed ? `（影子重试救回 ${shadowFixed}）` : ''}。用时 ${sec}s。${focusNote}`;
    setStatus(sum);
    log(`==== ${sum} ====`, fail ? 'warn' : 'ok');
    deleting = false;
    lockWhileDeleting(false);
    armStop(false);
    renderList(); updCount();

    if (fail + uncertain > 0) {
      const rb = document.getElementById(`${P}-retry`);
      rb.textContent = `↻ 重试未成功(${fail + uncertain})`;
      rb.style.display = 'inline-block';
    }
  }

  /* ═══════════ 小部件 ═══════════ */
  function log(msg, type) {
    const el = document.getElementById(`${P}-log`);
    if (!el) return;
    const d = document.createElement('div');
    d.className = `${P}-log-line ${P}-${type || 'info'}`;
    if (logOnlyBad && type !== 'err' && type !== 'warn') d.classList.add(`${P}-log-hide`);
    d.textContent = `[${new Date().toLocaleTimeString('zh-CN', { hour12: false })}] ${msg}`;
    const stick = el.scrollHeight - el.scrollTop - el.clientHeight < 48;
    el.appendChild(d);
    while (el.children.length > 300) el.removeChild(el.firstChild);
    if (stick) el.scrollTop = el.scrollHeight;
  }
  function setStatus(t) { const el = document.getElementById(`${P}-status`); if (el) el.textContent = t; }

  function digestLine() {
    const by = new Map();
    let ok = 0, bad = 0, nodeal = 0;
    const jm = journalMap();
    for (const c of comments) {
      const name = typeText(c.type);
      by.set(name, (by.get(name) || 0) + 1);
      const st = jm.get(Number(c.rpid));
      if (st === 'ok') ok++;
      else if (st === 'fail' || st === 'uncertain') bad++;
      if (!c.oid || !c.type) nodeal++;
    }
    const parts = [...by.entries()].sort((a, b) => b[1] - a[1]).slice(0, 4).map(([k, v]) => `${k} ${v}`);
    const extra = [];
    if (ok) extra.push(`已确认 ${ok}`);
    if (bad) extra.push(`未成功 ${bad}`);
    if (nodeal) extra.push(`无法删除 ${nodeal}`);
    return ` ${parts.join(' · ')}${extra.length ? ' · ' + extra.join(' · ') : ''}`;
  }

  function ask(text, okLabel) {
    return new Promise((resolve) => {
      const mask = document.getElementById(`${P}-ask`);
      const msg = document.getElementById(`${P}-askmsg`);
      const ok = document.getElementById(`${P}-askok`);
      const no = document.getElementById(`${P}-askno`);
      if (!mask || !msg || !ok || !no) { resolve(false); return; }
      msg.textContent = text;
      ok.textContent = okLabel || '确认';
      mask.style.display = 'flex';
      const done = (v) => {
        mask.style.display = 'none';
        ok.onclick = null;
        no.onclick = null;
        document.removeEventListener('keydown', onKey, true);
        resolve(v);
      };
      const onKey = (e) => {
        if (e.key !== 'Escape') return;
        e.preventDefault();
        e.stopPropagation();
        done(false);
      };
      ok.onclick = () => done(true);
      no.onclick = () => done(false);
      document.addEventListener('keydown', onKey, true);
      no.focus();
    });
  }
  function touchList(force) {
    const now = Date.now();
    if (!force && now - lastListPaint < 800) return;
    lastListPaint = now;
    renderList();
  }
  function showProg(show) {
    const el = document.getElementById(`${P}-prog`);
    if (!el) return;
    el.style.display = show ? 'flex' : 'none';
    if (show) {
      document.getElementById(`${P}-fill`).style.width = '0%';
      document.getElementById(`${P}-pct`).textContent = '0%';
    }
  }
  function setProg(done, total, phase) {
    const pct = total ? Math.round((done / total) * 100) : 0;
    const fill = document.getElementById(`${P}-fill`);
    const pctEl = document.getElementById(`${P}-pct`);
    if (fill) fill.style.width = pct + '%';
    if (pctEl) pctEl.textContent = `${phase ? phase + ' ' : ''}${pct}% (${done}/${total})`;
  }

  /* ═══════════ 初始化 ═══════════ */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => { injectCSS(); buildUI(); });
  } else {
    injectCSS(); buildUI();
  }
})();