// ==UserScript==
// @name         B站评论批量删除 v2.2（全面优化版）
// @namespace    bilibili-comment-deleter
// @version      2.2.128
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
  const VERSION = '2.2.128';
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
  const HISTORY_THREAD_OPEN_MAX = 8;  // 每个视频最多再补几条楼的第一页
  const HISTORY_THREAD_PS = 20;       // 补楼中楼时第一页条数
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
  const byRpid = new Map();           // 规范 rpid → 已收录评论
  let datasetUid = '';                // 枚举时所属 UID（防换号误解）
  let selected = new Set();
  let anchorRpid = 0;
  let filterKw = '';                  // 关键词
  let onlyClash = false;
  let filtSrc = 'all';
  let filtType = 'all';
  let filtState = 'all';          // all | ok | fail | uncertain | none
  let sortMode = 'default';           // default | tasc | tdesc
  let fetching = false;
  let logOnlyBad = false;
  let journalTrimWarned = false;
  let lastListPaint = 0;
  let savedTitle = '';
  let deleting = false;
  let confirming = false;
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
  function fmtDur(ms) {
    const s = Math.max(0, Math.round(ms / 1000));
    if (s < 60) return `${s} 秒`;
    const m = Math.floor(s / 60);
    const r = s % 60;
    return r ? `${m} 分 ${r} 秒` : `${m} 分`;
  }
  function fmtAgo(ms) {
    const s = Math.max(0, Math.round(ms / 1000));
    if (s < 60) return `${s} 秒`;
    const m = Math.round(s / 60);
    if (m < 60) return `${m} 分`;
    const h = Math.round(m / 60);
    if (h < 48) return `${h} 小时`;
    return `${Math.round(h / 24)} 天`;
  }
  function saveLastRun(text) {
    try {
      const full = String(text);
      const cut = full.length > 400;
      localStorage.setItem(`${P}_lastrun`, JSON.stringify({
        t: Date.now(),
        text: cut ? `${full.slice(0, 399)}…` : full,
        cut,
      }));
    } catch (e) { /* 存不下就只留在这一页 */ }
  }
  function lastRunNote() {
    try {
      const o = JSON.parse(localStorage.getItem(`${P}_lastrun`) || 'null');
      if (!o || !o.text) return '';
      const cut = o.cut || String(o.text).length >= 400;
      return ` 上次（${fmtAgo(Date.now() - (o.t || Date.now()))}前）${cut ? '，只留了前一段' : ''}：${o.text}`;
    } catch (e) { return ''; }
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

  function parseJsonKeepIds(text) {
    const src = String(text);
    let out = '';
    let i = 0;
    let inStr = false;
    let esc = false;
    while (i < src.length) {
      const ch = src[i];
      if (inStr) {
        out += ch;
        if (esc) esc = false;
        else if (ch === '\\') esc = true;
        else if (ch === '"') inStr = false;
        i++;
        continue;
      }
      if (ch === '"') { inStr = true; out += ch; i++; continue; }
      if (ch === '-' || (ch >= '0' && ch <= '9')) {
        const start = i;
        if (ch === '-') i++;
        const digits = i;
        while (i < src.length && src[i] >= '0' && src[i] <= '9') i++;
        const n = i - digits;
        const rest = src[i];
        const isInt = n > 0 && rest !== '.' && rest !== 'e' && rest !== 'E';
        const token = src.slice(start, i);
        if (isInt && n >= 16 && src[start] !== '-') out += `"${src.slice(digits, i)}"`;
        else out += token;
        continue;
      }
      out += ch;
      i++;
    }
    return JSON.parse(out);
  }
  function parseJsonRes(r) {
    const text = r && typeof r.responseText === 'string' ? r.responseText : '';
    if (text.trim()) {
      try { return parseJsonKeepIds(text); }
      catch (e) { throw new Error('非 JSON 响应 (HTTP ' + ((r && r.status) || '?') + ')'); }
    }
    const j = r && r.response;
    if (j && typeof j === 'object') return j;
    throw new Error('非 JSON 响应 (HTTP ' + ((r && r.status) || '?') + ')');
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
    catch (e) { j = explainNonJson(r); }
    return j;
  }

  function explainNonJson(r) {
    const text = String((r && r.responseText) || '');
    const status = (r && r.status) || '?';
    if (status === 412 || /<\s*html|waf|captcha/i.test(text.slice(0, 500))) {
      return { code: -9000, message: `返回了网页而不是接口数据（HTTP ${status}），多半是风控` };
    }
    if (!text.trim()) return { code: -9000, message: `空响应（HTTP ${status}）` };
    return { code: -9000, message: `无法解析响应（HTTP ${status}）` };
  }

  /* ═══════════ 处理日志（localStorage 持久化） ═══════════ */
  const JKEY = `${P}_journal`;
  let journalWhyCache = null;
  let journalMapCache = null;

  function journalLoad() {
    try { return JSON.parse(localStorage.getItem(JKEY) || '[]'); } catch (e) { return []; }
  }
  function journalMap() {
    if (journalMapCache) return journalMapCache;
    const m = new Map();
    for (const e of journalLoad()) {
      const id = idExact(e.rpid);
      if (!id || m.has(id)) continue;
      m.set(id, e.state);
    }
    journalMapCache = m;
    return m;
  }

  function journalStats() {
    const m = journalMap();
    let ok = 0, bad = 0;
    for (const st of m.values()) {
      if (st === 'ok') ok++;
      else if (st === 'fail' || st === 'uncertain') bad++;
    }
    return { n: m.size, ok, bad };
  }
  function journalCompact(list) {
    const seen = new Set();
    const out = [];
    for (const e of list || []) {
      const id = idExact(e && e.rpid);
      if (!id || seen.has(id)) continue;
      seen.add(id);
      const why = clipWhy(e.why);
      out.push(why ? { rpid: id, state: e.state, t: e.t || 0, why } : { rpid: id, state: e.state, t: e.t || 0 });
    }
    return out;
  }

  let journalCompactNote = '';
  function journalNormalize() {
    try {
      const raw = journalLoad();
      const next = journalCompact(raw).slice(0, JOURNAL_CAP);
      if (next.length === raw.length) return;
      localStorage.setItem(JKEY, JSON.stringify(next));
      journalMapCache = null; journalWhyCache = null;
      const dropped = raw.length - next.length;
      if (dropped > 0) journalCompactNote = ` 已合并 ${dropped} 条重复记录。`;
    } catch (e) { /* 打不开就不改 */ }
  }

  function clipWhy(s) {
    const t = String(s || '').replace(/\s+/g, ' ').trim();
    return t.length > 160 ? `${t.slice(0, 159)}…` : t;
  }
  function journalWhy(rpid) {
    if (!journalWhyCache) {
      journalWhyCache = new Map();
      for (const e of journalLoad()) {
        const id = idExact(e.rpid);
        if (!id || journalWhyCache.has(id) || !e.why) continue;
        journalWhyCache.set(id, clipWhy(e.why));
      }
    }
    return journalWhyCache.get(idExact(rpid)) || '';
  }
  function journalAdd(rpid, state, why) {
    const note = clipWhy(why);
    try {
      const id = idExact(rpid);
      if (!id) return;
      const j = journalCompact(journalLoad()).filter((e) => e.rpid !== id);
      const row = { rpid: id, state, t: Date.now() };
      if (note) row.why = note;
      j.unshift(row);
      if (j.length > JOURNAL_CAP && !journalTrimWarned) {
        journalTrimWarned = true;
        log(`处理记录超过 ${JOURNAL_CAP} 条，更早的已丢弃。那些评论再出现时不会被当成已删除。`, 'warn');
      }
      localStorage.setItem(JKEY, JSON.stringify(j.slice(0, JOURNAL_CAP)));
      journalMapCache = null; journalWhyCache = null;
    } catch (e) {
      journalMapCache = null; journalWhyCache = null;
      if (!journalTrimWarned) {
        journalTrimWarned = true;
        setStatus('浏览器拒绝保存处理记录，刷新后已确认状态可能丢失。');
        log(`处理记录写入失败：${e.message}`, 'err');
      }
    }
    paintMark(rpid, state, note);
  }

  /** 已渲染行即时改徽标，不必等整批结束再重绘列表 */
  function paintMark(rpid, state, why) {
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
    const note = clipWhy(why);
    if (note) b.title = note;
    else b.removeAttribute('title');
  }

  /** 标出正在处理的行，并只在列表内部滚动，不带动整页 */
  function markActive(rpid) {
    const list = document.getElementById(`${P}-list`);
    if (!list) return;
    const prev = list.querySelector(`.${P}-item.${P}-hot`);
    if (prev) prev.classList.remove(`${P}-hot`);
    if (rpid == null) return;
    let row = list.querySelector(`.${P}-item[data-rpid="${rpid}"]`);
    if (!row) {
      const idx = viewSnap.findIndex((c) => String(c.rpid) === String(rpid));
      let guard = 0;
      while (idx >= 0 && viewOffset <= idx && guard < 30) { appendChunk(); guard++; }
      row = list.querySelector(`.${P}-item[data-rpid="${rpid}"]`);
    }
    if (!row) return;
    row.classList.add(`${P}-hot`);
    const lr = list.getBoundingClientRect();
    const rr = row.getBoundingClientRect();
    if (rr.top < lr.top) list.scrollTop -= (lr.top - rr.top + 8);
    else if (rr.bottom > lr.bottom) list.scrollTop += (rr.bottom - lr.bottom + 8);
  }

  /* ═══════════ 数据层 ═══════════ */
  let filledRows = 0;
  let filledMeta = 0;
  let rootClash = 0;
  let placeClash = 0;
  let filledSrc = 0;
  let srcClash = 0;
  let restoredMarks = 0;
  function resetFillStats() {
    filledRows = 0;
    filledMeta = 0;
    rootClash = 0;
    placeClash = 0;
    filledSrc = 0;
    srcClash = 0;
    restoredMarks = 0;
  }
  function flagOn(v) {
    if (v === true || v === 1) return true;
    const s = String(v == null ? '' : v).trim().toLowerCase();
    return s === '1' || s === 'true' || s === 'yes' || s === '是';
  }
  function hasClash(c) {
    return !!(c && (c.placeClash || c.rootConflict || c.srcConflict));
  }
  function idExact(v) {
    if (v == null || v === '') return 0;
    const s = String(v).trim();
    if (!/^\d+$/.test(s)) return 0;
    const canon = BigInt(s).toString();
    if (canon === '0') return 0;
    if (BigInt(canon) <= BigInt(Number.MAX_SAFE_INTEGER)) return Number(canon);
    return canon;
  }
  function rpidKey(v) {
    const id = idExact(v);
    return id ? String(id) : '';
  }
  function cursorId(v) {
    if (typeof v === 'number' && Number.isFinite(v)) return String(v);
    if (typeof v === 'string' && /^\d+$/.test(v.trim())) return v.trim().replace(/^0+(?=\d)/, '');
    return '';
  }
  function addIfAbsent(item) {
    if (!item || !item.oid || !item.type) return false;
    item.rpid = idExact(item.rpid);
    const key = rpidKey(item.rpid);
    if (!key) return false;
    const cur = byRpid.get(key);
    if (cur) {
      const nextMsg = String(item.message || '');
      const curMsg = String(cur.message || '');
      if (nextMsg.length > curMsg.length) {
        cur.message = nextMsg;
        cur.cut = !!item.cut;
        filledRows++;
      } else if (item.cut && !cur.cut && nextMsg.length === curMsg.length && nextMsg.length > 0) {
        cur.cut = true;
        filledRows++;
      }
      let meta = false;
      const nextRoot = rpidKey(item.root);
      const curRoot = rpidKey(cur.root);
      if (!curRoot && nextRoot) { cur.root = idExact(item.root); meta = true; }
      else if (curRoot && nextRoot && curRoot !== nextRoot && !cur.rootConflict) {
        cur.rootConflict = true;
        rootClash++;
      }
      const nextTime = Number(item.ctime) || 0;
      if (!Number(cur.ctime) && nextTime) { cur.ctime = nextTime; meta = true; }
      let marked = false;
      if (item.placeClash && !cur.placeClash) { cur.placeClash = true; marked = true; }
      if (item.rootConflict && !cur.rootConflict) { cur.rootConflict = true; marked = true; }
      const realSrc = (s) => !!(s && s !== 'import');
      if (!realSrc(cur.src) && realSrc(item.src)) { cur.src = item.src; filledSrc++; }
      else if (realSrc(cur.src) && realSrc(item.src) && cur.src !== item.src && !cur.srcConflict) {
        cur.srcConflict = true;
        srcClash++;
      }
      if (item.srcConflict && !cur.srcConflict) { cur.srcConflict = true; marked = true; }
      if (marked) restoredMarks++;
      const nextOid = rpidKey(item.oid);
      const curOid = rpidKey(cur.oid);
      const nextType = Number(item.type) || 0;
      const curType = Number(cur.type) || 0;
      if (!cur.placeClash && ((nextOid && curOid && nextOid !== curOid) || (nextType && curType && nextType !== curType))) {
        cur.placeClash = true;
        placeClash++;
      }
      if (meta) filledMeta++;
      return false;
    }
    comments.push(item);
    rpidSet.add(item.rpid);
    byRpid.set(key, item);
    return true;
  }

  function resetDataset() {
    comments = [];
    rpidSet.clear();
    byRpid.clear();
    selected.clear();
    datasetUid = '';
    batchResults = null;
    filterKw = ''; filtSrc = 'all'; filtType = 'all'; filtState = 'all'; onlyClash = false; sortMode = 'default';
    syncFilterControls();
    const rb = document.getElementById(`${P}-retry`);
    if (rb) rb.style.display = 'none';
    renderList(); updCount();
    saveSettings();
  }

  function clipMessage(s) {
    const full = String(s || '');
    return { message: full.slice(0, 200), cut: full.length > 200 };
  }

  /** aicu 条目、原始单页，或本工具自己导出的扁对象 → 规范对象 */
  function mapAicuReply(it) {
    const rpid = idExact(it && it.rpid);
    const dyn = (it && it.dyn) || {};
    const oid = idExact((dyn && dyn.oid) || (it && it.oid));
    const type = Number((dyn && dyn.type) || (it && it.type));
    if (!rpid || !oid || !type) return null;
    const parent = (it && it.parent) || {};
    const clip = clipMessage(it && it.message);
    return {
      rpid,
      oid,
      type,
      message: clip.message,
      cut: clip.cut || flagOn(it && it.cut),
      placeClash: flagOn(it && it.placeClash),
      rootConflict: flagOn(it && it.rootConflict),
      srcConflict: flagOn(it && it.srcConflict),
      ctime: Number((it && (it.time || it.ctime)) || 0) || 0,
      root: parent.rootid ? idExact(parent.rootid) : (idExact(it && it.root) || 0),
      src: 'aicu',
    };
  }

  /* 枚举/扫描等待时每秒刷新已用时间。aborted 后不再改状态行。 */
  let beatTimer = 0;
  function startBeat(textFn) {
    stopBeat();
    const paint = () => {
      const text = textFn();
      if (!text || aborted) return;
      paintStatus(text);
      paintBusy(text);
    };
    paint();
    beatTimer = setInterval(paint, 1000);
  }
  function stopBeat() {
    if (beatTimer) clearInterval(beatTimer);
    beatTimer = 0;
  }
  async function waitTick(ms, textFn) {
    if (!(ms >= 1000)) { await sleep(ms); return; }
    const until = Date.now() + ms;
    try {
      startBeat(() => {
        if (aborted) return '';
        const left = Math.max(0, Math.ceil((until - Date.now()) / 1000));
        return textFn(left);
      });
      await sleep(ms);
    } finally { stopBeat(); }
  }

  /* ═══════════ 枚举一：AICU 自动拉取 ═══════════ */
  async function fetchAicuComments(uid) {
    const t0 = Date.now();
    let page = 1;
    let aicuUrl = AICU_APIS[0];
    let total = 0;
    let got = 0;
    let hop = '';
    let stopReason = '';
    resetFillStats();
    const spent = () => fmtDur(Date.now() - t0);
    const before = comments.length;
    const fresh = () => comments.length - before;

    try {
    while (true) {
      if (aborted) break;
      startBeat(() => `${hop ? hop + ' · ' : ''}枚举第 ${page} 页请求中 · 这次 +${fresh()}${total ? '/' + total : ''} · 已用 ${spent()}`);
      const url = `${aicuUrl}?uid=${encodeURIComponent(uid)}&pn=${page}&ps=${AICU_PS}&mode=0`;
      let data;
      try {
        data = await gmGetJSON(url, { timeoutMs: 20000, retries: 1 });
      } catch (e) {
        if (aicuUrl === AICU_APIS[0]) {
          hop = `主接口失败（${e.message}），改备用`;
          log(`主接口失败（${e.message}），切换备用…`, 'warn');
          aicuUrl = AICU_APIS[1];
          continue;
        }
        throw e;
      }

      if (data.code !== 0) {
        if (aicuUrl === AICU_APIS[0]) {
          hop = `主接口返回 code=${data.code}，改备用`;
          log(`主接口返回 code=${data.code}，切换备用…`, 'warn');
          aicuUrl = AICU_APIS[1];
          continue;
        }
        stopReason = `接口错误：${data.message || data.code}。后面的页没有继续。`;
        log(`AICU 错误: ${data.message || data.code}`, 'err');
        break;
      }

      if (page === 1) {
        total = (data.data && data.data.cursor && data.data.cursor.all_count) || 0;
        log(total ? `AICU 索引共 ${total} 条，开始拉取` : 'AICU 未给出总数，开始拉取');
        log('AICU 是第三方索引：已删的可能还在，刚发的可能没有。删除仍走官方接口。', 'warn');
      }

      const replies = (data.data && data.data.replies) || [];
      if (!replies.length) {
        if (data.data && data.data.cursor && data.data.cursor.is_end) {
          if (total && got !== total) log(`AICU 说已经结束，但索引 ${total} 条，这次收下 ${got} 条。`, 'warn');
        } else {
          stopReason = '这一页是空的，但索引没说已经结束。后面的页没有继续。';
          log(stopReason, 'warn');
        }
        break;
      }

      let added = 0;
      for (const it of replies) {
        if (addIfAbsent(mapAicuReply(it))) { added++; got++; }
      }
      hop = '';
      const host = aicuUrl === AICU_APIS[0] ? '主接口' : '备用接口';
      const skipped = replies.length - added;
      log(`第 ${page} 页（${host}）: +${added} 条（这次 +${fresh()}${total ? '/' + total : ''}）`, 'info');
      touchList(true);
      if (total) setProg(Math.min(fresh(), total), total, '枚举');

      if (data.data && data.data.cursor && data.data.cursor.is_end) {
        if (total && got !== total) log(`AICU 说已经结束，但索引 ${total} 条，这次收下 ${got} 条。`, 'warn');
        break;
      }
      const waitUntil = Date.now() + AICU_DELAY;
      const donePage = page;
      startBeat(() => `第 ${donePage} 页完成 · ${host} · 这次 +${fresh()}${total ? '/' + total : ''} · 本页 +${added}${skipped ? ` · 跳过 ${skipped}` : ''} · ${Math.max(0, Math.ceil((waitUntil - Date.now()) / 1000))}s 后下一页 · 已用 ${spent()}`);
      page++;
      await sleep(AICU_DELAY);
    }
    return { total, got, stopReason };
    } finally { stopBeat(); }
  }

  /* ═══════════ 枚举二：官方观看历史兜底（纯官方，仅视频评论） ═══════════ */
  async function fetchHistoryComments(myUid, scanPages) {
    const t0 = Date.now();
    const spent = () => fmtDur(Date.now() - t0);
    const mid = rpidKey(myUid);
    const aids = [];
    let cursorMax = 0;
    let viewAt = 0;
    const seenAids = new Set();
    let guard = 0;
    const before = comments.length;
    const fresh = () => comments.length - before;
    let historyStop = '';
    let videoFail = 0;
    let cappedVideos = 0;
    let threadSkipped = 0;
    let threadMore = 0;
    let threadFail = 0;
    resetFillStats();

    try {
    while (seenAids.size < HISTORY_VIDEO_CAP && guard < 400) {
      guard++;
      if (aborted) break;
      startBeat(() => `翻历史 · 已收集 ${seenAids.size}/${HISTORY_VIDEO_CAP} 个视频 · 每视频 ${scanPages} 页 · 已用 ${spent()}`);
      const url = `https://api.bilibili.com/x/web-interface/history/cursor?type=archive&ps=${HISTORY_PS}&max=${cursorMax}&view_at=${viewAt}`;
      let data;
      try { data = await gmGetJSON(url); }
      catch (e) {
        historyStop = `历史翻页失败：${e.message}。更早的视频没翻到。`;
        log(`历史翻页失败: ${e.message}`, 'err');
        break;
      }
      if (data.code !== 0) {
        historyStop = `历史接口错误：${data.message || data.code}。更早的视频没翻到。`;
        log(`历史接口错误: ${data.message || data.code}`, 'err');
        break;
      }

      const list = (data.data && data.data.list) || [];
      if (!list.length) break;
      for (const it of list) {
        const h = (it.history || {});
        if (h.aid && !seenAids.has(h.aid)) { seenAids.add(h.aid); aids.push(h.aid); }
      }
      const c = (data.data && data.data.cursor) || {};
      const maxId = cursorId(c.max);
      const view = cursorId(c.view_at);
      if (!maxId || !view) break;
      cursorMax = maxId; viewAt = view;
      await sleep(800);
    }
    if (!historyStop && !aborted && seenAids.size < HISTORY_VIDEO_CAP && guard >= 400) {
      historyStop = '历史翻了 400 页还没到头，更早的视频没翻到。';
      log(historyStop, 'warn');
    }

    const capNote = seenAids.size >= HISTORY_VIDEO_CAP ? `，已到 ${HISTORY_VIDEO_CAP} 个上限，更早的视频没翻` : '';
    log(`观看历史共 ${seenAids.size} 个视频${capNote}，逐个扫描（每视频 ${scanPages} 页，时间序）…`, capNote || historyStop ? 'warn' : 'info');
    for (let hi = 0; hi < aids.length; hi++) {
      if (aborted) break;
      const aid = aids[hi];
      const pace = { thread: '' };
      const gapNow = () => threadGapText(threadSkipped, threadMore, threadFail);
      startBeat(() => `扫描视频 ${hi + 1}/${aids.length}${pace.thread ? ` · ${pace.thread}` : ''}${gapNow() ? ` · 累计 ${gapNow()}` : ''} · 这次 +${fresh()} · 列表 ${comments.length} 条 · 已用 ${spent()}${videoFail ? ` · 失败 ${videoFail}` : ''}`);
      touchList(false);
      setProg(hi, aids.length, '扫描');
      let videoNote = '';
      try {
        const scan = await fetchOwnRepliesFromVideo(aid, mid, scanPages, pace);
        if (scan && scan.capped) cappedVideos++;
        const bits = [];
        if (scan && scan.capped) bits.push('后面还有评论，这次没翻');
        const one = scan && threadGapText(scan.threadSkipped, scan.threadMore, scan.threadFail);
        if (one) bits.push(one);
        if (bits.length) {
          videoNote = `这个视频：${bits.join('，')}`;
          log(`av${aid} ${bits.join('，')}`, 'warn');
        }
        threadSkipped += (scan && scan.threadSkipped) || 0;
        threadMore += (scan && scan.threadMore) || 0;
        threadFail += (scan && scan.threadFail) || 0;
      }
      catch (e) {
        videoFail++;
        videoNote = `视频 av${aid} 失败：${e.message}`;
        log(`视频 ${aid} 扫描失败: ${e.message}`, 'warn');
      }
      const waitUntil = Date.now() + HISTORY_VIDEO_DELAY;
      const doneAt = hi + 1;
      const running = gapNow();
      startBeat(() => `${videoNote || `视频 ${doneAt}/${aids.length} 完成`}${running ? ` · 累计 ${running}` : ''} · ${Math.max(0, Math.ceil((waitUntil - Date.now()) / 1000))}s 后下一个 · 这次 +${fresh()} · 列表 ${comments.length} 条 · 已用 ${spent()}${videoFail ? ` · 失败 ${videoFail}` : ''}`);
      await sleep(HISTORY_VIDEO_DELAY);
    }
    return { historyStop, videoFail, cappedVideos, threadSkipped, threadMore, threadFail };
    } finally { stopBeat(); }
  }

  function threadGapText(skipped, more, failed) {
    const bits = [];
    if (skipped) bits.push(`${skipped} 条楼没轮到补`);
    if (more) bits.push(`${more} 条楼第一页后面还有`);
    if (failed) bits.push(`${failed} 条楼第一页没要到`);
    return bits.join('，');
  }

  async function pullOwnThreadPage(aid, root, mid) {
    const d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/reply?type=1&oid=${aid}&root=${root}&pn=1&ps=${HISTORY_THREAD_PS}`, { retries: 1 });
    if (d.code !== 0) throw new Error(`code=${d.code}`);
    const rs = (d.data && d.data.replies) || [];
    let added = 0;
    for (const r of rs) {
      if (rpidKey(r.mid) !== mid) continue;
      const clip = clipMessage(r.content && r.content.message);
      if (addIfAbsent({
        rpid: idExact(r.rpid),
        oid: aid,
        type: 1,
        message: clip.message,
        cut: clip.cut,
        ctime: r.ctime || 0,
        root,
        src: 'history',
      })) added++;
    }
    const count = Number(d.data && d.data.page && d.data.page.count);
    const more = Number.isFinite(count) ? count > rs.length : rs.length >= HISTORY_THREAD_PS;
    return { more, added };
  }

  async function fetchOwnRepliesFromVideo(aid, mid, scanPages, pace) {
    let nextPage = 0;
    let guard = 0;
    let threadSkipped = 0;
    let threadMore = 0;
    let threadFail = 0;
    let openedThreads = 0;
    let capped = false;
    const queued = new Set();
    const later = [];
    const done = (cappedNow) => {
      if (pace) pace.thread = '';
      return { capped: cappedNow, threadSkipped, threadMore, threadFail };
    };
    async function openNow(list) {
      let n = 0;
      let addedN = 0;
      for (let i = 0; i < list.length; i++) {
        if (aborted) { threadSkipped += list.length - i; break; }
        const item = list[i];
        if (openedThreads >= HISTORY_THREAD_OPEN_MAX) { threadSkipped++; continue; }
        openedThreads++;
        n++;
        if (pace) pace.thread = `补楼 ${item.rootId}`;
        try {
          const extra = await pullOwnThreadPage(aid, item.rootId, mid);
          addedN += extra.added || 0;
          if (extra.more) threadMore++;
        } catch (e) {
          threadFail++;
          log(`楼 ${item.rootId} 第一页没补上: ${e.message}`, 'warn');
        }
        await sleep(400);
      }
      if (pace) pace.thread = '';
      return { n, addedN };
    }
    while (guard < scanPages) {
      guard++;
      if (aborted) { threadSkipped += later.length; return done(false); }
      const d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/main?type=1&oid=${aid}&mode=2&next=${nextPage}`);
      if (d.code !== 0) throw new Error(`av${aid} 评论接口 code=${d.code}`);
      let added = 0;
      const pageFirst = [];
      const tops = (d.data && d.data.replies) || [];
      for (const top of tops) {
        const preview = Array.isArray(top.replies) ? top.replies : [];
        const pool = [{ r: top, root: 0 }].concat(
          preview.map((s) => ({ r: s, root: idExact(top.rpid) || 0 }))
        );
        for (const entry of pool) {
          const r = entry.r;
          if (rpidKey(r.mid) === mid) {
            const clip = clipMessage(r.content && r.content.message);
            const item = {
              rpid: idExact(r.rpid),
              oid: aid,
              type: 1,
              message: clip.message,
              cut: clip.cut,
              ctime: r.ctime || 0,
              root: entry.root,
              src: 'history',
            };
            if (addIfAbsent(item)) added++;
          }
        }
        const rcount = Number(top.rcount);
        const rootId = idExact(top.rpid) || 0;
        if (rcount > preview.length && rootId && !queued.has(rootId)) {
          queued.add(rootId);
          const seen = preview.some((s) => rpidKey(s.mid) === mid);
          (seen ? later : pageFirst).push({ rootId });
        }
      }
      log(`  aid=${aid} 第${guard}页 +${added}`, 'info');
      const opened = await openNow(pageFirst);
      if (opened.n) log(`  aid=${aid} 第${guard}页补楼 ${opened.n}（预览里没有自己），+${opened.addedN}`, 'info');
      if (aborted) { threadSkipped += later.length; return done(capped); }
      const c = (d.data && d.data.cursor) || {};
      if (c.is_end) break;
      const nxt = cursorId(c.next);
      if (!nxt || nxt === String(nextPage)) break;
      if (guard >= scanPages) { capped = true; break; }
      nextPage = nxt;
      await sleep(500);
    }
    const rest = await openNow(later);
    if (rest.n) log(`  aid=${aid} 补楼 ${rest.n}（预览里已经有自己），+${rest.addedN}`, 'info');
    return done(capped);
  }

  /* ═══════════ 枚举三：离线 JSON 导入 ═══════════ */
  function importJson(raw) {
    resetFillStats();
    let data;
    try { data = JSON.parse(raw); }
    catch (e) { return { ok: false, msg: 'JSON 解析失败：' + e.message }; }

    let replies = null;
    if (Array.isArray(data)) replies = data;
    else if (Array.isArray(data.replies)) replies = data.replies;
    else if (data.data && Array.isArray(data.data.replies)) replies = data.data.replies;
    if (!replies) return { ok: false, msg: '未识别的结构：需要 replies 数组（aicu 导出 / 原始单页 JSON / 裸数组）' };

    let added = 0, dup = 0, invalid = 0, keptSrc = 0;
    const srcFrom = { aicu: 'aicu', history: 'history', import: 'import', manual: 'manual', '官方历史': 'history', '导入': 'import', '回查': 'manual' };
    const states = [];
    for (const it of replies) {
      const item = mapAicuReply(it);
      if (!item) { invalid++; continue; }
      const known = srcFrom[String((it && it.src) || '').trim()];
      const keepReal = !!(known && known !== 'import');
      item.src = keepReal ? known : 'import';
      if (addIfAbsent(item)) {
        added++;
        if (keepReal) keptSrc++;
      } else dup++;
      const st = stateFromExport(it && it.state);
      if (st) states.push({ rpid: item.rpid, state: st, why: it && it.why });
    }
    const restored = journalFillMissing(states);
    const extra = restored ? `，补回处理记录 ${restored}` : '';
    const partial = !Array.isArray(data) && data.exported != null && data.total != null && Number(data.exported) < Number(data.total);
    const scopeNote = partial ? `。这是筛选导出（${data.exported}/${data.total}），不是当时的全部` : '';
    const fillNote = `${filledRows ? `，补全更短正文 ${filledRows}` : ''}${filledMeta ? `，补上楼层或时间 ${filledMeta}` : ''}${rootClash ? `，${rootClash} 条楼层和后一次不一致，仍用先看到的` : ''}${placeClash ? `，${placeClash} 条的 oid 或类型和后一次不一致，删除仍用先看到的` : ''}${restoredMarks ? `，恢复冲突标记 ${restoredMarks}` : ''}${filledSrc ? `，补上来源 ${filledSrc}` : ''}${srcClash ? `，${srcClash} 条来源和后一次不一致，仍用先看到的` : ''}`;
    const srcNote = keptSrc && added > keptSrc
      ? `，沿用原来源 ${keptSrc}，其余新行标为导入`
      : keptSrc ? `，沿用原来源 ${keptSrc}` : (added ? '，新行标为导入' : '');
    const warn = !!(invalid || rootClash || placeClash || srcClash || partial);
    return { ok: true, warn, msg: `导入完成：新增 ${added}，重复 ${dup}，无效 ${invalid}${fillNote}${srcNote}${extra}${scopeNote}` };
  }

  function parseCsv(text) {
    const rows = [];
    let row = [];
    let cell = '';
    let quoted = false;
    const s = String(text || '').replace(/^\uFEFF/, '');
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (quoted) {
        if (ch === '"') {
          if (s[i + 1] === '"') { cell += '"'; i++; }
          else quoted = false;
        } else cell += ch;
      } else if (ch === '"') quoted = true;
      else if (ch === ',') { row.push(cell); cell = ''; }
      else if (ch === '\n') { row.push(cell); rows.push(row); row = []; cell = ''; }
      else if (ch !== '\r') cell += ch;
    }
    if (cell.length || row.length) { row.push(cell); rows.push(row); }
    return rows.filter((r) => r.some((c) => String(c).trim()));
  }

  function importCsv(raw) {
    const rows = parseCsv(raw);
    if (rows.length < 2) return { ok: false, msg: 'CSV 至少需要表头和一行数据。' };
    const head = rows[0].map((h) => String(h).trim());
    const at = (name) => head.indexOf(name);
    if (at('rpid') < 0 || at('oid') < 0 || at('type') < 0) {
      return { ok: false, msg: 'CSV 需要 rpid、oid、type 列。请用本工具导出的表。' };
    }
    const col = (cols, name) => {
      const i = at(name);
      return i >= 0 ? cols[i] : '';
    };
    const replies = rows.slice(1).map((cols) => ({
      rpid: col(cols, 'rpid'),
      oid: col(cols, 'oid'),
      type: col(cols, 'type'),
      message: col(cols, 'message'),
      ctime: col(cols, 'ctime'),
      root: col(cols, 'root'),
      src: col(cols, 'src'),
      state: col(cols, 'state'),
      cut: col(cols, 'cut'),
      placeClash: col(cols, 'placeClash'),
      rootConflict: col(cols, 'rootConflict'),
      srcConflict: col(cols, 'srcConflict'),
      why: col(cols, 'why'),
    }));
    return importJson(JSON.stringify(replies));
  }

  function importAny(raw) {
    if (raw.startsWith('[') || raw.startsWith('{')) return importJson(raw);
    if (/^"?rpid"?\s*,/i.test(raw)) return importCsv(raw);
    return importJson(raw);
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
    let complete = false, pages = 0, next = 0, walkError = '';
    for (let guard = 0; guard < RECHECK_TOP_MAX && !aborted; guard++) {
      let d;
      try {
        d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/main?type=${type}&oid=${oid}&mode=2&next=${next}`, { retries: 1 });
      } catch (e) {
        walkError = e.message || '网络错误';
        log(`回查 walk 失败 oid=${oid}: ${walkError}`, 'warn');
        break;
      }
      if (d.code === -101 || d.code === -111) {
        const why = ERR_TEXT[String(d.code)] || `code=${d.code}`;
        log(`回查 walk ${why} oid=${oid}`, 'err');
        return { map, complete: false, pages, auth: why };
      }
      if (d.code !== 0) {
        walkError = `code=${d.code}`;
        log(`回查 walk code=${d.code} oid=${oid} type=${type}`, 'warn');
        break;
      }
      pages++;
      for (const top of ((d.data && d.data.replies) || [])) {
        map.set(String(top.rpid), '');
        if (Array.isArray(top.replies)) for (const s of top.replies) map.set(String(s.rpid), String(top.rpid));
      }
      const c = (d.data && d.data.cursor) || {};
      const nxt = cursorId(c.next);
      if (c.is_end || !nxt || nxt === String(next)) { complete = true; break; }
      next = nxt;
      await sleep(RECHECK_WALK_DELAY);
    }
    const res = { map, complete, pages, walkError };
    recheckCache.set(key, res);
    return res;
  }

  /** 全量走完楼中楼根楼层下的全部子回复：{set:Set(rpidStr), complete} */
  async function walkThread(oid, type, root) {
    const key = `${oid}:${type}:${root}`;
    if (threadCache.has(key)) return threadCache.get(key);
    const set = new Set();
    let complete = false, walkError = '';
    for (let pn = 1; pn <= RECHECK_SUB_MAX && !aborted; pn++) {
      let d;
      try {
        d = await gmGetJSON(`https://api.bilibili.com/x/v2/reply/reply?type=${type}&oid=${oid}&root=${root}&pn=${pn}&ps=${RECHECK_SUB_PS}`, { retries: 1 });
      } catch (e) {
        walkError = e.message || '网络错误';
        log(`楼层 walk 失败 root=${root}: ${walkError}`, 'warn');
        break;
      }
      if (d.code !== 0) {
        walkError = `code=${d.code}`;
        log(`楼层 walk code=${d.code} root=${root}`, 'warn');
        break;
      }
      const rs = (d.data && d.data.replies) || [];
      for (const r of rs) set.add(String(r.rpid));
      const count = d.data && d.data.page && d.data.page.count;
      if ((typeof count === 'number' && pn * RECHECK_SUB_PS >= count) || rs.length < RECHECK_SUB_PS) { complete = true; break; }
      await sleep(RECHECK_WALK_DELAY);
    }
    const res = { set, complete, walkError };
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
    } catch (e) { return { soft: true, why: `单条回查失败：${e.message || '网络错误'}` }; }
    if (!d || typeof d.code !== 'number') return { soft: true, why: '单条回查没有返回 code' };
    if (d.code === -101 || d.code === -111) return { state: 'auth', why: ERR_TEXT[String(d.code)] || `code=${d.code}` };
    if (d.code === 12006 || d.code === -404) return { state: 'ok', why: `官方单条确认不存在(${d.code})` };
    if (d.code === 0) return { state: 'fail', why: '官方单条仍可见（删除接口可能假成功）' };
    return { soft: true, why: `单条回查 code=${d.code}` };
  }

  /** 可判定回查：{state:'ok'|'fail'|'uncertain', why}；接口不可用返回 null（按待确认处理） */
  async function recheckDefinitive(c) {
    const quick = await oracleCheck(c);
    if (quick && !quick.soft) return quick;
    const area = await walkArea(c.oid, c.type);
    const explain = (why, extra) => {
      const bits = [why];
      if (extra) bits.push(extra);
      if (area.walkError) bits.push(`区域翻页失败：${area.walkError}`);
      if (quick && quick.soft && quick.why) bits.push(quick.why);
      return bits.join('。');
    };
    if (area.auth) return { state: 'auth', why: area.auth };
    if (area.map.has(String(c.rpid))) {
      return { state: 'fail', why: area.map.get(String(c.rpid)) ? '楼中楼内联预览仍在' : '顶评仍在' };
    }
    if (c.root) {
      if (!area.complete && !area.map.has(String(c.root))) {
        return { state: 'uncertain', why: explain('区域未翻完，不能凭根楼缺失判断子评已删') };
      }
      if (!area.map.has(String(c.root))) return { state: 'ok', why: '根楼层已不存在，子评必然已删' };
      const th = await walkThread(c.oid, c.type, c.root);
      if (th.set.has(String(c.rpid))) return { state: 'fail', why: '楼内仍在' };
      if (!th.complete) return { state: 'uncertain', why: explain(`楼内翻页未走完(≤${RECHECK_SUB_MAX}页)`, th.walkError ? `楼内翻页失败：${th.walkError}` : '') };
      return { state: 'ok', why: `整楼未发现(根=${c.root})` };
    }
    if (!area.complete) return { state: 'uncertain', why: explain(`区域翻页未走完(≤${RECHECK_TOP_MAX}页)`) };
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

  function jumpHint(c) {
    if (c.type === 1) return '新标签打开视频页。BV 查不到时用 av 号。';
    if (c.type === 17) return '新标签打开动态页。';
    if (c.type === 12) return '新标签打开专栏页。';
    if (c.type === 11) return '先确认 oid 是分集号再打开。如果是季号，不会打开错误页面。';
    return `暂不支持 ${typeText(c.type)} 的跳转`;
  }

  const bangumiJumpCache = new Map();
  async function resolveBangumiJump(oid) {
    const key = String(oid);
    if (bangumiJumpCache.has(key)) return bangumiJumpCache.get(key);
    let res;
    try {
      const ep = await gmGetJSON(`https://api.bilibili.com/pgc/view/web/season?ep_id=${encodeURIComponent(oid)}`, { retries: 0 });
      if (ep && ep.code === 0 && ep.result) res = { kind: 'ep' };
      else {
        const season = await gmGetJSON(`https://api.bilibili.com/pgc/view/web/season?season_id=${encodeURIComponent(oid)}`, { retries: 0 });
        if (season && season.code === 0 && season.result) {
          res = { kind: 'season', title: season.result.season_title || season.result.title || '' };
        } else res = { kind: 'unknown' };
      }
    } catch (e) {
      return { kind: 'error', message: e.message || '网络错误' };
    }
    if (res.kind === 'ep' || res.kind === 'season') bangumiJumpCache.set(key, res);
    return res;
  }

  async function jumpTo(c) {
    if (!c.oid) { setStatus('该评论缺少 oid，无法跳转。'); return; }
    let url = null;
    let opened = '';
    if (c.type === 1) {
      const bv = await aidToBvid(c.oid);
      url = bv ? `https://www.bilibili.com/video/${bv}#reply${c.rpid}`
               : `https://www.bilibili.com/video/av${c.oid}#reply${c.rpid}`;
    } else if (c.type === 17) {
      url = `https://t.bilibili.com/${c.oid}#reply${c.rpid}`;
    } else if (c.type === 12) {
      url = `https://www.bilibili.com/read/cv${c.oid}#reply${c.rpid}`;
    } else if (c.type === 11) {
      setStatus(`正在确认 ${c.oid} 是分集号还是季号…`);
      const found = await resolveBangumiJump(c.oid);
      if (found.kind === 'season') {
        const title = found.title ? `（${found.title}）` : '';
        setStatus(`oid ${c.oid} 是番剧季号${title}，不是分集号。评论在某一集上，这里不能确定是哪一集，所以没有打开。`);
        log(`跳转未打开：oid=${c.oid} 是番剧季号，不是分集号`, 'warn');
        return;
      }
      url = `https://www.bilibili.com/bangumi/play/ep${c.oid}#reply${c.rpid}`;
      opened = found.kind === 'ep'
        ? `已确认 ep${c.oid} 是分集，正在打开。`
        : found.kind === 'error'
          ? `没能确认 ep${c.oid}（${found.message}），仍按分集打开。如果 404，说明这个 oid 不是分集号。`
          : `没能确认 ep${c.oid} 是分集号，仍按分集打开。如果 404，说明这个 oid 不是分集号。`;
    }
    if (url) {
      if (opened) setStatus(opened);
      window.open(url, '_blank');
    } else setStatus(`暂不支持 ${typeText(c.type)} 的跳转（oid=${c.oid}）。`);
  }

  /* ═══════════ 导出备份 ═══════════ */
  function csvCell(s) {
    s = String(s == null ? '' : s);
    return '"' + s.replace(/"/g, '""') + '"';
  }

  function stateFromExport(v) {
    const s = String(v == null ? '' : v).trim();
    if (s === 'ok' || s === '已删除') return 'ok';
    if (s === 'fail' || s === '未生效') return 'fail';
    if (s === 'uncertain' || s === '待确认') return 'uncertain';
    return '';
  }

  function journalFillMissing(pairs) {
    if (!pairs || !pairs.length) return 0;
    try {
      const j = journalCompact(journalLoad());
      const have = new Set(j.map((e) => e.rpid));
      let n = 0;
      for (const p of pairs) {
        const id = idExact(p.rpid);
        if (!id || have.has(id) || !p.state) continue;
        have.add(id);
        const row = { rpid: id, state: p.state, t: Date.now() };
        const note = clipWhy(p.why);
        if (note) row.why = note;
        j.unshift(row);
        n++;
      }
      if (!n) return 0;
      if (j.length > JOURNAL_CAP && !journalTrimWarned) {
        journalTrimWarned = true;
        log(`处理记录超过 ${JOURNAL_CAP} 条，更早的已丢弃。那些评论再出现时不会被当成已删除。`, 'warn');
      }
      localStorage.setItem(JKEY, JSON.stringify(j.slice(0, JOURNAL_CAP)));
      journalMapCache = null; journalWhyCache = null;
      return n;
    } catch (e) {
      journalMapCache = null; journalWhyCache = null;
      setStatus('浏览器拒绝保存处理记录，导入的结果列没有写回。');
      log(`处理记录写入失败：${e.message}`, 'err');
      return 0;
    }
  }

  function stateLabel(rpid) {
    const st = journalMap().get(idExact(rpid));
    return st === 'ok' ? '已删除' : st === 'fail' ? '未生效' : st === 'uncertain' ? '待确认' : '';
  }

  function doExport(kind) {
    const list = visibleComments();
    if (!list.length) { setStatus('当前筛选下没有数据可导出。'); return; }
    const stamped = list.map((c) => Object.assign({}, c, { state: stateLabel(c.rpid), why: journalWhy(c.rpid) }));
    const partial = filtersOn();
    const tag = partial ? '-part' : '';
    let blob, name;
    if (kind === 'json') {
      const payload = partial
        ? { note: '这是当前筛选，不是全部。', exported: list.length, total: comments.length, filter: filterBits(), replies: stamped }
        : stamped;
      blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
      name = `bili-comments${tag}-${Date.now()}.json`;
    } else {
      const head = 'rpid,oid,type,typeText,message,ctime,ctimeText,root,src,state,cut,placeClash,rootConflict,srcConflict,why';
      const rows = stamped.map((c) =>
        [c.rpid, c.oid, c.type, typeText(c.type), c.message, c.ctime, fmtTime(c.ctime), c.root, SRC_TEXT[c.src] || c.src, c.state, c.cut ? 1 : 0, c.placeClash ? 1 : 0, c.rootConflict ? 1 : 0, c.srcConflict ? 1 : 0, c.why || ''].map(csvCell).join(',')
      ).join('\r\n');
      blob = new Blob(['\ufeff' + head + '\r\n' + rows], { type: 'text/csv;charset=utf-8' });
      name = `bili-comments${tag}-${Date.now()}.csv`;
    }
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 3000);
    const scope = filtersOn() ? `当前筛选 ${list.length}/${comments.length}` : String(list.length);
    const bits = partial ? filterBits() : [];
    const filt = bits.length ? `筛选是${bits.join('、')}。` : '';
    setStatus(`已导出 ${scope} 条（${kind.toUpperCase()}，含处理结果、原因、截断和冲突标记）。${filt}${partial ? '文件名带 part，JSON 里写明这不是全部。' : ''}`);
    log(`已导出 ${scope} 条（${kind.toUpperCase()}）${bits.length ? `，${bits.join('、')}` : ''}`, 'ok');
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
      #${P}-toggle[data-busy="1"]{box-shadow:0 0 0 3px #ffb020, 0 2px 14px rgba(0,0,0,.35);font-size:13px;font-weight:700}
      @media (prefers-reduced-motion: reduce){ #${P}-toggle{transition:none} }

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
      .${P}-hit{background:#ffe08a;color:#1a1a1a;border-radius:2px}
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
          <button class="${P}-btn ${P}-btn-p" id="${P}-load" title="第三方索引，不是官方实时列表。已删的可能还在，刚发的可能没有。删除仍走官方接口">📥 AICU 获取</button>
          <button class="${P}-btn" id="${P}-hist" title="翻观看历史，逐视频扫自己的评论。不是全量：只扫下面页数，最多 ${HISTORY_VIDEO_CAP} 个视频。楼中楼先看预览；回复比预览多的楼，每视频最多再补 ${HISTORY_THREAD_OPEN_MAX} 条楼的第一页，名额先给预览里没有自己的楼">🏛️ 官方历史</button>
          <span style="color:var(--c-sub);font-size:12px">每视频</span>
          <input class="${P}-input" type="number" id="${P}-scanpages" value="${Math.max(1, Math.min(10, Number(localStorage.getItem(`${P}_scanpages`)) || VIDEO_SCAN_PAGES_DEFAULT))}" min="1" max="10" step="1" title="每个视频只扫最近这么多页。默认 2。调大更慢，也更不容易漏掉较早的评论">
          <span style="color:var(--c-sub);font-size:12px">页</span>
          <button class="${P}-btn" id="${P}-stop" style="display:none">⏹ 停止</button>
        </div>
        <div class="${P}-row" style="margin-top:7px">
          <textarea class="${P}-ta" id="${P}-ta" placeholder="离线兜底：粘贴 JSON，或本工具导出的 CSV"></textarea>
        </div>
        <div class="${P}-row" style="margin-top:4px">
          <button class="${P}-btn" id="${P}-import">📋 导入 JSON</button>
          <span class="${P}-hint">aicu 的 JSON，或本工具导出的 CSV，都可以粘贴</span>
        </div>
      </div>
      <div class="${P}-sec" id="${P}-cfg">
        <div class="${P}-row">
          <button class="${P}-btn ${P}-btn-d" id="${P}-dsel" disabled>🔥 删除选中</button>
          <button class="${P}-btn ${P}-btn-d" id="${P}-dall" disabled>💣 删除全部</button>
          <button class="${P}-btn ${P}-retry" id="${P}-retry">↻ 重试未成功</button>
          <button class="${P}-btn ${P}-retry" id="${P}-copybad" type="button">复制未成功</button>
          <span style="color:var(--c-sub);font-size:12px">间隔</span>
          <input class="${P}-input" type="number" id="${P}-delay" value="${DELAY_DEFAULT}" min="200" max="5000" step="50" title="两条删除之间的间隔，200 到 5000 毫秒。超出范围会改回边界">
          <span style="color:var(--c-sub);font-size:12px">ms</span>
        </div>
        <label><input type="checkbox" id="${P}-recheck" checked title="关掉之后，接口受理的只记为待确认，不算已删。下次删除才生效。"> 删除后官方单条确认（不信 code=0；仍在则自动降速重试）</label>
        <label><input type="checkbox" id="${P}-skipok" checked> 跳过日志里已确认删除的（下次删除不再请求这些，枚举仍会列出）</label>
      </div>
      <div class="${P}-strip">
        <div class="r">
          <input class="${P}-input w" type="text" id="${P}-kw" placeholder="正文，或至少 4 位编号">
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
             <option value="all">全部</option><option value="bad">未成功</option><option value="ok">已删除</option>
             <option value="fail">未生效</option><option value="uncertain">待确认</option>
             <option value="none">未处理</option>
           </select></label>
           <label>排序 <select class="${P}-sel" id="${P}-sortsel">
            <option value="default">默认</option><option value="tasc">时间↑</option><option value="tdesc">时间↓</option>
          </select></label>
          <label title="只显示位置、楼层或来源和后一次不一致的"><input type="checkbox" id="${P}-clashonly"> 只看冲突</label>
          <button class="${P}-btn" id="${P}-selall" style="padding:4px 10px" title="勾选当前筛选。按住 Shift 再点两行，会连选中间">全选</button>
          <button class="${P}-btn" id="${P}-selnone" style="padding:4px 10px" title="去掉全部勾选，包括当前筛选外面的">全不选</button>
          <button class="${P}-btn" id="${P}-expj" title="导出当前筛选下列表为 JSON（删除前备份）">💾JSON</button>
          <button class="${P}-btn" id="${P}-expc" title="导出当前筛选下列表为 CSV">💾CSV</button>
          <button class="${P}-btn" id="${P}-reset" title="清空当前列表与勾选">🧹清空</button>
          <button class="${P}-btn" id="${P}-forget" title="清除本地处理记录。已确认的评论下次不再自动跳过">清除记录</button>
        </div>
      </div>
      <div class="${P}-list" id="${P}-list">
        <div class="${P}-empty">三选一：AICU 全量获取 / 官方历史扫描 / 粘贴 JSON 或 CSV</div>
      </div>
      <div class="${P}-barwrap" id="${P}-prog" style="display:none">
        <div class="${P}-bar"><div class="${P}-fill" id="${P}-fill"></div></div>
        <span class="${P}-pct" id="${P}-pct">0%</span>
      </div>
      <div class="${P}-status" id="${P}-status"></div>
      <div class="${P}-logbar"><button type="button" class="${P}-btn" id="${P}-logbad" style="padding:2px 8px">只看问题</button><button type="button" class="${P}-btn" id="${P}-logcopy" style="padding:2px 8px" title="复制当前看得到的日志。只看问题开着时，藏起来的行不复制。更早被省略的行也不在其中">复制日志</button></div>
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
    const setPanelOpen = (open) => {
      panel.style.display = open ? 'flex' : 'none';
      if (open && !deleting && !fetching) paintBusy(null);
      saveSettings();
    };
    toggle.onclick = () => setPanelOpen(panel.style.display === 'none');
    $el(`${P}-close`).onclick = () => setPanelOpen(false);
    $el(`${P}-logbad`).onclick = () => {
      logOnlyBad = !logOnlyBad;
      $el(`${P}-logbad`).textContent = logOnlyBad ? '显示全部' : '只看问题';
      const box = $el(`${P}-log`);
      let hidden = 0, shown = 0;
      for (const line of box.children) {
        if (line.classList.contains(`${P}-log-trim`)) continue;
        const bad = line.classList.contains(`${P}-err`) || line.classList.contains(`${P}-warn`) || line.classList.contains(`${P}-keep`);
        const hide = logOnlyBad && !bad;
        line.classList.toggle(`${P}-log-hide`, hide);
        if (hide) hidden++; else shown++;
      }
      saveSettings();
      refreshLogCopyTitle();
      if (!hidden && !shown) setStatus(logOnlyBad ? '只看问题：日志是空的。' : '日志是空的。');
      else if (logOnlyBad) setStatus(hidden ? `只看问题：藏起 ${hidden} 行，还显示 ${shown} 行。` : '只看问题：当前没有要藏的行。');
      else setStatus(`已显示全部 ${shown} 行日志。`);
    };
    $el(`${P}-logcopy`).onclick = async () => {
      const box = $el(`${P}-log`);
      const all = [...box.children].filter((el) => !el.classList.contains(`${P}-log-trim`));
      const shown = logOnlyBad ? all.filter((el) => !el.classList.contains(`${P}-log-hide`)) : all;
      const lines = shown.map((el) => el.textContent);
      if (!lines.length) { setStatus(logOnlyBad && all.length ? '只看问题开着，当前没有可复制的问题日志。' : '日志是空的。'); return; }
      const hidden = all.length - lines.length;
      const trimmed = !!box.querySelector(`.${P}-log-trim`);
      const bits = [];
      if (hidden) bits.push(`只看问题开着，另外 ${hidden} 行没复制`);
      if (trimmed) bits.push('更早被省略的行不在其中');
      try {
        await navigator.clipboard.writeText(lines.join('\n'));
        setStatus(`已复制 ${lines.length} 行日志。${bits.length ? `${bits.join('。')}。` : '当前这些行都在。'}`);
      } catch (e) {
        setStatus('复制失败。请允许剪贴板，或从日志里手动选择。');
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
    $el(`${P}-srcsel`).onchange = () => {
      filtSrc = $el(`${P}-srcsel`).value;
      reportFilter(`来源：${filtSrc === 'all' ? '全部' : (SRC_TEXT[filtSrc] || filtSrc)}`);
    };
    $el(`${P}-typesel`).onchange = () => {
      filtType = $el(`${P}-typesel`).value;
      reportFilter(`类型：${filtType === 'all' ? '全部' : typeText(filtType)}`);
    };
    $el(`${P}-statesel`).onchange = () => {
      filtState = $el(`${P}-statesel`).value;
      const stateName = { all: '全部', ok: '已删除', fail: '未生效', uncertain: '待确认', none: '未处理', bad: '未成功' };
      reportFilter(`结果：${stateName[filtState] || filtState}`);
    };
    $el(`${P}-clashonly`).onchange = () => {
      onlyClash = $el(`${P}-clashonly`).checked;
      renderList(); updCount();
      say(onlyClash ? `只看冲突：当前 ${visibleComments().length} 条。` : '已取消只看冲突。');
    };
    $el(`${P}-kw`).addEventListener('input', () => {
      clearTimeout(kwTimer);
      kwTimer = setTimeout(() => onFilter(true), 250);
    });
    $el(`${P}-sortsel`).onchange = () => {
      sortMode = $el(`${P}-sortsel`).value;
      saveSettings();
      renderList(); updCount();
      const name = { default: '默认', tasc: '时间从早到晚', tdesc: '时间从晚到早' };
      say(`已按${name[sortMode] || '默认'}排序。换页之后还是这个顺序。当前 ${visibleComments().length} 条。`);
    };
    $el(`${P}-selall`).onclick = () => {
      const outside = outsideSelected();
      let n = 0;
      let skip = 0;
      visibleComments().forEach((c) => {
        if (c.oid && c.type) { selected.add(c.rpid); n++; }
        else skip++;
      });
      renderList(); updCount();
      const skipNote = skip ? `有 ${skip} 条缺 oid 或类型，没勾。` : '';
      say(outside ? `已勾选当前筛选 ${n} 条。筛选外还有 ${outside} 条，没有取消。${skipNote}` : `已勾选 ${n} 条。${skipNote}`);
    };
    $el(`${P}-selnone`).onclick = () => {
      const outside = outsideSelected();
      const n = selected.size;
      selected.clear();
      renderList(); updCount();
      say(!n ? '没有勾选。' : outside ? `已去掉全部勾选，包括筛选外的 ${outside} 条。` : `已去掉 ${n} 条勾选。`);
    };
    $el(`${P}-expj`).onclick = () => doExport('json');
    $el(`${P}-expc`).onclick = () => doExport('csv');
    $el(`${P}-reset`).onclick = async () => {
      if (!(await ask('清空当前列表与勾选？\n已删除记录不受影响。', '清空'))) return;
      resetDataset();
      setStatus('列表已清空。排序回到默认，换页之后也是默认。');
      log('🧹 列表已清空', 'warn');
    };
    $el(`${P}-forget`).onclick = async () => {
      const st = journalStats();
      if (!st.n) { setStatus('没有本地处理记录。'); return; }
      if (!(await ask(`清除 ${st.n} 条本地处理记录？\n已确认 ${st.ok}，未成功 ${st.bad}。\n列表还在，但这些评论不再被当成已删除。`, '清除'))) return;
      try { localStorage.removeItem(JKEY); } catch (e) { /* noop */ }
      journalMapCache = null; journalWhyCache = null;
      renderList();
      updCount();
      setStatus('处理记录已清除。');
      log('处理记录已清除', 'warn');
    };

    /* —— 删除 —— */
    $el(`${P}-dsel`).onclick = () => runDelete('selected');
    $el(`${P}-dall`).onclick = () => runDelete('all');
    $el(`${P}-retry`).onclick = () => {
      const targets = badInList();
      if (!targets.length) { setStatus('当前列表里没有未成功、且能删除的条目。'); return; }
      runDelete('explicit', targets, '重试未成功');
    };
    $el(`${P}-retry`).style.display = 'none';
    $el(`${P}-copybad`).onclick = async () => {
      const jm = journalMap();
      const ids = comments.filter((c) => {
        const st = jm.get(idExact(c.rpid));
        return st === 'fail' || st === 'uncertain';
      }).map((c) => `${c.rpid}\t${journalWhy(c.rpid)}`);
      if (!ids.length) { setStatus('没有未成功的 rpid 可复制。'); return; }
      const text = ids.join('\n');
      try {
        await navigator.clipboard.writeText(text);
        setStatus(`已复制 ${ids.length} 个未成功 rpid（每行后面是原因，没有原因就空着）。`);
      } catch (e) {
        setStatus('复制失败。请允许剪贴板，或从日志里复制。');
        log(`未成功 rpid：${ids.join(',')}`, 'warn');
      }
    };

    /* —— 列表事件委托（万级数据不挂） —— */
    const listEl = $el(`${P}-list`);
    let selLockNote = 0;
    const noteSelLocked = () => {
      const now = Date.now();
      if (now - selLockNote < 3000) return;
      selLockNote = now;
      log('勾选没有改：删除确认或进行中，这次范围已经定了。', 'warn');
      setStatus('勾选先不动。这次要删的范围已经定了，停掉之后再改。');
    };
    listEl.addEventListener('change', (e) => {
      if (!e.target.matches('input[type="checkbox"]')) return;
      if (e.target.dataset.skip === '1') { e.target.dataset.skip = ''; return; }
      if (deleting || confirming) {
        const rpid = idExact(e.target.dataset.rpid);
        e.target.checked = selected.has(rpid);
        noteSelLocked();
        return;
      }
      const rpid = idExact(e.target.dataset.rpid);
      e.target.checked ? selected.add(rpid) : selected.delete(rpid);
      updCount();
    });
    listEl.addEventListener('click', (e) => {
      const cp = e.target.closest('button[data-act="copyid"]');
      if (cp) {
        const c = comments.find((x) => x.rpid === idExact(cp.dataset.rpid));
        const text = c ? `rpid=${c.rpid}\toid=${c.oid || ''}\ttype=${c.type || ''}` : `rpid=${cp.dataset.rpid}`;
        navigator.clipboard.writeText(text).then(() => {
          setStatus(c ? `已复制 rpid=${c.rpid} oid=${c.oid || '无'} type=${c.type || '无'}` : `已复制 ${text}`);
        }).catch(() => setStatus('复制失败。请允许剪贴板，或从日志里手动选择。'));
        return;
      }
      const jb = e.target.closest('button[data-act="jump"]');
      if (jb) {
        const c = comments.find((x) => x.rpid === idExact(jb.dataset.rpid));
        if (c) jumpTo(c);
        return;
      }
      if (e.target.closest('a')) return;
      if (deleting || confirming) { noteSelLocked(); return; }
      const row = e.target.closest(`.${P}-item`);
      if (!row) return;
      const rpid = idExact(row.dataset.rpid);
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
      if (saved.logOnlyBad) {
        logOnlyBad = true;
        $el(`${P}-logbad`).textContent = '显示全部';
      }
      refreshLogCopyTitle();
      if (saved.left && saved.top && Number(saved.left) > 0 && Number(saved.left) < window.innerWidth - 100
          && Number(saved.top) > 0 && Number(saved.top) < window.innerHeight - 60) {
        panel.style.right = 'auto';
        panel.style.left = saved.left + 'px';
        panel.style.top = saved.top + 'px';
        panel.style.transform = 'none';
      }
      if (saved.sort === 'default' || saved.sort === 'tasc' || saved.sort === 'tdesc') {
        sortMode = saved.sort;
        const sortEl = $el(`${P}-sortsel`);
        if (sortEl) sortEl.value = saved.sort;
      }
      if (saved.open === true) panel.style.display = 'flex';
    } catch (e) { /* noop */ }
    readDelay();
    $el(`${P}-delay`).addEventListener('change', () => readDelay(true));
    $el(`${P}-scanpages`).addEventListener('change', () => readScanPages(true));
    window.addEventListener('beforeunload', (e) => {
      if (!deleting && !fetching) return;
      e.preventDefault();
      e.returnValue = '';
    });
    $el(`${P}-recheck`).addEventListener('change', () => {
      saveSettings();
      const on = $el(`${P}-recheck`).checked;
      say(on ? '回查已打开。下次删除会再向官方确认，仍在则降速重试。' : '回查已关闭。下次删除里，接口受理的只记为待确认，不算已删。');
    });
    $el(`${P}-skipok`).addEventListener('change', () => {
      saveSettings();
      const on = $el(`${P}-skipok`).checked;
      say(on ? '下次删除会跳过日志里已确认删除的。枚举仍会把它们列出来。' : '下次删除不再跳过已确认删除的，会再请求它们。');
    });
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
    journalNormalize();
    const remembered = journalStats();
    const mem = (remembered.n ? ` 本地记录 ${remembered.n} 条（已确认 ${remembered.ok}，未成功 ${remembered.bad}）。` : '') + journalCompactNote + lastRunNote();
    if (csrf && uid) setStatus(`已登录 UID=${uid}，bili_jct 就绪。删除不可逆，请谨慎。${mem}`);
    else setStatus(`⚠️ 未检测到登录态（请先在 bilibili.com 登录后刷新）。可先导入/浏览，删除需登录。${mem}`);
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
        logOnlyBad,
        sort: sortMode,
        open: !!(panel && panel.style.display !== 'none'),
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
    if (ia < 0 || ib < 0) {
      say('连选没生效。起点不在当前列表里，请先点一条，再按住 Shift 点另一条。');
      return;
    }
    const lo = Math.min(ia, ib);
    const hi = Math.max(ia, ib);
    let n = 0;
    let skip = 0;
    for (let i = lo; i <= hi; i++) {
      const c = list[i];
      if (!c.oid || !c.type) { skip++; continue; }
      selected.add(c.rpid);
      n++;
    }
    anchorRpid = b;
    renderList();
    updCount();
    say(`已连选 ${n} 条（当前筛选内，含两端）。${skip ? `缺字段跳过 ${skip} 条。` : ''}`);
  }

  function outsideSelected() {
    if (!filtersOn()) return 0;
    const visIds = new Set(visibleComments().map((c) => c.rpid));
    let n = 0;
    for (const id of selected) if (!visIds.has(id)) n++;
    return n;
  }

  function filtersOn() {
    return !!(filterKw || filtSrc !== 'all' || filtType !== 'all' || filtState !== 'all' || onlyClash);
  }

  function filterBits() {
    const stateName = { ok: '已删除', fail: '未生效', uncertain: '待确认', none: '未处理', bad: '未成功' };
    const bits = [];
    if (filterKw) bits.push(`关键词「${filterKw}」`);
    if (filtSrc !== 'all') bits.push(`来源 ${SRC_TEXT[filtSrc] || filtSrc}`);
    if (filtType !== 'all') bits.push(`类型 ${typeText(filtType)}`);
    if (filtState !== 'all') bits.push(`结果 ${stateName[filtState] || filtState}`);
    if (onlyClash) bits.push('只看冲突');
    return bits;
  }

  function syncFilterControls() {
    const kw = document.getElementById(`${P}-kw`);
    if (kw && kw.value !== filterKw) kw.value = filterKw;
    for (const [id, val] of [[`${P}-srcsel`, filtSrc], [`${P}-typesel`, filtType], [`${P}-statesel`, filtState], [`${P}-sortsel`, sortMode]]) {
      const el = document.getElementById(id);
      if (el && el.value !== val) el.value = val;
    }
    const clash = document.getElementById(`${P}-clashonly`);
    if (clash && clash.checked !== onlyClash) clash.checked = onlyClash;
  }

  function clearFilters() {
    filterKw = '';
    filtSrc = 'all';
    filtType = 'all';
    filtState = 'all';
    onlyClash = false;
    syncFilterControls();
    renderList();
    say('筛选已清除。排序还在。');
  }

  function idHit(c, q) {
    const needle = String(q || '').toLowerCase();
    if (!needle) return [];
    const rpid = String(c.rpid);
    const oid = String(c.oid || '').toLowerCase();
    const wide = [...needle].length >= 4;
    const hits = [];
    if (wide ? rpid.includes(needle) : rpid === needle) hits.push('rpid');
    if (wide ? oid.includes(needle) : oid === needle) hits.push('oid');
    return hits;
  }

  function visibleComments() {
    let list = comments;
    if (filterKw) {
      const q = filterKw.toLowerCase();
      list = list.filter((c) => (c.message || '').toLowerCase().includes(q) || idHit(c, q).length);
    }
    if (filtSrc !== 'all') list = list.filter((c) => c.src === filtSrc);
    if (filtType !== 'all') list = list.filter((c) => String(c.type) === filtType);
    if (filtState !== 'all') {
      const jm = journalMap();
      list = list.filter((c) => {
        const st = jm.get(c.rpid);
        if (filtState === 'none') return !st;
        if (filtState === 'bad') return st === 'fail' || st === 'uncertain';
        return st === filtState;
      });
    }
    if (onlyClash) list = list.filter(hasClash);
    if (sortMode === 'tasc') list = [...list].sort((a, b) => (a.ctime || 0) - (b.ctime || 0));
    else if (sortMode === 'tdesc') list = [...list].sort((a, b) => (b.ctime || 0) - (a.ctime || 0));
    return list;
  }

  let viewSnap = [];      // 当前渲染快照
  let viewOffset = 0;     // 已渲染条数
  let ro = null;          // IntersectionObserver
  let kwTimer = null;

  function appendQuery(parent, text, q) {
    const src = String(text || '');
    const needle = String(q || '').toLowerCase();
    if (!needle) { parent.textContent = src; return; }
    const lower = src.toLowerCase();
    let i = 0;
    let guard = 0;
    while (i < src.length && guard < 80) {
      guard++;
      const at = lower.indexOf(needle, i);
      if (at < 0) break;
      if (at > i) parent.appendChild(document.createTextNode(src.slice(i, at)));
      const mark = document.createElement('span');
      mark.className = `${P}-hit`;
      mark.textContent = src.slice(at, at + needle.length);
      parent.appendChild(mark);
      i = at + needle.length;
    }
    if (i < src.length) parent.appendChild(document.createTextNode(src.slice(i)));
  }

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
    if (c.message) appendQuery(msgDiv, c.message, filterKw);
    else msgDiv.textContent = '(空评论)';
    if (c.cut) {
      msgDiv.appendChild(document.createTextNode('…'));
      msgDiv.title = '只保留前 200 字。更后面的内容在这里搜不到。';
    }
    main.appendChild(msgDiv);

    const meta = document.createElement('div');
    meta.className = 'meta';
    meta.appendChild(document.createTextNode(`${typeText(c.type)} · ${fmtTime(c.ctime)} · rpid:${c.rpid} · ${SRC_TEXT[c.src] || c.src}`));
    if (c.cut) {
      const cut = document.createElement('span');
      cut.className = `${P}-mark`;
      cut.textContent = ' ·只显示前 200 字';
      cut.title = '更后面的内容在这里搜不到。';
      meta.appendChild(cut);
    }
    if (c.placeClash) {
      const clash = document.createElement('span');
      clash.className = `${P}-mark`;
      clash.textContent = ' ·位置有冲突';
      clash.title = '同一条评论后来的 oid 或类型不一样。删除仍用先看到的。';
      meta.appendChild(clash);
    }
    if (c.rootConflict) {
      const clash = document.createElement('span');
      clash.className = `${P}-mark`;
      clash.textContent = ' ·楼层有冲突';
      clash.title = '后来的根楼层不一样。回查和删除仍用先看到的。';
      meta.appendChild(clash);
    }
    if (c.srcConflict) {
      const clash = document.createElement('span');
      clash.className = `${P}-mark`;
      clash.textContent = ' ·来源有冲突';
      clash.title = '后来的来源不一样。仍用先看到的。';
      meta.appendChild(clash);
    }
    if (filterKw) {
      const q = filterKw.toLowerCase();
      const inMsg = (c.message || '').toLowerCase().includes(q);
      const hits = inMsg ? [] : idHit(c, q);
      if (hits.length) {
        const hit = document.createElement('span');
        hit.className = `${P}-mark`;
        hit.textContent = ` ·命中 ${hits.join('/')}`;
        meta.appendChild(hit);
      }
    }
    const jm = journalMap();
    if (jm.has(c.rpid)) {
      const st = jm.get(c.rpid);
      const b = document.createElement('span');
      b.className = `${P}-mark`;
      b.textContent = st === 'ok' ? ' ·上次已删除✓' : st === 'fail' ? ' ·上次失败' : ' ·上次待确认';
      const why = journalWhy(c.rpid);
      if (why) b.title = why;
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

    const idb = document.createElement('button');
    idb.className = `${P}-jump`;
    idb.textContent = '⧉';
    idb.title = '复制这一条的 rpid、oid、type';
    idb.dataset.act = 'copyid';
    idb.dataset.rpid = String(c.rpid);
    row.appendChild(idb);
    if (c.oid && c.type) {
      const jb = document.createElement('button');
      jb.className = `${P}-jump`;
      jb.textContent = '↗';
      jb.title = jumpHint(c);
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
      if (comments.length && filtersOn()) {
        d.textContent = `当前筛选无匹配：${filterBits().join('、')}。`;
        const b = document.createElement('button');
        b.className = `${P}-btn`;
        b.textContent = '清除筛选';
        b.style.marginTop = '8px';
        b.onclick = clearFilters;
        d.appendChild(b);
      } else d.textContent = '暂无评论数据。';
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
    if (dsel) { dsel.disabled = !nDel || deleting || fetching || confirming; dsel.textContent = `🔥 删除选中 (${nDel})`; }
    if (dall) {
      dall.disabled = !vis.length || deleting || fetching || confirming;
      dall.textContent = `${filtersOn() ? '💣 删除当前' : '💣 删除全部'} (${vis.length})`;
      dall.title = filtersOn() ? `只删除当前筛选里能删的评论（${filterBits().join('、')}），不会动被筛掉的` : '删除列表里能删的全部评论';
    }
    const copyBtn = document.getElementById(`${P}-copybad`);
    if (copyBtn) {
      let bad = 0;
      for (const c of comments) {
        const st = jm.get(idExact(c.rpid));
        if (st === 'fail' || st === 'uncertain') bad++;
      }
      copyBtn.style.display = bad && !deleting && !confirming ? 'inline-block' : 'none';
      copyBtn.textContent = `复制未成功 (${bad})`;
    }
    const retryBtn = document.getElementById(`${P}-retry`);
    if (retryBtn) {
      const nRetry = badInList().length;
      retryBtn.style.display = nRetry && !deleting && !confirming ? 'inline-block' : 'none';
      retryBtn.textContent = `↻ 重试未成功 (${nRetry})`;
    }
    const cnt = document.getElementById(`${P}-cnt`);
    if (cnt) {
      let outside = 0;
      if (filtersOn()) {
        const visIds = new Set(shown.map((c) => c.rpid));
        for (const id of selected) if (!visIds.has(id)) outside++;
      }
      let clashAll = 0;
      for (const c of comments) if (hasClash(c)) clashAll++;
      cnt.textContent = `${nSel}/${vis.length} · 已删${okN} 失败${failN} 待确认${uncN}${outside ? ` · 筛选外已勾${outside}` : ''}${clashAll ? ` · 冲突${clashAll}` : ''}`;
      const tips = [];
      if (outside) tips.push('这些勾选不在当前筛选里。删除选中不会动它们。清除筛选后会重新出现。');
      if (clashAll) tips.push(`整份列表里有 ${clashAll} 条位置、楼层或来源冲突。勾选「只看冲突」可以单独看。`);
      cnt.title = tips.join('');
    }
  }

  function reportFilter(text) {
    renderList();
    updCount();
    say(`${text}，当前 ${visibleComments().length} 条。`);
  }

  function onFilter(live) {
    const next = document.getElementById(`${P}-kw`).value.trim();
    if (live && next === filterKw) return;
    filterKw = next;
    renderList();
    const short = filterKw && [...filterKw].length < 4;
    say(filterKw ? `已按「${filterKw}」筛选。${short ? '少于 4 个字只搜正文，不拿去对编号。' : '正文、rpid、oid。'}` : '已清除关键词。');
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
    const had = comments.length;
    try {
      log(`开始 AICU 枚举 UID=${myUid}`);
      datasetUid = myUid;
      const t0 = Date.now();
      const aicu = await fetchAicuComments(myUid) || { total: 0, got: 0 };
      renderList(); updCount();
      const added = comments.length - had;
      const gap = (!aborted && aicu.total && aicu.got !== aicu.total) ? `索引报 ${aicu.total}，本次收下 ${aicu.got}。` : '';
      const aicuHead = aborted ? '已停止枚举' : (aicu.stopReason || gap) ? 'AICU 枚举未完成' : '✅ AICU 枚举完成';
      const fillNote = `${filledRows ? `补全了 ${filledRows} 条原来更短的正文。` : ''}${filledMeta ? `补上了 ${filledMeta} 条缺失的楼层或时间。` : ''}${rootClash ? `有 ${rootClash} 条的楼层和后一次不一致，仍用先看到的。` : ''}${placeClash ? `有 ${placeClash} 条的 oid 或类型和后一次不一致，删除仍用先看到的。` : ''}${filledSrc ? `补上了 ${filledSrc} 条原来没有的来源。` : ''}${srcClash ? `有 ${srcClash} 条的来源和后一次不一致，仍用先看到的。` : ''}`;
      const aicuSum = `${aicuHead}：这次 +${added}，列表共 ${comments.length} 条（去重）。${fillNote}${aicu.stopReason || ''}${gap}索引可能滞后，不是官方实时列表。用时 ${fmtDur(Date.now() - t0)}。${aborted ? '后面的页没有继续。' : ''}${digestLine()}`;
      saveLastRun(aicuSum);
      setStatus(aicuSum);
      const aicuWhy = `${aicu.stopReason || ''}${gap}`;
      log(`${aicuHead}，这次 +${added}，列表共 ${comments.length} 条${aicuWhy ? `。${aicuWhy}` : ''}${fillNote ? ` ${fillNote}` : ''}`, aborted || aicuWhy ? 'warn' : 'ok');
    } catch (e) {
      stopBeat();
      const added = comments.length - had;
      const kept = added > 0 ? `这次已经收下 ${added} 条，还在列表里。` : '这次没有新收下评论。';
      saveLastRun(`枚举失败：${e.message}。${kept}`);
      setStatus(`❌ 枚举失败：${e.message}。${kept}`);
      log(`枚举失败: ${e.message}。${kept}`, 'err');
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
    const pagesEl = document.getElementById(`${P}-scanpages`);
    const pagesTitle = pagesEl ? pagesEl.title : '';
    btn.disabled = true; fetching = true; aborted = false;
    document.getElementById(`${P}-load`).disabled = true;
    if (pagesEl) {
      pagesEl.disabled = true;
      pagesEl.title = '这次扫描已经开始，页数不能改。停掉之后再改，下次生效。';
    }
    armStop(true);
    setStatus('官方历史扫描：翻历史 → 逐视频扫评论（仅视频，aicu 的兜底）…');
    showProg(true);
    const had = comments.length;
    try {
      if (datasetUid && datasetUid !== myUid) log(`⚠️ 列表属于 UID=${datasetUid}，本次扫描账号 UID=${myUid}`, 'warn');
      else if (!datasetUid) datasetUid = myUid;
      const scanPages = readScanPages();
      log(`开始官方历史扫描 UID=${myUid}（每视频 ${scanPages} 页，最多 ${HISTORY_VIDEO_CAP} 个视频，楼中楼每视频最多补 ${HISTORY_THREAD_OPEN_MAX} 条楼的第一页）`);
      const t0 = Date.now();
      const hist = await fetchHistoryComments(myUid, scanPages) || {};
      renderList(); updCount();
      const added = comments.length - had;
      const videoNote = hist.videoFail ? `${hist.videoFail} 个视频没扫成。` : '';
      const moreNote = hist.cappedVideos ? `${hist.cappedVideos} 个视频后面还有评论，这次没翻。` : '';
      const threadNote = threadGapText(hist.threadSkipped, hist.threadMore, hist.threadFail);
      const histHead = aborted ? '已停止扫描' : hist.historyStop ? '官方扫描未翻完' : (videoNote || moreNote || threadNote) ? '官方扫描有遗漏' : '✅ 官方扫描完成';
      const threadTail = threadNote ? `${threadNote}。每视频最多补 ${HISTORY_THREAD_OPEN_MAX} 条楼的第一页。` : '';
      const fillNote = `${filledRows ? `补全了 ${filledRows} 条原来更短的正文。` : ''}${filledMeta ? `补上了 ${filledMeta} 条缺失的楼层或时间。` : ''}${rootClash ? `有 ${rootClash} 条的楼层和后一次不一致，仍用先看到的。` : ''}${placeClash ? `有 ${placeClash} 条的 oid 或类型和后一次不一致，删除仍用先看到的。` : ''}${filledSrc ? `补上了 ${filledSrc} 条原来没有的来源。` : ''}${srcClash ? `有 ${srcClash} 条的来源和后一次不一致，仍用先看到的。` : ''}`;
      const histSum = `${histHead}：这次 +${added}，列表共 ${comments.length} 条。每视频最近 ${scanPages} 页，最多 ${HISTORY_VIDEO_CAP} 个视频。用时 ${fmtDur(Date.now() - t0)}。${fillNote}${hist.historyStop || ''}${videoNote}${moreNote}${threadTail}${aborted ? '后面的视频没有继续。' : ''}${digestLine()}`;
      saveLastRun(histSum);
      setStatus(histSum);
      const histWhy = `${hist.historyStop || ''}${videoNote}${moreNote}${threadNote ? `${threadNote}。` : ''}`;
      log(`${histHead}，这次 +${added}，列表共 ${comments.length} 条${histWhy ? `。${histWhy}` : ''}${fillNote ? ` ${fillNote}` : ''}`, aborted || histWhy ? 'warn' : 'ok');
    } catch (e) {
      stopBeat();
      const added = comments.length - had;
      const kept = added > 0 ? `这次已经收下 ${added} 条，还在列表里。` : '这次没有新收下评论。';
      saveLastRun(`官方扫描失败：${e.message}。${kept}`);
      setStatus(`❌ 官方扫描失败：${e.message}。${kept}`);
      log(`官方扫描失败: ${e.message}。${kept}`, 'err');
    } finally {
      btn.disabled = false; fetching = false;
      document.getElementById(`${P}-load`).disabled = false;
      if (pagesEl) { pagesEl.disabled = false; pagesEl.title = pagesTitle; }
      armStop(false);
      showProg(false);
      updCount();
    }
  }

  function onImport() {
    const raw = document.getElementById(`${P}-ta`).value.trim();
    if (!raw) { setStatus('请先粘贴 JSON 或 CSV。'); return; }
    const r = importAny(raw);
    renderList();
    if (r.ok) document.getElementById(`${P}-ta`).value = '';
    const importNote = r.ok
      ? `${r.msg}。输入框已清空。这份列表只在当前页，刷新后会清空，处理记录里补上的状态还在。`
      : `${r.msg}。当前列表没改。`;
    saveLastRun(r.ok ? `${r.warn ? '导入有问题' : '导入'}：${importNote}` : `导入失败：${importNote}`);
    setStatus(r.ok ? `${r.warn ? '⚠️' : '✅'} ${importNote}${digestLine()}` : `❌ ${importNote}`);
    log(r.ok ? `导入: ${r.msg}` : `导入失败: ${r.msg}`, !r.ok ? 'err' : r.warn ? 'warn' : 'ok');
  }

  function lockWhileDeleting(locked) {
    const keys = ['dsel', 'dall', 'retry', 'copybad', 'load', 'hist', 'import', 'reset', 'forget',
      'kw', 'filter', 'clearf', 'srcsel', 'typesel', 'statesel', 'sortsel', 'clashonly', 'selall', 'selnone', 'expj', 'expc',
      'delay', 'recheck', 'skipok'];
    const whyFixed = '这次删除已经按开始时的间隔、回查和跳过设置在跑。停掉之后再改，下次生效';
    const why = '删除确认或进行中，筛选和导出先锁住，避免列表和正在删的范围对不上';
    keys.forEach((k) => {
      const el = document.getElementById(`${P}-${k}`);
      if (!el) return;
      el.disabled = locked;
      if (locked) {
        if (el.dataset.lockTitle == null) el.dataset.lockTitle = el.title || '';
        el.title = (k === 'delay' || k === 'recheck' || k === 'skipok') ? whyFixed : why;
      } else if (el.dataset.lockTitle != null) {
        el.title = el.dataset.lockTitle;
        delete el.dataset.lockTitle;
      }
    });
  }

  /* ═══════════ 控制器：删除 ═══════════ */
  async function runDelete(mode, explicitTargets, scopeLabel) {
    if (deleting || fetching || confirming) {
      setStatus('已有任务在进行，请等它结束或先关掉确认框。');
      return;
    }
    confirming = true;
    updCount();
    let ok = 0, fail = 0, uncertain = 0, shadowFixed = 0, seen = 0, recheckLeft = 0, planned = 0, stopWhy = '';
    const pending = [];           // 已提交删除、留待统一回查的条目
    try {
    let targets, scope;
    if (mode === 'explicit' && explicitTargets) {
      targets = explicitTargets; scope = scopeLabel || '重试';
    } else if (mode === 'all') {
      targets = visibleComments().filter((c) => c.oid && c.type);
      scope = filtersOn() ? '当前筛选' : '全部列表';
    } else {
      targets = visibleComments().filter((c) => c.oid && c.type && selected.has(c.rpid));
      scope = filtersOn() ? '当前筛选里选中的' : '选中的';
    }
    if (mode !== 'explicit' && filtersOn()) {
      const bits = filterBits();
      if (bits.length) scope = `${scope}：${bits.join('、')}`;
    }
    let skippedOk = 0;
    const skipBox = document.getElementById(`${P}-skipok`);
    if (skipBox && skipBox.checked) {
      const jm = journalMap();
      const kept = [];
      for (const c of targets) {
        if (jm.get(idExact(c.rpid)) === 'ok') skippedOk++;
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
    const delay = readDelay();
    const per = delay + (recheckOn ? 600 : 0);
    const sample = String(targets[0].message || '(空评论)').replace(/\s+/g, ' ').slice(0, 36);
    const skipNote = skippedOk ? `\n已跳过 ${skippedOk} 条已确认删除。` : '';
    const clashN = targets.filter(hasClash).length;
    const clashNote = clashN ? `\n其中 ${clashN} 条位置、楼层或来源和后一次不一致，删除仍用先看到的。${onlyClash ? '' : '\n可先勾选「只看冲突」核对。'}` : '';
    let outside = '';
    if (mode !== 'all' && mode !== 'explicit') {
      const visIds = new Set(visibleComments().map((c) => c.rpid));
      let hiddenSel = 0;
      for (const id of selected) if (!visIds.has(id)) hiddenSel++;
      if (hiddenSel) outside = `\n另有 ${hiddenSel} 条已勾选但不在当前筛选里，这次不会删。`;
    }
    lockWhileDeleting(true);
    if (!(await ask(`即将删除 ${targets.length} 条（${scope}）。\n间隔 ${delay}ms，回查${recheckOn ? '开' : '关（受理不算已删）'}，预计 ${fmtEta(targets.length * per)}。${skipNote}${clashNote}${outside}\n首条：${sample}\n\n不可撤销。`, '删除'))) return;

    deleting = true; aborted = false;
    planned = targets.length;
    batchResults = new Map();
    recheckCache = new Map(); threadCache = new Map();   // 回查缓存仅批次内有效
    const retryBtn = document.getElementById(`${P}-retry`);
    if (retryBtn) { retryBtn.style.display = 'none'; }

    lockWhileDeleting(true);
    armStop(true);
    showProg(true);
    const t0 = Date.now();
    log(`🔥 开始删除 ${targets.length} 条（${scope}），间隔 ${delay}ms，回查${recheckOn ? '开' : '关'}`, 'warn');

    for (let i = 0; i < targets.length; i++) {
      if (aborted) { log('⏹ 已停止', 'warn'); break; }
      seen++;
      const c = targets[i];
      markActive(c.rpid);
      setProg(i, targets.length, '①删除');
      const leftDel = (targets.length - i) * delay + (recheckOn ? targets.length * 600 : 0);
      const snippet = String(c.message || '(空)').replace(/\s+/g, ' ').slice(0, 22);

      let result = null;          // 'ok' | 'uncertain' | 'fail'
      let whyNote = '';
      let submittedPending = false;
      let attempt = 0;
      while (attempt < DELETE_MAX_RETRY) {
        if (aborted) break;
        let j = null;
        try {
          startBeat(() => `①删除 ${i + 1}/${targets.length} · ${snippet} · 请求中 · 已用 ${fmtDur(Date.now() - t0)} · 剩余 ${fmtEta(leftDel)}`);
          j = await doDelete(c, csrf);
        } catch (e) {
          result = 'uncertain';
          whyNote = `请求异常：${e.message || '网络错误'}，不知道这次有没有删掉`;
          log(`～ 请求异常 rpid=${c.rpid} ${whyNote}`, 'warn');
          break;
        }
        finally { stopBeat(); }
        const codeStr = String(j.code);
        if (j.code === 0 || j.code === 12022 || j.code === -404) {
          if (!recheckOn) {
            result = j.code === 0 ? 'uncertain' : 'ok';
            whyNote = j.code === 0 ? '已提交但未回查，不算已删' : `评论已不存在（${j.code}）`;
            log(j.code === 0 ? `✓ 已提交（未回查，不算已删） rpid=${c.rpid}` : `• ${j.code}：评论已不存在 rpid=${c.rpid}`, j.code === 0 ? 'warn' : 'info');
          } else {
            submittedPending = true;
            log(`${j.code === 0 ? '✓' : '•'} ${j.code === 0 ? '接口已受理（不等于已删）' : `接口${j.code}（视为已不存在）`}，待官方确认 rpid=${c.rpid}`);
          }
          break;
        }
        if (j.code === -101 || j.code === -111) {
          result = 'uncertain';
          aborted = true;
          const why = ERR_TEXT[codeStr] || `code=${j.code}`;
          whyNote = why;
          if (!stopWhy) stopWhy = why;
          setStatus(`已停止：${why}。这条算待确认，后面的还没请求。请重新登录或刷新后再试。`);
          log(`✗ rpid=${c.rpid} ${why}，停止后续删除`, 'err');
          break;
        }
        if (j.code === -509 || j.code === -412 || j.code === -9000) {
          const wait = (j.code === -509 ? 2000 : 3000) * (attempt + 1);
          const why = j.code === -509 ? '限流 -509' : (j.message || `code=${j.code}`);
          if (attempt + 1 >= DELETE_MAX_RETRY) {
            result = 'fail';
            whyNote = `${why}，重试后仍失败`;
            setStatus(`${why}，已达重试上限 · rpid=${c.rpid}`);
            log(`✗ rpid=${c.rpid} ${why}，重试后仍失败`, 'err');
            break;
          }
          log(`⏳ ${why}，${wait}ms 后重试（${attempt + 1}/${DELETE_MAX_RETRY - 1}）…`, 'warn');
          await waitTick(wait, (left) => `${why}，${left}s 后重试 ${attempt + 1}/${DELETE_MAX_RETRY - 1} · rpid=${c.rpid} · 已用 ${fmtDur(Date.now() - t0)}`);
          attempt++;
          continue;
        }
        result = 'fail';
        whyNote = `code=${j.code} ${j.message || ERR_TEXT[codeStr] || ''}`.trim();
        log(`✗ rpid=${c.rpid} code=${j.code} ${j.message || ERR_TEXT[codeStr] || ''}`, 'err');
        break;
      }
      if (!result && !submittedPending) {   // 限流耗尽 / 中途停止 → 显式记录（不是静默漏计）
        result = aborted ? 'uncertain' : 'fail';
        whyNote = aborted ? '停在这条，请求可能没发出，按待确认' : '限流后放弃';
        log(aborted ? `⏹ 停止于 rpid=${c.rpid}（按待确认处理，可重试）`
                    : `✗ rpid=${c.rpid} 连续 ${DELETE_MAX_RETRY - 1} 次限流后放弃（可用「重试未成功」）`, 'err');
      }
      if (result) {
        batchResults.set(c.rpid, result);
        journalAdd(c.rpid, result, whyNote);
        if (result === 'ok') ok++; else if (result === 'uncertain') uncertain++; else fail++;
      } else {
        pending.push(c);
      }
      await waitTick(delay, (left) => `本条已请求 · ${left}s 后下一条 · 已用 ${fmtDur(Date.now() - t0)}`);
    }

    // ── 统一回查（v2.2.2：单条官方接口；仍在则降速重删；walk 仅兜底） ──
    if (pending.length) {
      setStatus(`②回查 0/${pending.length} · 官方单条确认中…`);
      log(`🔍 统一回查 ${pending.length} 条（先 /reply/detail 单条；不可用才全区/整楼翻页）`);
      for (let i = 0; i < pending.length; i++) {
        if (aborted) {
          recheckLeft = pending.length - i;
          for (let k = i; k < pending.length; k++) {
            const left = pending[k];
            batchResults.set(left.rpid, 'uncertain');
            journalAdd(left.rpid, 'uncertain', '回查停了，已经请求但没确认');
            uncertain++;
          }
          log(`回查停了，剩下 ${recheckLeft} 条已经请求但没确认，记为待确认。`, 'warn');
          break;
        }
        const c = pending[i];
        markActive(c.rpid);
        setProg(i, pending.length, '②回查');
        const snippet = String(c.message || '(空)').replace(/\s+/g, ' ').slice(0, 22);
        let v = null;
        try {
          startBeat(() => `②回查 ${i + 1}/${pending.length} · ${snippet} · 请求中 · 已确认 ${ok} · 已用 ${fmtDur(Date.now() - t0)} · 剩余 ${fmtEta((pending.length - i) * 600)}`);
          v = await recheckDefinitive(c);
        } catch (e) { v = { state: 'uncertain', why: e.message || '回查失败' }; }
        finally { stopBeat(); }
        if (v && v.state === 'auth') {
          aborted = true;
          if (!stopWhy) stopWhy = v.why;
          setStatus(`已停止回查：${v.why}。已确认的保留，没查完的不算失败。`);
          log(`回查停止：${v.why}`, 'err');
          v = { state: 'uncertain', why: v.why };
        }
        if (v && v.state === 'fail' && !aborted) {
          let lastClear = false;
          let softWhy = '';
          for (let s = 0; s < SHADOW_RETRY; s++) {
            lastClear = false;
            log(`↻ 评论仍在，降速重试 ${s + 1}/${SHADOW_RETRY} rpid=${c.rpid}`, 'warn');
            await waitTick(SHADOW_WAIT, (left) => `↻ 影子重试 ${s + 1}/${SHADOW_RETRY} · ${left}s 后提交 · rpid=${c.rpid} · 已用 ${fmtDur(Date.now() - t0)}`);
            let dj = null;
            try {
              startBeat(() => `↻ 影子重试 ${s + 1}/${SHADOW_RETRY} · 提交中 · rpid=${c.rpid} · 已用 ${fmtDur(Date.now() - t0)}`);
              dj = await doDelete(c, csrf);
            } catch (e) {
              v = { state: 'uncertain', why: `影子重试提交失败：${e.message || '网络错误'}，不知道这次有没有删掉` };
              break;
            }
            finally { stopBeat(); }
            if (dj && (dj.code === -101 || dj.code === -111)) {
              aborted = true;
              const why = ERR_TEXT[String(dj.code)] || `code=${dj.code}`;
              if (!stopWhy) stopWhy = why;
              setStatus(`已停止回查：${why}。已确认的保留，没查完的不算失败。`);
              log(`回查停止：${why}`, 'err');
              v = { state: 'uncertain', why };
              break;
            }
            await sleep(800);
            let again = null;
            try {
              startBeat(() => `↻ 影子重试 ${s + 1}/${SHADOW_RETRY} · 回查中 · rpid=${c.rpid} · 已用 ${fmtDur(Date.now() - t0)}`);
              again = await oracleCheck(c);
            } catch (e) {
              softWhy = `影子重试后回查失败：${e.message || '网络错误'}`;
              again = null;
            }
            finally { stopBeat(); }
            if (again && again.soft) softWhy = again.why || '影子重试后回查没有结果';
            if (again && again.state === 'auth') {
              aborted = true;
              if (!stopWhy) stopWhy = again.why;
              setStatus(`已停止回查：${again.why}。已确认的保留，没查完的不算失败。`);
              log(`回查停止：${again.why}`, 'err');
              v = { state: 'uncertain', why: again.why };
              break;
            }
            if (again && again.state === 'ok') {
              v = { state: 'ok', why: `影子失败后第${s + 1}次重试已确认删除` };
              shadowFixed++;
              lastClear = true;
              break;
            }
            if (again && again.state === 'fail') {
              v = again;
              lastClear = true;
            }
          }
          if (v && v.state === 'fail' && !lastClear) {
            v = { state: 'uncertain', why: softWhy || '影子重试后没能确认评论是否还在' };
          }
        }
        let state, msg;
        if (!v || !v.state) { state = 'uncertain'; msg = `回查不可用（区/楼接口异常），↗跳转复核`; }
        else if (v.state === 'ok') { state = 'ok'; msg = `已确认删除（${v.why}）`; }
        else if (v.state === 'fail') { state = 'fail'; msg = `未生效（${v.why}）`; }
        else { state = 'uncertain'; msg = v.why; }
        batchResults.set(c.rpid, state);
        journalAdd(c.rpid, state, msg);
        if (state === 'ok') ok++; else if (state === 'uncertain') uncertain++; else fail++;
        log(`${state === 'ok' ? '✓' : state === 'fail' ? '✗' : '～'} rpid=${c.rpid} ${msg}`,
            state === 'ok' ? 'ok' : state === 'fail' ? 'err' : 'warn');
        await sleep(150);
      }
    }

    markActive(null);
    const unsent = targets.length - seen;
    setProg(targets.length, targets.length, aborted ? '已停止' : (fail || uncertain || unsent) ? '未完全删除' : '完成');
    const sec = Math.max(1, Math.round((Date.now() - t0) / 1000));
    let focusNote = '';
    if (fail > 0 && uncertain > 0) {
      filtState = 'bad';
      const sel = document.getElementById(`${P}-statesel`);
      if (sel) sel.value = 'bad';
      focusNote = ' 列表已切到「未成功」（含未生效和待确认）。';
    } else if (fail > 0) {
      filtState = 'fail';
      const sel = document.getElementById(`${P}-statesel`);
      if (sel) sel.value = 'fail';
      focusNote = ' 列表已切到「未生效」。';
    } else if (uncertain > 0) {
      filtState = 'uncertain';
      const sel = document.getElementById(`${P}-statesel`);
      if (sel) sel.value = 'uncertain';
      focusNote = ' 列表已切到「待确认」。';
    } else if (unsent > 0) {
      filtState = 'none';
      const sel = document.getElementById(`${P}-statesel`);
      if (sel) sel.value = 'none';
      focusNote = ' 列表已切到「未处理」（这些还没请求）。';
    }
    if (unsent && filtState !== 'none' && filtState !== 'all') {
      focusNote += `另有 ${unsent} 条还没请求，这个筛选里看不到。`;
    }
    if (focusNote) {
      const left = [];
      if (filterKw) left.push(`关键词「${filterKw}」`);
      if (filtSrc !== 'all') left.push(`来源 ${SRC_TEXT[filtSrc] || filtSrc}`);
      if (filtType !== 'all') left.push(`类型 ${typeText(filtType)}`);
      if (onlyClash) left.push('只看冲突');
      if (left.length) focusNote += `另外还留着${left.join('、')}，被筛掉的不在眼前。`;
    }
    const stopBits = [unsent ? `未请求 ${unsent}` : '', recheckLeft ? `回查未完成 ${recheckLeft}` : ''].filter(Boolean).join('，');
    const skipBit = skippedOk ? `跳过已确认 ${skippedOk}。` : '';
    const trust = recheckOn ? '' : '未开回查，接口受理的记为待确认。';
    const deleteBad = !!(fail || uncertain || unsent || recheckLeft || aborted);
    const sumHead = aborted ? `已停止。${stopWhy ? `${stopWhy}。` : ''}` : (fail || uncertain || unsent || recheckLeft) ? '未完全删除：' : '完成：';
    const sum = `${sumHead}确认删除 ${ok}，未生效 ${fail}，待确认 ${uncertain}${shadowFixed ? `（影子重试救回 ${shadowFixed}）` : ''}。用时 ${sec}s。${trust}${skipBit}${stopBits ? stopBits + '。' : ''}${focusNote}`;
    saveLastRun(sum);
    setStatus(sum);
    log(`==== ${sum} ====`, deleteBad ? 'warn' : 'ok');
    deleting = false;
    lockWhileDeleting(false);
    armStop(false);
    renderList(); updCount();
    } finally {
      const crashed = deleting;
      confirming = false;
      if (crashed) {
        deleting = false;
        stopBeat();
        lockWhileDeleting(false);
        armStop(false);
        let parked = 0;
        try {
          for (const c of pending) {
            if (batchResults && batchResults.has(c.rpid)) continue;
            journalAdd(c.rpid, 'uncertain', '删除中途出错，已经请求但没确认');
            if (batchResults) batchResults.set(c.rpid, 'uncertain');
            uncertain++;
            parked++;
          }
        } catch (e2) { /* 记不下也要把按钮解开 */ }
        if (parked && !recheckLeft) recheckLeft = parked;
        const unsentCrash = Math.max(0, planned - seen);
        const crashBits = [unsentCrash ? `未请求 ${unsentCrash} 条` : '', recheckLeft ? `回查未完成 ${recheckLeft} 条` : ''].filter(Boolean).join('，');
        const crashText = `这次删除中途出错，已停下。${stopWhy ? `${stopWhy}。` : ''}已请求 ${seen}${planned ? ` / ${planned}` : ''} 条：确认删除 ${ok}，未生效 ${fail}，待确认 ${uncertain}。${crashBits ? `${crashBits}。` : ''}已经发出的请求不会收回，请看日志和列表上的标记。`;
        saveLastRun(crashText);
        setStatus(crashText);
        log(crashText, 'err');
        try { renderList(); updCount(); } catch (e2) { /* 列表画不出来也要解开按钮 */ }
      } else {
        lockWhileDeleting(false);
        updCount();
      }
    }
  }

  /* ═══════════ 小部件 ═══════════ */
  function log(msg, type) {
    const el = document.getElementById(`${P}-log`);
    if (!el) return;
    const d = document.createElement('div');
    const keep = type === 'keep';
    d.className = `${P}-log-line ${P}-${keep ? 'info' : (type || 'info')}${keep ? ` ${P}-keep` : ''}`;
    if (logOnlyBad && !keep && type !== 'err' && type !== 'warn') d.classList.add(`${P}-log-hide`);
    d.textContent = `[${new Date().toLocaleTimeString('zh-CN', { hour12: false })}] ${msg}`;
    const stick = el.scrollHeight - el.scrollTop - el.clientHeight < 48;
    el.appendChild(d);
    let trimmed = false;
    while (el.children.length > 300) {
      if (!dropLogLine(el)) break;
      trimmed = true;
    }
    if (trimmed) {
      let note = el.querySelector(`.${P}-log-trim`);
      if (!note) {
        note = document.createElement('div');
        note.className = `${P}-log-line ${P}-warn ${P}-log-trim`;
        note.textContent = '更早的普通日志已优先省略。警告和操作说明会多留一会儿，仍超过约 300 行时才丢掉最旧的。';
      }
      el.insertBefore(note, el.firstChild);
      while (el.children.length > 301) {
        if (!dropLogLine(el)) break;
      }
    }
    if (stick) el.scrollTop = el.scrollHeight;
    if (trimmed) refreshLogCopyTitle();
  }
  function refreshLogCopyTitle() {
    const btn = document.getElementById(`${P}-logcopy`);
    const box = document.getElementById(`${P}-log`);
    if (!btn || !box) return;
    const bits = ['复制当前看得到的日志。'];
    if (logOnlyBad) bits.push('只看问题开着，藏起来的行不复制。');
    bits.push(box.querySelector(`.${P}-log-trim`) ? '更早被省略的行也不在其中。' : '更早的行还没有被省略。');
    btn.title = bits.join('');
  }

  function dropLogLine(el) {
    let plain = null;
    let important = null;
    for (const node of el.children) {
      if (node.classList.contains(`${P}-log-trim`)) continue;
      const keep = node.classList.contains(`${P}-err`) || node.classList.contains(`${P}-warn`) || node.classList.contains(`${P}-keep`);
      if (!keep) { plain = node; break; }
      if (!important) important = node;
    }
    const drop = plain || important;
    if (!drop) return false;
    el.removeChild(drop);
    return true;
  }
  function badInList() {
    const jm = journalMap();
    return comments.filter((c) => {
      const st = jm.get(idExact(c.rpid));
      return c.oid && c.type && (st === 'fail' || st === 'uncertain');
    });
  }
  function readDelay(announce) {
    const el = document.getElementById(`${P}-delay`);
    const raw = parseInt(el && el.value, 10);
    const n = Math.max(200, Math.min(5000, raw || DELAY_DEFAULT));
    const clamped = Number.isFinite(raw) && raw !== n;
    if (el && el.value !== String(n)) el.value = String(n);
    if (announce || clamped) saveSettings();
    if (announce) say(clamped ? `间隔已改成 ${n} 毫秒。允许 200 到 5000。下次删除用这个。` : `间隔 ${n} 毫秒。下次删除用这个。`);
    return n;
  }
  function readScanPages(announce) {
    const el = document.getElementById(`${P}-scanpages`);
    const raw = parseInt(el && el.value, 10);
    const n = Math.max(1, Math.min(10, raw || VIDEO_SCAN_PAGES_DEFAULT));
    const clamped = Number.isFinite(raw) && raw !== n;
    if (el && el.value !== String(n)) el.value = String(n);
    try { localStorage.setItem(`${P}_scanpages`, String(n)); } catch (e) { /* 记不住就用这一次的值 */ }
    if (announce) say(clamped ? `每个视频已改成 ${n} 页。允许 1 到 10。下次扫描用这个。` : `每个视频扫 ${n} 页。下次扫描用这个。`);
    return n;
  }
  function paintStatus(t) { const el = document.getElementById(`${P}-status`); if (el) el.textContent = t; }
  function setStatus(t) {
    if (beatTimer && !aborted) { log(t, 'keep'); return; }
    paintStatus(t);
  }
  function say(t) {
    if (beatTimer) log(t, 'keep');
    else setStatus(t);
  }

  function digestLine() {
    const by = new Map();
    let ok = 0, bad = 0, nodeal = 0;
    const jm = journalMap();
    for (const c of comments) {
      const name = typeText(c.type);
      by.set(name, (by.get(name) || 0) + 1);
      const st = jm.get(idExact(c.rpid));
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

  let askOpen = false;
  function ask(text, okLabel) {
    if (askOpen) {
      setStatus('请先处理当前确认框。');
      return Promise.resolve(false);
    }
    return new Promise((resolve) => {
      const mask = document.getElementById(`${P}-ask`);
      const msg = document.getElementById(`${P}-askmsg`);
      const ok = document.getElementById(`${P}-askok`);
      const no = document.getElementById(`${P}-askno`);
      if (!mask || !msg || !ok || !no) { resolve(false); return; }
      askOpen = true;
      msg.textContent = text;
      ok.textContent = okLabel || '确认';
      mask.style.display = 'flex';
      const done = (v) => {
        askOpen = false;
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
  function paintBusy(label) {
    const btn = document.getElementById(`${P}-toggle`);
    if (!savedTitle) savedTitle = document.title;
    if (label) {
      document.title = `${label} · ${savedTitle}`;
      if (btn) {
        const pct = String(label).match(/(\d+)%\s*\(\d+\/\d+\)/);
        if (pct) btn.dataset.pct = pct[1] + '%';
        btn.dataset.busy = '1';
        btn.textContent = btn.dataset.pct || '…';
        btn.title = `${label}。点此打开面板`;
      }
    } else {
      if (savedTitle) document.title = savedTitle;
      if (btn) {
        btn.dataset.busy = '';
        delete btn.dataset.pct;
        btn.textContent = '\u{1F5D1}\uFE0F';
        btn.title = `B站评论批量删除 v${VERSION}`;
      }
    }
  }
  function showProg(show) {
    const el = document.getElementById(`${P}-prog`);
    if (!el) return;
    el.style.display = show ? 'flex' : 'none';
    if (show) {
      document.getElementById(`${P}-fill`).style.width = '0%';
      document.getElementById(`${P}-pct`).textContent = '0%';
    } else paintBusy(null);
  }
  function setProg(done, total, phase) {
    const pct = total ? Math.round((done / total) * 100) : 0;
    const fill = document.getElementById(`${P}-fill`);
    const pctEl = document.getElementById(`${P}-pct`);
    const label = `${phase ? phase + ' ' : ''}${pct}% (${done}/${total})`;
    if (fill) fill.style.width = pct + '%';
    if (pctEl) pctEl.textContent = label;
    if (phase) paintBusy(label);
  }

  /* ═══════════ 初始化 ═══════════ */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => { injectCSS(); buildUI(); });
  } else {
    injectCSS(); buildUI();
  }
})();