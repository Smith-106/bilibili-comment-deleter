// ==UserScript==
// @name         B站评论批量删除
// @namespace    bilibili-comment-deleter
// @version      2.0.1
// @description  通过 AICU API 获取全部评论并批量删除，支持预览选择、进度显示、速率控制
// @author       You
// @match        *://*.bilibili.com/*
// @grant        GM_xmlhttpRequest
// @connect      api.aicu.cc
// @connect      apibackup2.aicu.cc
// @run-at       document-idle
// ==/UserScript==

(function () {
  'use strict';

  /* ═══════════ 常量 ═══════════ */
  const P = 'bcd'; // class/id 前缀
  const DELAY_DEFAULT = 400;
  const AICU_PS = 500; // AICU 每页条数
  const AICU_DELAY = 3000; // AICU 翻页延迟（避免风控）
  const AICU_APIS = [
    'https://api.aicu.cc/api/v3/search/getreply',
    'https://apibackup2.aicu.cc:88/api/v3/search/getreply',
  ];

  /* ═══════════ 状态 ═══════════ */
  let comments = [];
  let selected = new Set();
  let deleting = false;
  let aborted = false;
  let stats = { ok: 0, fail: 0 };

  /* ═══════════ 工具 ═══════════ */
  const $ = (s) => document.querySelector(s);
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const getCSRF = () => document.cookie.match(/bili_jct=([^;]+)/)?.[1] || '';

  /** 跨域 GET 请求（用于 AICU API） */
  function gmFetch(url) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET',
        url,
        responseType: 'json',
        timeout: 15000,
        onload(res) {
          if (res.status !== 200) {
            reject(new Error(`HTTP ${res.status}`));
            return;
          }
          // 防止接口返回 HTML 错误页时解析出 null,报无法理解的错误
          const ct = (res.responseHeaders || '').toLowerCase();
          const notJson =
            !ct.includes('application/json') ||
            res.response === null ||
            typeof res.response !== 'object';
          if (notJson) {
            reject(new Error('接口返回的不是 JSON(可能已失效或触发风控)'));
            return;
          }
          resolve(res.response);
        },
        onerror(err) { reject(new Error('网络错误')); },
        ontimeout() { reject(new Error('请求超时')); },
      });
    });
  }

  /* ═══════════ API ═══════════ */
  /** B 站 /x/ 接口仅在 api.bilibili.com 提供,www 域名下会返回 404 错误页 */
  const API_HOST = 'https://api.bilibili.com';

  async function getUserInfo() {
    const res = await fetch(`${API_HOST}/x/web-interface/nav`, {
      credentials: 'include',
    });
    if (!res.ok) throw new Error(`nav 接口 HTTP ${res.status}`);
    const d = await res.json();
    if (d.code !== 0) throw new Error(d.message || '未登录');
    return { mid: d.data.mid, uname: d.data.uname };
  }

  /** 从 AICU API 获取用户的全部评论 */
  async function fetchAicuComments(uid) {
    let page = 1;
    let totalCount = 0;
    let aicuUrl = AICU_APIS[0];

    while (true) {
      if (aborted) break;

      const url = `${aicuUrl}?uid=${uid}&pn=${page}&ps=${AICU_PS}&mode=0`;
      let data;
      try {
        data = await gmFetch(url);
      } catch (e) {
        // 主 API 失败，尝试备用
        if (aicuUrl === AICU_APIS[0]) {
          log('AICU 主接口失败，尝试备用...', 'warn');
          aicuUrl = AICU_APIS[1];
          continue;
        }
        throw e;
      }

      if (data.code !== 0) {
        log(`AICU 错误: ${data.message || data.code}`, 'err');
        break;
      }

      const replies = data.data?.replies || [];
      if (page === 1) {
        totalCount = data.data?.cursor?.all_count || 0;
        log(`AICU 共收录 ${totalCount} 条评论`, 'info');
      }

      if (!replies.length) {
        log('AICU 数据已全部获取', 'info');
        break;
      }

      for (const item of replies) {
        const rpid = Number(item.rpid);
        if (!rpid) continue;
        if (comments.some((c) => c.rpid === rpid)) continue;

        const dyn = item.dyn || {};
        const oid = Number(dyn.oid);
        const type = Number(dyn.type);
        if (!oid || !type) continue;

        comments.push({
          rpid,
          oid,
          type,
          message: (item.message || '').slice(0, 200),
          ctime: item.time,
        });
      }

      log(`第 ${page} 页: +${replies.length} 条 (累计 ${comments.length}/${totalCount})`, 'info');

      if (data.data?.cursor?.is_end) break;

      page++;
      await sleep(AICU_DELAY);
    }
  }

  async function delComment(type, oid, rpid) {
    const body = new URLSearchParams({
      type: String(type),
      oid: String(oid),
      rpid: String(rpid),
      csrf: getCSRF(),
    });
    const d = await (
      await fetch(`${API_HOST}/x/v2/reply/del`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body,
        credentials: 'include',
      })
    ).json();
    if (d.code !== 0) throw new Error(d.message || `code:${d.code}`);
  }

  /* ═══════════ 样式 ═══════════ */
  function injectCSS() {
    const s = document.createElement('style');
    s.textContent = `
      #${P}-toggle {
        position:fixed; bottom:80px; right:24px; z-index:999999;
        width:48px; height:48px; border-radius:50%; border:none;
        background:#00a1d6; color:#fff; font-size:22px; cursor:pointer;
        box-shadow:0 2px 14px rgba(0,0,0,.35);
        display:flex; align-items:center; justify-content:center;
        transition:transform .2s, box-shadow .2s;
        user-select:none;
      }
      #${P}-toggle:hover { transform:scale(1.12); box-shadow:0 4px 20px rgba(0,161,214,.45); }

      #${P}-panel {
        position:fixed; top:50%; right:24px; transform:translateY(-50%);
        width:460px; max-height:82vh; z-index:999998;
        background:#1e1e2e; border-radius:14px;
        box-shadow:0 10px 40px rgba(0,0,0,.55);
        color:#e0e0e0; font:13px/1.6 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;
        display:flex; flex-direction:column; overflow:hidden;
      }

      .${P}-hd {
        display:flex; align-items:center; justify-content:space-between;
        padding:14px 18px; background:#252540;
        font-size:15px; font-weight:600; letter-spacing:.3px;
      }
      .${P}-hd button { background:none; border:none; color:#888; font-size:20px; cursor:pointer; padding:0 4px; line-height:1; }
      .${P}-hd button:hover { color:#fff; }

      .${P}-sec { padding:10px 18px; border-bottom:1px solid #2c2c48; }
      .${P}-row { display:flex; gap:8px; align-items:center; flex-wrap:wrap; }

      .${P}-btn {
        padding:7px 16px; border-radius:7px; border:1px solid #444;
        background:#2a2a3e; color:#e0e0e0; cursor:pointer; font-size:12px;
        transition:background .15s, border-color .15s; white-space:nowrap;
      }
      .${P}-btn:hover:not(:disabled) { background:#3a3a5e; }
      .${P}-btn:disabled { opacity:.4; cursor:not-allowed; }
      .${P}-btn-p { background:#00a1d6; border-color:#00a1d6; color:#fff; }
      .${P}-btn-p:hover:not(:disabled) { background:#00b5e5; }
      .${P}-btn-d { background:#ff4757; border-color:#ff4757; color:#fff; }
      .${P}-btn-d:hover:not(:disabled) { background:#ff6b7a; }

      .${P}-bar-wrap {
        padding:10px 18px; display:flex; align-items:center; gap:12px;
      }
      .${P}-bar { flex:1; height:8px; background:#333; border-radius:4px; overflow:hidden; }
      .${P}-fill { height:100%; width:0%; background:linear-gradient(90deg,#00a1d6,#23e5a0); border-radius:4px; transition:width .3s; }
      .${P}-pct { font-size:12px; color:#aaa; min-width:90px; text-align:right; white-space:nowrap; }

      .${P}-toolbar {
        display:flex; align-items:center; justify-content:space-between;
        padding:7px 18px; background:#20203a; font-size:12px; color:#999;
      }
      .${P}-toolbar label { cursor:pointer; display:flex; align-items:center; gap:5px; }
      .${P}-toolbar input[type=checkbox] { accent-color:#00a1d6; }

      .${P}-list {
        flex:1; min-height:100px; max-height:320px;
        overflow-y:auto; padding:0;
      }
      .${P}-list::-webkit-scrollbar { width:6px; }
      .${P}-list::-webkit-scrollbar-thumb { background:#444; border-radius:3px; }
      .${P}-list::-webkit-scrollbar-track { background:transparent; }

      .${P}-item {
        display:flex; align-items:center; gap:8px;
        padding:9px 18px; border-bottom:1px solid #262642;
        transition:background .12s; font-size:12px;
      }
      .${P}-item:hover { background:#252540; }
      .${P}-item.checked { background:#1a2a3e; }
      .${P}-item input[type=checkbox] { accent-color:#00a1d6; cursor:pointer; flex-shrink:0; }
      .${P}-item-text { flex:1; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; color:#ccc; }
      .${P}-item-time { color:#5a5a7a; font-size:11px; flex-shrink:0; }

      .${P}-empty { padding:40px 18px; text-align:center; color:#555; font-size:13px; }

      .${P}-log {
        max-height:160px; overflow-y:auto; padding:8px 18px;
        font-size:11px; font-family:'Cascadia Code',Consolas,'Courier New',monospace;
        background:#141428; border-top:1px solid #2c2c48;
      }
      .${P}-log::-webkit-scrollbar { width:5px; }
      .${P}-log::-webkit-scrollbar-thumb { background:#444; border-radius:3px; }
      .${P}-log-line { padding:2px 0; word-break:break-all; }
      .${P}-log-ok   { color:#2ed573; }
      .${P}-log-err  { color:#ff4757; }
      .${P}-log-warn { color:#ffa502; }
      .${P}-log-info { color:#70a1ff; }

      .${P}-input {
        width:72px; padding:5px 8px; border-radius:5px;
        border:1px solid #444; background:#2a2a3e; color:#e0e0e0;
        font-size:12px; text-align:center;
      }
      .${P}-input:focus { outline:none; border-color:#00a1d6; }

      .${P}-sep { width:1px; height:20px; background:#444; margin:0 4px; }
    `;
    document.head.appendChild(s);
  }

  /* ═══════════ 构建 UI ═══════════ */
  function buildUI() {
    const toggle = document.createElement('button');
    toggle.id = `${P}-toggle`;
    toggle.innerHTML = '🗑️';
    toggle.title = 'B站评论批量删除';
    document.body.appendChild(toggle);

    const panel = document.createElement('div');
    panel.id = `${P}-panel`;
    panel.style.display = 'none';
    panel.innerHTML = `
      <div class="${P}-hd">
        <span>🗑️ B站评论批量删除</span>
        <button id="${P}-close">×</button>
      </div>

      <div class="${P}-sec">
        <div class="${P}-row">
          <button class="${P}-btn ${P}-btn-p" id="${P}-load">📥 获取全部评论</button>
          <button class="${P}-btn" id="${P}-stop" style="display:none">⏹ 停止</button>
          <div class="${P}-sep"></div>
          <span style="color:#888;font-size:12px">删除间隔</span>
          <input class="${P}-input" type="number" id="${P}-delay" value="${DELAY_DEFAULT}" min="200" max="5000" step="50">
          <span style="color:#888;font-size:12px">ms</span>
        </div>
      </div>

      <div class="${P}-sec">
        <div class="${P}-row">
          <button class="${P}-btn ${P}-btn-d" id="${P}-dsel" disabled>🔥 删除选中</button>
          <button class="${P}-btn ${P}-btn-d" id="${P}-dall" disabled>💣 删除全部</button>
        </div>
      </div>

      <div class="${P}-toolbar">
        <label><input type="checkbox" id="${P}-sa"> 全选</label>
        <span id="${P}-cnt">0 条评论</span>
      </div>

      <div class="${P}-list" id="${P}-list">
        <div class="${P}-empty">点击「获取全部评论」拉取你的所有评论（通过 AICU API）</div>
      </div>

      <div class="${P}-bar-wrap" id="${P}-prog" style="display:none">
        <div class="${P}-bar"><div class="${P}-fill" id="${P}-fill"></div></div>
        <span class="${P}-pct" id="${P}-pct">0%</span>
      </div>

      <div class="${P}-log" id="${P}-log"></div>
    `;
    document.body.appendChild(panel);

    toggle.onclick = () => {
      panel.style.display = panel.style.display === 'none' ? 'flex' : 'none';
    };
    $(`#${P}-close`).onclick = () => (panel.style.display = 'none');
    $(`#${P}-load`).onclick = loadComments;
    $(`#${P}-dsel`).onclick = () => startDelete(false);
    $(`#${P}-dall`).onclick = () => {
      if (!confirm(`确认删除全部 ${comments.length} 条评论？此操作不可撤销！`)) return;
      startDelete(true);
    };
    $(`#${P}-stop`).onclick = () => {
      aborted = true;
      log('正在停止...', 'warn');
    };
    $(`#${P}-sa`).onchange = onSelAll;
  }

  /* ═══════════ 渲染评论列表 ═══════════ */
  function renderList() {
    const el = $(`#${P}-list`);
    if (!comments.length) {
      el.innerHTML = `<div class="${P}-empty">没有找到评论 🎉</div>`;
      return;
    }
    el.innerHTML = comments
      .map((c) => {
        const t = c.ctime ? new Date(c.ctime * 1000).toLocaleDateString('zh-CN') : '';
        const chk = selected.has(c.rpid) ? 'checked' : '';
        return `<div class="${P}-item ${chk ? 'checked' : ''}" data-rpid="${c.rpid}">
          <input type="checkbox" data-rpid="${c.rpid}" ${chk}>
          <span class="${P}-item-text" title="${escHtml(c.message)}">${escHtml(c.message) || '(无内容)'}</span>
          <span class="${P}-item-time">${t}</span>
        </div>`;
      })
      .join('');

    el.querySelectorAll('input[type=checkbox]').forEach((cb) => {
      cb.onchange = () => {
        const rpid = Number(cb.dataset.rpid);
        cb.checked ? selected.add(rpid) : selected.delete(rpid);
        cb.closest(`.${P}-item`).classList.toggle('checked', cb.checked);
        updCount();
      };
    });
    updCount();
  }

  function updCount() {
    $(`#${P}-cnt`).textContent = `${selected.size}/${comments.length} 条`;
    $(`#${P}-dsel`).disabled = !selected.size || deleting;
    $(`#${P}-dall`).disabled = !comments.length || deleting;
  }

  function onSelAll() {
    const all = $(`#${P}-sa`).checked;
    selected = all ? new Set(comments.map((c) => c.rpid)) : new Set();
    renderList();
    $(`#${P}-sa`).checked = all;
  }

  function showProg(show) {
    $(`#${P}-prog`).style.display = show ? 'flex' : 'none';
    $(`#${P}-stop`).style.display = show ? 'inline-block' : 'none';
    if (show) {
      $(`#${P}-fill`).style.width = '0%';
      $(`#${P}-pct`).textContent = '0%';
    }
  }

  function setProg(done, total) {
    const pct = Math.round((done / total) * 100);
    $(`#${P}-fill`).style.width = pct + '%';
    $(`#${P}-pct`).textContent = `${pct}% (${done}/${total})`;
  }

  function log(msg, type = 'info') {
    const el = $(`#${P}-log`);
    const d = document.createElement('div');
    d.className = `${P}-log-line ${P}-log-${type}`;
    d.textContent = `[${now()}] ${msg}`;
    el.appendChild(d);
    el.scrollTop = el.scrollHeight;
  }

  function now() {
    return new Date().toLocaleTimeString('zh-CN', { hour12: false });
  }

  function escHtml(s) {
    return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }

  function lockBtns(locked) {
    $(`#${P}-load`).disabled = locked;
    $(`#${P}-dsel`).disabled = locked;
    $(`#${P}-dall`).disabled = locked;
  }

  /* ═══════════ 控制器：通过 AICU 获取全部评论 ═══════════ */
  async function loadComments() {
    const btn = $(`#${P}-load`);
    btn.disabled = true;
    btn.textContent = '⏳ 获取中...';
    comments = [];
    selected.clear();
    aborted = false;

    try {
      const csrf = getCSRF();
      if (!csrf) {
        log('未检测到 bili_jct，请先登录B站', 'err');
        return;
      }

      const user = await getUserInfo();
      log(`当前账号: ${user.uname} (UID: ${user.mid})`, 'info');
      log('正在通过 AICU API 获取全部评论...', 'info');

      await fetchAicuComments(user.mid);

      log(`✅ 共获取 ${comments.length} 条评论`, 'ok');
      renderList();
    } catch (e) {
      log(`获取失败: ${e.message}`, 'err');
    } finally {
      btn.disabled = false;
      btn.textContent = '📥 获取全部评论';
      updCount();
    }
  }

  /* ═══════════ 控制器：删除评论 ═══════════ */
  async function startDelete(all) {
    const targets = all
      ? [...comments]
      : comments.filter((c) => selected.has(c.rpid));
    if (!targets.length) {
      log('没有可删除的评论', 'warn');
      return;
    }

    deleting = true;
    aborted = false;
    stats = { ok: 0, fail: 0 };
    const delay = parseInt($(`#${P}-delay`).value) || DELAY_DEFAULT;

    lockBtns(true);
    showProg(true);
    log(`🔥 开始删除 ${targets.length} 条，间隔 ${delay}ms`, 'warn');

    for (let i = 0; i < targets.length; i++) {
      if (aborted) {
        log('⏹ 已停止', 'warn');
        break;
      }

      const c = targets[i];
      setProg(i, targets.length);

      try {
        await delComment(c.type, c.oid, c.rpid);
        stats.ok++;
        log(`✓ ${c.message.slice(0, 50)}`, 'ok');
      } catch (e) {
        stats.fail++;
        log(`✗ ${c.message.slice(0, 50)} → ${e.message}`, 'err');
        if (e.message.includes('频率') || e.message.includes('频繁')) {
          const cool = delay * 3;
          log(`⏳ 频率限制，冷却 ${cool}ms...`, 'warn');
          await sleep(cool);
        }
      }

      await sleep(delay);
    }

    setProg(targets.length, targets.length);
    log(
      `🎉 完成！成功 ${stats.ok}，失败 ${stats.fail}`,
      stats.fail ? 'warn' : 'ok'
    );
    deleting = false;
    lockBtns(false);
    showProg(false);
  }

  /* ═══════════ 初始化 ═══════════ */
  injectCSS();
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', buildUI);
  } else {
    buildUI();
  }
})();
