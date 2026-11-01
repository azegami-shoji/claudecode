'use strict';
(() => {
  const $ = (s, root = document) => root.querySelector(s);
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const SVGNS = 'http://www.w3.org/2000/svg';

  const COLORS = ['#e53935', '#1e88e5', '#2e7d32', '#f9a825'];
  const MONTHS = [4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 2, 3];
  const START_CASH = 10000;
  const MAX_CARDS = 5;
  const CARD_TYPES = [
    { key: 'kyuko', name: '急行カード', dice: 2, w: 55 },
    { key: 'tokkyu', name: '特急カード', dice: 3, w: 30 },
    { key: 'shinkansen', name: '新幹線カード', dice: 4, w: 15 },
  ];
  const SQUARE_LABEL = { plus: '青マス', minus: '赤マス', card: '黄マス' };
  const WORLD = { minX: 0, minY: 0, maxX: 1380, maxY: 1460 };
  const MAX_W = 1800;

  function fmt(v) {
    const neg = v < 0;
    v = Math.abs(Math.round(v));
    const oku = Math.floor(v / 10000), man = v % 10000;
    let s = '';
    if (oku) s += oku.toLocaleString() + '億';
    if (man || !oku) s += man.toLocaleString() + '万';
    return (neg ? '-' : '') + s + '円';
  }

  function mulberry32(a) {
    return () => {
      a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // ---------- 盤面 ----------
  const nodes = [];
  const adj = [];
  const links = [];
  const stationByName = {};

  function addNode(n) {
    n.id = nodes.length;
    nodes.push(n);
    adj.push([]);
    return n.id;
  }
  function link(a, b, sea) {
    adj[a].push(b);
    adj[b].push(a);
    links.push({ a, b, sea: !!sea });
  }

  function buildBoard() {
    const rnd = mulberry32(20261022);
    STATIONS.forEach(s => {
      stationByName[s.name] = addNode({
        type: 'station', name: s.name, lp: s.lp,
        x: (s.lon - PROJ.lon0) * PROJ.kx, y: (PROJ.lat0 - s.lat) * PROJ.ky,
        props: s.props.map(([name, price, rate]) => ({ name, price, rate, owner: -1 })),
      });
    });
    ROUTES.forEach(([a, b, kind]) => {
      const A = nodes[stationByName[a]], B = nodes[stationByName[b]];
      const d = Math.hypot(A.x - B.x, A.y - B.y);
      const n = Math.max(1, Math.min(4, Math.round(d / 40)));
      let prev = A.id;
      for (let i = 1; i <= n; i++) {
        const t = i / (n + 1);
        const r = rnd();
        const type = r < 0.45 ? 'plus' : r < 0.8 ? 'minus' : 'card';
        const id = addNode({ type, x: A.x + (B.x - A.x) * t, y: A.y + (B.y - A.y) * t });
        link(prev, id, kind === 'sea');
        prev = id;
      }
      link(prev, B.id, kind === 'sea');
    });
  }

  const distCache = new Map();
  function distFrom(target) {
    if (distCache.has(target)) return distCache.get(target);
    const d = new Array(nodes.length).fill(Infinity);
    d[target] = 0;
    const q = [target];
    for (let i = 0; i < q.length; i++) {
      const u = q[i];
      for (const v of adj[u]) if (d[v] === Infinity) { d[v] = d[u] + 1; q.push(v); }
    }
    distCache.set(target, d);
    return d;
  }

  // 出目ちょうどで止まれるマス (直前のマスへは戻れない。行き止まりのみ折り返し可)
  // 目的地は途中でも止まれる
  function reachable(start, steps, dest) {
    const res = new Map();
    let frontier = [{ node: start, prev: -1, path: [] }];
    for (let s = 1; s <= steps; s++) {
      const next = [];
      const seen = new Set();
      for (const f of frontier) {
        let nbrs = adj[f.node].filter(n => n !== f.prev);
        if (nbrs.length === 0) nbrs = adj[f.node];
        for (const n of nbrs) {
          const key = n * 100000 + f.node;
          if (seen.has(key)) continue;
          seen.add(key);
          const path = f.path.concat(n);
          if (n === dest && !res.has(n)) res.set(n, path);
          next.push({ node: n, prev: f.node, path });
        }
      }
      frontier = next;
    }
    frontier.forEach(f => { if (!res.has(f.node)) res.set(f.node, f.path); });
    return res;
  }

  // ---------- ゲーム状態 ----------
  let G = null;
  const cur = () => G.players[G.turn];
  const yearFactor = () => 1 + 0.25 * (G.year - 1);
  const delay = (ms = 600) => (G.fast ? ms * 0.25 : ms);
  const stations = () => nodes.filter(n => n.type === 'station');

  function monopolyOwner(n) {
    const o = n.props[0].owner;
    return o >= 0 && n.props.every(p => p.owner === o) ? o : -1;
  }
  function ownedProps(pi) {
    const list = [];
    stations().forEach(n => n.props.forEach(p => { if (p.owner === pi) list.push({ st: n, p }); }));
    return list;
  }
  function assets(pi) {
    return G.players[pi].cash + ownedProps(pi).reduce((s, o) => s + o.p.price, 0);
  }
  function income(pi) {
    let sum = 0;
    stations().forEach(n => {
      const mono = monopolyOwner(n) === pi ? 2 : 1;
      n.props.forEach(p => { if (p.owner === pi) sum += (p.price * p.rate / 100) * mono; });
    });
    return Math.round(sum);
  }
  function drawCard() {
    let r = Math.random() * CARD_TYPES.reduce((s, c) => s + c.w, 0);
    for (const c of CARD_TYPES) { if ((r -= c.w) < 0) return c.key; }
    return CARD_TYPES[0].key;
  }
  const cardDef = key => CARD_TYPES.find(c => c.key === key);

  // ---------- SVG描画 ----------
  const svg = $('#map');
  const layers = {};
  const tokenEls = [];
  function el(tag, attrs, parent) {
    const e = document.createElementNS(SVGNS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  function drawBoard() {
    svg.innerHTML = '';
    ['sea', 'land', 'routes', 'squares', 'stations', 'marks', 'path', 'cands', 'tokens'].forEach(n => {
      layers[n] = el('g', { class: 'layer-' + n }, svg);
    });
    el('rect', { x: -3000, y: -3000, width: 7000, height: 7000, class: 'sea' }, layers.sea);
    el('path', { d: COAST_OTHER, class: 'foreign' }, layers.land);
    el('path', { d: COAST_JAPAN, class: 'land' }, layers.land);
    links.forEach(l => {
      const A = nodes[l.a], B = nodes[l.b];
      el('line', { x1: A.x, y1: A.y, x2: B.x, y2: B.y, class: l.sea ? 'route sea-route' : 'route' }, layers.routes);
    });
    nodes.forEach(n => {
      if (n.type === 'station') {
        const g = el('g', { class: 'station', 'data-id': n.id }, layers.stations);
        n.el = el('rect', { x: n.x - 9, y: n.y - 9, width: 18, height: 18, rx: 4, class: 'st-box' }, g);
        const off = { t: [0, -16, 'middle'], b: [0, 25, 'middle'], l: [-14, 5, 'end'], r: [14, 5, 'start'], br: [8, 28, 'start'] }[n.lp || 't'];
        const t = el('text', { x: n.x + off[0], y: n.y + off[1], 'text-anchor': off[2], class: 'st-label' }, g);
        t.textContent = n.name;
        n.pips = n.props.map((p, i) => el('circle', {
          cx: n.x - (n.props.length - 1) * 2.6 + i * 5.2, cy: n.y + 3.5, r: 2, class: 'pip',
        }, g));
        g.addEventListener('click', () => { if (!dragMoved) showStationInfo(n); });
      } else {
        el('circle', { cx: n.x, cy: n.y, r: 5.5, class: 'sq sq-' + n.type }, layers.squares);
      }
    });
    tokenEls.length = 0;
  }

  function drawTokens() {
    layers.tokens.innerHTML = '';
    tokenEls.length = 0;
    G.players.forEach((p, i) => {
      const g = el('g', { class: 'token' }, layers.tokens);
      el('circle', { r: 10, fill: p.color, class: 'token-body' }, g);
      const t = el('text', { y: 4, 'text-anchor': 'middle', class: 'token-text' }, g);
      t.textContent = p.name.slice(0, 1);
      tokenEls.push(g);
    });
    placeTokens();
  }
  function tokenOffset(i) {
    const n = G.players.length;
    if (n === 1) return [0, 0];
    const a = (i / n) * Math.PI * 2 - Math.PI / 2;
    return [Math.cos(a) * 9, Math.sin(a) * 9];
  }
  function placeToken(i, nodeId) {
    const n = nodes[nodeId], [ox, oy] = tokenOffset(i);
    tokenEls[i].setAttribute('transform', `translate(${n.x + ox},${n.y + oy})`);
  }
  function placeTokens() {
    G.players.forEach((p, i) => placeToken(i, p.pos));
    // 手番プレイヤーを最前面に
    if (tokenEls[G.turn]) layers.tokens.appendChild(tokenEls[G.turn]);
    tokenEls.forEach((t, i) => t.classList.toggle('active', i === G.turn));
  }

  function refreshStations() {
    stations().forEach(n => {
      const mono = monopolyOwner(n);
      n.el.style.fill = mono >= 0 ? G.players[mono].color : '';
      n.el.classList.toggle('mono', mono >= 0);
      n.props.forEach((p, i) => {
        n.pips[i].style.fill = p.owner >= 0 ? G.players[p.owner].color : '';
        n.pips[i].classList.toggle('owned', p.owner >= 0);
      });
    });
  }

  function drawDest() {
    layers.marks.innerHTML = '';
    if (G.dest == null) return;
    const n = nodes[G.dest];
    el('circle', { cx: n.x, cy: n.y, r: 18, class: 'dest-ring' }, layers.marks);
    const g = el('g', { transform: `translate(${n.x},${n.y - 12})`, class: 'dest-flag' }, layers.marks);
    el('line', { x1: 0, y1: 0, x2: 0, y2: -30, class: 'flag-pole' }, g);
    el('path', { d: 'M0,-30 L22,-24 L0,-17 Z', class: 'flag-cloth' }, g);
  }

  // ---------- カメラ ----------
  const cam = { x: 690, y: 730, w: 1400, tx: 690, ty: 730, tw: 1400 };
  let dragMoved = false;
  function aspect() {
    const r = svg.getBoundingClientRect();
    return r.width ? r.height / r.width : 1;
  }
  function applyCam() {
    const h = cam.w * aspect();
    svg.setAttribute('viewBox', `${cam.x - cam.w / 2} ${cam.y - h / 2} ${cam.w} ${h}`);
  }
  function camLoop() {
    const k = 0.14;
    cam.x += (cam.tx - cam.x) * k;
    cam.y += (cam.ty - cam.y) * k;
    cam.w += (cam.tw - cam.w) * k;
    applyCam();
    requestAnimationFrame(camLoop);
  }
  function fitBox(minX, minY, maxX, maxY, pad = 40, minW = 260) {
    const asp = aspect();
    cam.tx = (minX + maxX) / 2;
    cam.ty = (minY + maxY) / 2;
    cam.tw = Math.min(MAX_W, Math.max(minW, maxX - minX + pad * 2, (maxY - minY + pad * 2) / asp));
  }
  function focusNodes(ids, minW = 680) {
    const xs = ids.map(i => nodes[i].x), ys = ids.map(i => nodes[i].y);
    fitBox(Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys), 50, minW);
  }
  function showAll() { fitBox(WORLD.minX, WORLD.minY, WORLD.maxX, WORLD.maxY, 0, 300); }

  function setupCameraControls() {
    let drag = null;
    svg.addEventListener('pointerdown', e => {
      drag = { x: e.clientX, y: e.clientY, cx: cam.x, cy: cam.y };
      dragMoved = false;
    });
    window.addEventListener('pointermove', e => {
      if (!drag) return;
      const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
      if (!dragMoved && Math.hypot(dx, dy) < 6) return;
      dragMoved = true;
      const s = cam.w / svg.getBoundingClientRect().width;
      cam.x = cam.tx = drag.cx - dx * s;
      cam.y = cam.ty = drag.cy - dy * s;
    });
    window.addEventListener('pointerup', () => { drag = null; setTimeout(() => { dragMoved = false; }, 0); });
    svg.addEventListener('wheel', e => {
      e.preventDefault();
      zoom(e.deltaY > 0 ? 1.15 : 1 / 1.15);
    }, { passive: false });
    document.querySelectorAll('#map-ctrl button').forEach(b => b.addEventListener('click', () => {
      const z = b.dataset.z;
      if (z === 'in') zoom(1 / 1.3);
      else if (z === 'out') zoom(1.3);
      else if (z === 'all') showAll();
      else if (z === 'me' && G) focusNodes([cur().pos, G.dest]);
    }));
    window.addEventListener('resize', applyCam);
  }
  function zoom(f) { cam.tw = Math.min(MAX_W, Math.max(150, cam.tw * f)); }

  // ---------- UI ----------
  function renderHeader() {
    const d = G.dest != null ? distFrom(G.dest)[cur().pos] : 0;
    $('#date').innerHTML = `<b>${G.year}年目 ${MONTHS[G.month]}月</b><span>（全${G.years}年）</span>`;
    $('#dest').innerHTML = G.dest != null
      ? `🚩 目的地 <b>${esc(nodes[G.dest].name)}</b><span>あと${d}マス・賞金${fmt(G.destBonus)}</span>`
      : '';
  }
  function renderPlayers() {
    const ranks = G.players.map((_, i) => i).sort((a, b) => assets(b) - assets(a));
    $('#players').innerHTML = G.players.map((p, i) => {
      const props = ownedProps(i).length;
      return `<div class="pl ${i === G.turn ? 'active' : ''}" style="--c:${p.color}">
        <div class="pl-head"><span class="dot"></span><span class="pl-name">${esc(p.name)}</span>${p.cpu ? '<span class="tag">CPU</span>' : ''}<span class="rank">${ranks.indexOf(i) + 1}位</span></div>
        <div class="pl-row"><span>所持金</span><b class="${p.cash < 0 ? 'neg' : ''}">${fmt(p.cash)}</b></div>
        <div class="pl-row"><span>総資産</span><b>${fmt(assets(i))}</b></div>
        <div class="pl-row sub"><span>物件${props}件・年収${fmt(income(i))}</span><span title="カード">🎫${p.cards.length}</span></div>
      </div>`;
    }).join('');
  }
  function renderAll() {
    renderHeader();
    renderPlayers();
    refreshStations();
    drawDest();
    placeTokens();
  }
  function log(msg, color) {
    const div = document.createElement('div');
    div.className = 'log-item';
    if (color) div.style.borderLeftColor = color;
    div.innerHTML = msg;
    const box = $('#log');
    box.prepend(div);
    while (box.children.length > 80) box.lastChild.remove();
  }
  let toastTimer = 0;
  function toast(html, cls = '') {
    const t = $('#toast');
    t.className = 'show ' + cls;
    t.innerHTML = html;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { t.className = ''; }, G && G.fast ? 1200 : 2200);
  }
  function setActions(html) {
    $('#actions').innerHTML = html;
    return $('#actions');
  }

  function openModal(html, cls = '') {
    const m = $('#modal');
    m.className = cls;
    $('.modal-box', m).innerHTML = html;
    return $('.modal-box', m);
  }
  function closeModal() { $('#modal').className = 'hidden'; }
  function modalOk(html, label = 'OK', autoMs = 0) {
    return new Promise(res => {
      const box = openModal(html + `<div class="modal-actions"><button class="btn primary" id="m-ok">${label}</button></div>`);
      let done = false;
      const finish = () => { if (done) return; done = true; closeModal(); res(); };
      $('#m-ok', box).onclick = finish;
      if (autoMs) setTimeout(finish, autoMs);
    });
  }

  const PIPS = { 1: [4], 2: [0, 8], 3: [0, 4, 8], 4: [0, 2, 6, 8], 5: [0, 2, 4, 6, 8], 6: [0, 2, 3, 5, 6, 8] };
  const dieHtml = v => `<div class="die">${Array.from({ length: 9 }, (_, i) => `<i class="${PIPS[v].includes(i) ? 'on' : ''}"></i>`).join('')}</div>`;
  async function rollDice(n) {
    const ov = $('#dice-overlay');
    ov.classList.add('show');
    let vals = [];
    const frames = G.fast ? 5 : 12;
    for (let i = 0; i < frames; i++) {
      vals = Array.from({ length: n }, () => 1 + Math.floor(Math.random() * 6));
      ov.innerHTML = `<div class="dice-row">${vals.map(dieHtml).join('')}</div>`;
      await sleep(60);
    }
    const sum = vals.reduce((a, b) => a + b, 0);
    ov.innerHTML = `<div class="dice-row">${vals.map(dieHtml).join('')}</div><div class="dice-sum">${sum}</div>`;
    await sleep(delay(900));
    ov.classList.remove('show');
    return sum;
  }

  function propTable(n, buyable) {
    const mono = monopolyOwner(n);
    return `<table class="props"><thead><tr><th>物件</th><th>価格</th><th>収益率</th><th></th></tr></thead><tbody>
      ${n.props.map((p, i) => {
        let right;
        if (p.owner >= 0) {
          const o = G.players[p.owner];
          right = `<span class="owner" style="--c:${o.color}">${esc(o.name)}</span>`;
        } else if (buyable) {
          right = `<button class="btn small" data-buy="${i}" ${cur().cash >= p.price ? '' : 'disabled'}>購入</button>`;
        } else right = '<span class="muted">売出中</span>';
        return `<tr><td>${esc(p.name)}</td><td class="num">${fmt(p.price)}</td><td class="num">${p.rate}%</td><td>${right}</td></tr>`;
      }).join('')}</tbody></table>
      ${mono >= 0 ? `<p class="mono-note" style="--c:${G.players[mono].color}">👑 ${esc(G.players[mono].name)}が独占中（収益2倍）</p>` : '<p class="muted small">全物件を買い占めると独占！ 収益が2倍になります。</p>'}`;
  }
  function showStationInfo(n) {
    if (!G || !$('#modal').classList.contains('hidden')) return;
    const box = openModal(`<h2>${esc(n.name)}駅</h2>${propTable(n, false)}<div class="modal-actions"><button class="btn" id="m-close">閉じる</button></div>`);
    $('#m-close', box).onclick = closeModal;
  }
  function showMyProps(pi) {
    const list = ownedProps(pi);
    const p = G.players[pi];
    const box = openModal(`<h2>${esc(p.name)}の物件</h2>
      ${list.length ? `<table class="props"><thead><tr><th>駅</th><th>物件</th><th>価格</th><th>収益率</th></tr></thead><tbody>
      ${list.map(o => `<tr><td>${esc(o.st.name)}${monopolyOwner(o.st) === pi ? '👑' : ''}</td><td>${esc(o.p.name)}</td><td class="num">${fmt(o.p.price)}</td><td class="num">${o.p.rate}%</td></tr>`).join('')}
      </tbody></table>` : '<p class="muted">まだ物件を持っていません。</p>'}
      <p>年間収益見込み: <b>${fmt(income(pi))}</b></p>
      <div class="modal-actions"><button class="btn" id="m-close">閉じる</button></div>`);
    $('#m-close', box).onclick = closeModal;
  }

  // ---------- ターン処理 ----------
  function askRoll(p) {
    if (p.cpu) {
      const d = distFrom(G.dest)[p.pos];
      let best = -1;
      p.cards.forEach((k, i) => {
        const dice = cardDef(k).dice;
        // 遠いときだけカードを使う
        if (d >= dice * 3 && (best < 0 || dice > cardDef(p.cards[best]).dice)) best = i;
      });
      return sleep(delay(500)).then(() => (best >= 0 ? { dice: cardDef(p.cards[best]).dice, card: best } : { dice: 1, card: -1 }));
    }
    return new Promise(res => {
      const cards = p.cards.map((k, i) => {
        const c = cardDef(k);
        return `<button class="btn card card-${k}" data-card="${i}">${c.name}<small>サイコロ${c.dice}個</small></button>`;
      }).join('');
      const a = setActions(`<div class="prompt" style="--c:${p.color}">${esc(p.name)}の番です</div>
        <button class="btn primary big" id="roll">🎲 サイコロを振る</button>
        ${cards ? `<div class="cards">${cards}</div>` : ''}
        <button class="btn ghost" id="myprops">📋 自分の物件を見る</button>`);
      $('#roll', a).onclick = () => res({ dice: 1, card: -1 });
      a.querySelectorAll('[data-card]').forEach(b => {
        b.onclick = () => { const i = +b.dataset.card; res({ dice: cardDef(p.cards[i]).dice, card: i }); };
      });
      $('#myprops', a).onclick = () => showMyProps(G.turn);
    });
  }

  function nodeLabel(id) {
    const n = nodes[id];
    return n.type === 'station' ? n.name + '駅' : SQUARE_LABEL[n.type];
  }

  function askMove(p, cands, steps) {
    const dist = distFrom(G.dest);
    const ids = [...cands.keys()];
    if (p.cpu) {
      let best = null, bestScore = Infinity;
      ids.forEach(id => {
        const n = nodes[id];
        let score = dist[id] * 10 + Math.random() * 3;
        if (n.type === 'minus') score += 8;
        if (n.type === 'plus') score -= 3;
        if (n.type === 'card') score -= 4;
        if (n.type === 'station' && n.props.some(pr => pr.owner < 0 && pr.price <= p.cash)) score -= 6;
        if (id === G.dest) score = -1000;
        if (score < bestScore) { bestScore = score; best = id; }
      });
      return sleep(delay(400)).then(() => best);
    }
    return new Promise(res => {
      layers.cands.innerHTML = '';
      const choose = id => {
        layers.cands.innerHTML = '';
        layers.path.innerHTML = '';
        res(id);
      };
      const preview = id => {
        layers.path.innerHTML = '';
        const pts = [p.pos, ...cands.get(id)].map(i => `${nodes[i].x},${nodes[i].y}`).join(' ');
        el('polyline', { points: pts, class: 'path-preview', stroke: p.color }, layers.path);
      };
      ids.forEach(id => {
        const n = nodes[id];
        const c = el('circle', { cx: n.x, cy: n.y, r: 15, class: 'cand' + (id === G.dest ? ' cand-dest' : '') }, layers.cands);
        c.addEventListener('mouseenter', () => preview(id));
        c.addEventListener('mouseleave', () => { layers.path.innerHTML = ''; });
        c.addEventListener('click', () => { if (!dragMoved) choose(id); });
      });
      const sorted = ids.slice().sort((a, b) => dist[a] - dist[b]);
      const a = setActions(`<div class="prompt" style="--c:${p.color}">${steps}マス進めます。止まるマスを選んでください</div>
        <div class="cand-list">${sorted.map(id => `<button class="btn cand-btn t-${nodes[id].type}" data-id="${id}">
          <span>${id === G.dest ? '🚩 ' : ''}${esc(nodeLabel(id))}</span><small>目的地まで${dist[id]}</small></button>`).join('')}</div>`);
      a.querySelectorAll('[data-id]').forEach(b => {
        const id = +b.dataset.id;
        b.onclick = () => choose(id);
        b.onmouseenter = () => preview(id);
        b.onmouseleave = () => { layers.path.innerHTML = ''; };
      });
    });
  }

  async function animateMove(pi, path) {
    const step = delay(220);
    for (const id of path) {
      placeToken(pi, id);
      G.players[pi].pos = id;
      cam.tx = nodes[id].x;
      cam.ty = nodes[id].y;
      await sleep(step);
    }
  }

  function settleDebt(pi) {
    const p = G.players[pi];
    if (p.cash >= 0) return;
    const list = ownedProps(pi).sort((a, b) => a.p.price - b.p.price);
    for (const o of list) {
      if (p.cash >= 0) break;
      o.p.owner = -1;
      const v = Math.round(o.p.price / 2);
      p.cash += v;
      log(`💸 ${esc(p.name)}は借金返済のため<b>${esc(o.st.name)}の${esc(o.p.name)}</b>を${fmt(v)}で売却`, p.color);
    }
  }

  function pickDestination() {
    const positions = G.players.map(p => p.pos);
    const all = stations().map(n => n.id).filter(id => id !== G.dest);
    // 全員からある程度離れた駅を選ぶ
    let pool = all.filter(id => positions.every(pos => distFrom(id)[pos] >= 15));
    if (!pool.length) pool = all;
    G.dest = pool[Math.floor(Math.random() * pool.length)];
    const avg = positions.reduce((s, pos) => s + distFrom(G.dest)[pos], 0) / positions.length;
    G.destBonus = Math.round(((6000 + avg * 300) * yearFactor()) / 1000) * 1000;
  }

  async function arriveDest(pi) {
    const p = G.players[pi];
    const bonus = G.destBonus;
    p.cash += bonus;
    const name = nodes[G.dest].name;
    log(`🚩 ${esc(p.name)}が目的地<b>${esc(name)}</b>に一番乗り！ 賞金${fmt(bonus)}`, p.color);
    pickDestination();
    renderAll();
    const msg = `<h2>🎉 目的地到着！</h2><p class="big-msg"><b style="color:${p.color}">${esc(p.name)}</b>が<b>${esc(name)}</b>に一番乗り！</p>
      <p class="big-money">賞金 ${fmt(bonus)}</p><p>次の目的地は <b>${esc(nodes[G.dest].name)}</b> です！</p>`;
    await modalOk(msg, 'OK', G.players.some(x => !x.cpu) && !p.cpu ? 0 : delay(2600));
  }

  function buyProp(pi, n, i) {
    const p = G.players[pi], pr = n.props[i];
    if (pr.owner >= 0 || p.cash < pr.price) return false;
    p.cash -= pr.price;
    pr.owner = pi;
    log(`🏠 ${esc(p.name)}が<b>${esc(n.name)}の${esc(pr.name)}</b>を${fmt(pr.price)}で購入`, p.color);
    if (monopolyOwner(n) === pi) {
      log(`👑 ${esc(p.name)}が<b>${esc(n.name)}</b>を独占！`, p.color);
      toast(`👑 ${esc(p.name)}が${esc(n.name)}を独占！`, 'gold');
    }
    return true;
  }

  async function visitStation(pi, n) {
    const p = G.players[pi];
    if (!n.props.some(pr => pr.owner < 0)) {
      toast(`${esc(n.name)}駅の物件はすべて売約済み`);
      await sleep(delay(700));
      return;
    }
    if (p.cpu) {
      const reserve = Math.round(2000 * yearFactor());
      const order = n.props.map((pr, i) => ({ pr, i })).filter(o => o.pr.owner < 0).sort((a, b) => b.pr.rate - a.pr.rate);
      let bought = 0;
      for (const o of order) {
        if (p.cash - o.pr.price >= reserve && buyProp(pi, n, o.i)) bought++;
      }
      if (bought) toast(`🏠 ${esc(p.name)}が${esc(n.name)}で物件を${bought}件購入`);
      renderAll();
      await sleep(delay(700));
      return;
    }
    await new Promise(res => {
      const render = () => {
        const box = openModal(`<h2>${esc(n.name)}駅に到着</h2>
          <p>所持金: <b class="${p.cash < 0 ? 'neg' : ''}">${fmt(p.cash)}</b></p>
          ${propTable(n, true)}
          <div class="modal-actions"><button class="btn primary" id="m-done">買い物を終える</button></div>`);
        box.querySelectorAll('[data-buy]').forEach(b => {
          b.onclick = () => { buyProp(pi, n, +b.dataset.buy); renderAll(); render(); };
        });
        $('#m-done', box).onclick = () => { closeModal(); res(); };
      };
      render();
    });
  }

  async function land(pi) {
    const p = G.players[pi];
    const n = nodes[p.pos];
    if (n.type === 'plus') {
      const v = Math.round(((800 + Math.random() * 2400) * yearFactor()) / 100) * 100;
      p.cash += v;
      const ev = PLUS_EVENTS[Math.floor(Math.random() * PLUS_EVENTS.length)];
      toast(`💰 ${ev}<br><b>${esc(p.name)}</b> +${fmt(v)}`, 'plus');
      log(`💰 ${esc(p.name)}：${ev} +${fmt(v)}`, p.color);
    } else if (n.type === 'minus') {
      const winter = [12, 1, 2].includes(MONTHS[G.month]) ? 1.5 : 1;
      const v = Math.round(((600 + Math.random() * 2000) * yearFactor() * winter) / 100) * 100;
      p.cash -= v;
      const ev = MINUS_EVENTS[Math.floor(Math.random() * MINUS_EVENTS.length)];
      toast(`💥 ${ev}<br><b>${esc(p.name)}</b> -${fmt(v)}`, 'minus');
      log(`💥 ${esc(p.name)}：${ev} -${fmt(v)}`, p.color);
      settleDebt(pi);
    } else if (n.type === 'card') {
      if (p.cards.length >= MAX_CARDS) {
        toast(`🎫 カードがいっぱいで受け取れない…`);
      } else {
        const k = drawCard();
        p.cards.push(k);
        toast(`🎫 <b>${esc(p.name)}</b>は${cardDef(k).name}を手に入れた！`, 'card');
        log(`🎫 ${esc(p.name)}が${cardDef(k).name}を入手`, p.color);
      }
    } else if (n.type === 'station') {
      if (p.pos === G.dest) await arriveDest(pi);
      renderAll();
      await visitStation(pi, n);
    }
    renderAll();
    await sleep(delay(800));
  }

  async function playTurn() {
    const pi = G.turn, p = cur();
    renderAll();
    focusNodes([p.pos, G.dest].filter(x => x != null), 720);
    if (p.cpu) setActions(`<div class="prompt" style="--c:${p.color}">${esc(p.name)}（CPU）が考え中…</div>`);
    const choice = await askRoll(p);
    if (choice.card >= 0) {
      const c = cardDef(p.cards[choice.card]);
      p.cards.splice(choice.card, 1);
      toast(`🎫 ${esc(p.name)}は${c.name}を使った！`, 'card');
      log(`🎫 ${esc(p.name)}が${c.name}を使用`, p.color);
      renderPlayers();
      await sleep(delay(600));
    }
    if (p.cpu) setActions(`<div class="prompt" style="--c:${p.color}">${esc(p.name)}（CPU）の番</div>`);
    else setActions(`<div class="prompt" style="--c:${p.color}">サイコロを振っています…</div>`);
    const steps = await rollDice(choice.dice);
    const cands = reachable(p.pos, steps, G.dest);
    focusNodes([p.pos, ...cands.keys()], 600);
    const target = await askMove(p, cands, steps);
    setActions(`<div class="prompt" style="--c:${p.color}">${esc(p.name)}が移動中…</div>`);
    await animateMove(pi, cands.get(target));
    await land(pi);
  }

  async function settlement() {
    const rows = G.players.map((p, i) => {
      const inc = income(i);
      p.cash += inc;
      return { p, i, inc };
    });
    G.players.forEach((_, i) => settleDebt(i));
    renderAll();
    log(`📊 <b>${G.year}年目の決算</b>`);
    const ranking = G.players.map((p, i) => ({ p, i, a: assets(i) })).sort((a, b) => b.a - a.a);
    const html = `<h2>📊 ${G.year}年目 決算</h2>
      <table class="props"><thead><tr><th>プレイヤー</th><th>物件収益</th></tr></thead><tbody>
      ${rows.map(r => `<tr><td><span class="owner" style="--c:${r.p.color}">${esc(r.p.name)}</span></td><td class="num">+${fmt(r.inc)}</td></tr>`).join('')}
      </tbody></table>
      <h3>総資産ランキング</h3>
      <ol class="ranking">${ranking.map(r => `<li><span class="owner" style="--c:${r.p.color}">${esc(r.p.name)}</span><b>${fmt(r.a)}</b></li>`).join('')}</ol>`;
    await modalOk(html, G.year >= G.years ? '最終結果へ' : `${G.year + 1}年目へ`, G.players.every(p => p.cpu) ? delay(3000) : 0);
  }

  function endGame() {
    const ranking = G.players.map((p, i) => ({ p, i, a: assets(i) })).sort((a, b) => b.a - a.a);
    const winner = ranking[0];
    setActions(`<div class="prompt">ゲーム終了！</div><button class="btn primary" id="again">もう一度遊ぶ</button>`);
    $('#again').onclick = () => restart();
    const box = openModal(`<h2>🏆 最終結果</h2>
      <p class="big-msg"><b style="color:${winner.p.color}">${esc(winner.p.name)}</b>が日本一の資産家に！</p>
      <ol class="ranking final">${ranking.map(r => `<li><span class="owner" style="--c:${r.p.color}">${esc(r.p.name)}</span>
        <span class="muted small">物件${ownedProps(r.i).length}件</span><b>${fmt(r.a)}</b></li>`).join('')}</ol>
      <div class="modal-actions"><button class="btn" id="m-close">盤面を見る</button><button class="btn primary" id="m-again">もう一度遊ぶ</button></div>`);
    $('#m-close', box).onclick = closeModal;
    $('#m-again', box).onclick = () => restart();
    log(`🏆 <b>${esc(winner.p.name)}</b>の優勝！`, winner.p.color);
  }

  function restart() {
    closeModal();
    $('#log').innerHTML = '';
    setupScreen();
  }

  async function gameLoop() {
    for (;;) {
      await playTurn();
      G.turn++;
      if (G.turn >= G.players.length) {
        G.turn = 0;
        if (MONTHS[G.month] === 3) {
          await settlement();
          if (G.year >= G.years) { renderAll(); endGame(); return; }
          G.year++;
        }
        G.month = (G.month + 1) % 12;
        log(`🗓 ${G.year}年目 ${MONTHS[G.month]}月`);
      }
    }
  }

  // ---------- 開始画面 ----------
  function setupScreen() {
    const defaults = ['あなた', 'CPU 桃子', 'CPU 金太', 'CPU 銀次'];
    const box = openModal(`<h1 class="title">🎲 サイコロ日本一周</h1>
      <p class="subtitle">日本中の駅で物件を買い占め、資産1位を目指そう！</p>
      <div class="setup">
        ${defaults.map((d, i) => `<div class="setup-row" style="--c:${COLORS[i]}">
          <label class="chk"><input type="checkbox" data-on="${i}" ${i < 4 ? 'checked' : ''} ${i === 0 ? 'disabled' : ''}></label>
          <span class="dot"></span>
          <input type="text" maxlength="8" value="${d}" data-name="${i}">
          <select data-cpu="${i}"><option value="0" ${i === 0 ? 'selected' : ''}>人間</option><option value="1" ${i > 0 ? 'selected' : ''}>CPU</option></select>
        </div>`).join('')}
        <div class="setup-opts">
          <label>プレイ年数 <select id="years"><option>1</option><option selected>3</option><option>5</option><option>10</option></select> 年</label>
          <label><input type="checkbox" id="fast"> CPUを高速にする</label>
        </div>
      </div>
      <details class="rules"><summary>遊び方</summary>
        <ul>
          <li>サイコロを振って、出た目の数だけ進めるマスから止まる場所を選びます。</li>
          <li><b>駅</b>に止まると、その駅の物件を買えます。毎年3月の決算で、物件の収益（価格×収益率）が入ります。</li>
          <li>1つの駅の物件を全部買うと<b>独占</b>！ その駅の収益が2倍になります。</li>
          <li><span class="sq-ic plus"></span>青マスはお金がもらえ、<span class="sq-ic minus"></span>赤マスはお金を失います（冬は被害大）。<span class="sq-ic card"></span>黄マスではサイコロを増やせるカードがもらえます。</li>
          <li>🚩<b>目的地</b>は全国100駅からランダムに決まります。一番乗りすると賞金がもらえます。</li>
          <li>所持金がマイナスになると、安い物件から半額で売却されます。</li>
          <li>最終年の決算後、<b>総資産（所持金＋物件価格）</b>が一番多い人の勝ち！</li>
        </ul>
      </details>
      <div class="modal-actions"><button class="btn primary big" id="start">ゲーム開始</button></div>`, 'setup-modal');
    $('#start', box).onclick = () => {
      const players = [];
      defaults.forEach((_, i) => {
        if (!$(`[data-on="${i}"]`, box).checked) return;
        players.push({
          name: $(`[data-name="${i}"]`, box).value.trim() || `P${i + 1}`,
          cpu: $(`[data-cpu="${i}"]`, box).value === '1',
          color: COLORS[i],
          cash: START_CASH,
          pos: stationByName['東京'],
          cards: [],
        });
      });
      closeModal();
      startGame(players, +$('#years', box).value, $('#fast', box).checked);
    };
  }

  function startGame(players, years, fast) {
    G = { players, years, fast, year: 1, month: 0, turn: 0, dest: null, destBonus: 0 };
    stations().forEach(n => n.props.forEach(p => { p.owner = -1; }));
    drawTokens();
    pickDestination();
    renderAll();
    log(`🚃 ゲーム開始！ 全${years}年。東京駅から出発します。`);
    log(`🚩 最初の目的地は<b>${esc(nodes[G.dest].name)}</b>`);
    toast(`🚩 最初の目的地は <b>${esc(nodes[G.dest].name)}</b>！`);
    gameLoop();
  }

  buildBoard();
  drawBoard();
  setupCameraControls();
  showAll();
  cam.x = cam.tx; cam.y = cam.ty; cam.w = cam.tw;
  camLoop();
  setupScreen();
})();
