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
  const CAR_MONTHS = 6;           // 購入した車の有効期間 (ヶ月)
  // 車: use=ガソリン消費倍率 speed=出目の倍率 refuel=給油代の倍率 price=購入価格(万円)
  const CAR_TYPES = [
    { key: 'hv', name: 'ハイブリッド車', emoji: '🚙', price: 300, use: 0.5, speed: 1, refuel: 1, desc: 'ガソリンの減りが半分' },
    { key: 'ev', name: '電気自動車', emoji: '🔋', price: 500, use: 0.5, speed: 1, refuel: 0.25, desc: 'ガソリンの減りが半分・給油代が4分の1' },
    { key: 'sport', name: 'スポーツカー', emoji: '🏎️', price: 400, use: 2, speed: 2, refuel: 1, desc: '出目の2倍進める・ガソリンの減りは2倍' },
  ];
  const NORMAL_CAR = { key: 'normal', name: 'ふつうの車', emoji: '🚗', use: 1, speed: 1, refuel: 1 };
  const carDef = k => CAR_TYPES.find(c => c.key === k);
  const carOf = p => (p.car && carDef(p.car.key)) || NORMAL_CAR;
  const fmtF = v => (Number.isInteger(v) ? String(v) : v.toFixed(1));
  const FUEL_MAX = 30;            // タンク容量 (マス数)
  const FUEL_PRICE = 30;          // ガソリン1目盛の値段 (万円)
  const TOLL = { road: 8, bridge: 20, sea: 40 }; // 1マスあたりの通行料 (万円)
  const JAF_FEE = 1500;           // ガス欠の救援費用 (万円)
  const CARD_TYPES = [
    { key: 'etc', name: 'ETCカード', dice: 2, w: 55 },
    { key: 'turbo', name: 'ターボカード', dice: 3, w: 30 },
    { key: 'nitro', name: 'ニトロカード', dice: 4, w: 15 },
  ];
  const SQUARE_LABEL = { plus: '青マス', minus: '赤マス', card: '黄マス', car: '紫マス' };
  const KIND_LABEL = { sa: 'サービスエリア', pa: 'パーキングエリア', mi: '道の駅' };
  const WORLD = { minX: -160, minY: 0, maxX: 1380, maxY: 1560 };
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
  const spotByLabel = {};

  function addNode(n) {
    n.id = nodes.length;
    nodes.push(n);
    adj.push([]);
    return n.id;
  }
  const roads = [];
  const linkKind = new Map();
  function link(a, b, kind) {
    adj[a].push(b);
    adj[b].push(a);
    linkKind.set(a + ',' + b, kind || 'road');
    linkKind.set(b + ',' + a, kind || 'road');
    links.push({ a, b, kind });
  }

  function buildBoard() {
    const rnd = mulberry32(20261022);
    SPOTS.forEach(s => {
      spotByLabel[s.label] = addNode({
        type: 'station', name: s.name, label: s.label, kind: s.kind, lp: s.lp,
        x: (s.lon - PROJ.lon0) * PROJ.kx, y: (PROJ.lat0 - s.lat) * PROJ.ky,
        props: s.props.map(([name, price, rate]) => ({ name, price, rate, owner: -1 })),
      });
    });
    ROUTES.forEach(([a, b, road, kind]) => {
      const A = nodes[spotByLabel[a]], B = nodes[spotByLabel[b]];
      roads.push({ a: A.id, b: B.id, road });
      const d = Math.hypot(A.x - B.x, A.y - B.y);
      const n = Math.max(1, Math.min(kind === 'sea' ? 6 : 4, Math.round(d / 40)));
      let prev = A.id;
      for (let i = 1; i <= n; i++) {
        const t = i / (n + 1);
        const r = rnd();
        const type = r < 0.45 ? 'plus' : r < 0.8 ? 'minus' : r < 0.93 ? 'card' : 'car';
        const id = addNode({ type, x: A.x + (B.x - A.x) * t, y: A.y + (B.y - A.y) * t });
        link(prev, id, kind);
        prev = id;
      }
      link(prev, B.id, kind);
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
  const fuelPrice = () => FUEL_PRICE * yearFactor();
  const unitPrice = p => fuelPrice() * carOf(p).refuel;   // 電気自動車は給油代が安い
  // 経路の費用: フェリーは燃料を使わない。ETC使用時は通行料が半額。燃料の減りは車で変わる
  function pathCost(start, path, etc, p) {
    const use = carOf(p).use;
    let toll = 0, fuel = 0, prev = start;
    for (const id of path) {
      const k = linkKind.get(prev + ',' + id) || 'road';
      toll += TOLL[k] * yearFactor() * (etc ? 0.5 : 1);
      if (k !== 'sea') fuel += use;
      prev = id;
    }
    return { toll: Math.round(toll), fuel };
  }
  function refuel(pi, units) {
    const p = G.players[pi];
    units = Math.max(0, Math.min(units, FUEL_MAX - Math.ceil(p.fuel), Math.floor(p.cash / unitPrice(p))));
    if (units <= 0) return 0;
    const cost = Math.round(units * unitPrice(p));
    p.fuel = Math.min(FUEL_MAX, p.fuel + units);
    p.cash -= cost;
    log(`⛽ ${esc(p.name)}が給油（${units}目盛・${fmt(cost)}）`, p.color);
    return units;
  }
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
    ['sea', 'land', 'routes', 'roadnames', 'squares', 'stations', 'marks', 'path', 'cands', 'tokens'].forEach(n => {
      layers[n] = el('g', { class: 'layer-' + n }, svg);
    });
    el('rect', { x: -3000, y: -3000, width: 7000, height: 7000, class: 'sea' }, layers.sea);
    el('path', { d: COAST_OTHER, class: 'foreign' }, layers.land);
    el('path', { d: COAST_JAPAN, class: 'land' }, layers.land);
    // 沖縄 (左下の枠内に、位置を北へ寄せて表示)
    const okX = lon => (lon - PROJ.lon0) * PROJ.kx, okY = lat => (PROJ.lat0 - (lat + OKINAWA_SHIFT)) * PROJ.ky;
    el('rect', { x: -150, y: 1388, width: 130, height: 140, rx: 10, class: 'inset-frame' }, layers.land);
    el('text', { x: -85, y: 1382, 'text-anchor': 'middle', class: 'inset-label' }, layers.land).textContent = '沖縄（位置を移動して表示）';
    el('path', { d: OKINAWA_COAST.map(([la, lo], i) => (i ? 'L' : 'M') + okX(lo).toFixed(1) + ',' + okY(la).toFixed(1)).join('') + 'Z', class: 'land' }, layers.land);
    links.forEach(l => {
      const A = nodes[l.a], B = nodes[l.b];
      const cls = l.kind === 'sea' ? 'route sea-route' : l.kind === 'bridge' ? 'route bridge-route' : 'route';
      el('line', { x1: A.x, y1: A.y, x2: B.x, y2: B.y, class: cls }, layers.routes);
    });
    roads.forEach(r => {
      const A = nodes[r.a], B = nodes[r.b];
      let ang = Math.atan2(B.y - A.y, B.x - A.x) * 180 / Math.PI;
      if (ang > 90 || ang < -90) ang += 180;
      const mx = (A.x + B.x) / 2, my = (A.y + B.y) / 2;
      const t = el('text', { x: 0, y: -8, 'text-anchor': 'middle', class: 'road-label', transform: `translate(${mx},${my}) rotate(${ang})` }, layers.roadnames);
      t.textContent = r.road;
    });
    nodes.forEach(n => {
      if (n.type === 'station') {
        const g = el('g', { class: 'station k-' + n.kind, 'data-id': n.id }, layers.stations);
        n.el = el('rect', { x: n.x - 9, y: n.y - 9, width: 18, height: 18, rx: n.kind === 'mi' ? 9 : 4, class: 'st-box' }, g);
        const off = { t: [0, -16, 'middle'], b: [0, 25, 'middle'], l: [-14, 5, 'end'], r: [14, 5, 'start'], br: [8, 28, 'start'] }[n.lp || 't'];
        const t = el('text', { x: n.x + off[0], y: n.y + off[1], 'text-anchor': off[2], class: 'st-label' }, g);
        t.textContent = n.label;
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
      el('circle', { r: 11, fill: p.color, class: 'token-body' }, g);
      const t = el('text', { y: 4, 'text-anchor': 'middle', class: 'token-text' }, g);
      t.textContent = '🚗';
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
    tokenEls.forEach((t, i) => {
      t.classList.toggle('active', i === G.turn);
      t.querySelector('text').textContent = carOf(G.players[i]).emoji;
    });
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
    svg.classList.toggle('zoomed', cam.w < 450);
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
        <div class="pl-row fuel ${p.fuel <= 8 ? 'low' : ''}"><span>⛽</span><span class="fbar"><i style="width:${Math.round(p.fuel / FUEL_MAX * 100)}%"></i></span><b>${fmtF(p.fuel)}/${FUEL_MAX}</b></div>
        ${p.car ? `<div class="pl-row car"><span>${carOf(p).emoji} ${carOf(p).name}</span><span>残り${Math.max(0, p.car.until - G.t)}ヶ月</span></div>` : ''}
        <div class="pl-row sub"><span>お店${props}軒・年収${fmt(income(i))}</span><span title="カード">🎫${p.cards.length}</span></div>
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
    return `<table class="props"><thead><tr><th>お店</th><th>価格</th><th>収益率</th><th></th></tr></thead><tbody>
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
      ${mono >= 0 ? `<p class="mono-note" style="--c:${G.players[mono].color}">👑 ${esc(G.players[mono].name)}が独占中（収益2倍）</p>` : '<p class="muted small">全店舗を買い占めると独占！ 収益が2倍になります。</p>'}`;
  }
  function showStationInfo(n) {
    if (!G || !$('#modal').classList.contains('hidden')) return;
    const box = openModal(`<h2>${esc(n.name)}</h2><p class="muted small">${KIND_LABEL[n.kind]}</p>${propTable(n, false)}<div class="modal-actions"><button class="btn" id="m-close">閉じる</button></div>`);
    $('#m-close', box).onclick = closeModal;
  }
  function showMyProps(pi) {
    const list = ownedProps(pi);
    const p = G.players[pi];
    const box = openModal(`<h2>${esc(p.name)}のお店</h2>
      ${list.length ? `<table class="props"><thead><tr><th>スポット</th><th>お店</th><th>価格</th><th>収益率</th></tr></thead><tbody>
      ${list.map(o => `<tr><td>${esc(o.st.label)}${monopolyOwner(o.st) === pi ? '👑' : ''}</td><td>${esc(o.p.name)}</td><td class="num">${fmt(o.p.price)}</td><td class="num">${o.p.rate}%</td></tr>`).join('')}
      </tbody></table>` : '<p class="muted">まだお店を持っていません。</p>'}
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
        <button class="btn ghost" id="myprops">📋 自分のお店を見る</button>`);
      $('#roll', a).onclick = () => res({ dice: 1, card: -1 });
      a.querySelectorAll('[data-card]').forEach(b => {
        b.onclick = () => { const i = +b.dataset.card; res({ dice: cardDef(p.cards[i]).dice, card: i }); };
      });
      $('#myprops', a).onclick = () => showMyProps(G.turn);
    });
  }

  function nodeLabel(id) {
    const n = nodes[id];
    return n.type === 'station' ? n.name : SQUARE_LABEL[n.type];
  }

  function askMove(p, cands, steps, etc) {
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
        if (n.type === 'car') score -= 2;
        if (n.type === 'station' && n.props.some(pr => pr.owner < 0 && pr.price <= p.cash)) score -= 6;
        if (n.type === 'station' && p.fuel <= 12) score -= 8;
        score += pathCost(p.pos, cands.get(id), etc, p).toll / 40;
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
          <span>${id === G.dest ? '🚩 ' : ''}${esc(nodeLabel(id))}</span><small>目的地まで${dist[id]}・通行料${fmt(pathCost(p.pos, cands.get(id), etc, p).toll)}・⛽${fmtF(pathCost(p.pos, cands.get(id), etc, p).fuel)}</small></button>`).join('')}</div>`);
      a.querySelectorAll('[data-id]').forEach(b => {
        const id = +b.dataset.id;
        b.onclick = () => choose(id);
        b.onmouseenter = () => preview(id);
        b.onmouseleave = () => { layers.path.innerHTML = ''; };
      });
    });
  }

  async function animateMove(pi, path, etc) {
    const step = delay(220);
    const p = G.players[pi];
    const cost = pathCost(p.pos, path, etc, p);
    for (const id of path) {
      placeToken(pi, id);
      p.pos = id;
      cam.tx = nodes[id].x;
      cam.ty = nodes[id].y;
      await sleep(step);
    }
    p.fuel = Math.max(0, p.fuel - cost.fuel);
    p.cash -= cost.toll;
    if (cost.toll || cost.fuel) {
      log(`🛣 ${esc(p.name)}：通行料 -${fmt(cost.toll)}${etc ? '（ETC割引）' : ''}・ガソリン -${fmtF(cost.fuel)}`, p.color);
      toast(`🛣 通行料 -${fmt(cost.toll)}${etc ? '（ETC半額）' : ''}　⛽ -${fmtF(cost.fuel)}`, 'toll');
    }
    settleDebt(pi);
    renderAll();
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
      log(`💸 ${esc(p.name)}は借金返済のため<b>${esc(o.st.label)}の${esc(o.p.name)}</b>を${fmt(v)}で売却`, p.color);
    }
  }

  function pickDestination() {
    const positions = G.players.map(p => p.pos);
    const all = stations().map(n => n.id).filter(id => id !== G.dest);
    // 全員からある程度離れたスポットを選ぶ
    let pool = all.filter(id => positions.every(pos => distFrom(id)[pos] >= 16));
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
    log(`🏠 ${esc(p.name)}が<b>${esc(n.label)}の${esc(pr.name)}</b>を${fmt(pr.price)}で購入`, p.color);
    if (monopolyOwner(n) === pi) {
      log(`👑 ${esc(p.name)}が<b>${esc(n.label)}</b>を独占！`, p.color);
      toast(`👑 ${esc(p.name)}が${esc(n.label)}を独占！`, 'gold');
    }
    return true;
  }

  async function visitStation(pi, n) {
    const p = G.players[pi];
    const hasShop = n.props.some(pr => pr.owner < 0);
    if (!hasShop && p.fuel > FUEL_MAX - 1) {
      toast(`${esc(n.label)}のお店はすべて売約済み`);
      await sleep(delay(700));
      return;
    }
    if (p.cpu) {
      const reserve = Math.round(2000 * yearFactor());
      // ガソリンが減っていたら先に給油 (残金の余裕を見ながら)
      if (p.fuel <= 20) {
        const afford = Math.floor(Math.max(0, p.cash - reserve / 2) / unitPrice(p));
        const u = refuel(pi, Math.min(FUEL_MAX - p.fuel, afford));
        if (u) toast(`⛽ ${esc(p.name)}が${esc(n.label)}で給油`);
      }
      const order = n.props.map((pr, i) => ({ pr, i })).filter(o => o.pr.owner < 0).sort((a, b) => b.pr.rate - a.pr.rate);
      let bought = 0;
      for (const o of order) {
        if (p.cash - o.pr.price >= reserve && buyProp(pi, n, o.i)) bought++;
      }
      if (bought) toast(`🏠 ${esc(p.name)}が${esc(n.label)}でお店を${bought}軒購入`);
      renderAll();
      await sleep(delay(700));
      return;
    }
    await new Promise(res => {
      const render = () => {
        const need = FUEL_MAX - Math.ceil(p.fuel);
        const units = Math.min(need, Math.floor(Math.max(0, p.cash) / unitPrice(p)));
        const box = openModal(`<h2>${esc(n.name)}に到着</h2>
          <p>所持金: <b class="${p.cash < 0 ? 'neg' : ''}">${fmt(p.cash)}</b></p>
          <div class="fuel-box ${p.fuel <= 8 ? 'low' : ''}">
            <span>⛽ ガソリン</span><span class="fbar"><i style="width:${Math.round(p.fuel / FUEL_MAX * 100)}%"></i></span><b>${fmtF(p.fuel)}/${FUEL_MAX}</b>
            <button class="btn small" id="m-fuel" ${units > 0 ? '' : 'disabled'}>${need > 0 ? `給油 +${units}（${fmt(Math.round(units * unitPrice(p)))}）` : '満タン'}</button>
          </div>
          ${hasShop ? propTable(n, true) : '<p class="muted small">このスポットのお店はすべて売約済みです。</p>'}
          <div class="modal-actions"><button class="btn primary" id="m-done">出発する</button></div>`);
        box.querySelectorAll('[data-buy]').forEach(b => {
          b.onclick = () => { buyProp(pi, n, +b.dataset.buy); renderAll(); render(); };
        });
        $('#m-fuel', box).onclick = () => { refuel(pi, units); renderAll(); render(); };
        $('#m-done', box).onclick = () => { closeModal(); res(); };
      };
      render();
    });
  }

  const carPrice = c => Math.round(c.price * yearFactor() / 50) * 50;
  function buyCar(pi, c) {
    const p = G.players[pi];
    const price = carPrice(c);
    if (p.cash < price) return false;
    p.cash -= price;
    p.car = { key: c.key, until: G.t + CAR_MONTHS };
    log(`${c.emoji} ${esc(p.name)}が<b>${c.name}</b>を購入（${fmt(price)}・${CAR_MONTHS}ヶ月）`, p.color);
    toast(`${c.emoji} <b>${esc(p.name)}</b>が${c.name}を購入！<br>${CAR_MONTHS}ヶ月間 ${c.desc}`, 'car');
    return true;
  }
  async function carDealer(pi) {
    const p = G.players[pi];
    if (p.cpu) {
      const reserve = Math.round(3000 * yearFactor());
      const d = distFrom(G.dest)[p.pos];
      const [hv, ev, sport] = CAR_TYPES;
      let pick = null;
      if (!p.car) {
        if (d >= 10 && Math.random() < 0.35 && p.cash >= carPrice(sport) + reserve) pick = sport;
        else if (p.cash >= carPrice(ev) + reserve) pick = ev;
        else if (p.cash >= carPrice(hv) + reserve) pick = hv;
      }
      if (pick) buyCar(pi, pick);
      return;
    }
    await new Promise(res => {
      const now = carOf(p);
      const box = openModal(`<h2>🟣 カーディーラー</h2>
        <p>車を購入すると<b>${CAR_MONTHS}ヶ月間</b>乗れます。${p.car ? `（今は${now.name}・残り${p.car.until - G.t}ヶ月。買うと乗り換え）` : ''}</p>
        <p>所持金: <b>${fmt(p.cash)}</b></p>
        <div class="car-list">${CAR_TYPES.map(c => `<button class="btn car-btn" data-car="${c.key}" ${p.cash >= carPrice(c) ? '' : 'disabled'}>
          <span class="car-emoji">${c.emoji}</span><span class="car-info"><b>${c.name}</b><small>${c.desc}</small></span><span class="car-price">${fmt(carPrice(c))}</span></button>`).join('')}</div>
        <div class="modal-actions"><button class="btn" id="m-skip">買わない</button></div>`);
      box.querySelectorAll('[data-car]').forEach(b => {
        b.onclick = () => { buyCar(pi, carDef(b.dataset.car)); closeModal(); renderAll(); res(); };
      });
      $('#m-skip', box).onclick = () => { closeModal(); res(); };
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
    } else if (n.type === 'car') {
      await carDealer(pi);
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
    if (p.fuel < carOf(p).use) {
      const fee = Math.round(JAF_FEE * yearFactor() / 100) * 100;
      p.cash -= fee;
      p.fuel = 8;
      toast(`🆘 ガス欠！ JAFを呼んだ<br><b>${esc(p.name)}</b> -${fmt(fee)}（ガソリン8目盛）`, 'minus');
      log(`🆘 ${esc(p.name)}がガス欠でJAFを呼んだ -${fmt(fee)}`, p.color);
      settleDebt(pi);
      renderAll();
      await sleep(delay(1200));
    }
    const choice = await askRoll(p);
    let etc = false;
    if (choice.card >= 0) {
      const c = cardDef(p.cards[choice.card]);
      etc = c.key === 'etc';
      p.cards.splice(choice.card, 1);
      toast(`🎫 ${esc(p.name)}は${c.name}を使った！`, 'card');
      log(`🎫 ${esc(p.name)}が${c.name}を使用`, p.color);
      renderPlayers();
      await sleep(delay(600));
    }
    if (p.cpu) setActions(`<div class="prompt" style="--c:${p.color}">${esc(p.name)}（CPU）の番</div>`);
    else setActions(`<div class="prompt" style="--c:${p.color}">サイコロを振っています…</div>`);
    const rolled = await rollDice(choice.dice);
    const car = carOf(p);
    const want = rolled * car.speed;
    const steps = Math.min(want, Math.floor(p.fuel / car.use + 1e-9));
    if (car.speed > 1) {
      toast(`${car.emoji} ${car.name}！ 出目${rolled}×${car.speed} = ${want}マス`, 'car');
      await sleep(delay(900));
    }
    if (steps < want) {
      toast(`⛽ ガソリンが少ないので${steps}マスまで進めます`, 'minus');
      await sleep(delay(900));
    }
    const cands = reachable(p.pos, steps, G.dest);
    focusNodes([p.pos, ...cands.keys()], 600);
    const target = await askMove(p, cands, steps, etc);
    setActions(`<div class="prompt" style="--c:${p.color}">${esc(p.name)}が移動中…</div>`);
    await animateMove(pi, cands.get(target), etc);
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
      <table class="props"><thead><tr><th>プレイヤー</th><th>お店の収益</th></tr></thead><tbody>
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
        <span class="muted small">お店${ownedProps(r.i).length}軒</span><b>${fmt(r.a)}</b></li>`).join('')}</ol>
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
        G.t++;
        G.players.forEach(p => {
          if (p.car && G.t >= p.car.until) {
            log(`🚗 ${esc(p.name)}の${carOf(p).name}を返却しました`, p.color);
            p.car = null;
          }
        });
        log(`🗓 ${G.year}年目 ${MONTHS[G.month]}月`);
      }
    }
  }

  // ---------- 開始画面 ----------
  function setupScreen() {
    const defaults = ['あなた', 'CPU 桃子', 'CPU 金太', 'CPU 銀次'];
    const box = openModal(`<h1 class="title">🚗 サイコロ日本一周ドライブ</h1>
      <p class="subtitle">全国の高速道路をクルマで走り、SA・道の駅のお店を買い占めよう！</p>
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
          <li>クルマで高速道路を走ります。サイコロを振って、出た目の数だけ進めるマスから止まる場所を選びます。</li>
          <li><b>SA・PA・道の駅</b>（<span class="sq-ic sa"></span>四角=SA/PA、<span class="sq-ic mi"></span>丸=道の駅）に止まると、ご当地のお店を買えます。毎年3月の決算で、お店の収益（価格×収益率）が入ります。</li>
          <li>1つのスポットのお店を全部買うと<b>独占</b>！ そのスポットの収益が2倍になります。</li>
          <li><span class="sq-ic plus"></span>青マスはお金がもらえ、<span class="sq-ic minus"></span>赤マスは渋滞や故障でお金を失います（冬は被害大）。<span class="sq-ic card"></span>黄マスではサイコロを増やせるカード（ETC・ターボ・ニトロ）がもらえます。</li>
          <li><b>⛽ガソリン</b>：1マス進むごとに1目盛減ります（満タン30）。SA・道の駅に止まると給油できます（1目盛30万円）。0になるとJAFを呼んで1,500万円。残りが少ないと進めるマスも減ります。</li>
          <li><b>🛣通行料</b>：高速道路は1マス8万円、橋は20万円、フェリーは40万円（ガソリンは使いません）。ETCカードを使うターンは半額です。</li>
          <li><span class="sq-ic car"></span><b>紫マス</b>はカーディーラー。車を買うと<b>6ヶ月間</b>乗れます。🚙ハイブリッド車＝ガソリンの減りが半分、🔋電気自動車＝減りが半分で給油代が4分の1、🏎️スポーツカー＝出目の2倍進めるがガソリンの減りは2倍（1マスあたり）。</li>
          <li>北海道・四国・九州・沖縄へは<b>フェリー</b>（点線）や<b>橋</b>（青い道）で渡ります。</li>
          <li>🚩<b>目的地</b>は全国72か所のSA・道の駅からランダムに決まります。一番乗りすると賞金がもらえます。</li>
          <li>所持金がマイナスになると、安いお店から半額で売却されます。</li>
          <li>最終年の決算後、<b>総資産（所持金＋お店の価格）</b>が一番多い人の勝ち！</li>
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
          pos: spotByLabel['海老名SA'],
          cards: [],
          fuel: FUEL_MAX,
          car: null,
        });
      });
      closeModal();
      startGame(players, +$('#years', box).value, $('#fast', box).checked);
    };
  }

  function startGame(players, years, fast) {
    G = { players, years, fast, t: 0, year: 1, month: 0, turn: 0, dest: null, destBonus: 0 };
    stations().forEach(n => n.props.forEach(p => { p.owner = -1; }));
    drawTokens();
    pickDestination();
    renderAll();
    log(`🚗 ドライブ開始！ 全${years}年。海老名SAから出発します。`);
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
