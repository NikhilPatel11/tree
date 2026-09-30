const $ = i => document.getElementById(i);
let T = 'bst', root = null, heap = [], trie, steps = [], idx = 0, timer = null, quiet = false, pend = null, nid = 0;
const INFO = {
  bst: ['Binary Search Tree', 'Left ma nana, right ma moda number. Search, insert, delete darek vakhate root thi shuru thai ne ek ek step niche jay chhe.', 'Average O(log n), worst O(n) (sorted order ma insert karo to)'],
  avl: ['AVL Tree', 'Self-balancing BST: darek node no balance (left unchai - right unchai) -1, 0 ke 1 j rehvo joie, nahi to rotation thay chhe. Node ni niche balance number dekhay chhe.', 'Badhu O(log n) guaranteed'],
  minheap: ['Min Heap', 'Complete binary tree jema parent hamesha bachha thi nano. Root = sauthi nano. Insert ma sift-up, extract ma sift-down thay chhe.', 'Insert/extract O(log n), min jovu O(1)'],
  maxheap: ['Max Heap', 'Complete binary tree jema parent hamesha bachha thi moto. Root = sauthi moto. Insert ma sift-up, extract ma sift-down thay chhe.', 'Insert/extract O(log n), max jovu O(1)'],
  trie: ['Trie (Prefix Tree)', 'Darek akshar ek node. Sarkha prefix vala words same path share kare chhe. Double circle = ahiya word purun thay chhe.', 'Insert/search O(L), L = word ni lambai']
};
const isBin = () => T == 'bst' || T == 'avl', isHeap = () => T == 'minheap' || T == 'maxheap';
const nd = k => ({ k, id: ++nid, l: null, r: null });
const ht = n => n ? 1 + Math.max(ht(n.l), ht(n.r)) : 0;

/* ---- snapshots ---- */
function snap() {
  if (pend) pend.d = 0;
  if (isBin()) return { bin: 1, r: g(root) }; if (T == 'trie') return { r: gt(trie, '') }; return { bin: 1, r: gh(0) }
}
function g(n) {
  if (pend && n === pend.o && !pend.d) { pend.d = 1; n = pend.n }
  return n && { id: n.id, lab: n.k, sub: T == 'avl' ? ht(n.l) - ht(n.r) : null, ch: [g(n.l), g(n.r)] }
}
const gh = i => i < heap.length ? { id: i, lab: heap[i], ch: [gh(2 * i + 1), gh(2 * i + 2)] } : null;
const gt = (n, p) => ({ id: '^' + p, lab: p ? p.slice(-1) : '•', e: n.e, ch: Object.keys(n.c).sort().map(c => gt(n.c[c], p + c)) });
const rec = (hl, m) => { if (!quiet) steps.push({ t: snap(), hl: hl || {}, m }) };

/* ---- BST / AVL ---- */
function rotR(y) { const x = y.l; y.l = x.r; x.r = y; return x }
function rotL(x) { const y = x.r; x.r = y.l; y.l = x; return y }
function bal(n) {
  if (T != 'avl') return n; const b = ht(n.l) - ht(n.r); if (Math.abs(b) < 2) return n;
  rec({ [n.id]: 'w' }, `Node ${n.k} unbalanced chhe (balance ${b}), rotation joie.`); let x;
  if (b > 1) { if (ht(n.l.l) < ht(n.l.r)) { n.l = rotL(n.l); rec({ [n.l.id]: 'p' }, 'LR case: pehla left child par left rotation.') } x = rotR(n); pend = { o: n, n: x, d: 0 }; rec({ [x.id]: 's' }, `Right rotation: ${x.k} navo root banyo.`) }
  else { if (ht(n.r.r) < ht(n.r.l)) { n.r = rotR(n.r); rec({ [n.r.id]: 'p' }, 'RL case: pehla right child par right rotation.') } x = rotL(n); pend = { o: n, n: x, d: 0 }; rec({ [x.id]: 's' }, `Left rotation: ${x.k} navo root banyo.`) }
  pend = null; return x
}
function insR(n, k) {
  rec({ [n.id]: 'c' }, `${k} ne ${n.k} sathe sarkhavyo: ${k < n.k ? 'nano, left jao' : 'moto, right jao'}.`);
  if (k == n.k) { rec({ [n.id]: 'p' }, `${k} pehla thi chhe, duplicate add nathi karyu.`); return n }
  const d = k < n.k ? 'l' : 'r'; if (n[d]) n[d] = insR(n[d], k); else { n[d] = nd(k); rec({ [n[d].id]: 's' }, `Jagya mali, ${k} ne ${d == 'l' ? 'left' : 'right'} ma mukyo.`) }
  return bal(n)
}
function delR(n, k) {
  if (!n) { rec({}, `${k} tree ma malyo nahi.`); return null }
  rec({ [n.id]: 'c' }, `${k} ne ${n.k} sathe sarkhavyo.`);
  if (k < n.k) n.l = delR(n.l, k); else if (k > n.k) n.r = delR(n.r, k);
  else {
    if (!n.l || !n.r) { rec({ [n.id]: 'w' }, `${n.k} mali gayo. ${n.l || n.r ? 'Ek j child chhe, te tenu sthan le chhe.' : 'Leaf chhe, seedho kadhi nakhyo.'}`); return n.l || n.r }
    let s = n.r; while (s.l) s = s.l; rec({ [n.id]: 'w', [s.id]: 'p' }, `${n.k} ne 2 child chhe. Inorder successor ${s.k} (right ma sauthi nano) vaparvo.`);
    n.k = s.k; rec({ [n.id]: 'w' }, `Value ${s.k} thi replace karyu, have right ma thi ${s.k} kadhvo.`); n.r = delR(n.r, s.k)
  }
  return bal(n)
}
function find(k) {
  let c = root; if (!c) { rec({}, 'Tree khali chhe.'); return }
  while (c) { if (k == c.k) { rec({ [c.id]: 's' }, `${k} mali gayo!`); return } rec({ [c.id]: 'c' }, `${k} ne ${c.k} sathe sarkhavyo: ${k < c.k ? 'nano, left' : 'moto, right'}.`); c = k < c.k ? c.l : c.r }
  rec({}, `${k} tree ma nathi (null sudhi pahonchya).`)
}
function trav(t) {
  const out = [], vis = {}; if (!root) { rec({}, 'Tree khali chhe.'); return }
  const visit = n => { out.push(n.k); vis[n.id] = 'v'; rec({ ...vis, [n.id]: 'c' }, `${n.k} visit karyo. Output: ${out.join(', ')}`) };
  const go = n => { if (!n) return; if (t == 'pre') visit(n); go(n.l); if (t == 'in') visit(n); go(n.r); if (t == 'post') visit(n) };
  if (t == 'lvl') { const q = [root]; while (q.length) { const n = q.shift(); visit(n); n.l && q.push(n.l); n.r && q.push(n.r) } } else go(root);
  rec({ ...vis }, `Traversal purun. Output: ${out.join(', ')}`)
}

/* ---- Heap ---- */
const better = (a, b) => T == 'minheap' ? a < b : a > b;
function hIns(k) {
  heap.push(k); let i = heap.length - 1; rec({ [i]: 's' }, `${k} ne chhelle (index ${i}) mukyo.`);
  while (i > 0) {
    const p = (i - 1) >> 1; rec({ [i]: 'c', [p]: 'c' }, `${heap[i]} ne parent ${heap[p]} sathe sarkhavyo.`);
    if (better(heap[i], heap[p])) { [heap[i], heap[p]] = [heap[p], heap[i]]; rec({ [i]: 'w', [p]: 'w' }, 'Heap rule tootyo hato, swap karyo (sift-up).'); i = p } else { rec({ [i]: 'v' }, 'Heap rule barabar chhe, have swap nahi.'); break }
  }
}
function hExt() {
  if (!heap.length) { rec({}, 'Heap khali chhe.'); return } const top = heap[0], last = heap.pop();
  if (!heap.length) { rec({}, `${top} kadhyo. Heap have khali chhe.`); return }
  rec({ 0: 'p' }, `Root ${top} kadhvo chhe. Chhello ${last} ne root par lavo.`); heap[0] = last; rec({ 0: 'w' }, `${last} root par aavyo, have sift-down karvo.`); let i = 0;
  while (1) {
    let m = i, L = 2 * i + 1, R = L + 1; if (L < heap.length && better(heap[L], heap[m])) m = L; if (R < heap.length && better(heap[R], heap[m])) m = R;
    rec({ [i]: 'c', [L]: 'c', [R]: 'c' }, `${heap[i]} ne tena bachha sathe sarkhavyo.`);
    if (m == i) { rec({ [i]: 'v' }, `Heap rule barabar. ${top} kadhi didho.`); break }
    [heap[i], heap[m]] = [heap[m], heap[i]]; rec({ [i]: 'w', [m]: 'w' }, `Bachho ${T == 'minheap' ? 'nano' : 'moto'} hato, swap karyo (sift-down).`); i = m
  }
}

/* ---- Trie ---- */
function tIns(w) {
  let n = trie, p = ''; rec({ '^': 'p' }, `"${w}" insert karvo chhe, root thi shuru.`);
  for (const ch of w) { p += ch; if (!n.c[ch]) { n.c[ch] = { c: {}, e: false }; rec({ ['^' + p]: 's' }, `'${ch}' navo node banyo.`) } else rec({ ['^' + p]: 'c' }, `'${ch}' pehla thi chhe, same path vaparyo.`); n = n.c[ch] }
  n.e = true; rec({ ['^' + p]: 'v' }, `"${w}" purun. Double circle = word no end.`)
}
function tFind(w) {
  let n = trie, p = ''; rec({ '^': 'p' }, `"${w}" shodhvo chhe.`);
  for (const ch of w) { p += ch; if (!n.c[ch]) { rec({}, `'${ch}' no node nathi, "${w}" trie ma nathi.`); return } n = n.c[ch]; rec({ ['^' + p]: 'c' }, `'${ch}' mali gayo.`) }
  rec({ ['^' + p]: n.e ? 's' : 'w' }, n.e ? `"${w}" mali gayo (word end chhe).` : `"${w}" prefix chhe, pan word tarike add nathi karyo.`)
}

/* ---- rendering ---- */
function render(t, hl) {
  const svg = $('svg');
  if (!t.r) { svg.setAttribute('viewBox', '0 0 420 70'); svg.style.width = '420px'; svg.innerHTML = '<text x="10" y="40" class="mt">Tree khali chhe. Upar thi Insert karo.</text>'; return }
  let cnt = 0, md = 0; const ns = [], es = [];
  const lay = (n, d) => {
    md = Math.max(md, d); n.y = d;
    if (t.bin) { n.ch[0] && lay(n.ch[0], d + 1); n.x = cnt++; n.ch[1] && lay(n.ch[1], d + 1) }
    else { n.ch.forEach(c => lay(c, d + 1)); n.x = n.ch.length ? (n.ch[0].x + n.ch[n.ch.length - 1].x) / 2 : cnt++ }
    ns.push(n); n.ch.forEach(c => c && es.push([n, c]))
  };
  lay(t.r, 0); const W = Math.max(cnt, 1) * 46 + 20, H = (md + 1) * 66 + 24, X = n => n.x * 46 + 33, Y = n => n.y * 66 + 30;
  svg.setAttribute('viewBox', `0 0 ${W} ${H}`); svg.style.width = W + 'px';
  svg.innerHTML = es.map(([a, b]) => `<line class="ed" x1="${X(a)}" y1="${Y(a)}" x2="${X(b)}" y2="${Y(b)}"/>`).join('') +
    ns.map(n => `<g class="nd ${hl[n.id] || ''}"><circle cx="${X(n)}" cy="${Y(n)}" r="17"/>${n.e ? `<circle class="ring" cx="${X(n)}" cy="${Y(n)}" r="21"/>` : ''}<text x="${X(n)}" y="${Y(n)}">${n.lab}</text>${n.sub !== null && n.sub !== undefined ? `<text class="sb" x="${X(n)}" y="${Y(n) + 29}">b:${n.sub}</text>` : ''}</g>`).join('')
}
function draw() {
  const s = steps[idx] || { t: snap(), hl: {}, m: 'Value lakho ane Insert dabavo.' }; render(s.t, s.hl); $('msg').textContent = s.m;
  $('cnt').textContent = steps.length ? `Step ${idx + 1} / ${steps.length}` : ''; $('prev').disabled = idx <= 0; $('next').disabled = idx >= steps.length - 1; if (idx >= steps.length - 1) stop()
}
function stop() { clearInterval(timer); timer = null; $('play').textContent = 'Play' }
function play() {
  if (timer) return stop(); if (idx >= steps.length - 1) idx = 0; $('play').textContent = 'Pause';
  timer = setInterval(() => { if (idx < steps.length - 1) { idx++; draw() } else stop() }, 1100 - $('spd').value * 100)
}
function run(fn) { stop(); steps = []; rec({}, 'Operation shuru. Tree ni current sthiti.'); fn(); idx = 0; draw(); if (steps.length > 1) play() }

/* ---- UI ---- */
function val() { const v = $('inp').value.trim(); if (T == 'trie') return /^[a-z]{1,8}$/.test(v) ? v : null; const n = +v; return v !== '' && Number.isInteger(n) && n >= 1 && n <= 99 ? n : null }
function bad() { $('msg').textContent = T == 'trie' ? '1 thi 8 nana english akshar (a-z) nu word lakho.' : '1 thi 99 vachche number lakho.' }
function add(k) { if (isBin()) { if (!root) { root = nd(k); rec({ [root.id]: 's' }, `Tree khali hatu, ${k} root bane chhe.`) } else root = insR(root, k) } else if (isHeap()) hIns(k); else tIns(k) }
function clear() { root = null; heap = []; trie = { c: {}, e: false }; steps = []; idx = 0; stop() }
function setT(k) {
  T = k; clear(); document.querySelectorAll('.chip').forEach(b => b.setAttribute('aria-pressed', b.dataset.k == k));
  $('an').textContent = INFO[k][0]; $('ad').textContent = INFO[k][1]; $('ac').textContent = INFO[k][2];
  $('inp').placeholder = k == 'trie' ? 'word, jem ke cat' : '1 thi 99 number'; $('inp').value = '';
  $('del').style.display = k == 'trie' ? 'none' : ''; $('del').textContent = isHeap() ? 'Extract root' : 'Delete';
  $('srch').style.display = isHeap() ? 'none' : ''; $('trv').style.display = isBin() ? '' : 'none'; $('inp').disabled = false; rnd();
}
function rnd() {
  stop(); quiet = true; clearData(); if (T == 'trie') ['cat', 'car', 'cart', 'dog', 'do'].forEach(tIns); else { const s = new Set(); while (s.size < 7) s.add(1 + Math.floor(Math.random() * 99));[...s].forEach(add) }
  quiet = false; steps = []; idx = 0; steps.push({ t: snap(), hl: {}, m: 'Random tree taiyar. Have Insert / Delete / Search try karo.' }); draw()
}
function clearData() { root = null; heap = []; trie = { c: {}, e: false } }
$('chips').innerHTML = Object.keys(INFO).map(k => `<button class="chip" data-k="${k}" aria-pressed="false">${INFO[k][0]}</button>`).join('');
$('chips').onclick = e => { if (e.target.dataset.k) setT(e.target.dataset.k) };
$('ins').onclick = () => { const v = val(); if (v === null) return bad(); run(() => { add(v); rec({}, `Insert purun.`) }); $('inp').value = '' };
$('del').onclick = () => { if (isHeap()) return run(() => hExt()); const v = val(); if (v === null) return bad(); run(() => { if (root) root = delR(root, v); else rec({}, 'Tree khali chhe.'); rec({}, 'Delete purun.') }) };
$('srch').onclick = () => { const v = val(); if (v === null) return bad(); run(() => T == 'trie' ? tFind(v) : find(v)) };
$('rnd').onclick = rnd; $('clr').onclick = () => { clear(); draw() };
$('trv').onclick = e => { if (e.target.dataset.t) run(() => trav(e.target.dataset.t)) };
$('inp').onkeydown = e => { if (e.key == 'Enter') $('ins').click() };
$('next').onclick = () => { stop(); if (idx < steps.length - 1) { idx++; draw() } }; $('prev').onclick = () => { stop(); if (idx > 0) { idx--; draw() } };
$('rst').onclick = () => { stop(); idx = 0; draw() }; $('play').onclick = play; $('spd').oninput = () => { if (timer) { stop(); play() } };
setT('bst');
