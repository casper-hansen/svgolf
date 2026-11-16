// site/site.js's tabs and charts.js's schematic, outside a browser (no libraries): a small DOM, built from the
// skeleton of a real record page (test_detail.DetailTest.test_the_tab_script writes it: every element with an id, the
// tab bars, links to fragments, the schematic's box, tools and drawing), with a layout model of one rule: an element
// inside a hidden pane, or the other course's, has no size. Checked (decided 2026-11-16: a detail page's five tabs):
//   * the page's tabs: roles, aria-selected/aria-controls/aria-labelledby, roving tabindex, the first one chosen;
//   * a click shows its pane and pushes `#id` as a new history entry; the Left, Right, Home and End keys move and
//     replace it;
//   * a fragment on load (a tab's, a card's inside a tab, the netlist card's pane inside the Schematics tab, a cell
//     of the drawing) opens every tab around it, outer first, and scrolls to it; a click on a link into a tab too;
//   * Back to an entry of the script's shows its tab and leaves the scroll to the browser; a fragment reached another
//     way is scrolled to; `hashchange` after `popstate` does nothing twice;
//   * the schematic, drawn in a hidden tab, is fitted to its box when its tab is first shown (site.js's `tabshow`
//     event: here there is no ResizeObserver), and a critical-path link from another tab opens the drawing's tabs;
//   * the page's bar, where style.css makes it stick (decided 2026-11-16, the owner's item 2): `--tabs-bar` on <html>
//     is its height (style.css's scroll margin in the panes: nothing a link or the focus brings lands under it), its
//     panes keep no inline scroll margin, the netlist card's panes add the bar's; a tab chosen in the stuck bar (the
//     panel's top above the view) shows its pane from the top, and one chosen while the bar is in its place scrolls
//     nothing. Without the sticky bar, no `--tabs-bar` is set;
//   * the display-instance note's button (decided 2026-11-16, the owner's item 6): a click opens its note
//     (aria-expanded), a second one closes it, Escape closes it, a click elsewhere closes it, a click in the note
//     does not.
//     node tests/site/tabsjs_check.js site/site.js site/charts.js SKELETON.json
const fs = require("fs");
const [siteSrc, chartsSrc] = [fs.readFileSync(process.argv[2], "utf8"), fs.readFileSync(process.argv[3], "utf8")];
const skeleton = JSON.parse(fs.readFileSync(process.argv[4], "utf8"));
let fails = 0, oks = 0;
function ok(c, msg) { if (!c) { fails++; console.log("FAIL " + msg); } else { oks++; } }

// -- selectors: compound parts (tag, #id, .class, [a], [a='v'], [a^='v']) joined by " " or ">", lists by "," --------
function parseCompound(s) {
  const c = { tag: null, id: null, classes: [], attrs: [], scope: false };
  const re = /(:scope)|#([\w-]+)|\.([\w-]+)|\[([\w-]+)(?:(\^?=)(?:'([^']*)'|"([^"]*)"|([^\]]*)))?\]|([\w-]+|\*)/g;
  let m;
  while ((m = re.exec(s))) {
    if (m[1]) { c.scope = true; } else if (m[2]) { c.id = m[2]; } else if (m[3]) { c.classes.push(m[3]); }
    else if (m[4]) { c.attrs.push([m[4], m[5] || null, m[6] !== undefined ? m[6] : m[7] !== undefined ? m[7] : m[8]]); }
    else if (m[9] && m[9] !== "*") { c.tag = m[9].toLowerCase(); }
  }
  return c;
}
function parse(sel) {
  return sel.split(",").map(function (one) {
    const parts = [], toks = one.trim().replace(/\s*>\s*/g, " > ").split(/\s+/);
    let comb = " ";
    toks.forEach(function (t) { if (t === ">") { comb = ">"; } else { parts.push({ comb, c: parseCompound(t) }); comb = " "; } });
    return parts;
  });
}
function matchC(el, c, scope) {
  if (!el || !el.tagName) { return false; }
  if (c.scope) { return el === scope; }
  if (c.tag && el.tagName !== c.tag) { return false; }
  if (c.id && el.getAttribute("id") !== c.id) { return false; }
  for (const k of c.classes) { if (!el.classList.contains(k)) { return false; } }
  for (const [a, op, v] of c.attrs) {
    const got = el.getAttribute(a);
    if (got === null) { return false; }
    if (op === "=" && got !== v) { return false; }
    if (op === "^=" && got.indexOf(v) !== 0) { return false; }
  }
  return true;
}
function matchParts(el, parts, i, scope) {          // parts[0..i] end at el
  if (!matchC(el, parts[i].c, scope)) { return false; }
  if (i === 0) { return true; }
  if (parts[i].comb === ">") { return matchParts(el.parentNode, parts, i - 1, scope); }
  for (let p = el.parentNode; p && p.tagName; p = p.parentNode) { if (matchParts(p, parts, i - 1, scope)) { return true; } }
  return false;
}
function matches(el, sel, scope) { return parse(sel).some(function (parts) { return matchParts(el, parts, parts.length - 1, scope); }); }

// -- the DOM ----------------------------------------------------------------------------------------------------------
let doc, win;
class Element {
  constructor(tag, attrs) {
    this.tagName = tag; this.attrs = Object.assign({}, attrs); this.children = []; this.parentNode = null;
    this.listeners = {}; this.style = {}; this.scrolledTo = 0; this.scrollLeft = 0; this.scrollTop = 0;
  }
  getAttribute(k) { return k in this.attrs ? String(this.attrs[k]) : null; }
  setAttribute(k, v) { this.attrs[k] = String(v); }
  removeAttribute(k) { delete this.attrs[k]; }
  hasAttribute(k) { return k in this.attrs; }
  get id() { return this.getAttribute("id") || ""; }
  set id(v) { this.setAttribute("id", v); }
  get hidden() { return "hidden" in this.attrs; }
  set hidden(v) { if (v) { this.attrs.hidden = ""; } else { delete this.attrs.hidden; } }
  get tabIndex() { return "tabindex" in this.attrs ? Number(this.attrs.tabindex) : (this.tagName === "a" ? 0 : -1); }
  set tabIndex(v) { this.attrs.tabindex = String(v); }
  get open() { return "open" in this.attrs; }
  set open(v) { if (v) { this.attrs.open = ""; } else { delete this.attrs.open; } }
  get classList() {
    const el = this;
    const list = () => (el.attrs.class || "").split(/\s+/).filter(Boolean);
    return { contains: (c) => list().indexOf(c) >= 0,
             add: (c) => { if (list().indexOf(c) < 0) { el.attrs.class = list().concat([c]).join(" "); } },
             remove: (c) => { el.attrs.class = list().filter((x) => x !== c).join(" "); },
             toggle: (c, on) => { const has = list().indexOf(c) >= 0; if (on === undefined) { on = !has; }
                                  if (on && !has) { el.attrs.class = list().concat([c]).join(" "); }
                                  if (!on && has) { el.attrs.class = list().filter((x) => x !== c).join(" "); } } };
  }
  get parentElement() { return this.parentNode && this.parentNode.tagName ? this.parentNode : null; }
  get textContent() { return this.attrs["#text"] || this.children.map((c) => c.textContent).join(""); }
  set textContent(v) { this.attrs["#text"] = v; }
  appendChild(c) { c.parentNode = this; this.children.push(c); return c; }
  contains(el) { for (let p = el; p; p = p.parentNode) { if (p === this) { return true; } } return false; }
  all() { const out = []; (function walk(n) { n.children.forEach((c) => { out.push(c); walk(c); }); })(this); return out; }
  querySelectorAll(sel) { const me = this; return this.all().filter((el) => matches(el, sel, me)); }
  querySelector(sel) { return this.querySelectorAll(sel)[0] || null; }
  matches(sel) { return matches(this, sel, null); }
  closest(sel) { for (let p = this; p && p.tagName; p = p.parentNode) { if (matches(p, sel, null)) { return p; } } return null; }
  addEventListener(t, f, o) { (this.listeners[t] = this.listeners[t] || []).push({ f, capture: o === true || !!(o && o.capture) }); }
  removeEventListener() {}
  dispatchEvent(e) {
    const path = [];
    for (let p = this; p; p = p.parentNode) { path.push(p); }
    path.push(win);
    e.target = this;
    const fire = (n, capture) => (n.listeners[e.type] || []).filter((l) => l.capture === capture)
      .forEach((l) => l.f.call(n, e));
    for (let i = path.length - 1; i >= 0; i--) { fire(path[i], true); }
    fire(this, false);
    if (e.bubbles !== false) { for (let i = 1; i < path.length && !e.stopped; i++) { fire(path[i], false); } }
    return !e.defaultPrevented;
  }
  click() { this.dispatchEvent(event("click")); }
  focus() { doc.activeElement = this; }
  // the layout: hidden (by its pane, the other course or a closed disclosure's content) is no size; the schematic's
  // box is 800 px wide inside, a drawing its own width
  shown() {
    for (let p = this; p && p.tagName; p = p.parentNode) {
      if (p.hidden) { return false; }
      const cls = p.attrs.class || "";
      if (/\bpdk-asap7pnr\b/.test(cls) && doc.documentElement.getAttribute("data-pdk") !== "asap7pnr") { return false; }
    }
    return true;
  }
  get clientWidth() { return !this.shown() ? 0 : this.classList.contains("sch-box") ? 800 : 1000; }
  get clientHeight() { return !this.shown() ? 0 : 600; }
  get clientLeft() { return 0; }
  get clientTop() { return 0; }
  get scrollWidth() { return this.clientWidth; }
  get offsetWidth() { return this.clientWidth; }
  get offsetHeight() { return this.clientHeight; }
  getBoundingClientRect() {
    const w = !this.shown() ? 0 : this.tagName === "svg" ? Number(this.getAttribute("width")) || 0 : this.clientWidth;
    const h = !this.shown() ? 0 : this.tagName === "svg" ? Number(this.getAttribute("height")) || 0 : 20;
    const top = this.rectTop || 0;                 // a test moves an element above the view (the stuck bar's panel)
    return { top, left: 0, right: w, bottom: top + h, width: w, height: h };
  }
  scrollIntoView() { this.scrolledTo++; }
}
function event(type, extra) {
  return Object.assign({ type, bubbles: true, button: 0, defaultPrevented: false,
                         preventDefault() { this.defaultPrevented = true; }, stopPropagation() { this.stopped = true; } },
                       extra || {});
}

function build(node, parent) {
  const el = new Element(node.tag, node.attrs || {});
  if (node.text) { el.attrs["#text"] = node.text; }
  if (node.tag === "svg") {                          // the viewBox, read by nothing here; width/height are attributes
    el.viewBox = { baseVal: { width: Number(node.attrs.width) || 0 } };
  }
  parent.appendChild(el);
  (node.children || []).forEach((c) => build(c, el));
  return el;
}

// a page, loaded at `hash`, with the two scripts run (site.js first, as the page loads them)
function load(hash, opts) {
  opts = opts || {};
  const entries = [{ state: null, hash: hash || "" }];
  let at = 0;
  const html = new Element("html", { "data-pdk": opts.pdk || "sky130" });
  const body = html.appendChild(new Element("body", {}));
  doc = {
    documentElement: html, body, readyState: "interactive", activeElement: null, listeners: {},
    getElementById(id) { return html.all().find((e) => e.getAttribute("id") === id) || null; },
    querySelectorAll(sel) { return html.querySelectorAll(sel); },
    querySelector(sel) { return html.querySelector(sel); },
    createElement(t) { return new Element(t, {}); },
    addEventListener(t, f, o) { Element.prototype.addEventListener.call(this, t, f, o); },
  };
  html.parentNode = doc;
  doc.tagName = null;
  build(skeleton, body);
  const calls = { push: 0, replace: 0 };
  const location = {
    get hash() { return entries[at].hash; },
    get href() { return "http://x/r.html" + entries[at].hash; },
  };
  const history = {
    get state() { return entries[at].state; },
    get length() { return entries.length; },
    pushState(s, t, u) { calls.push++; entries.splice(at + 1); entries.push({ state: s, hash: u }); at++; },
    replaceState(s, t, u) { calls.replace++; entries[at] = { state: s, hash: u === undefined ? entries[at].hash : u }; },
  };
  const scrolls = [];
  win = {
    listeners: {}, location, history, innerHeight: 900, pageYOffset: 0, scrolls,
    scrollTo(x, y) { scrolls.push([x, y]); },
    CustomEvent: function (type, init) { return event(type, { bubbles: !!(init && init.bubbles) }); },
    // style.css's sticky page bar, where the test asks for it (`opts.sticky`)
    getComputedStyle(el) { return { display: el.shown() ? "inline-flex" : "none",
                                     position: opts.sticky && el.matches(".tabs-page > .tabs-nav") ? "sticky" : "static" }; },
    addEventListener(t, f, o) { Element.prototype.addEventListener.call(this, t, f, o); },
    isSecureContext: false,
  };
  if (opts.resizeObserver) { win.ResizeObserver = opts.resizeObserver; }
  for (const src of [siteSrc, chartsSrc]) {
    new Function("window", "document", "location", "history", "navigator", "ResizeObserver", src)(
      win, doc, location, history, {}, win.ResizeObserver);
  }
  // the browser: Back and Forward (`popstate` with the entry's state, then `hashchange` when the fragment changed),
  // a fragment reached another way (a new entry with no state)
  function traverse(d) {
    if (at + d < 0 || at + d >= entries.length) { return; }       // no entry there: the browser does nothing
    const before = entries[at].hash;
    at += d;
    Element.prototype.dispatchEvent.call(win, Object.assign(event("popstate"), { state: entries[at].state, bubbles: false }));
    if (entries[at].hash !== before) { Element.prototype.dispatchEvent.call(win, Object.assign(event("hashchange"), { bubbles: false })); }
  }
  function navigate(h) {
    entries.splice(at + 1); entries.push({ state: null, hash: h }); at++;
    Element.prototype.dispatchEvent.call(win, Object.assign(event("popstate"), { state: null, bubbles: false }));
    Element.prototype.dispatchEvent.call(win, Object.assign(event("hashchange"), { bubbles: false }));
  }
  return { doc, win, calls, entries, back: () => traverse(-1), forward: () => traverse(1), navigate, get at() { return at; } };
}

// -- the page's tabs -----------------------------------------------------------------------------------------------------
const TABS = ["source", "writeup", "schematics", "charts", "reproduce"];
function pageTabs(d) { return d.querySelectorAll(".tabs-page > .tabs-nav > a"); }
function chosen(d) { return TABS.filter((id) => !d.getElementById(id).hidden); }
function inner(d) { return ["schematic", "critical-path", "cells"].filter((id) => !d.getElementById(id).hidden); }

let P = load("");
let d = P.doc, tabs = pageTabs(d);
ok(tabs.length === 5, "five tabs: " + tabs.length);
ok(d.querySelector(".tabs-page > .tabs-nav").getAttribute("role") === "tablist", "the bar is a tablist");
ok(tabs.every((t, k) => t.getAttribute("role") === "tab" && t.getAttribute("aria-controls") === TABS[k]), "tabs control their panes");
ok(TABS.every((id, k) => d.getElementById(id).getAttribute("role") === "tabpanel" &&
   d.getElementById(id).getAttribute("aria-labelledby") === tabs[k].id), "panes are tabpanels labelled by their tabs");
ok(tabs.map((t) => t.getAttribute("aria-selected")).join() === "true,false,false,false,false", "the first tab is chosen");
ok(tabs.map((t) => t.tabIndex).join() === "0,-1,-1,-1,-1", "roving tabindex");
ok(chosen(d).join() === "source", "one pane shown: " + chosen(d));
ok(d.querySelector(".tabs-page").classList.contains("js-tabs"), "the panel is marked js-tabs");
ok(P.entries[0].state && P.entries[0].state.svgolfTabs === 1, "the page's first entry is marked");
const box = d.querySelector("[data-schematic]"), svg = box && box.querySelector("svg.sch");
const w0 = svg ? Number(svg.getAttribute("width")) : 0;
ok(svg && w0 > 800, "the skeleton has a drawing wider than its box (" + w0 + " px)");
ok(svg && Number(svg.getAttribute("width")) === w0, "a drawing in a hidden tab is not fitted at load (its box has no width)");

// a click: a new entry, the pane shown, the drawing fitted on first show
tabs[2].click();
ok(chosen(d).join() === "schematics" && P.win.location.hash === "#schematics" && P.calls.push === 1,
   "a click on Schematics shows it and pushes #schematics");
ok(svg && Number(svg.getAttribute("width")) <= 800 && box.classList.contains("zoomable"),
   "the drawing is fitted to its box when its tab is first shown (" + (svg && svg.getAttribute("width")) + " px)");
tabs[2].click();
ok(P.calls.push === 1, "a click on the tab already chosen adds no entry");
tabs[3].click();
ok(chosen(d).join() === "charts" && P.calls.push === 2, "Charts");
let scrolled = d.getElementById("schematics").scrolledTo;
P.back();
ok(chosen(d).join() === "schematics" && d.getElementById("schematics").scrolledTo === scrolled,
   "Back: Schematics, the scroll left to the browser");
P.back();
ok(chosen(d).join() === "source", "Back to the first entry (no fragment): the first tab");
P.forward();
ok(chosen(d).join() === "schematics", "Forward: Schematics");
P.navigate("#area-time");
ok(chosen(d).join() === "charts" && d.getElementById("area-time").scrolledTo === 1,
   "a fragment reached another way (#area-time): Charts, scrolled to once (hashchange after popstate is not done twice)");

// keys: they move the choice and replace the entry
P = load(""); d = P.doc; tabs = pageTabs(d);
tabs[0].focus();
const key = (k) => d.activeElement.dispatchEvent(event("keydown", { key: k }));
key("ArrowRight");
ok(tabs[1].getAttribute("aria-selected") === "true" && d.activeElement === tabs[1] && tabs[1].tabIndex === 0 &&
   tabs[0].tabIndex === -1, "ArrowRight: the next tab, focused");
ok(P.calls.push === 0 && P.win.location.hash === "#writeup", "the keys replace the entry: " + P.win.location.hash);
key("End");
ok(d.activeElement === tabs[4] && chosen(d).join() === "reproduce", "End: the last");
key("ArrowRight");
ok(d.activeElement === tabs[0] && chosen(d).join() === "source", "ArrowRight on the last: the first");
key("ArrowLeft");
ok(d.activeElement === tabs[4], "ArrowLeft on the first: the last");
key("Home");
ok(d.activeElement === tabs[0], "Home: the first");

// fragments on load: every tab around the target, outer first, then scrolled to
for (const [hash, outer, innerPane] of [["#writeup", "writeup", null], ["#sources", "source", null],
                                        ["#area-time", "charts", null], ["#critical-path", "schematics", "critical-path"],
                                        ["#cells", "schematics", "cells"], ["#reproduce", "reproduce", null]]) {
  if (!skeleton.ids.includes(hash.slice(1))) { continue; }
  P = load(hash); d = P.doc;
  ok(chosen(d).join() === outer && (!innerPane || inner(d).join() === innerPane) &&
     d.getElementById(hash.slice(1)).scrolledTo >= 1,
     `${hash} on load: ${outer}${innerPane ? " > " + innerPane : ""}, scrolled to`);
}
const heading = skeleton.ids.find((i) => i.indexOf("writeup-") === 0);
if (heading) {
  P = load("#" + heading); d = P.doc;
  ok(chosen(d).join() === "writeup", `#${heading} on load: Writeup`);
}
// a link into a tab, from outside the tabs (the dashboard's): the tabs open, a new entry
P = load(""); d = P.doc;
const dash = d.querySelectorAll("#dashboard a[href^='#']").find((a) => a.getAttribute("href") === "#cells");
if (dash) {
  dash.click();
  ok(chosen(d).join() === "schematics" && inner(d).join() === "cells" && P.win.location.hash === "#cells" &&
     P.calls.push === 1 && d.getElementById("cells").scrolledTo === 1, "the dashboard's #cells: Schematics > Cells, pushed");
}
// a cell of the drawing on load, and a critical-path link: the drawing's tabs open, the cell picked
const cell = skeleton.ids.find((i) => i.indexOf("sch-") === 0);
if (cell) {
  P = load("#" + cell); d = P.doc;
  ok(chosen(d).join() === "schematics" && inner(d).join() === "schematic" &&
     d.getElementById(cell).classList.contains("picked"), `#${cell} on load: Schematics > Schematic, the cell picked`);
  P = load("#critical-path"); d = P.doc;
  const link = d.querySelector("a.sch-link");
  if (link) {
    link.click();
    const target = d.getElementById(link.getAttribute("href").slice(1));
    ok(inner(d).join() === "schematic" && target.classList.contains("picked") && P.win.history.state &&
       P.win.history.state.svgolfTabs === 1, "a critical-path link opens the drawing's tab and keeps the entry's state");
  }
}
// with a ResizeObserver as well, a drawing is fitted once, on its first show
let observed = 0;
P = load("", { resizeObserver: function (cb) { this.observe = () => { observed++; }; this.disconnect = () => {}; } });
d = P.doc;
pageTabs(d)[2].click();
const s2 = d.querySelector("[data-schematic] svg.sch");
ok(observed === 1 && Number(s2.getAttribute("width")) <= 800, "with a ResizeObserver too: watched, and fitted on first show");

// the stuck bar (style.css's sticky page bar): --tabs-bar is the bar's height, the panes keep no inline margin
P = load(""); d = P.doc;
ok(!d.documentElement.style["--tabs-bar"], "no sticky bar: no --tabs-bar set");
P = load("", { sticky: true }); d = P.doc; tabs = pageTabs(d);
const nav = d.querySelector(".tabs-page > .tabs-nav"), panel = d.querySelector(".tabs-page");
ok(d.documentElement.style["--tabs-bar"] === (nav.offsetHeight + 8) + "px",
   "the stuck bar: --tabs-bar is its height (" + d.documentElement.style["--tabs-bar"] + ")");
ok(TABS.every((id) => !d.getElementById(id).style.scrollMarginTop || d.getElementById(id).hidden),
   "the stuck bar: the pane shown keeps no inline scroll margin (style.css's --tabs-bar)");
tabs[2].click();
const cp = d.getElementById("schematic");
ok(cp && /^calc\(var\(--tabs-bar, 0px\) \+ \d+px\)$/.test(cp.style.scrollMarginTop),
   "the netlist card's pane shown: its margin adds the stuck bar's (" + (cp && cp.style.scrollMarginTop) + ")");
tabs[0].click();
tabs[1].click();
ok(P.win.scrolls.length === 0, "a tab chosen while the bar is in its place scrolls nothing");
panel.rectTop = -1500;                     // deep in the pane: the panel's top far above the view, the bar stuck
tabs[3].click();
ok(chosen(d).join() === "charts" && P.win.scrolls.length === 1 && P.win.scrolls[0][1] === -1500,
   "a tab chosen in the stuck bar shows its pane from the top (scrolled to the panel's top)");
tabs[3].click();
ok(P.win.scrolls.length === 1, "a click on the tab already chosen scrolls nothing");
d.activeElement = tabs[3];
tabs[3].dispatchEvent(event("keydown", { key: "ArrowRight" }));
ok(chosen(d).join() === "reproduce" && P.win.scrolls.length === 2, "a key in the stuck bar too");

// the display-instance note's button
P = load(""); d = P.doc;
const nbtn = d.querySelector("button.hnote-btn");
if (skeleton.ids.includes("schematic-note")) {
  const nbody = d.getElementById("schematic-note");
  const open = () => nbtn.getAttribute("aria-expanded") === "true";
  ok(nbtn && !open(), "the note's button, closed at first");
  nbtn.click();
  ok(open() && !nbtn.hasAttribute("data-dismissed"), "a click opens the note");
  nbody.click();
  ok(open(), "a click in the note leaves it open");
  nbtn.click();
  ok(!open() && nbtn.hasAttribute("data-dismissed"), "a second click closes it (hidden while the pointer stays)");
  nbtn.dispatchEvent(event("mouseleave", { bubbles: false }));
  ok(!nbtn.hasAttribute("data-dismissed"), "the pointer gone: hover may show it again");
  nbtn.click();
  d.body.dispatchEvent(event("keydown", { key: "Escape" }));
  ok(!open() && nbtn.hasAttribute("data-dismissed"), "Escape closes it, and hides it while the focus stays");
  nbtn.dispatchEvent(event("blur", { bubbles: false }));
  nbtn.click();
  d.querySelector(".tabs-page > .tabs-nav > a").dispatchEvent(event("click"));
  ok(!open(), "a click elsewhere closes it");
} else {
  ok(!nbtn, "no display-instance note on this page: no button");
}

console.log(fails ? `${fails} failed, ${oks} ok` : `all ok (${oks})`);
process.exit(fails ? 1 : 0);
