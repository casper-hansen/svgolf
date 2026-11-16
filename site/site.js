// svGolf site: the one shared script. Every page reads without it; it adds a copy button to each
// code block (page.py's code_block and the Markdown renderer emit `pre.code`) and turns a task
// page's property panel, a detail page's five tabs and its netlist card (tabs inside the Schematics tab) into tabs
// (with the links into their panes: a second click on a link whose fragment the URL already names still shows its
// pane; a link into a pane of a pane opens both). A page's tabs are history entries: choosing one by a click names it
// in the URL as a new entry (`#writeup`), so Back shows the tab before, and a link or a URL that names a tab or
// anything inside one opens it. A pane shown that was hidden gets a `tabshow` event (bubbling), for what can only be
// measured once it is shown (charts.js: the schematic's first fit). No libraries, nothing fetched.
(function () {
  "use strict";

  // the history entries this script made or marked carry this key in their state: Back or Forward to one of them
  // restores its own scroll position (the browser's), where a fragment reached any other way is scrolled to here
  var KEY = "svgolfTabs";

  function mark(state) {
    var out = {};
    if (state && typeof state === "object") {
      Object.keys(state).forEach(function (k) { out[k] = state[k]; });
    }
    out[KEY] = 1;
    return out;
  }

  function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      return navigator.clipboard.writeText(text);
    }
    return new Promise(function (resolve, reject) {     // file:// and plain http: a hidden textarea
      var ta = document.createElement("textarea");
      ta.value = text;
      ta.setAttribute("readonly", "");
      ta.style.position = "fixed";
      ta.style.opacity = "0";
      document.body.appendChild(ta);
      ta.select();
      try {
        document.execCommand("copy") ? resolve() : reject(new Error("copy refused"));
      } catch (e) {
        reject(e);
      } finally {
        document.body.removeChild(ta);
      }
    });
  }

  function addCopy(pre) {
    var box = pre.parentElement;
    if (!box || !box.classList.contains("codebox")) {
      box = document.createElement("div");
      box.className = "codebox";
      pre.parentNode.insertBefore(box, pre);
      box.appendChild(pre);
    }
    var btn = document.createElement("button");
    btn.type = "button";
    btn.className = "copy";
    btn.textContent = "Copy";
    btn.setAttribute("aria-label", "Copy the code to the clipboard");
    btn.addEventListener("click", function () {
      var code = pre.querySelector("code") || pre;
      copyText(code.textContent).then(function () {
        btn.textContent = "Copied";
        btn.classList.add("done");
        setTimeout(function () { btn.textContent = "Copy"; btn.classList.remove("done"); }, 1600);
      }, function () {
        btn.textContent = "Select and copy";
      });
    });
    var actions = box.querySelector(":scope > .codebox-head .codebox-actions");
    if (actions) {
      actions.appendChild(btn);
    } else {
      box.appendChild(btn);
    }
  }

  // A tab set: the property panel (page.py's props_panel), a card's tabs (page.py's tabs: a detail page's netlist) or
  // a page's tabs (page.py's tabs with page=True, data-tabs="page": a detail page's five). Without this script the
  // links jump to panes that stand one under the other. A link or a URL fragment that names a pane, or something
  // inside one (a card: #prop-COMPUTES_SUM, #def-SvGolf.HoldAll; a group: #reject-at-proof; a card of a page's tab:
  // #area-time), shows that pane and opens the card.
  function initTabs(panel) {
    var page = panel.getAttribute("data-tabs") === "page";
    var tabs = Array.prototype.slice.call(panel.querySelectorAll(     // the panel's tabs, or a card's or a page's
      ":scope > .props-head > .props-tabs > a[href^='#'], " +         // (page.py's tabs)
      ":scope > .tabs-nav > a[href^='#']"));
    var panes = tabs.map(function (tab) { return document.getElementById(tab.getAttribute("href").slice(1)); });
    if (tabs.length < 2 || panes.some(function (p) { return !p; })) {
      return null;
    }
    panel.classList.add("js-tabs");
    var list = tabs[0].parentNode;
    list.setAttribute("role", "tablist");
    // a tab its course hides (the routed course's Layout on sky130: style.css hides `.pdk-asap7pnr`) is never the one
    // shown; when the reader changes the course (pdk.js sets <html data-pdk>), a pane that left is replaced by the first
    function shown(k) {
      return window.getComputedStyle(tabs[k]).display !== "none";
    }
    function usable(k) {
      if (k >= 0 && shown(k)) { return k; }
      for (var j = 0; j < tabs.length; j++) { if (shown(j)) { return j; } }
      return 0;
    }

    tabs.forEach(function (tab, k) {
      tab.setAttribute("role", "tab");
      tab.id = tab.id || panes[k].id + "-tab";
      tab.setAttribute("aria-controls", panes[k].id);
      panes[k].setAttribute("role", "tabpanel");
      panes[k].setAttribute("aria-labelledby", tab.id);
    });

    // a pane scrolled to (by a link, the URL's fragment or the browser's own scroll to it) leaves the tabs above
    // it in view: its scroll margin is the height of the panel's head
    function margin(k) {
      var gap = panes[k].getBoundingClientRect().top - panel.getBoundingClientRect().top;
      panes[k].style.scrollMarginTop = Math.max(0, Math.round(gap)) + "px";
    }

    var current = 0;
    function select(k, focus) {
      k = usable(k);
      current = k;
      var showing = panes[k].hidden;
      tabs.forEach(function (tab, j) {
        tab.setAttribute("aria-selected", j === k ? "true" : "false");
        tab.tabIndex = j === k ? 0 : -1;
        panes[j].hidden = j !== k;
      });
      margin(k);
      // what can only be measured once shown (the schematic's first fit) is told: charts.js listens
      if (showing && typeof window.CustomEvent === "function") {
        panes[k].dispatchEvent(new window.CustomEvent("tabshow", { bubbles: true }));
      }
      if (focus) {
        tabs[k].focus();
      }
    }

    // a reader's choice of tab: the URL names the pane shown. A page's tab chosen by a click is a new history entry
    // (Back shows the tab before); by the keys, and a card's tab, it replaces the entry (for a reload)
    function choose(k, how) {
      var before = current;
      select(k, how === "key");
      if (!window.history || !history.replaceState) {
        return;
      }
      var hash = "#" + panes[current].id;
      if (page && how === "click") {
        if (current !== before && location.hash !== hash) { history.pushState(mark(null), "", hash); }
      } else {
        history.replaceState(mark(history.state), "", hash);
      }
    }

    tabs.forEach(function (tab, k) {
      tab.addEventListener("click", function (e) {
        e.preventDefault();
        choose(k, "click");
      });
      tab.addEventListener("keydown", function (e) {
        var to = { ArrowRight: k + 1, ArrowLeft: k - 1, Home: 0, End: tabs.length - 1 }[e.key];
        if (to === undefined) {
          return;
        }
        e.preventDefault();
        var step = to < k || e.key === "End" ? -1 : 1, n = (to + tabs.length) % tabs.length;
        for (var i = 0; i < tabs.length && !shown(n); i++) { n = (n + step + tabs.length) % tabs.length; }
        choose(n, "key");
      });
    });
    select(0, false);
    if (window.MutationObserver) {
      new MutationObserver(function () {
        if (!shown(current)) { select(0, false); }
      }).observe(document.documentElement, { attributes: true, attributeFilter: ["data-pdk"] });
    }

    return {
      page: page,
      // show the pane holding `el` (its card is open already: bring): null when `el` is in no pane of this set, else
      // whether that pane is the one shown (a pane its course hides is not: the first tab is shown instead)
      reveal: function (el) {
        var k = panes.findIndex(function (p) { return p === el || p.contains(el); });
        if (k < 0) {
          return null;
        }
        select(k, false);
        return current === k;
      },
      first: function () { select(0, false); }
    };
  }

  function fragment(hash) {
    try {
      return decodeURIComponent(hash.slice(1));
    } catch (e) {
      return hash.slice(1);
    }
  }

  // the element a fragment names: show the panes that hide it, the outer tabs' first (a page's tab, then the netlist
  // card's tab inside it: `sets` is in document order), open the disclosures around it, and with `scroll` scroll to
  // it, which the browser cannot do while it is hidden. True when it is in a pane (this script then scrolls), false
  // when the browser's own scroll is to follow.
  function bring(id, sets, scroll) {
    var el = id && document.getElementById(id);
    if (!el) {
      return false;
    }
    for (var d = el.closest("details"); d; d = d.parentElement && d.parentElement.closest("details")) {
      d.open = true;                     // "The proof in detail", a property's card, ...
    }
    var inside = false, visible = true;
    sets.forEach(function (s) {
      var r = s.reveal(el);
      if (r !== null) {
        inside = true;
        visible = visible && r;
      }
    });
    if (inside && visible && scroll) {
      el.scrollIntoView();
    }
    return inside;
  }

  // the tabs the URL names: its fragment's panes, or with no fragment a page's first tab (Back to the page as it was
  // first shown); a fragment outside every tab (#main) leaves the tabs as they are
  function sync(sets, scroll) {
    var id = fragment(location.hash);
    if (!id) {
      sets.forEach(function (s) { if (s.page) { s.first(); } });
      return;
    }
    bring(id, sets, scroll);
  }

  function init() {
    Array.prototype.forEach.call(document.querySelectorAll("pre.code"), addCopy);
    var sets = Array.prototype.map.call(document.querySelectorAll(".props[data-tabs], .tabs[data-tabs]"), initTabs)
      .filter(Boolean);
    if (!sets.length) {
      return;
    }
    if (window.history && history.replaceState) {
      try { history.replaceState(mark(history.state), ""); } catch (e) { /* file:// in some browsers */ }
    }
    // Back and Forward (and a fragment reached another way: a typed address, a link this script left to the browser):
    // the tabs follow the URL. To an entry of this script's the browser restores the scroll position; any other
    // fragment is scrolled to. `hashchange` follows `popstate` for the same change: done once.
    var popped = null;
    window.addEventListener("popstate", function (e) {
      popped = location.href;
      sync(sets, !(e.state && e.state[KEY]));
    });
    window.addEventListener("hashchange", function () {
      if (popped === location.href) {
        popped = null;
        return;
      }
      popped = null;
      sync(sets, true);
    });
    // a link to this page's own fragment: the browser does nothing when the URL already names it (a second
    // click on "what does not count" after a tab was chosen), and does not scroll to a hidden pane
    document.addEventListener("click", function (e) {
      if (e.defaultPrevented || e.button !== 0 || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey) {
        return;
      }
      var a = e.target.closest && e.target.closest("a[href^='#']");
      if (!a || a.getAttribute("href").length < 2) {
        return;
      }
      var hash = a.getAttribute("href");
      if (bring(fragment(hash), sets, true)) {
        e.preventDefault();
        if (location.hash !== hash && window.history && history.pushState) {
          history.pushState(mark(null), "", hash);
        }
      }
    });
    bring(fragment(location.hash), sets, true);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
