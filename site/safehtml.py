"""The strict allowlist sanitizer of the record writeups (decided 2026-11-16: the owner asked for HTML writeups, so that
they can hold inline SVG figures). Standard library only, as the rest of the site.

A writeup comes in a pull request from anyone and is published on the site's own origin, so its HTML is never passed
through: `parse` reads it with the standard library's HTML tokenizer (html.parser) into a tree, checks every element,
attribute, value and nesting against the allowlists below, and REFUSES anything else with an HtmlError that names the
line and the element or attribute (it never strips silently, so the author sees what was refused). The site then
writes its page from the tree (`serialize`, and site/writeup.py's renderer), never from the author's text: every text
is escaped, every attribute is quoted and escaped, only allowlisted names are written. The nesting rules keep the
tree exactly what a browser's HTML parser builds from that output: no element a browser would close or move on its
own (a <div> inside a <p>, text loose in a <table>, a misnested end tag), no HTML inside <svg> (the foreign-content
"breakout" of mutation XSS), no raw-text element (<script>, <style>, <textarea>, <title> outside <svg>), no comment,
CDATA section, declaration or processing instruction. `sanitize(text)` is the tree written back without the site's
additions; it is idempotent: sanitize(sanitize(x)) == sanitize(x).

THE ALLOWLISTS (README.md, "Writeups", says them for authors):

* text structure: h2 h3 h4 p ul ol li pre code em strong a sub sup br hr blockquote span div table thead tbody tr th
  td figure figcaption, and no attribute but: a href; ol start; th/td class (al-left, al-center, al-right), colspan,
  rowspan; span/div class (muted); code class (language-X, inside <pre> only); figure data-figure, data-alt (a figure
  the site generates, site/figs);
* drawings, inside a <figure> only: svg g path rect circle ellipse line polyline polygon text tspan title desc defs
  marker clipPath linearGradient stop, with their geometry attributes, the presentation attributes PRESENTATION (fill
  and stroke only `none`, `currentColor` or `url(#id)`: colours come from the classes SVG_CLASSES, which style.css
  draws from the site's light and dark tokens), `id` only on marker, clipPath and linearGradient (what `url(#id)`
  names, in the same drawing), and every value checked against its grammar (numbers, a path's commands, a transform's
  functions);
* never: script, style, iframe, object, embed, img, image, link, meta, base, form elements, foreignObject, use, a in
  SVG, animate, set, any attribute starting with `on`, `style`, `id` elsewhere, `name`, `xlink:href`, `href` on SVG,
  `javascript:`/`data:`/`vbscript:` or any other scheme (a link is http(s), mailto, `#id` of the same writeup or a
  relative path), and a `class` outside the lists.

The links' `#id` targets and the generated figures' names are checked by site/writeup.py, which knows the ids it
makes and the figures it can draw.
"""

import html
import html.entities
import html.parser
import re

__all__ = ["HtmlError", "Element", "Text", "parse", "serialize", "sanitize", "text_of", "SVG_NS",
           "SVG_CLASSES", "PROSE_CLASSES", "ALIGN_CLASSES", "CODE_LANGUAGES", "LIMITS"]

SVG_NS = "http://www.w3.org/2000/svg"

LIMITS = {
    "bytes": 200_000,          # a writeup's body (leaderboard.py WRITEUP_SIZE_MAX caps the whole file the same)
    "depth": 32,               # elements nested at most this deep (a tree, not a recursion bomb)
    "svg_bytes": 50_000,       # one drawing, written out (README: "at most 50 kB")
    "svg_width": 1200,         # its viewBox width: drawn at most at this many CSS pixels
    "svg_height": 2000,
    "caption": 300,            # characters of a figure's caption (its text)
    "alt": 300,                # characters of a figure's text alternative (data-alt, a drawing's <title>)
    "desc": 2000,              # characters of a drawing's <desc>
    "id": 40,                  # characters of an id
}

# --- the elements ------------------------------------------------------------------------------------------------

PHRASING = frozenset({"a", "em", "strong", "code", "sub", "sup", "br", "span"})
FLOW = frozenset({"h2", "h3", "h4", "p", "ul", "ol", "pre", "blockquote", "figure", "table", "div", "hr"})
HEADINGS = frozenset({"h2", "h3", "h4"})
VOID = frozenset({"br", "hr"})
SVG_SHAPES = frozenset({"path", "rect", "circle", "ellipse", "line", "polyline", "polygon"})
SVG_GRAPHICS = SVG_SHAPES | {"g", "text"}
SVG_ELEMENTS = SVG_GRAPHICS | {"svg", "tspan", "title", "desc", "defs", "marker", "clippath", "lineargradient", "stop"}
HTML_ELEMENTS = PHRASING | FLOW | {"li", "figcaption", "thead", "tbody", "tr", "th", "td"}
# html.parser lower-cases names; SVG's are case-sensitive (a browser adjusts them the same way when it parses)
SVG_CASE = {"clippath": "clipPath", "lineargradient": "linearGradient", "viewbox": "viewBox", "refx": "refX",
            "refy": "refY", "markerwidth": "markerWidth", "markerheight": "markerHeight", "markerunits": "markerUnits",
            "clippathunits": "clipPathUnits", "gradientunits": "gradientUnits",
            # (refused, named in their case in the messages)
            "foreignobject": "foreignObject", "animatemotion": "animateMotion", "animatetransform": "animateTransform",
            "feimage": "feImage", "textpath": "textPath"}

# parent -> the elements it may hold; TEXT: the parents that may hold text that is not only white space
CHILDREN = {
    "#root": FLOW,
    "p": PHRASING, "em": PHRASING, "strong": PHRASING, "sub": PHRASING, "sup": PHRASING, "span": PHRASING,
    "h2": PHRASING - {"a", "br"}, "h3": PHRASING - {"a", "br"}, "h4": PHRASING - {"a", "br"},
    "a": PHRASING - {"a"}, "code": frozenset(), "br": frozenset(), "hr": frozenset(),
    "ul": frozenset({"li"}), "ol": frozenset({"li"}),
    "li": (FLOW - HEADINGS - {"figure"}) | PHRASING,
    "blockquote": FLOW - HEADINGS - {"figure"},
    "div": FLOW | PHRASING,
    "pre": frozenset({"code"}),
    "figure": frozenset({"svg", "figcaption"}), "figcaption": PHRASING,
    "table": frozenset({"thead", "tbody"}), "thead": frozenset({"tr"}), "tbody": frozenset({"tr"}),
    "tr": frozenset({"th", "td"}), "th": PHRASING, "td": PHRASING,
    "svg": SVG_GRAPHICS | {"title", "desc", "defs"},
    "g": SVG_GRAPHICS,
    "defs": frozenset({"marker", "clippath", "lineargradient"}),
    "marker": SVG_SHAPES | {"g"},
    "clippath": SVG_SHAPES,
    "lineargradient": frozenset({"stop"}),
    "text": frozenset({"tspan"}), "tspan": frozenset({"tspan"}),
    "title": frozenset(), "desc": frozenset(), "stop": frozenset(),
    **{s: frozenset() for s in SVG_SHAPES},
}
TEXT = frozenset({"p", "em", "strong", "sub", "sup", "span", "h2", "h3", "h4", "a", "code", "li", "div", "figcaption",
                  "th", "td", "text", "tspan", "title", "desc"})

# why an element is refused, for the ones an author is most likely to try
REFUSED_WHY = {
    "script": "scripts never run in a writeup", "style": "use the classes the site defines (README.md, Writeups)",
    "img": "a picture from a file or another site is not allowed: draw an inline <svg> figure",
    "image": "a picture from a file or another site is not allowed: draw it in SVG",
    "picture": "draw an inline <svg> figure", "video": "draw an inline <svg> figure",
    "audio": "not allowed", "iframe": "no embedded pages", "frame": "no embedded pages",
    "object": "no embedded objects", "embed": "no embedded objects",
    "link": "no external resources", "meta": "the page's head is the site's", "base": "the page's head is the site's",
    "form": "no forms", "input": "no forms", "button": "no forms", "textarea": "no forms", "select": "no forms",
    "foreignobject": "no HTML inside a drawing", "use": "write the shape out (no references to other drawings)",
    "animate": "no animation", "set": "no animation", "animatemotion": "no animation",
    "animatetransform": "no animation", "a": "links go in the text, not in a drawing",
    "math": "write formulas as text or <code>", "h1": "line 1's <h1> is the title; sections start at <h2>",
    "b": "use <strong>", "i": "use <em>", "u": "use <em>", "font": "use the classes",
    "html": "a writeup is a fragment, no <html>", "head": "a writeup is a fragment, no <head>",
    "body": "a writeup is a fragment, no <body>", "title": "line 1's <h1> is the title",
    "noscript": "not allowed", "template": "not allowed", "slot": "not allowed",
}

# --- the attributes ----------------------------------------------------------------------------------------------

SVG_CLASSES = ("t-lab", "t-head", "t-note", "t-mono", "t-hot", "t-on", "w", "w-faint", "e", "e-hot", "e-blue",
               "e-dash", "n", "n-hot", "n-open", "b", "b-hot", "b-blue", "b-soft", "b-on", "arrow", "arrow-hot")
PROSE_CLASSES = ("muted",)
ALIGN_CLASSES = ("al-left", "al-center", "al-right")
CODE_LANGUAGES = ("lean", "lean4", "systemverilog", "sv", "verilog", "v", "bash", "sh", "shell", "console", "text")

PRESENTATION = frozenset({"class", "fill", "stroke", "stroke-width", "stroke-dasharray", "stroke-linecap",
                          "stroke-linejoin", "stroke-opacity", "fill-opacity", "opacity", "fill-rule", "clip-path",
                          "transform", "text-anchor", "dominant-baseline", "font-weight", "font-style",
                          "vector-effect"})
MARKERS = frozenset({"marker-start", "marker-mid", "marker-end"})
TEXT_POSITION = frozenset({"x", "y", "dx", "dy"})
ATTRS = {
    "a": {"href"}, "ol": {"start"},
    "th": {"class", "colspan", "rowspan"}, "td": {"class", "colspan", "rowspan"},
    "span": {"class"}, "div": {"class"}, "code": {"class"},
    "figure": {"data-figure", "data-alt"},
    "svg": {"viewbox", "xmlns"},
    "g": PRESENTATION,
    "path": PRESENTATION | MARKERS | {"d"},
    "line": PRESENTATION | MARKERS | {"x1", "y1", "x2", "y2"},
    "polyline": PRESENTATION | MARKERS | {"points"},
    "polygon": PRESENTATION | MARKERS | {"points"},
    "rect": PRESENTATION | {"x", "y", "width", "height", "rx", "ry"},
    "circle": PRESENTATION | {"cx", "cy", "r"},
    "ellipse": PRESENTATION | {"cx", "cy", "rx", "ry"},
    "text": PRESENTATION | TEXT_POSITION,
    "tspan": PRESENTATION | TEXT_POSITION | {"baseline-shift"},
    "marker": {"id", "viewbox", "refx", "refy", "markerwidth", "markerheight", "markerunits", "orient"},
    "clippath": {"id", "clippathunits"},
    "lineargradient": {"id", "x1", "y1", "x2", "y2", "gradientunits"},
    "stop": {"offset", "stop-color", "stop-opacity"},
}
REQUIRED = {"a": ("href",), "svg": ("viewbox",), "marker": ("id",), "clippath": ("id",), "lineargradient": ("id",)}

_NUM = r"[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?"
_NUMS = re.compile(rf"\s*{_NUM}(?:(?:\s*,\s*|\s+){_NUM})*\s*")
_NUMBER = re.compile(_NUM)
_PERCENT = re.compile(rf"{_NUM}%?")
_PATH = re.compile(r"\s*[Mm][MmZzLlHhVvCcSsQqTtAa0-9eE.,+\-\s]*")
_TRANSFORM = re.compile(rf"\s*(?:(?:matrix|translate|scale|rotate|skewX|skewY)\s*\(\s*{_NUM}(?:(?:\s*,\s*|\s+){_NUM})*"
                        rf"\s*\)\s*,?\s*)+")
_ID = re.compile(r"[a-z][a-z0-9-]*")
_URL_REF = re.compile(r"url\(#([a-z][a-z0-9-]*)\)")
_FIGURE_NAME = re.compile(r"[a-z0-9][a-z0-9-]*")
# links (decoded values): an absolute http(s) address with a plain host (site/writeup.py safe_target's rule), a mailto
# address, a fragment, or a relative path of plain segments (no scheme, no `//`, no `\`, no `%`: nothing to decode)
HTTP_URL = re.compile(r"https?://[A-Za-z0-9.-]+(?::[0-9]{1,5})?(?:[/?#][^\s\"'<>\\`\x00-\x1f\x7f]*)?")
MAILTO = re.compile(r"mailto:[A-Za-z0-9._+-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+")
FRAGMENT = re.compile(r"#([\w-]+)")
RELATIVE = re.compile(r"(?:\.\./)*(?:[A-Za-z0-9_][A-Za-z0-9._~-]*/)*(?:[A-Za-z0-9_][A-Za-z0-9._~-]*)?"
                      r"(?:#[A-Za-z0-9._~-]+)?")
# a character no text or value may hold, even written as a character reference: a control character but the newline
# (tabs and carriage returns included, as in the raw file), DEL, a byte-order mark, a bidirectional override or isolate
_BAD_CHAR = re.compile("[\x00-\x09\x0b-\x1f\x7f‪-‮⁦-⁩﻿]")
_SPACE = " \n"
# a numeric character reference (with or without its `;`), and a named one in an attribute value
_NUM_REF = re.compile(r"&#(?:[xX]([0-9a-fA-F]+)|([0-9]+))")
_ATTR_AMP = re.compile(r"&(?:#[xX][0-9a-fA-F]+;|#[0-9]+;|([A-Za-z][A-Za-z0-9]*;))?")
# where an element goes, for the refusal of one that is elsewhere
PLACES = {"li": "a <ul> or <ol>", "tr": "a <thead> or <tbody>", "th": "a <tr>", "td": "a <tr>",
          "thead": "a <table>", "tbody": "a <table>", "figcaption": "a <figure>, after its drawing",
          "code": "a <p> (or alone in a <pre>)"}


def _bad_code_point(cp):
    """A code point a numeric character reference may not name: one a browser and Python's decoder treat differently
    (NUL, a C1 control, a surrogate, past U+10FFFF, a noncharacter: one replaces, the other drops) or one no text may
    hold (_BAD_CHAR)."""
    return (cp > 0x10FFFF or 0xD800 <= cp <= 0xDFFF or 0x7F <= cp <= 0x9F or 0xFDD0 <= cp <= 0xFDEF
            or cp & 0xFFFE == 0xFFFE or bool(_BAD_CHAR.match(chr(cp))))

ENUMS = {
    "stroke-linecap": {"butt", "round", "square"}, "stroke-linejoin": {"miter", "round", "bevel"},
    "fill-rule": {"nonzero", "evenodd"}, "text-anchor": {"start", "middle", "end"},
    "dominant-baseline": {"auto", "middle", "central", "hanging", "alphabetic", "mathematical"},
    "font-weight": {"normal", "bold"}, "font-style": {"normal", "italic"},
    "vector-effect": {"none", "non-scaling-stroke"}, "baseline-shift": {"sub", "super", "baseline"},
    "markerunits": {"strokeWidth", "userSpaceOnUse"}, "clippathunits": {"userSpaceOnUse", "objectBoundingBox"},
    "gradientunits": {"userSpaceOnUse", "objectBoundingBox"},
}
NUMBER_ATTRS = {"x1", "y1", "x2", "y2", "width", "height", "rx", "ry", "cx", "cy", "r", "refx", "refy",
                "markerwidth", "markerheight", "stroke-width", "stroke-opacity", "fill-opacity", "opacity",
                "stop-opacity"}
LIST_ATTRS = {"points", "x", "y", "dx", "dy"}


class HtmlError(ValueError):
    """A writeup's HTML outside the allowlists, with the file and line."""

    def __init__(self, source, line, message):
        super().__init__(f"{source}:{line}: {message}")
        self.source, self.line, self.message = source, line, message


class Text:
    __slots__ = ("data", "line")

    def __init__(self, data, line):
        self.data, self.line = data, line


class Element:
    """An element of the tree: `tag` (lower case, as parsed), `attrs` ({name: decoded value}, the author's order),
    `children` (Element and Text), `line` (its start tag's line in the file), `svg` (inside a drawing)."""
    __slots__ = ("tag", "attrs", "children", "line", "svg")

    def __init__(self, tag, attrs, line, svg=False):
        self.tag, self.attrs, self.children, self.line, self.svg = tag, attrs, [], line, svg

    def elements(self):
        return [c for c in self.children if isinstance(c, Element)]


def text_of(node):
    """The text of an element and its descendants (decoded), as a browser shows it before white space collapses."""
    if isinstance(node, Text):
        return node.data
    return "".join(text_of(c) for c in node.children)


def _shown(value, n=60):
    """A value as an error message quotes it: repr, cut at `n` characters."""
    r = repr(value)
    return r if len(r) <= n else r[:n - 4] + "...'"


def _name(tag):
    return SVG_CASE.get(tag, tag)


class _Parser(html.parser.HTMLParser):
    # never enter a raw-text mode: <script>, <style>, <textarea> and <title> outside SVG are refused at their start
    # tag anyway, and without these lists every Python version tokenizes a writeup the same way
    CDATA_CONTENT_ELEMENTS = ()
    RCDATA_CONTENT_ELEMENTS = ()

    def __init__(self, source, first_line):
        super().__init__(convert_charrefs=True)
        self.source, self.first = source, first_line
        self.root = Element("#root", {}, first_line)
        self.stack = [self.root]

    # -- positions and refusals -----------------------------------------------------------------------------------

    def line(self):
        return self.getpos()[0] + self.first - 1

    def fail(self, message, line=None):
        raise HtmlError(self.source, self.line() if line is None else line, message)

    def attr_line(self, name):
        """The line of attribute `name` in the start tag being handled (a tag may span lines)."""
        raw = self.get_starttag_text() or ""
        m = re.search(r"[\s/\"']" + re.escape(name) + r"(?=[\s=/>])", raw, re.I)
        return self.line() + (raw.count("\n", 0, m.start() + 1) if m else 0)

    # -- the tokenizer's events -----------------------------------------------------------------------------------

    def handle_starttag(self, tag, attrs):
        self.start(tag, attrs, closed=False)

    def handle_startendtag(self, tag, attrs):
        self.start(tag, attrs, closed=True)

    def handle_endtag(self, tag):
        top = self.stack[-1]
        if tag in VOID:
            self.fail(f"</{tag}> is not a tag: <{tag}> has no end tag")
        if top.tag != tag:
            open_ = [e.tag for e in self.stack[1:]]
            if tag in open_:
                self.fail(f"</{_name(tag)}> closes <{_name(top.tag)}> (opened on line {top.line}): close it first")
            self.fail(f"</{_name(tag)}> has no open <{_name(tag)}>")
        self.stack.pop()
        self.finish(top)

    def handle_data(self, data):
        parent = self.stack[-1]
        bad = _BAD_CHAR.search(data)
        if bad:
            self.fail(f"the character U+{ord(bad.group(0)):04X} (a control character, a byte-order mark or a "
                      "bidirectional override, also when written as a character reference)",
                      self.line() + data.count("\n", 0, bad.start()))
        if data.strip(_SPACE):
            if parent.tag not in TEXT:
                where = ("outside a block: put it in a <p>" if parent.tag == "#root" else
                         f"directly inside <{_name(parent.tag)}>")
                lead = len(data) - len(data.lstrip(_SPACE))
                self.fail(f"text {_shown(data.strip(_SPACE), 40)} {where}",
                          self.line() + data.count("\n", 0, lead))
        elif parent.tag == "pre":
            self.fail("a <pre> holds one <code> and nothing else (white space included)")
        if parent.children and isinstance(parent.children[-1], Text):
            parent.children[-1].data += data
        else:
            parent.children.append(Text(data, self.line()))

    def handle_comment(self, data):
        self.fail("a comment is not allowed in a writeup (say it in the pull request)")

    def handle_decl(self, decl):
        self.fail(f"<!{decl[:20]}...> is not allowed (a writeup is a fragment: no doctype)")

    def unknown_decl(self, data):
        self.fail("a CDATA section or <!...> declaration is not allowed")

    def handle_pi(self, data):
        self.fail("a processing instruction <?...> is not allowed")

    def parse_endtag(self, i):
        if self.rawdata.startswith("</>", i):
            self.fail("`</>` is not a tag (write &lt;/&gt; for the text)")
        return super().parse_endtag(i)

    # -- the checks -----------------------------------------------------------------------------------------------

    def start(self, tag, attrs, closed):
        parent = self.stack[-1]
        in_svg = parent.svg or parent.tag == "svg"
        known = SVG_ELEMENTS if in_svg else HTML_ELEMENTS | {"svg"}
        if tag not in known:
            if tag in SVG_ELEMENTS - {"svg"} and not in_svg:
                self.fail(f"<{_name(tag)}> is a drawing's element: it goes inside an <svg>")
            if tag in HTML_ELEMENTS and in_svg:
                self.fail(f"<{tag}> inside a drawing: no HTML inside <svg> (the caption goes in <figcaption>)")
            why = REFUSED_WHY.get(tag, "it is not on the list of allowed elements (README.md, Writeups)")
            self.fail(f"the element <{_name(tag)}> is not allowed: {why}")
        if tag == "svg" and in_svg:
            self.fail("an <svg> inside an <svg> is not allowed")
        if tag not in CHILDREN.get(parent.tag, ()):
            if tag == "svg":
                self.fail("an <svg> drawing goes in a <figure>, before its <figcaption>")
            if tag in PLACES and not (tag == "code" and parent.tag != "#root"):
                where = "the top" if parent.tag == "#root" else f"<{_name(parent.tag)}>"
                self.fail(f"<{tag}> is not allowed directly inside {where}: it goes in {PLACES[tag]}")
            if parent.tag == "#root":
                self.fail(f"<{_name(tag)}> outside a block: put it in a <p>")
            self.fail(f"<{_name(tag)}> is not allowed directly inside <{_name(parent.tag)}>")
        if tag == "a" and any(e.tag == "a" for e in self.stack):
            self.fail("a link inside a link is not allowed")
        if len(self.stack) > LIMITS["depth"]:
            self.fail(f"elements nested more than {LIMITS['depth']} deep")
        if closed and not (in_svg or tag == "svg" or tag in VOID):
            self.fail(f"<{tag}/> does not close an HTML element: write <{tag}></{tag}>")
        el = Element(tag, self.attributes(tag, attrs, parent), self.line(), svg=in_svg)
        parent.children.append(el)
        if closed or tag in VOID:
            self.finish(el)
        else:
            self.stack.append(el)

    def attributes(self, tag, attrs, parent):
        out = {}
        allowed = ATTRS.get(tag, set())
        # an `&` in a value is a whole character reference with its `;`: a browser leaves `&copy=1` in an attribute
        # as it is, where Python's decoder makes it `©=1`, so the two would read different values
        raw = self.get_starttag_text() or ""
        for m in _ATTR_AMP.finditer(raw):
            if m.group(0) == "&" or (m.group(1) and m.group(1) not in html.entities.html5):
                self.fail(f"<{_name(tag)}>: an & in an attribute's value starts a character reference ending in ; "
                          "(write & as &amp;)", self.line() + raw.count("\n", 0, m.start()))
        for name, value in attrs:
            line = self.attr_line(name)
            if name in out:
                self.fail(f"<{_name(tag)}> has the attribute {name} twice", line)
            if name.startswith("on"):
                self.fail(f"<{_name(tag)}>: the attribute {name} is not allowed (event handlers never are)", line)
            if name not in allowed:
                hint = {"style": "use the classes (README.md, Writeups)",
                        "id": "only marker, clipPath and linearGradient have ids (what url(#id) names); headings "
                              "and figures get theirs from the site",
                        "xlink:href": "no references (xlink:href) in a drawing",
                        "href": "only <a> in the text links", "src": "nothing is loaded from elsewhere",
                        "class": "no class on this element"}.get(name, "it is not on this element's list")
                self.fail(f"<{_name(tag)}>: the attribute {_name(name)} is not allowed: {hint}", line)
            if value is None:
                self.fail(f"<{_name(tag)}>: the attribute {_name(name)} needs a value", line)
            bad = _BAD_CHAR.search(value)
            if bad:
                self.fail(f"<{_name(tag)}>: the attribute {_name(name)} holds the character U+{ord(bad.group(0)):04X} "
                          "(a control character, a byte-order mark or a bidirectional override)", line)
            why = self.value_problem(tag, name, value, parent)
            if why:
                self.fail(f"<{_name(tag)}>: {_name(name)}={_shown(value)}: {why}", line)
            out[name] = value
        for name in REQUIRED.get(tag, ()):
            if name not in out:
                self.fail(f"<{_name(tag)}> needs the attribute {_name(name)}")
        if tag == "code" and "class" in out and parent.tag != "pre":
            self.fail("<code>: a language (class) only on the <code> of a <pre>")
        if tag == "figure" and ("data-figure" in out) != ("data-alt" in out):
            self.fail("<figure>: a generated figure has both data-figure (its name) and data-alt (its text "
                      "alternative)")
        return out

    def value_problem(self, tag, name, value, parent):
        """Why `value` is no value of attribute `name` on `tag`, or None."""
        v = value
        if name == "href":
            if HTTP_URL.fullmatch(v) or MAILTO.fullmatch(v) or FRAGMENT.fullmatch(v):
                return None
            if v and not v.startswith("#") and RELATIVE.fullmatch(v):
                return None
            return ("a link is an http(s) address, a mailto: address, #id of this writeup or a relative path to a "
                    "page of the site (no other scheme: no javascript:, data:, vbscript:)")
        if name == "class":
            lists = {"th": ALIGN_CLASSES, "td": ALIGN_CLASSES, "span": PROSE_CLASSES, "div": PROSE_CLASSES}
            if tag == "code":
                langs = ", ".join(CODE_LANGUAGES)
                m = re.fullmatch(r"language-([a-z0-9]+)", v)
                ok = m and m.group(1) in CODE_LANGUAGES
                return None if ok else f"a code block's class is language-X, X one of {langs}"
            allowed = SVG_CLASSES if tag in SVG_ELEMENTS else lists.get(tag, ())
            words = v.split()
            wrong = [w for w in words if w not in allowed]
            if not words or wrong:
                return f"a class here is one of {', '.join(allowed)}"
            return None
        if name in ("colspan", "rowspan"):
            return None if re.fullmatch(r"[1-9][0-9]?", v) else "a whole number from 1 to 99"
        if name == "start":
            return None if re.fullmatch(r"[0-9]{1,6}", v) else "a whole number"
        if name == "data-figure":
            return None if _FIGURE_NAME.fullmatch(v) else "the name of a figure the site draws (site/figs)"
        if name == "data-alt":
            if not v.strip():
                return "the text alternative is empty"
            return None if len(v) <= LIMITS["alt"] else f"{len(v)} characters, over {LIMITS['alt']}"
        if name == "xmlns":
            return None if v == SVG_NS else f"the SVG namespace is {SVG_NS}"
        if name == "id":
            if not _ID.fullmatch(v):
                return "an id is lower-case letters, digits and hyphens, starting with a letter"
            return None if len(v) <= LIMITS["id"] else f"an id has at most {LIMITS['id']} characters"
        if name == "viewbox":
            nums = v.replace(",", " ").split()
            if len(nums) != 4 or not all(_NUMBER.fullmatch(x) for x in nums):
                return "a viewBox is four numbers: min-x min-y width height"
            w, h = float(nums[2]), float(nums[3])
            if w <= 0 or h <= 0:
                return "a viewBox's width and height are positive"
            if tag == "svg" and (w > LIMITS["svg_width"] or h > LIMITS["svg_height"]):
                return (f"a drawing is at most {LIMITS['svg_width']} wide and {LIMITS['svg_height']} high (viewBox "
                        "units are CSS pixels at full size)")
            return None
        if name in ("fill", "stroke"):
            if v in ("none", "currentColor") or _URL_REF.fullmatch(v):
                return None
            return ("a colour comes from a class (README.md, Writeups) or is none, currentColor or url(#id), so the "
                    "drawing works in the light and the dark theme")
        if name == "stop-color":
            return None if v == "currentColor" else "a gradient's stop-color is currentColor (vary stop-opacity)"
        if name in ("clip-path", "marker-start", "marker-mid", "marker-end"):
            return None if _URL_REF.fullmatch(v) else "url(#id) of this drawing"
        if name in ENUMS:
            return None if v in ENUMS[name] else "one of " + ", ".join(sorted(ENUMS[name]))
        if name == "orient":
            ok = v in ("auto", "auto-start-reverse") or _NUMBER.fullmatch(v)
            return None if ok else "auto, auto-start-reverse or an angle"
        if name == "d":
            return None if _PATH.fullmatch(v) else "a path's commands (M, L, H, V, C, S, Q, T, A, Z) and numbers"
        if name == "transform":
            return None if _TRANSFORM.fullmatch(v) else "translate, scale, rotate, skewX, skewY or matrix of numbers"
        if name == "stroke-dasharray":
            return None if v == "none" or _NUMS.fullmatch(v) else "none or numbers"
        if name in ("offset",) or (tag == "lineargradient" and name in ("x1", "y1", "x2", "y2")):
            return None if _PERCENT.fullmatch(v) else "a number or a percentage"
        if name in NUMBER_ATTRS or (tag == "rect" and name in ("x", "y")):
            return None if _NUMBER.fullmatch(v) else "a number"
        if name in LIST_ATTRS:
            return None if _NUMS.fullmatch(v) else "numbers"
        return "no value is allowed"          # (every allowed attribute has a rule above)

    def finish(self, el):
        """Checks of a closed element as a whole."""
        tag = el.tag
        kids = el.elements()
        if tag == "pre":
            if len(kids) != 1:
                self.fail("a <pre> holds one <code> and nothing else", el.line)
        elif tag == "figure":
            names = [k.tag for k in kids]
            if "data-figure" in el.attrs:
                if names != ["figcaption"]:
                    self.fail("a generated figure (data-figure) holds one <figcaption> and nothing else", el.line)
            elif names != ["svg", "figcaption"]:
                self.fail("a <figure> holds an <svg> drawing and then its <figcaption>, or names a figure the site "
                          "draws (data-figure) and holds its <figcaption>", el.line)
        elif tag == "figcaption":
            n = len(" ".join(text_of(el).split()))
            if not n:
                self.fail("a figure's caption is empty", el.line)
            if n > LIMITS["caption"]:
                self.fail(f"a figure's caption has {n} characters, over {LIMITS['caption']}", el.line)
        elif tag == "svg":
            self.check_svg(el)

    def check_svg(self, svg):
        kids = svg.elements()
        if not kids or kids[0].tag != "title":
            self.fail("a drawing's first element is its <title>, the text alternative a screen reader reads",
                      svg.line)
        for k in kids[1:]:
            if k.tag == "title" or (k.tag == "desc" and k is not kids[1]):
                self.fail(f"<{k.tag}> comes once, at the start of the drawing (<title>, then <desc>)", k.line)
        for k in kids[:2]:
            if k.tag in ("title", "desc"):
                n = len(" ".join(text_of(k).split()))
                cap = LIMITS["alt"] if k.tag == "title" else LIMITS["desc"]
                if not n:
                    self.fail(f"the drawing's <{k.tag}> is empty", k.line)
                if n > cap:
                    self.fail(f"the drawing's <{k.tag}> has {n} characters, over {cap}", k.line)
        ids, refs = {}, []
        stack = [svg]
        while stack:
            e = stack.pop()
            for c in e.elements():
                stack.append(c)
                if "id" in c.attrs:
                    if c.attrs["id"] in ids:
                        self.fail(f"the id {c.attrs['id']!r} is used twice in this drawing", c.line)
                    ids[c.attrs["id"]] = c.tag
                for a in ("fill", "stroke", "clip-path", "marker-start", "marker-mid", "marker-end"):
                    m = _URL_REF.fullmatch(c.attrs.get(a, ""))
                    if m:
                        refs.append((c, a, m.group(1)))
        want = {"fill": "lineargradient", "stroke": "lineargradient", "clip-path": "clippath"}
        for c, a, ref in refs:
            kind = want.get(a, "marker")
            if ids.get(ref) != kind:
                self.fail(f"<{_name(c.tag)}>: {a}=url(#{ref}) names no <{_name(kind)}> of this drawing", c.line)
        size = len(serialize(svg).encode("utf-8"))
        if size > LIMITS["svg_bytes"]:
            self.fail(f"the drawing is {size} bytes, over {LIMITS['svg_bytes']}", svg.line)


def parse(text, *, source="<writeup>", first_line=1):
    """The tree of a writeup's body (an Element "#root"), or HtmlError naming the line and what was refused."""
    size = len(text.encode("utf-8"))
    if size > LIMITS["bytes"]:
        raise HtmlError(source, first_line, f"{size} bytes, over the cap of {LIMITS['bytes']}")
    for m in _NUM_REF.finditer(text):
        cp = int(m.group(1), 16) if m.group(1) else int(m.group(2))
        if _bad_code_point(cp):
            raise HtmlError(source, first_line + text.count("\n", 0, m.start()),
                            f"the character reference {m.group(0)}{';' if text[m.end():m.end() + 1] == ';' else ''} "
                            f"names U+{min(cp, 0x110000):04X} (a control character, a byte-order mark, a "
                            "bidirectional override, a surrogate or a noncharacter)")
    p = _Parser(source, first_line)
    p.feed(text)
    p.close()
    if len(p.stack) > 1:
        top = p.stack[-1]
        p.fail(f"<{_name(top.tag)}> (opened on line {top.line}) is never closed", top.line)
    return p.root


def _esc(s):
    return html.escape(s, quote=False)


def _attr(s):
    return html.escape(s, quote=True)


def serialize(node):
    """A tree (or one node of it) written out: every text escaped, every value quoted and escaped, SVG names in their
    case, a void element without an end tag, an empty drawing element as <x/>."""
    if isinstance(node, Text):
        return _esc(node.data)
    inner = "".join(serialize(c) for c in node.children)
    if node.tag == "#root":
        return inner
    name = _name(node.tag)
    attrs = "".join(f' {_name(k)}="{_attr(v)}"' for k, v in node.attrs.items())
    if node.tag in VOID:
        return f"<{name}{attrs}>"
    if (node.svg or node.tag == "svg") and not node.children:
        return f"<{name}{attrs}/>"
    return f"<{name}{attrs}>{inner}</{name}>"


def sanitize(text, *, source="<writeup>", first_line=1):
    """The writeup's body checked and written back (the tree, without the site's additions): idempotent."""
    return serialize(parse(text, source=source, first_line=first_line))
