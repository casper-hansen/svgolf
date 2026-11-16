"""A record's writeup on its page (decided 2026-11-13, the owner's UI feedback items 3 and 6; HTML since 2026-11-16, the
owner's request "Can you make the write-ups html, so they can contain inline svg figures?").

A writeup is an optional HTML file `leaderboard/writeups/<record_hash>.html`, kept OUTSIDE the record (no field of
the record and none of its hashes name it), so adding or improving one never changes a record. Its first line
`<h1>title</h1>` holds the submission's short title (plain text, character references allowed, at most TITLE_MAX
characters), shown as the record page's heading, in the task page's submissions list and in every chart tooltip; the
rest is an HTML fragment, a blog-post-style account of the design and its proof, shown on the record page.
leaderboard.py `writeup_problems` checks a file's shape (its name, UTF-8, the title line, the size cap, the
characters); this module renders it.

The body is written by a player, so it is rendered SAFELY. site/safehtml.py parses it and refuses (HtmlError, with the
line and the element or attribute) anything outside its allowlists; this module then writes the page's HTML from the
checked tree, never from the author's text:

* headings: <h2>, <h3>, <h4> are shown one level down, under the card's title (an h2), each with the id
  `writeup-<its text as a slug>` and an anchor link, so no heading can take an id of the page's own;
* links: an http(s) address carries rel="nofollow ugc noopener"; `#id` must name a heading or a figure of this
  writeup (`#the-idea`, `#figure-1`) and points at its `writeup-` id; a relative path or a mailto address is kept;
* code: <pre><code class="language-X"> is highlighted by the site (`highlight`, the build's), plain without a class;
* a table sits in the site's scroll box (div.table-wrap).

FIGURES are numbered together, "Figure n.", each with the id `writeup-figure-n`:

* a figure the site draws from the design (decided 2026-11-16, site/figs), never a picture the writer supplies:

      <figure data-figure="add-kogge-stone" data-alt="The Kogge-Stone prefix graph at N = 8.">
      <figcaption>Every carry after four levels.</figcaption>
      </figure>

  `data-figure` must be a registered figure (figs.REGISTRY), and, when the caller says which design the writeup's
  record has (`design_sha256`; the site build always does), one drawn from that design; `data-alt` is its text
  alternative (the drawing's <title>). After the caption the site adds a line made from the figure's registration,
  never typed: the size it is drawn at, the record's scoring point, who made it, and (with `rules_href`) a link to
  how figures are made;
* a drawing by the writer: `<figure><svg viewBox="..."><title>...</title><desc>...</desc>...</svg>
  <figcaption>...</figcaption></figure>` (safehtml's SVG allowlist). The site gives the drawing the class of the
  figures' marks (style.css colours them from the theme's tokens), role="img" labelled by its <title> and <desc>, and
  its size: at most its viewBox width in CSS pixels, on a narrow screen never below MIN_SHARE of it (nor below
  MIN_PX), its box scrolling sideways instead; its ids become `writeup-figure-n-<id>`, and its url(#id) references
  with them. No generated line: the writer's caption says who drew it.

Last, `audit` reads the HTML this module wrote and refuses it unless every element, attribute, link and id is one
this module writes: a second check, independent of the first, of what reaches the page.

Standard library only, as md.py and safehtml.py.
"""

import html
import html.parser
import re

import figs
import md
import safehtml

TITLE_MAX = 60                        # the title's length cap, in characters (leaderboard.py WRITEUP_TITLE_MAX)
ID_PREFIX = "writeup-"
MIN_SHARE = 2 / 3                     # a writer's drawing on a narrow screen: never below this share of its width
MIN_PX = 320                          # ... nor below this many CSS pixels (a drawing narrower than it never shrinks)
CAPTION_MAX = safehtml.LIMITS["caption"]
ALT_MAX = safehtml.LIMITS["alt"]
_TITLE_LINE = re.compile(r"<h1>([^<>]*)</h1>")
_SAFE_URL = safehtml.HTTP_URL
# the containers whose white space between elements never shows: written as one newline
_BLOCKS = frozenset({"#root", "ul", "ol", "blockquote", "table", "thead", "tbody", "tr"})
_SVG_QUIET = frozenset({"svg", "g", "defs", "marker", "clippath", "lineargradient"})


class HtmlError(safehtml.HtmlError):
    pass


def safe_target(target):
    """`target` when it is an absolute http or https address with a plain host name and no quote, angle bracket,
    backslash, backtick, space or control character; else None."""
    return target if _SAFE_URL.fullmatch(target or "") else None


class _Slugger(md.Slugger):
    """md.py's heading anchors, each with the prefix `writeup-` (no heading takes an id of the page's own)."""

    def slug(self, text):
        return ID_PREFIX + super().slug(text)


def split(text):
    """(title, body, the body's first line number) of a writeup's text: the title is line 1's <h1> text, character
    references decoded (plain text: the caller escapes it); the body is everything after it. Raises ValueError when
    line 1 is not a title line (leaderboard.py checks this first, with its own words)."""
    first, _, body = text.partition("\n")
    m = _TITLE_LINE.fullmatch(first)
    title = html.unescape(m.group(1)) if m else ""
    if not re.fullmatch(r"\S(?:.*\S)?", title):
        raise ValueError("line 1 is not `<h1>title</h1>`")
    return title, body, 2


def esc(s):
    return html.escape(str(s), quote=True)


def _text(s):
    return html.escape(s, quote=False)


def _walk(node):
    """The elements under `node`, in document order."""
    for c in node.children:
        if isinstance(c, safehtml.Element):
            yield c
            yield from _walk(c)


def _plain(el):
    return " ".join(safehtml.text_of(el).split())


class _Writer:
    def __init__(self, source, highlight, design_sha256, rules_href):
        self.source, self.highlight = source, highlight or (lambda code, lang: _text(code))
        self.design, self.rules_href = design_sha256, rules_href
        self.slugger = _Slugger()
        self.ids, self.numbers = {}, {}

    def fail(self, line, message):
        raise HtmlError(self.source, line, message)

    def plan(self, root):
        """The ids of the headings and figures, in document order through one slugger (md.py's order: a heading
        "Figure 1" before the first figure moves the figure's id on), so a link may point forward."""
        n = 0
        for el in _walk(root):
            if el.tag in safehtml.HEADINGS:
                self.ids[id(el)] = self.slugger.slug(_plain(el))
            elif el.tag == "figure":
                n += 1
                self.numbers[id(el)] = n
                self.ids[id(el)] = self.slugger.slug(f"figure {n}")
        self.targets = set(self.ids.values())

    # -- the text ---------------------------------------------------------------------------------------------------

    def children(self, el):
        out = []
        kids = el.children
        for k, c in enumerate(kids):
            if isinstance(c, safehtml.Text):
                if el.tag in _BLOCKS and not c.data.strip(" \n"):
                    # white space between blocks: one newline (none before the first block or after the last at the
                    # top, md.py's form)
                    if el.tag != "#root" or 0 < k < len(kids) - 1:
                        out.append("\n")
                else:
                    out.append(_text(c.data))
            else:
                out.append(self.element(c))
        return "".join(out)

    def element(self, el):
        tag = el.tag
        if tag in safehtml.HEADINGS:
            level = int(tag[1]) + 1
            hid = self.ids[id(el)]
            return (f'<h{level} id="{esc(hid)}">{self.children(el)}'
                    f' <a class="anchor" href="#{esc(hid)}" aria-label="link to this section">#</a></h{level}>')
        if tag == "a":
            return f"<a{self.link(el)}>{self.children(el)}</a>"
        if tag == "pre":
            code = el.elements()[0]
            lang = code.attrs.get("class", "")[len("language-"):]
            lang_attr = f' data-lang="{esc(lang)}"' if lang else ""
            return (f'<pre class="code"{lang_attr}><code>{self.highlight(safehtml.text_of(code), lang)}'
                    f"</code></pre>")
        if tag == "table":
            return f'<div class="table-wrap"><table>{self.children(el)}</table></div>'
        if tag == "figure":
            return self.figure(el)
        if tag in safehtml.VOID:
            return f"<{tag}>"
        attrs = "".join(f' {k}="{esc(v)}"' for k, v in el.attrs.items())      # (ol start, th/td class, span class...)
        return f"<{tag}{attrs}>{self.children(el)}</{tag}>"

    def link(self, el):
        href = el.attrs["href"]
        if _SAFE_URL.fullmatch(href):
            return f' rel="nofollow ugc noopener" href="{esc(href)}"'
        m = safehtml.FRAGMENT.fullmatch(href)
        if m:
            target = ID_PREFIX + m.group(1)
            if target not in self.targets:
                self.fail(el.line, f"<a>: href={href!r} names no heading or figure of this writeup (a heading's id "
                                   "is its text in lower case, spaces as hyphens; a figure's is figure-n)")
            return f' href="#{esc(target)}"'
        return f' href="{esc(href)}"'                    # a relative path or a mailto address (safehtml checked it)

    # -- figures ----------------------------------------------------------------------------------------------------

    def caption(self, fig):
        cap = next(e for e in fig.elements() if e.tag == "figcaption")
        return self.children(cap).strip(" \n")

    def figure(self, el):
        fid, n = self.ids[id(el)], self.numbers[id(el)]
        name = el.attrs.get("data-figure")
        if name is not None:
            fig = figs.get(name)
            if fig is None:
                self.fail(el.line, f"no figure is named {name!r} (site/figs registers them)")
            if self.design is not None and self.design not in fig.designs:
                self.fail(el.line, f"figure {name!r} is drawn from another design than this record's")
            how = f' (<a href="{esc(self.rules_href)}">how</a>)' if self.rules_href else ""
            return (f'<figure class="wfig" id="{esc(fid)}"><div class="wfig-box">'
                    f'{figs.svg_of(fig, alt=el.attrs["data-alt"], uid=fid)}</div>'
                    f'<figcaption><span class="wfig-n">Figure {n}.</span> {self.caption(el)} '
                    f'<span class="wfig-credit">{esc(figs.credit(fig))}{how}.</span></figcaption></figure>')
        svg = el.elements()[0]
        return (f'<figure class="wfig" id="{esc(fid)}"><div class="wfig-box">{self.drawing(svg, fid)}</div>'
                f'<figcaption><span class="wfig-n">Figure {n}.</span> {self.caption(el)}</figcaption></figure>')

    def drawing(self, svg, fid):
        vb = svg.attrs["viewbox"]
        w, h = (float(x) for x in vb.replace(",", " ").split()[2:])
        lo = w if w <= MIN_PX else max(MIN_PX, w * MIN_SHARE)
        kids = svg.elements()
        desc = kids[1] if len(kids) > 1 and kids[1].tag == "desc" else None
        label = f"{fid}-t" + (f" {fid}-d" if desc else "")
        for e in _walk(svg):
            if e.attrs.get("id") in ("t", "d"):
                self.fail(e.line, f"<{safehtml._name(e.tag)}>: the ids t and d are the site's (the drawing's "
                                  "<title> and <desc>)")
        inner = (f'<title id="{esc(fid)}-t">{_text(safehtml.text_of(kids[0]))}</title>'
                 + (f'<desc id="{esc(fid)}-d">{_text(safehtml.text_of(desc))}</desc>' if desc else "")
                 + "".join(self.svg_node(c, fid) for c in kids[1 + bool(desc):]))  # (its text is white space)
        return (f'<svg class="wfig-svg" viewBox="{esc(vb)}" width="{figs.svg.f(w)}" height="{figs.svg.f(h)}" '
                f'style="max-width:{figs.svg.f(w)}px;min-width:{figs.svg.f(lo)}px" role="img" '
                f'aria-labelledby="{esc(label)}" xmlns="{safehtml.SVG_NS}">{inner}</svg>')

    def svg_node(self, node, fid):
        """A drawing's element, its ids and their url(#id) references in the figure's namespace; the white space of
        a container that is not text left out."""
        name = safehtml._name(node.tag)
        attrs = []
        for k, v in node.attrs.items():
            if k == "id":
                v = f"{fid}-{v}"
                if v in self.targets:
                    self.fail(node.line, f"<{name}>: the id {node.attrs['id']!r} becomes {v!r}, which a heading of "
                                         "this writeup has: rename it")
            else:
                m = safehtml._URL_REF.fullmatch(v)
                if m:
                    v = f"url(#{fid}-{m.group(1)})"
            attrs.append(f' {safehtml._name(k)}="{esc(v)}"')
        quiet = node.tag in _SVG_QUIET
        parts = []
        for c in node.children:
            if isinstance(c, safehtml.Text):
                if not (quiet and not c.data.strip(" \n")):
                    parts.append(_text(c.data))
            else:
                parts.append(self.svg_node(c, fid))
        inner = "".join(parts)
        a = "".join(attrs)
        return f"<{name}{a}>{inner}</{name}>" if inner else f"<{name}{a}/>"


def render(text, *, source, highlight=None, design_sha256=None, rules_href=None):
    """(title, the body as HTML) of a writeup's text (`source`: its path, for the errors). The title is plain text (the
    caller escapes it); the body is written by the rules above. `design_sha256`: the sha256 of the record's design
    file, which every generated figure must be drawn from; `rules_href`: where "how" in a generated figure's caption
    links (both from the site build). Raises HtmlError (a ValueError) for HTML outside the allowlists, ValueError for
    a text with no title line."""
    title, body, first = split(text)
    tree = safehtml.parse(body, source=source, first_line=first)
    w = _Writer(source, highlight, design_sha256, rules_href)
    w.plan(tree)
    out = w.children(tree)
    audit(out, source=source)
    return title, out


# --- the second check: the page's HTML read back -------------------------------------------------------------------

_OUT_TAGS = (safehtml.HTML_ELEMENTS | {"h5"} | safehtml.SVG_ELEMENTS) - {"h2"}
_OUT_ATTRS = frozenset({"id", "class", "href", "rel", "aria-label", "aria-labelledby", "role", "style", "width",
                        "height", "viewbox", "xmlns", "data-lang", "start", "colspan", "rowspan"}
                       | set().union(*(a for t, a in safehtml.ATTRS.items() if t in safehtml.SVG_ELEMENTS)))
_OUT_CLASSES = frozenset({"anchor", "code", "table-wrap", "wfig", "wfig-box", "wfig-svg", "wfig-n", "wfig-credit",
                          *safehtml.SVG_CLASSES, *safehtml.PROSE_CLASSES, *safehtml.ALIGN_CLASSES})
_OUT_STYLE = re.compile(r"max-width:[0-9.]+px;min-width:[0-9.]+px")


class _Audit(html.parser.HTMLParser):
    CDATA_CONTENT_ELEMENTS = ()
    RCDATA_CONTENT_ELEMENTS = ()

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.problems, self.ids = [], set()

    def handle_starttag(self, tag, attrs):
        self.check(tag, attrs)

    def handle_startendtag(self, tag, attrs):
        self.check(tag, attrs)

    def check(self, tag, attrs):
        bad = self.problems.append
        if tag not in _OUT_TAGS:
            bad(f"element <{tag}>")
        for k, v in attrs:
            v = v or ""
            if k not in _OUT_ATTRS or k.startswith("on"):
                bad(f"attribute {k} on <{tag}>")
            elif k == "style" and not (tag == "svg" and _OUT_STYLE.fullmatch(v)):
                bad(f"style {v!r} on <{tag}>")
            elif k == "href" and not (tag == "a" and (_SAFE_URL.fullmatch(v) or safehtml.MAILTO.fullmatch(v)
                                                      or re.fullmatch(r"#writeup-[\w-]+", v)
                                                      or (v and not v.startswith("#")
                                                          and safehtml.RELATIVE.fullmatch(v)))):
                bad(f"href {v!r} on <{tag}>")
            elif k == "id":
                if not v.startswith(ID_PREFIX):
                    bad(f"id {v!r}")
                if v in self.ids:
                    bad(f"the id {v!r} twice")
                self.ids.add(v)
            elif k == "class" and not all(c in _OUT_CLASSES or c.startswith("hl-") for c in v.split()):
                bad(f"class {v!r} on <{tag}>")

    def handle_comment(self, data):
        self.problems.append("a comment")

    def handle_decl(self, decl):
        self.problems.append("a declaration")

    def unknown_decl(self, data):
        self.problems.append("a declaration")

    def handle_pi(self, data):
        self.problems.append("a processing instruction")


def audit(out, *, source):
    """Refuse (HtmlError, line 0: the writer's own output) HTML this module would not write: an element, attribute,
    class, style, link or id outside what it writes, or an id twice."""
    a = _Audit()
    a.feed(out)
    a.close()
    if a.problems:
        raise HtmlError(source, 0, "internal: the rendered writeup holds " + "; ".join(sorted(set(a.problems))[:5]))


def fallback_title(design_name):
    """A record's title without a writeup: its design file's stem ("mul_tree.sv" -> "mul_tree")."""
    name = design_name.rsplit("/", 1)[-1]
    return name[:-3] if name.endswith(".sv") else name
