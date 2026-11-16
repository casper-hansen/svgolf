"""A record's writeup on its page (decided 2026-11-13, the owner's UI feedback items 3 and 6).

A writeup is an optional Markdown file `leaderboard/writeups/<record_hash>.md`, kept OUTSIDE the record (no field
of the record and none of its hashes name it), so adding or improving one never changes a record. Its first line
`# <title>` is the submission's short title (plain text, at most TITLE_MAX characters), shown as the record page's
heading, in the task page's submissions list and in every chart tooltip; the rest is a blog-post-style account of
the design and its proof, shown on the record page. leaderboard.py `writeup_problems` checks a file's shape (its
name, UTF-8, the title line, the size cap, the characters); this module renders it.

The body is written by a player, so it is rendered SAFELY, by md.py (the site's own Markdown subset: headings,
paragraphs, lists, code spans and fenced code, emphasis, tables, links) under three rules of its own:

* nothing a writer types becomes markup: md.py has no raw HTML (every `<` is text, escaped), refuses images (no
  picture from another origin, no tracking pixel) and every construct outside its subset (a blockquote, a footnote,
  a reference link: MarkdownError, with the file and line);
* a link is a link only when its target is an absolute http or https address (`safe_target`); any other target
  (`javascript:`, `data:`, a relative path, an address with a quote or a control character) is shown as its text,
  linking nothing; a link carries rel="nofollow ugc noopener";
* the headings are the card's: `#` and `##` start at the card's sub-level (h3), and their anchors carry the prefix
  `writeup-`, so that no heading a writer picks can take an id of the page's own.

FIGURES (decided 2026-11-16): a fenced block with the info string `figure` shows a figure the site draws from the
design (site/figs), never a picture the writer supplies. Its lines are `key: value`, exactly these three:

    ```figure
    name: add-kogge-stone
    alt: The Kogge-Stone prefix graph at N = 8: four levels of combining nodes.
    caption: Every carry after four levels; each dot combines two (generate, propagate) pairs.
    ```

`name` must be a registered figure (figs.REGISTRY), and, when the caller says which design the writeup's record has
(`design_sha256`; the site build always does), one drawn from that design; `alt` is plain text (the drawing's
<title>, read by a screen reader), `caption` one line of the writeup's inline Markdown, at most CAPTION_MAX
characters (a caption is short). The page shows "Figure n." and the caption, then a line the site makes from the
figure's registration, never typed: the size it is drawn at, the record's scoring point, who made it, and (with
`rules_href`) a link to how figures are made. Anything else in such a block is a MarkdownError, with its line.

Standard library only, as md.py.
"""

import html
import re

import figs
import md

FIGURE_KEYS = ("name", "alt", "caption")
CAPTION_MAX = 300                     # characters of a figure's caption (definitions go behind a link)
ALT_MAX = 300                         # characters of a figure's alt text

TITLE_MAX = 60                        # the title's length cap, in characters (leaderboard.py WRITEUP_TITLE_MAX)
ID_PREFIX = "writeup-"
_SAFE_URL = re.compile(r"https?://[A-Za-z0-9.-]+(?::[0-9]{1,5})?(?:[/?#][^\s\"'<>\\`\x00-\x1f\x7f]*)?")


def safe_target(target):
    """`target` when it is an absolute http or https address with a plain host name and no quote, angle bracket,
    backslash, backtick, space or control character; else None (the link's text is shown, linking nothing)."""
    return target if _SAFE_URL.fullmatch(target or "") else None


class _Slugger(md.Slugger):
    """md.py's heading anchors, each with the prefix `writeup-` (no heading takes an id of the page's own)."""

    def slug(self, text):
        return ID_PREFIX + super().slug(text)


def split(text):
    """(title, body, the body's first line number) of a writeup's text: the title is line 1 without its `# `; the
    body is everything after it. Raises ValueError when line 1 is not a title line (leaderboard.py checks this
    first, with its own words)."""
    first, _, body = text.partition("\n")
    m = re.fullmatch(r"# (\S(?:.*\S)?)", first)
    if not m:
        raise ValueError("line 1 is not `# <title>`")
    return m.group(1), body, 2


def figure_fields(block, *, source, line):
    """{name, alt, caption} of a figure block's body (its first line is `line` + 1 of `source`); md.MarkdownError
    for anything but exactly those three `key: value` lines."""
    out = {}
    for k, raw in enumerate(block.split("\n")):
        no = line + 1 + k
        if not raw.strip():
            continue
        m = re.fullmatch(r"([a-z]+): (\S(?:.*\S)?)", raw.strip())
        if not m:
            raise md.MarkdownError(source, no, "a figure block's lines are `key: value` (name, alt, caption)")
        key, value = m.groups()
        if key not in FIGURE_KEYS:
            raise md.MarkdownError(source, no, f"a figure block has no key {key!r} (name, alt, caption)")
        if key in out:
            raise md.MarkdownError(source, no, f"a figure block's {key!r} is given twice")
        out[key] = value
    missing = [k for k in FIGURE_KEYS if k not in out]
    if missing:
        raise md.MarkdownError(source, line, "a figure block needs " + ", ".join(missing))
    for key, cap in (("caption", CAPTION_MAX), ("alt", ALT_MAX)):
        if len(out[key]) > cap:
            raise md.MarkdownError(source, line, f"a figure's {key} has {len(out[key])} characters, over {cap}")
    return out


def render(text, *, source, highlight=None, design_sha256=None, rules_href=None):
    """(title, the body as HTML) of a writeup's text (`source`: its path, for md.py's errors). The title is plain
    text (the caller escapes it); the body is md.py's rendering under the rules above. `design_sha256`: the sha256
    of the record's design file, which every figure block must be drawn from; `rules_href`: where "how" in a figure's
    caption links (both from the site build). Raises md.MarkdownError for a construct outside the subset, ValueError
    for a text with no title line."""
    title, body, first = split(text)
    slugger = _Slugger()
    count = [0]

    def figure(block, no):
        f = figure_fields(block, source=source, line=no)
        fig = figs.get(f["name"])
        if fig is None:
            raise md.MarkdownError(source, no, f"no figure is named {f['name']!r} (site/figs registers them)")
        if design_sha256 is not None and design_sha256 not in fig.designs:
            raise md.MarkdownError(source, no, f"figure {f['name']!r} is drawn from another design than this "
                                               "record's")
        count[0] += 1
        fid = slugger.slug(f"figure {count[0]}")
        caption = md.render_inline(f["caption"], source=source, line=no, resolve_link=safe_target)
        how = f' (<a href="{esc(rules_href)}">how</a>)' if rules_href else ""
        return (f'<figure class="wfig" id="{esc(fid)}"><div class="wfig-box">'
                f'{figs.svg_of(fig, alt=f["alt"], uid=fid)}</div>'
                f'<figcaption><span class="wfig-n">Figure {count[0]}.</span> {caption} '
                f'<span class="wfig-credit">{esc(figs.credit(fig))}{how}.</span></figcaption></figure>')

    r = md.render(body, source=source, first_line=first, resolve_link=safe_target, highlight=highlight,
                  slugger=slugger, heading_shift=1, figure=figure)
    out = r.html
    # md.py writes `<a href="...">` for a link it resolved, nothing else (a writer's `<` is escaped): mark each one
    out = out.replace('<a href="http', '<a rel="nofollow ugc noopener" href="http')
    # the headings start at h3 (the card's title is an h2): `#` would be h2 after the shift
    out = re.sub(r"<(/?)h2\b", r"<\1h3", out)
    return title, out


def fallback_title(design_name):
    """A record's title without a writeup: its design file's stem ("mul_tree.sv" -> "mul_tree")."""
    name = design_name.rsplit("/", 1)[-1]
    return name[:-3] if name.endswith(".sv") else name


def esc(s):
    return html.escape(str(s), quote=True)
