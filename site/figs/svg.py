"""A small SVG writer for the writeups' figures (site/figs): standard library only, deterministic.

Every coordinate is rounded to 0.1 (svgplot.py's rule), nothing depends on dict or set order, and nothing carries a
colour: each mark has a class that style.css colours from the site's tokens ("svg.wfig-svg ..."), so one drawing
follows the page's light and dark themes, as the charts and the schematics do. The classes:

  text   t-lab (a label, the system font), t-head (a heading), t-note (small, quiet), t-mono (code-like), t-hot (the
         accent's ink), t-on (text on an accent-soft fill)
  lines  w (a wire or a column line, quiet), w-faint (a guide), e (an edge), e-hot (the accent: what the figure
         points at), e-blue (a second kind of edge), e-dash (dashed)
  fills  n (a node: a dot), n-hot, n-open (a hollow node), b (a box), b-hot (an accented box), b-blue (a box of the
         second kind), b-soft (a quiet cell fill), b-on (an accent-soft cell), arrow, arrow-hot (arrow heads)
"""

import html
import math


def f(v):
    """A coordinate, rounded to 0.1, in a fixed text form."""
    s = f"{round(v, 1):.1f}"
    return "0.0" if s == "-0.0" else s


def esc(s):
    return html.escape(str(s), quote=True)


class Drawing:
    """The marks of one figure, in drawing order, on a w x h canvas (viewBox units = CSS pixels at full size)."""

    def __init__(self, w, h):
        self.w, self.h = w, h
        self.parts = []

    def line(self, x1, y1, x2, y2, cls="w"):
        self.parts.append(f'<line class="{cls}" x1="{f(x1)}" y1="{f(y1)}" x2="{f(x2)}" y2="{f(y2)}"/>')

    def path(self, d, cls="e"):
        """`d`: a list of ("M"|"L"|"H"|"V", numbers...) steps, or a ready string."""
        if not isinstance(d, str):
            d = "".join(op + " ".join(f(v) for v in vals) for op, *vals in d)
        self.parts.append(f'<path class="{cls}" d="{d}"/>')

    def poly(self, pts, cls="e", closed=False):
        tag = "polygon" if closed else "polyline"
        self.parts.append(f'<{tag} class="{cls}" points="{" ".join(f"{f(x)},{f(y)}" for x, y in pts)}"/>')

    def circle(self, cx, cy, r, cls="n"):
        self.parts.append(f'<circle class="{cls}" cx="{f(cx)}" cy="{f(cy)}" r="{f(r)}"/>')

    def rect(self, x, y, w, h, cls="b"):
        self.parts.append(f'<rect class="{cls}" x="{f(x)}" y="{f(y)}" width="{f(w)}" height="{f(h)}"/>')

    def text(self, x, y, s, cls="t-lab", anchor="start"):
        a = "" if anchor == "start" else f' text-anchor="{anchor}"'
        self.parts.append(f'<text class="{cls}" x="{f(x)}" y="{f(y)}"{a}>{esc(s)}</text>')

    def arrow(self, x1, y1, x2, y2, cls="e", head=6):
        """A line from (x1, y1) to (x2, y2) with a filled head at the end."""
        dx, dy = x2 - x1, y2 - y1
        n = math.hypot(dx, dy) or 1.0
        ux, uy = dx / n, dy / n
        bx, by = x2 - ux * head, y2 - uy * head
        self.line(x1, y1, bx, by, cls)
        hcls = "arrow-hot" if cls == "e-hot" else "arrow"
        self.poly([(x2, y2), (bx - uy * head * 0.5, by + ux * head * 0.5), (bx + uy * head * 0.5, by - ux * head * 0.5)],
                  hcls, closed=True)

    def svg(self, *, uid, title, desc, min_w=None):
        """The figure as inline SVG: role="img", labelled by its <title> (the writeup's alt text) and described by its
        <desc> (the generator's words); `uid` makes the two ids unique on the page. It is drawn at most at its own
        size and, on a narrow screen, never below `min_w` px (its box scrolls instead), so its text stays legible."""
        lo = self.w if min_w is None else min(min_w, self.w)
        return (f'<svg class="wfig-svg" viewBox="0 0 {f(self.w)} {f(self.h)}" width="{f(self.w)}" height="{f(self.h)}" '
                f'style="max-width:{f(self.w)}px;min-width:{f(lo)}px" role="img" '
                f'aria-labelledby="{esc(uid)}-t {esc(uid)}-d" xmlns="http://www.w3.org/2000/svg">'
                f'<title id="{esc(uid)}-t">{esc(title)}</title><desc id="{esc(uid)}-d">{esc(desc)}</desc>'
                + "".join(self.parts) + "</svg>")
