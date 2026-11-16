"""The figures of the writeups (decided 2026-11-16: the owner asked for more figures in the writeups, the best designs
first). Standard library only, as the rest of the site.

A FIGURE IS DRAWN BY THE SITE AT BUILD TIME AND NEVER STORED. Each one is a registered generator (`register`, in this
package's task modules) that draws from the design's own parameters and the same index formulas as its
SystemVerilog source (its generate conditions, loop bounds and cells' update rules), at a small display size, and
returns an SVG drawing (figs/svg.py) with a description in words. A writeup shows one with a fenced block whose info
string is `figure` (site/writeup.py), naming it; it can show nothing else: a writeup may come from a pull request,
and a figure is reviewed site code, never a file a pull request supplies and the page inlines.

Each registration names the design file(s) it is drawn from by sha256, so a writeup cannot show the figure of
another design (writeup.py refuses it when it knows the record's design; the site build always does), and states
the size it is drawn at and the record's scoring point; the caption's last line is made from them, never typed.

THE CHECKS (tests/site/test_figures.py): every generator is deterministic, and the structure it draws is compared
with the design itself: a combinational figure with the netlist Yosys elaborates from the design at the
drawn size (no synthesis, so the generate structure is there to read: which signal each drawn node reads); a clocked
figure with an Icarus Verilog simulation of the design on the figure's own inputs (every value the figure prints,
cycle by cycle). Those tests skip without the tools; each generator also has a tool-free test of its model.
"""

import dataclasses

from . import svg     # noqa: F401  (the drawing helper of the task modules)


@dataclasses.dataclass(frozen=True)
class Figure:
    name: str               # what a writeup's figure block names
    task: str
    designs: tuple          # the sha256 of each design file it is drawn from (a record's files.sv.sha256)
    drawn_at: str           # the display size, as the caption says it: "N = 8"
    scored_at: str          # the records' scoring point, as the caption says it: "N = 16" (a test checks it)
    make: object            # () -> (svg.Drawing, description in words, minimum width in px or None)
    by: str = "the maintainers"


REGISTRY = {}


def register(name, *, task, designs, drawn_at, scored_at, make, by="the maintainers"):
    if name in REGISTRY:
        raise ValueError(f"figure {name!r} registered twice")
    REGISTRY[name] = Figure(name, task, tuple(designs), drawn_at, scored_at, make, by)


def get(name):
    """The registered figure `name`, or None."""
    return REGISTRY.get(name)


def svg_of(fig, *, alt, uid):
    """The figure as inline SVG, its <title> the writeup's `alt` text, its ids made unique by `uid`."""
    drawing, desc, min_w = fig.make()
    return drawing.svg(uid=uid, title=alt, desc=desc, min_w=min_w)


def credit(fig):
    """The caption's generated last line (without its final full stop): the size it is drawn at against the record's
    scoring point, and who made it."""
    size = (f"Drawn at the scoring size, {fig.drawn_at}" if fig.drawn_at == fig.scored_at else
            f"Drawn at {fig.drawn_at}; the record is scored at {fig.scored_at}")
    return f"{size}. Figure by {fig.by}, generated from the design"


from . import adders, multipliers, clmul, divider, matmul, clocked   # noqa: E402,F401  (they register their figures)
