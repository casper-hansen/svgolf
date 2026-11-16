"""The clocked tasks' figures beside matmul's: the sorter's insertion cells at work, and the arbiter's grant rotation.

Each figure is a cycle-by-cycle table from a model that restates the design's always_ff bodies on the figure's own
inputs; tests/site/test_figures.py simulates the design itself (Icarus Verilog) on the same inputs and compares
every value the table shows.
"""

from . import register
from .svg import Drawing


# ---- the sorter's insertion-cell array (sorter_ins.sv of par's record 7b878f6d; sol1.sv of record 3b1ec4b1 has the
# same behaviour, its conditions tested in the other order, and is simulated against the same table)

SORTER_N, SORTER_W = 4, 4
SORTER_INPUTS = (5, 2, 9, 2)        # one duplicate: duplicates are kept
SORTER_EDGES = 9


def sorter_run(n, inputs, edges):
    """The registers after each clock edge after reset, the inputs on consecutive in_valid edges: sorter_ins.sv's
    cells (`if (in_valid) { if (in_data > data[k+1]) data[k] <= data[k+1]; else if (in_data > data[k]) data[k] <=
    in_data; } else data[k] <= data[k+1]`, the top cell taking in_data when it beats it and 0 when the input stops),
    the tokens (`tok[k] <= tok[k+1]; tok[N-1] <= in_valid`) and the registered output (`out_valid <= tok[0];
    out_data <= data[0]`). Returns [{"in": value or None, "cells": [cell 0 .. N-1], "how": ["in" | "down" | "hold"],
    "tok", "ov", "od"}] for edges 1..edges."""
    cells, tok, ov, od = [0] * n, [0] * n, 0, 0
    out = []
    for e in range(edges):
        x = inputs[e] if e < len(inputs) else None
        nc, how = cells[:], ["hold"] * n
        for k in range(n):
            up = cells[k + 1] if k + 1 < n else None
            if x is not None:
                if up is not None and x > up:
                    nc[k], how[k] = up, "down"
                elif x > cells[k]:
                    nc[k], how[k] = x, "in"
            else:
                nc[k], how[k] = (up if up is not None else 0), "down"
        ov, od = tok[0], cells[0]
        tok = tok[1:] + [1 if x is not None else 0]
        cells = nc
        out.append({"in": x, "cells": cells[:], "how": how, "tok": tok[:], "ov": ov, "od": od})
    return out


def sorter_figure():
    n = SORTER_N
    rows = sorter_run(n, SORTER_INPUTS, SORTER_EDGES)
    cw, ch, gap = 34, 22, 6
    x_in, x0 = 70, 120
    x_out = x0 + n * (cw + gap) + 22
    top = 46
    w = x_out + 70
    h = top + (len(rows) + 1) * (ch + gap) + 52
    d = Drawing(w, h)
    d.text(4, top - 14, "edge", "t-note")
    d.text(x_in, top - 14, "input", "t-note", "middle")
    d.text(x0 + (n * (cw + gap) - gap) / 2, top - 30, "cells (the top on the left)", "t-note", "middle")
    for k in range(n):
        d.text(x0 + (n - 1 - k) * (cw + gap) + cw / 2, top - 14, str(k), "t-note", "middle")
    d.text(x_out + 20, top - 14, "output", "t-note", "middle")

    def row(r, label, inp, cells, how, out):
        y = top + r * (ch + gap)
        d.text(4, y + 15, label, "t-mono")
        d.text(x_in, y + 15, "–" if inp is None else str(inp), "t-mono", "middle")
        for k in range(n):
            x = x0 + (n - 1 - k) * (cw + gap)
            cls = {"in": "b-hot", "down": "b-blue", "hold": "b"}[how[k]]
            d.rect(x, y, cw, ch, cls)
            d.text(x + cw / 2, y + 15, str(cells[k]), "t-mono" if cells[k] else "t-note", "middle")
        d.text(x_out + 20, y + 15, "–" if out is None else str(out), "t-hot" if out is not None else "t-mono",
               "middle")
    row(0, "reset", None, [0] * n, ["hold"] * n, None)
    for e, s in enumerate(rows, 1):
        row(e, str(e), s["in"], s["cells"], s["how"], s["od"] if s["ov"] else None)
    ly = h - 30
    d.rect(4, ly - 10, 12, 12, "b-hot")
    d.text(20, ly, "took the input", "t-note")
    d.rect(124, ly - 10, 12, 12, "b-blue")
    d.text(140, ly, "took the cell above (or 0 at the top)", "t-note")
    d.text(4, ly + 18, "A cell keeps its value when the input beats neither it nor the cell above.", "t-note")
    outs = [s["od"] for s in rows if s["ov"]]
    desc = (f"The insertion-cell sorter at N = {n}, W = {SORTER_W}, edge by edge after reset: the inputs "
            f"{', '.join(map(str, SORTER_INPUTS))} arrive on four consecutive edges. Each input goes to the cell where "
            "it belongs: the cells below that point take the value of the cell above them, the cells above it hold; "
            "so the cells stay in order, the largest at the top, the zeros of padding at the bottom. When the input "
            f"stops every cell takes the one above and the top takes 0, so the values leave through cell 0, "
            f"smallest first: the registered output shows {', '.join(map(str, outs))} on edges "
            f"{', '.join(str(e) for e, s in enumerate(rows, 1) if s['ov'])}.")
    return d, desc


# ---- the arbiter (rr_mask.sv of par's record d354b82f)

ARB_N = 4
ARB_REQS = (0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1011, 0b1011, 0b1011, 0b0100, 0b0000, 0b0101)


def arbiter_run(n, reqs):
    """rr_mask.sv after reset (gnt = 0, mask = all ones), one request vector per edge: `mreq = req & mask; pick =
    mreq != 0 ? lowest set bit of mreq : lowest set bit of req`; on the edge `gnt <= pick` and, when pick != 0,
    `mask <= ~((pick << 1) - 1)` (N bits). Returns [{"req", "mask" (before the edge), "gnt", "mask_after",
    "wrap"}]."""
    full = (1 << n) - 1
    mask = full
    out = []
    for r in reqs:
        mreq = r & mask
        x = mreq if mreq else r
        pick = x & (-x) & full
        nm = (~(((pick << 1) - 1) & full)) & full if pick else mask
        out.append({"req": r, "mask": mask, "gnt": pick, "mask_after": nm, "wrap": bool(r) and not mreq})
        mask = nm
    return out


def arbiter_figure():
    n = ARB_N
    rows = arbiter_run(n, ARB_REQS)
    sq, gap, rh = 16, 4, 24
    groups = (("requests", "req"), ("mask before", "mask"), ("grant after", "gnt"))
    gw = n * (sq + gap)
    x0 = 52
    xs = [x0 + k * (gw + 34) for k in range(len(groups))]
    top = 58
    w = xs[-1] + gw + 110
    h = top + len(rows) * rh + 64
    d = Drawing(w, h)
    d.text(4, top - 32, "edge", "t-note")
    for (title, _), x in zip(groups, xs):
        d.text(x, top - 32, title, "t-note")
        for c in range(n):
            d.text(x + (n - 1 - c) * (sq + gap) + sq / 2, top - 14, str(c), "t-note", "middle")
    for r, s in enumerate(rows):
        y = top + r * rh
        d.text(4, y + 12, str(r + 1), "t-mono")
        for (_, key), x in zip(groups, xs):
            v = s[key]
            for c in range(n):
                bx = x + (n - 1 - c) * (sq + gap)
                on = (v >> c) & 1
                cls = ("b-hot" if key == "gnt" else "b-blue" if key == "mask" else "b-soft") if on else "b"
                if key == "req" and on:
                    cls = "n"
                d.rect(bx, y, sq, sq, cls)
        g = s["gnt"]
        note = (f"client {g.bit_length() - 1}" if g else "none") + (" (wrap)" if s["wrap"] else "")
        d.text(xs[-1] + gw + 8, y + 12, note, "t-hot" if g else "t-note")
    d.text(4, h - 40, "Filled: a requesting client. Blue: the mask, the clients above the last grant.", "t-note")
    d.text(4, h - 24, "Accent: the grant. The lowest masked requester wins; with none, the lowest", "t-note")
    d.text(4, h - 8, "requester (the wrap).", "t-note")
    desc = (f"The round-robin arbiter at N = {n}, edge by edge after reset, clients 3 to 0 from left to right: the "
            "requests, the mask before the edge (the clients above the last grant) and the grant registered on the "
            "edge. With all four requesting the grant rotates 0, 1, 2, 3 and wraps to 0; when client 2 stops asking "
            "it is skipped; an edge with no request grants nothing and leaves the mask as it was.")
    return d, desc


SORTER_INS = "2f51939328bf61aa1ec44097e954bdf7616a9341555683dbddb1e6b9b439f8e2"   # sorter_ins.sv (par), 7b878f6d
SORTER_SOL1 = "bb75dc83f25a2cbe8a99720416520ee7e7ae2980fb9078dbce0d36db6a71c928"  # sol1.sv, 3b1ec4b1
RR_MASK = "f8b02272b7f264d935673b0fa5522fbfb877bdf2985b5c1ad27b861b3a5de784"      # rr_mask.sv (par), d354b82f

register("sorter-insertion", task="sorter", designs=[SORTER_INS, SORTER_SOL1], drawn_at="N = 4, W = 4",
         scored_at="N = 8, W = 8", make=lambda: (*sorter_figure(), 330))
register("arbiter-rotation", task="arbiter", designs=[RR_MASK], drawn_at="N = 4", scored_at="N = 8",
         make=lambda: (*arbiter_figure(), 380))
