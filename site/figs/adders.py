"""The add task's figures: the carry network of each adder on the board, drawn in one language (a prefix graph:
bit positions across, levels down, a dot per combining node), and the carry-select adder's blocks.

Every model below restates its design's generate conditions and index formulas (quoted beside it); the drawing is
made from the model only, and tests/site/test_figures.py compares the model with the netlist Yosys elaborates
from the design itself (which signal bit each node's gates read).
"""

from . import register
from .svg import Drawing

SCORED = "N = 16"                 # task add's scoring point (tasks/add/task.json; a test checks every record's)


def clog2(x):
    """SystemVerilog's $clog2 for x >= 1."""
    return (x - 1).bit_length()


# ---- the models: [(level, position, partner)] of the combining nodes over positions 0..N (0: the carry in,
# k + 1: bit k), and the number of levels

def kogge_stone(n):
    """add_n_kogge_stone.sv: L = $clog2(N + 1) levels; `if (i >= (1 << l))` position i combines with
    i - (1 << l), every other position passes."""
    levels = clog2(n + 1)
    return levels, [(l, i, i - (1 << l)) for l in range(levels) for i in range(n + 1) if i >= (1 << l)]


def sklansky(n):
    """add_n_sklansky.sv: L = $clog2(N + 1) levels; `if (((i >> l) & 1) == 1)` position i combines with
    ((i >> l) << l) - 1, every other position passes."""
    levels = clog2(n + 1)
    return levels, [(l, i, ((i >> l) << l) - 1) for l in range(levels) for i in range(n + 1) if (i >> l) & 1]


def ripple(n):
    """The ripple-carry adders (add_n, add_n_byhand.sv, add_proc.sv, add_proc_m.sv, add_mux.sv): `c[i+1]` is
    computed from `c[i]` and bit i's operands, one cell per bit; as a prefix graph, level l combines position l + 1
    with position l."""
    return n, [(l, l + 1, l) for l in range(n)]


def carries(n, levels, nodes, a, b, cin):
    """The value at each position after the last level, evaluating the model on operands a, b and the carry in:
    (g, p) pairs combined as g | (p & g_low), p & p_low (the tests check that position k ends as the carry into bit
    k for every input at the drawn size)."""
    g = [cin] + [(a >> k) & (b >> k) & 1 for k in range(n)]
    p = [0] + [((a ^ b) >> k) & 1 for k in range(n)]
    by_level = {}
    for l, i, j in nodes:
        by_level.setdefault(l, []).append((i, j))
    for l in range(levels):
        g2, p2 = g[:], p[:]
        for i, j in by_level.get(l, []):
            g2[i] = g[i] | (p[i] & g[j])
            p2[i] = p[i] & p[j]
        g, p = g2, p2
    return g


# ---- the drawing

DX, DY, LEFT, TOP = 36, 30, 46, 40


def prefix_graph(n, levels, nodes, *, name, cell, fan_out=None):
    """The prefix graph: positions 0..n across (the carry in on the right, as an adder is drawn, its top bit on the
    left), a row per level; a dot is a combining node, its diagonal edge comes from its partner one level up; a
    column with no dot on a row passes its value down. `fan_out`: (level, source position) whose edges are drawn in
    the accent (the fan-out the writeup names)."""
    w = LEFT + n * DX + 30
    rows = levels
    h = TOP + (rows + 1) * DY + 44
    d = Drawing(w, h)
    x = lambda i: LEFT + (n - i) * DX + 12         # noqa: E731
    y_in = TOP
    y = lambda l: TOP + (l + 1) * DY               # noqa: E731
    y_out = TOP + (rows + 1) * DY
    for i in range(n + 1):
        d.line(x(i), y_in + 6, x(i), y_out - 4, "w")
        d.text(x(i), y_in - 6, "cin" if i == 0 else str(i - 1), "t-mono", "middle")
        d.text(x(i), y_out + 12, "cout" if i == n else f"c{i}", "t-mono", "middle")
    d.text(4, y_in - 6, "bit", "t-note")
    d.text(4, y_out + 12, "carry", "t-note")
    for l in range(rows):
        d.text(4, y(l) + 4, f"L{l}", "t-note")
    for l, i, j in nodes:
        hot = fan_out is not None and (l, j) == fan_out
        y0 = y_in + 6 if l == 0 else y(l - 1)
        d.line(x(j), y0, x(i), y(l), "e-hot" if hot else "e")
    for l, i, j in nodes:
        d.circle(x(i), y(l), 5.5, "n-hot" if fan_out is not None and (l, j) == fan_out else "n")
    per = [sum(1 for l2, _, _ in nodes if l2 == l) for l in range(levels)]
    d.text(4, h - 8, f"{len(nodes)} combining nodes in {levels} levels ({', '.join(map(str, per))})", "t-note")
    desc = (f"The {name} prefix graph of the {n}-bit adder: positions 0 (the carry in) to {n} (bit {n - 1}) across, "
            f"the top bit on the left, {levels} levels down. A dot at level l and position i combines position i "
            f"with the position its edge comes from, one level up: {cell}. "
            f"There are {len(nodes)} dots ({', '.join(map(str, per))} per level). After the last level position k "
            f"holds the carry into bit k (c0 to c{n - 1}) and position {n} the carry out.")
    return d, desc


def _prefix(model, n, name, **kw):
    def make():
        levels, nodes = model(n)
        d, desc = prefix_graph(n, levels, nodes, name=name, **kw)
        return d, desc, 300
    return make




# ---- the carry-select adder (solution.sv of record 9e0b4286): Q = N / 6 blocks of six bits and an R = N % 6 bit tail

def carry_select(n):
    """solution.sv: `localparam integer Q = N / 6; R = N % 6`; block j (j < Q) covers bits 6j .. 6j+5 with the two
    ripple chains c0[j] (carry in 0) and c1[j] (carry in 1), the row cs[j] of multiplexers picking the carry into
    each bit by the block carry cb[j], and `cb[j+1] = cb[j] ? c1[j][6] : c0[j][6]`; the tail ripples bits
    6Q .. 6Q+R-1 from `c[6*Q] = cb[Q]`. Returns ([(j, first bit, last bit)], (first, last) of the tail or None)."""
    q, r = n // 6, n % 6
    return [(j, 6 * j, 6 * j + 5) for j in range(q)], ((6 * q, 6 * q + r - 1) if r else None)


def carry_select_figure(n):
    """The blocks low bits on the right (as an adder is drawn): in each block the two chains of six cells, the row
    of multiplexers that picks each bit's carry, and the block's multiplexer on the block-carry line, which runs
    from the carry in through one multiplexer per block to the tail's ripple cells (the accent)."""
    blocks, tail = carry_select(n)
    cw, pad, gap = 22, 8, 46
    bw = 6 * cw + pad + 18                         # a block: six cells, the constants' room on its right
    tw = (tail[1] - tail[0] + 1) * cw + 2 * pad if tail else 0
    left = 40
    w = left + tw + 30 + len(blocks) * (gap + bw) + 34
    y_t, y1, y0, yb0, yb1, y_s, y_r = 18, 50, 78, 98, 120, 138, 166
    h = y_r + 40
    d = Drawing(w, h)

    def cells(x_right, y, k, cls, arrow_cls):
        """k cells right to left from x_right; returns the x of the chain's left end and each cell's centre."""
        xs = []
        x = x_right
        for _ in range(k):
            d.arrow(x, y, x - 6, y, arrow_cls, head=4)
            d.rect(x - 6 - 14, y - 7, 14, 14, cls)
            xs.append(x - 13)
            x -= cw
        return x + 2, xs

    xr = w - 34                                    # the carry in enters here
    d.text(xr + 4, y_r + 4, "cin", "t-mono")
    for j, lo, hi in blocks:
        bx1 = xr - 10 if j == 0 else xr - gap / 2 - 4
        bx0 = bx1 - bw
        d.rect(bx0, y_t + 12, bw, y_s - y_t - 2, "b-soft")
        d.text((bx0 + bx1) / 2, y_t, f"block {j}: bits {lo}–{hi}", "t-head", "middle")
        x_in = bx1 - 18
        d.text(x_in + 4, y1 + 4, "1", "t-mono")
        d.text(x_in + 4, y0 + 4, "0", "t-mono")
        e1, xs1 = cells(x_in, y1, 6, "b", "e")
        e0, xs0 = cells(x_in, y0, 6, "b", "e")
        # every bit's carry into it, from both chains, into the row of multiplexers
        for xa in xs1:
            d.line(xa + 9, y1 + 2, xa + 9, yb0, "w-faint")
        for xa in xs0:
            d.line(xa + 9, y0 + 7, xa + 9, yb0, "w-faint")
        d.rect(bx0 + pad, yb0, bw - 2 * pad, yb1 - yb0, "b")
        d.text((bx0 + bx1) / 2, yb1 - 6, "6 carry muxes", "t-note", "middle")
        d.text((bx0 + bx1) / 2, y_s - 2, f"s{lo}–s{hi}", "t-note", "middle")
        # the block carry: the select of the six multiplexers, and of the block's own multiplexer on its left
        mx = bx0 - gap / 2
        d.line(e1, y1, mx - 6, y1, "w")
        d.line(mx - 6, y1, mx - 6, y_r - 11, "w")
        d.line(e0, y0, mx + 6, y0, "w")
        d.line(mx + 6, y0, mx + 6, y_r - 11, "w")
        d.line(bx1 - 12, y_r, bx1 - 12, yb1, "w")
        d.circle(bx1 - 12, y_r, 3, "n-hot")
        d.line(xr, y_r, mx + 13, y_r, "e-hot")
        d.text(bx1 - 16, y_r + 18, f"cb[{j}]", "t-mono", "end")
        d.rect(mx - 13, y_r - 11, 26, 22, "b-hot")
        d.text(mx, y_r + 4, "mux", "t-note", "middle")
        xr = mx - 13
    if tail:
        lo, hi = tail
        tx1 = xr - 30
        d.line(xr, y_r, tx1, y_r, "e-hot")
        d.text(xr - 2, y_r + 18, f"cb[{len(blocks)}]", "t-mono", "end")
        d.text(tx1 - tw / 2, y_t, f"tail: bits {lo}–{hi}", "t-head", "middle")
        e, xs = cells(tx1, y_r, hi - lo + 1, "b-hot", "e-hot")
        for xa in xs:
            d.line(xa + 7, y_r - 7, xa + 7, y_s + 4, "w-faint")
        d.text(tx1 - tw / 2, y_s - 2, f"s{lo}–s{hi}", "t-note", "middle")
        d.arrow(e, y_r, left - 4, y_r, "e-hot", head=5)
        d.text(left - 6, y_r - 10, "cout", "t-mono", "middle")
    d.text(6, h - 6, "Accent: the block carry, one mux per block, then the tail's cells.", "t-note")
    nt = tail[1] - tail[0] + 1 if tail else 0
    desc = (f"The carry-select adder at N = {n}: {len(blocks)} blocks of six bits and a {nt}-bit tail, the low bits "
            "on the right. Each block holds two chains of six ripple cells, one started from carry 1 and one from "
            "carry 0, and a row of six multiplexers that picks each bit's carry by the block carry. The block carry "
            "runs from the carry in through one multiplexer per block, which picks the block's carry out from the "
            "two chains, and then through the tail's ripple cells to the carry out.")
    return d, desc


def _cs(n):
    def make():
        d, desc = carry_select_figure(n)
        return d, desc, 420
    return make


# ---- the registrations: each names the design file it is drawn from (files.sv.sha256 of the record)

DRAWN = 8
KOGGE_STONE = "c69f27263a9122680a53e711956c20d415259ce22d0699e2d2257f0e946ed062"     # add_n_kogge_stone.sv, 2140324c
SKLANSKY = "f274cc954edcb1179025cfac2df267c4458a4c24e60757d4cdfbff057aee96c9"        # add_n_sklansky.sv, 2387ec60
RIPPLE_BYHAND = "6579283e86a83926c68dbaa616514d26e83f7ede393aad333cafb7af3cc47ec5"   # add_n_byhand.sv (par), 710c4589
RIPPLE_PROC = "e7a066631b417e4a58179a26e8c1596b823a9e3ab7ffb1f416307b7a1789346e"     # add_proc.sv, b1a6c9b7
RIPPLE_PROC_M = "dfd98e1517ef5a0dd364dfcf108bf474615061c851ecca801ffc5f753a098ddb"   # add_proc_m.sv, 19562fe5
RIPPLE_MUX = "824073f06b1ce4600e10ec7cbe8606ad3defda46d2d59a56ea153b37643f9d54"      # add_mux.sv, e30d319a
CARRY_SELECT = "52e1d40feb1823cf5a143674deb33d6d77ea611f898ee83b81fa3725abbebee9"    # solution.sv, 9e0b4286

PG = "generate g | (p & g_low) and propagate p & p_low"
CARRY_CELL = "the carry cell of bit l, which makes the carry out of bit l from the carry into it and the bit's two operands"
register("add-kogge-stone", task="add", designs=[KOGGE_STONE], drawn_at=f"N = {DRAWN}", scored_at=SCORED,
         make=_prefix(kogge_stone, DRAWN, "Kogge-Stone", cell=PG))
register("add-sklansky", task="add", designs=[SKLANSKY], drawn_at=f"N = {DRAWN}", scored_at=SCORED,
         make=_prefix(sklansky, DRAWN, "Sklansky", cell=PG, fan_out=(2, 3)))
register("add-ripple", task="add", designs=[RIPPLE_BYHAND, RIPPLE_PROC, RIPPLE_PROC_M, RIPPLE_MUX],
         drawn_at=f"N = {DRAWN}", scored_at=SCORED, make=_prefix(ripple, DRAWN, "ripple-carry", cell=CARRY_CELL))
register("add-carry-select", task="add", designs=[CARRY_SELECT], drawn_at=SCORED, scored_at=SCORED,
         make=_cs(16))
