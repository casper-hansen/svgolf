"""The clmul task's figures: par's array (an XOR chain per column), the record's balanced XOR tree per column, the
one-level Karatsuba's three products and where they land, and the level-by-level Karatsuba's recursion.

Each model restates its design's index formulas (quoted beside it); tests/site/test_figures.py compares it with the
netlist Yosys elaborates from the design (which signal bits each drawn node reads).
"""

from . import register
from .svg import Drawing

SCORED = "N = 16"


# ---- par: the carry-less array (clmul_n.sv of record 0d28d278)

def array(n):
    """clmul_n.sv: `r[0][j] = a[0] & b[j]`; for i >= 1, `r[i][j] = r[i-1][j+1] ^ (a[i] & b[j])` (j < N-1) and
    `r[i][N-1] = a[i] & b[N-1]`; p[i] = r[i][0], p[N+m] = r[N-1][m+1]. Returns {(i, j): the cell it XORs onto, or
    None for a bare partial product}."""
    return {(i, j): ((i - 1, j + 1) if i > 0 and j < n - 1 else None) for i in range(n) for j in range(n)}


def column_chain(n, k):
    """The cells output bit k is accumulated through, from the top row down (weight k: i + j = k)."""
    cells = sorted((i, k - i) for i in range(n) if 0 <= k - i < n)
    return cells


def array_figure(n):
    cells = array(n)
    hot = set(column_chain(n, n - 1))
    dx, dy, r = 30, 32, 7
    left, top = 40, 40
    cols = 2 * n - 1
    w = left + cols * dx + 30
    h = top + (n - 1) * dy + 66
    d = Drawing(w, h)
    x = lambda wt: left + (cols - 1 - wt) * dx + dx / 2      # noqa: E731
    y = lambda i: top + i * dy                               # noqa: E731
    for wt in range(cols):
        d.text(x(wt), top - 22, str(wt), "t-note", "middle")
    d.text(4, top - 22, "weight", "t-note")
    for (i, j), src in sorted(cells.items(), key=lambda c: (c[0] in hot, c[0])):
        if src:
            on = (i, j) in hot and src in hot
            d.line(x(src[0] + src[1]), y(src[0]), x(i + j), y(i), "e-hot" if on else "e")
    for (i, j), src in sorted(cells.items()):
        on = (i, j) in hot
        if src:
            d.circle(x(i + j), y(i), r, "b-hot" if on else "b")
            d.line(x(i + j) - 4, y(i), x(i + j) + 4, y(i), "e")
            d.line(x(i + j), y(i) - 4, x(i + j), y(i) + 4, "e")
        else:
            d.circle(x(i + j), y(i), 3.5, "n-hot" if on else "n")
    for i in range(n):
        d.text(4, y(i) + 4, f"row {i}", "t-note")
    d.text(4, h - 22, f"Dot: a partial product a[i] & b[j]. Circled plus: that product XORed onto the cell above.",
           "t-note")
    d.text(4, h - 6, f"The accent: output bit {n - 1}, a chain of {len(hot) - 1} XORs as written.", "t-note")
    desc = (f"The carry-less array at N = {n}, by weight (the top bit on the left): row i holds the running XOR of "
            f"the first i + 1 rows of partial products, each cell adding a[i] & b[j] to the cell one weight up in "
            f"the row above. Output bit i < {n} leaves row i at its right end, the top bits leave the last row. As "
            f"written, output bit {n - 1} is a chain of {len(hot) - 1} XORs, marked; synthesis rebalances such "
            "chains.")
    return d, desc


# ---- the balanced XOR tree per column (clmul_tree.sv of record 3aa7a23f)

def tree(n):
    """clmul_tree.sv: each output column k has a tape T[k] of 2N-1 positions; positions 0..N-1 are its N leaves
    (partial products, zero-padded to exactly N); XOR node g = 0..N-2 writes position N+g from positions 2g and
    2g+1 (`T[k][N+g] = T[k][2*g] ^ T[k][2*g+1]`); the root, position 2N-2, drives p[k]. Returns {position:
    (input, input)} of the nodes."""
    return {n + g: (2 * g, 2 * g + 1) for g in range(n - 1)}


def tree_depths(n):
    nodes = tree(n)
    dep = {p: 0 for p in range(n)}
    for p in sorted(nodes):
        a, b = nodes[p]
        dep[p] = 1 + max(dep[a], dep[b])
    return dep


def _tree_panel(d, n, x0, y0, sx, sy):
    """One column's tree at size n, leaves at the top; returns the panel's width."""
    nodes = tree(n)
    dep = tree_depths(n)
    top_dep = max(dep.values())
    pos = {p: (x0 + p * sx + sx / 2, y0) for p in range(n)}
    for p in sorted(nodes):
        a, b = nodes[p]
        pos[p] = ((pos[a][0] + pos[b][0]) / 2, y0 + dep[p] * sy)
    for p, (a, b) in nodes.items():
        for c in (a, b):
            d.line(pos[c][0], pos[c][1], pos[p][0], pos[p][1], "e")
    for p in range(n):
        d.circle(*pos[p], 11, "b")
        d.text(pos[p][0], pos[p][1] + 4, str(p), "t-mono", "middle")
    for p in nodes:
        d.circle(*pos[p], 11, "b")                      # an opaque disc under the accent's soft fill
        d.circle(*pos[p], 11, "b-hot")
        d.text(pos[p][0], pos[p][1] + 4, str(p), "t-mono", "middle")
    root = 2 * n - 2
    d.arrow(pos[root][0], pos[root][1] + 11, pos[root][0], pos[root][1] + 30, "e", head=5)
    d.text(pos[root][0] + 6, pos[root][1] + 30, "p[k]", "t-mono")
    d.text(x0, y0 - 22, f"N = {n}: {n - 1} XORs, {top_dep} levels", "t-head")
    return n * sx


def tree_figure(sizes):
    sx, sy = 34, 46
    top = 44
    depth = max(max(tree_depths(n).values()) for n in sizes)
    w = 16 + sum(n * sx for n in sizes) + 40 * (len(sizes) - 1) + 16
    h = top + depth * sy + 86
    d = Drawing(w, h)
    x = 16
    for n in sizes:
        x += _tree_panel(d, n, x, top, sx, sy) + 40
    d.text(16, h - 22, "Top row: the column's partial products, tape positions 0 to N-1.", "t-note")
    d.text(16, h - 6, "Node N+g XORs positions 2g and 2g+1.", "t-note")
    desc = ("One output column's XOR tree, as the design lays it out on the column's tape, for "
            + " and ".join(f"N = {n}" for n in sizes) + ": the leaves are tape positions 0 to N-1, the column's "
            "partial products, and XOR node g writes position N+g from positions 2g and 2g+1, so the root at "
            "position 2N-2 drives the output bit. "
            + " ".join(f"At N = {n} the tree has {n - 1} XORs in {max(tree_depths(n).values())} levels."
                       for n in sizes)
            + " The same rule makes a perfect tree when N is a power of 2 and a valid tree for any other N.")
    return d, desc


# ---- one-level Karatsuba (clmul_k1.sv of record 62d43f9b)

def karatsuba1(n):
    """clmul_k1.sv: H = (N + 1) / 2; three H x H arrays of par's shape, rl = aL (x) bL, rh = aH (x) bH and
    rm = (aL ^ aH) (x) (bL ^ bH); coefficient c of an array's product is row c's bit 0 for c < H, else bit c-H+1 of
    row H-1. Product bit i of pf (4H-1 bits) is the XOR of: L's coefficient i, (M ^ L ^ Hh)'s coefficient i-H, and
    Hh's coefficient i-2H, where they exist (the five generate families g_c0 .. g_c3). Returns (H, {i: [(array,
    coefficient)]}) for the output bits 0 .. 2N-2."""
    h = (n + 1) // 2
    out = {}
    for i in range(2 * n - 1):
        terms = []
        if 0 <= i <= 2 * h - 2:
            terms.append(("L", i))
        if 0 <= i - h <= 2 * h - 2:
            terms += [("M", i - h), ("L", i - h), ("H", i - h)]
        if 0 <= i - 2 * h <= 2 * h - 2:
            terms.append(("H", i - 2 * h))
        out[i] = terms
    return h, out


def karatsuba1_figure(n):
    h, out = karatsuba1(n)
    nb = 2 * n - 1
    cw = 15
    left, top = 116, 40
    w = left + nb * cw + 20
    rows = [("L = aL·bL", 0, "b"), ("x^H (M + L + H)", h, "b-hot"), ("x^2H · H = aH·bH", 2 * h, "b-blue")]
    rh, gap = 18, 12
    h_px = top + len(rows) * (rh + gap) + rh + 64
    d = Drawing(w, h_px)
    x = lambda i: left + (nb - 1 - i) * cw                   # noqa: E731
    for i in range(nb):
        if i % 2 == 0 or i == nb - 1:
            d.text(x(i) + cw / 2, top - 8, str(i), "t-note", "middle")
    d.text(4, top - 8, "product bit", "t-note")
    for k, (label, shift, cls) in enumerate(rows):
        y = top + k * (rh + gap)
        lo, hi = shift, min(shift + 2 * h - 2, nb - 1)
        d.rect(x(hi), y, (hi - lo + 1) * cw, rh, cls)
        for i in range(lo, hi + 1):
            d.line(x(i), y, x(i), y + rh, "w-faint")
        d.text(4, y + 13, label, "t-mono")
    yo = top + len(rows) * (rh + gap)
    d.rect(x(nb - 1), yo, nb * cw, rh, "b")
    for i in range(nb):
        d.line(x(i), yo, x(i), yo + rh, "w-faint")
        k = len(out[i])
        d.text(x(i) + cw / 2, yo + 13, str(k), "t-note", "middle")
    d.text(4, yo + 13, "terms per bit", "t-mono")
    d.text(4, h_px - 40, f"Three {h} x {h} carry-less arrays: L = aL·bL, H = aH·bH, M = (aL ^ aH)·(bL ^ bH);",
           "t-note")
    d.text(4, h_px - 24, f"{3 * h * h} partial-product ANDs against {n * n} for the {n} x {n} array. Each product "
           f"has {2 * h - 1} coefficients.", "t-note")
    d.text(4, h_px - 8, "A column XORs every bar that covers it; the middle bar is three coefficients in one.",
           "t-note")
    desc = (f"The one-level Karatsuba at N = {n} (H = {h}): three {h} x {h} carry-less products, each "
            f"{2 * h - 1} coefficients long, land in the {nb}-bit product at three offsets: L = aL·bL at bit 0, "
            f"M + L + H at bit {h} (M = (aL ^ aH)·(bL ^ bH)), and H = aH·bH at bit {2 * h}. Each product bit is "
            "the XOR of the bars that cover it; the last row counts the coefficients XORed into each bit.")
    return d, desc


# ---- level-by-level Karatsuba (kara_lv.sv of record 18a301ef)

def clog2(x):
    return (x - 1).bit_length()


def karatsuba_tree(n):
    """kara_lv.sv: L = $clog2((N + 3) / 4) levels, operands padded to P = 4 * 2^L bits; level l holds 3^l nodes,
    node t's operands in the slots `av[l][t*(P>>l) +: (P>>l)]`; going down, node t hands child 3t its low halves,
    3t+1 its high halves and 3t+2 their XOR (the g_split family); at level L each node is a 4 x 4 schoolbook
    product (g_base), and going up each node combines its children's products (g_comb). Returns (L, P, {(l, t):
    (operand width, how it is made from its parent: "operands" | "low" | "high" | "low ^ high")})."""
    levels = clog2((n + 3) // 4)
    p = 4 * 2 ** levels
    nodes = {(0, 0): (p, "operands")}
    for l in range(levels):
        for t in range(3 ** l):
            for c, kind in enumerate(("low", "high", "low ^ high")):
                nodes[(l + 1, 3 * t + c)] = (p >> (l + 1), kind)
    return levels, p, nodes


def karatsuba_tree_figure(n):
    levels, p, nodes = karatsuba_tree(n)
    leaves = 3 ** levels
    bw, bh, sx, sy = 46, 34, 52, 74
    left, top = 64, 30
    w = left + leaves * sx + 16
    h = top + levels * sy + bh + 96
    d = Drawing(w, h)
    pos = {}
    for t in range(leaves):
        pos[(levels, t)] = (left + t * sx + sx / 2, top + levels * sy)
    for l in range(levels - 1, -1, -1):
        for t in range(3 ** l):
            xs = [pos[(l + 1, 3 * t + c)][0] for c in range(3)]
            pos[(l, t)] = (sum(xs) / 3, top + l * sy)
    for (l, t), (width, kind) in nodes.items():
        if l == 0:
            continue
        px, py = pos[(l - 1, t // 3)]
        x, y = pos[(l, t)]
        d.line(px, py + bh / 2, x, y - bh / 2, "e-hot" if kind == "low ^ high" else "e")
    for (l, t), (width, kind) in nodes.items():
        x, y = pos[(l, t)]
        cls = "b-blue" if l == levels else ("b-hot" if kind == "low ^ high" else "b")
        d.rect(x - bw / 2, y - bh / 2, bw, bh, cls)
        d.text(x, y - 1, f"{width}×{width}", "t-mono", "middle")
        d.text(x, y + 12, {"operands": "a·b", "low": "lo", "high": "hi", "low ^ high": "lo^hi"}[kind], "t-note",
               "middle")
    for l in range(levels + 1):
        d.text(4, top + l * sy - 2, f"level {l}", "t-note")
        d.text(4, top + l * sy + 12, f"{3 ** l} node{'s' if l else ''}", "t-note")
    d.text(4, h - 56, "Down: each node hands its children the low halves, the high halves", "t-note")
    d.text(4, h - 40, f"and their XOR (accent). At the bottom: {leaves} 4×4 schoolbook products.", "t-note")
    d.text(4, h - 24, "Up: each node combines its children's products L, H, M as", "t-note")
    d.text(4, h - 8, "L + x^m (M + L + H) + x^2m H, column by column.", "t-note")
    desc = (f"The Karatsuba recursion at N = {n}: operands padded to {p} bits, {levels} levels of splitting. The "
            "root multiplies the two operands; each node hands its three children the low halves, the high halves "
            f"and the XOR of the halves, so level l has 3 to the l nodes, and level {levels}'s {leaves} nodes are "
            f"4 x 4 schoolbook products, {16 * leaves} partial-product ANDs in all. Going back up, each node "
            "combines its three children's products as L + x^m (M + L + H) + x^2m H.")
    return d, desc


def _make(fn, arg, min_w):
    def make():
        d, desc = fn(arg)
        return d, desc, min_w
    return make


ARRAY = "4637e72ba5368a35cf427b948aeab0ba3ce8aa6c2f249d2ab90f1ef44372f1ad"         # clmul_n.sv (par), 0d28d278
TREE = "6085340d779a98cdfb85df1fe3817236abdbc9fb787bc7d0d8d3274ab1ad7419"          # clmul_tree.sv, 3aa7a23f
K1 = "f2806e9f3d9bf621bb5aa7875a3a7b6c38fcd644ec0ad5441b81f45df955c4a6"            # clmul_k1.sv, 62d43f9b
KLV = "0cc4457548ad64997b461152c637a16fd3a1f8136b50ee64e3aeb75120309ed6"           # kara_lv.sv, 18a301ef

register("clmul-array", task="clmul", designs=[ARRAY], drawn_at="N = 8", scored_at=SCORED,
         make=_make(array_figure, 8, 420))
register("clmul-column-tree", task="clmul", designs=[TREE], drawn_at="N = 8 and N = 6", scored_at=SCORED,
         make=_make(tree_figure, (8, 6), 460))
register("clmul-karatsuba-1", task="clmul", designs=[K1], drawn_at=SCORED, scored_at=SCORED,
         make=_make(karatsuba1_figure, 16, 480))
register("clmul-karatsuba-tree", task="clmul", designs=[KLV], drawn_at=SCORED, scored_at=SCORED,
         make=_make(karatsuba_tree_figure, 16, 440))
