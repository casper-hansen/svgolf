"""The mul task's figures: the record's heap of 4:2 compressors, par's array of ripple-carry rows, and the Dadda
tree's reduction stage by stage.

Each model restates its design's index formulas (quoted beside it); tests/site/test_figures.py compares it with the
netlist Yosys elaborates from the design (which signal bits each cell reads).
"""

from . import register
from .svg import Drawing

SCORED = "N = 16"


# ---- the two-row-leaf 4:2 heap (solution.sv of record 7d6d9bd9; the layout of mul_tree_h.sv)

def heap(n):
    """solution.sv: `H = (N + 1) / 2` leaves in binary-heap numbering: leaf j is node H-1+j and holds the
    partial-product rows 2j and 2j+1 (`S[H-1+j][c] = bb[2*j] & ...`, `C[H-1+j][c] = ... & bb[2*j+1]`); internal
    node k < H-1 is a 4:2 compressor on its children 2k+1 and 2k+2; node 0's two rows go to the ripple final adder.
    Returns (H, {leaf node: (row, row)}, {internal node: (child, child)})."""
    h = (n + 1) // 2
    leaves = {h - 1 + j: (2 * j, 2 * j + 1) for j in range(h)}
    inner = {k: (2 * k + 1, 2 * k + 2) for k in range(h - 1)}
    return h, leaves, inner


def depth_of(k):
    """A heap node's depth (the root's is 0)."""
    return (k + 1).bit_length() - 1


def heap_figure(n):
    h, leaves, inner = heap(n)
    depth = max(depth_of(k) for k in leaves)
    bw, bh, sx, sy = 54, 26, 64, 62
    left, top = 16, 22
    w = left + h * sx + 128
    h_px = top + (depth + 1) * sy + 74
    d = Drawing(w, h_px)
    pos = {}
    for idx, k in enumerate(sorted(leaves)):
        pos[k] = (left + idx * sx + bw / 2, top + 14)
    for k in sorted(inner, reverse=True):
        a, b = inner[k]
        pos[k] = ((pos[a][0] + pos[b][0]) / 2, top + 14 + (depth - depth_of(k)) * sy)
    for k, (a, b) in inner.items():
        for c in (a, b):
            d.line(pos[c][0], pos[c][1] + bh / 2, pos[k][0], pos[k][1] - bh / 2, "e")
    for k, rows in leaves.items():
        x, y = pos[k]
        d.rect(x - bw / 2, y - bh / 2, bw, bh, "b")
        d.text(x, y + 4, f"pp {rows[0]},{rows[1]}", "t-mono", "middle")
    for k in inner:
        x, y = pos[k]
        d.rect(x - bw / 2, y - bh / 2, bw, bh, "b-hot")
        d.text(x, y + 4, "4:2", "t-head", "middle")
    rx, ry = pos[0]
    fy = ry + sy - 6
    d.line(rx, ry + bh / 2, rx, fy - bh / 2, "e")
    d.rect(rx - 70, fy - bh / 2, 140, bh, "b-blue")
    d.text(rx, fy + 4, "ripple adder", "t-head", "middle")
    d.arrow(rx, fy + bh / 2, rx, fy + bh / 2 + 18, "e", head=5)
    d.text(rx + 8, fy + bh / 2 + 16, f"p (2N = {2 * n} bits)", "t-mono")
    # the rows per level, on the right
    xr = left + h * sx + 8
    count = 2 * h
    for lev in range(depth, -1, -1):
        y = top + 14 + (depth - lev) * sy + 4
        nodes = sum(1 for k in list(leaves) + list(inner) if depth_of(k) == lev)
        what = "leaves" if lev == depth else ("root" if lev == 0 else "nodes")
        d.text(xr, y, f"{nodes} {what}: {count} rows" if lev else f"root: {count} rows", "t-note")
        count //= 2
    d.text(xr, fy + 4, "1 row", "t-note")
    desc = (f"The heap of 4:2 compressors at N = {n}: the {n} partial-product rows enter in pairs at {h} leaves "
            f"(rows 0 and 1, rows 2 and 3, and so on); each 4:2 node, two stacked rows of full adders, turns its two "
            f"children's pairs of rows into one pair, so {depth} levels of nodes ({h - 1} nodes) bring the {2 * h} "
            "rows down to two, which a ripple-carry adder adds into the product.")
    return d, desc


# ---- par's array multiplier (mul_n_byhand.sv of record cc95273d: par's design, byte for byte)

def array(n):
    """mul_n_byhand.sv: row 0 is pp[0]; row i = 1..N-1 is N full adders, cell (i, j) adding `s[i-1][j+1]` (the
    previous row's sum one place up, `s[i-1][N]` its carry out) and `pp[i][j] = a[j] & b[i]` to the ripple carry
    `c[i][j]`, giving `s[i][j]` and `c[i][j+1]`; p[i] = s[i][0], the top half s[N-1][N:1]. Returns the cells'
    inputs from other cells: {(i, j): [(i', j'), ...]} (the carry from (i, j-1), the sum or carry out from row i-1)."""
    ins = {}
    for i in range(1, n):
        for j in range(n):
            src = []
            if j > 0:
                src.append((i, j - 1))                 # c[i][j], the carry of the cell before
            if i > 1:
                src.append((i - 1, j + 1) if j + 1 < n else (i - 1, n - 1))   # s[i-1][j+1]; s[i-1][N] = c[i-1][N]
            ins[(i, j)] = src
    return ins


def longest_path(ins):
    """The longest chain of cells (one of them, the first found in a fixed order), as a list of cells."""
    best = {}
    for cell in sorted(ins):                           # rows in order, cells in order: inputs come first
        prev = max(ins[cell], key=lambda c: (best[c][0], c), default=None)
        best[cell] = (1 + (best[prev][0] if prev else 0), prev)
    end = max(best, key=lambda c: (best[c][0], c))
    path = []
    while end is not None:
        path.append(end)
        end = best[end][1]
    return path[::-1]


def path_words(path):
    """The chain in words, row by row: "2 in each of rows 1 to 6, then 8 along row 7"."""
    per = {}
    for i, _ in path:
        per[i] = per.get(i, 0) + 1
    rows = sorted(per)
    head = [r for r in rows[:-1] if per[r] == per[rows[0]]]
    if len(head) == len(rows) - 1 and head:
        return (f"{per[rows[0]]} in each of rows {rows[0]} to {head[-1]}, then {per[rows[-1]]} along row "
                f"{rows[-1]}")
    return ", ".join(f"{per[r]} in row {r}" for r in rows)


def array_figure(n):
    ins = array(n)
    path = longest_path(ins)
    on = set(path)
    dx, dy, sq = 30, 34, 16
    left, top = 34, 40
    cols = 2 * n - 1
    w = left + cols * dx + 52
    h = top + n * dy + 80
    d = Drawing(w, h)
    x = lambda wt: left + (cols - 1 - wt) * dx + dx / 2      # noqa: E731  (weight wt; the top bit on the left)
    y = lambda i: top + i * dy                               # noqa: E731
    for wt in range(cols):
        d.text(x(wt), top - 22, str(wt), "t-note", "middle")
    d.text(x(0) + 12, top - 22, "weight", "t-note")
    for j in range(1, n):                                    # row 0's bits j >= 1 go down into row 1
        d.line(x(j), y(0), x(j), y(1), "e")
    for j in range(n):                                       # row 0: pp[0], no adder
        d.circle(x(j), y(0), 3.5, "n")
    d.text(4, y(0) + 4, "pp0", "t-note")
    edges = []
    for (i, j), src in ins.items():
        for c in src:
            hot = c in on and (i, j) in on and path.index((i, j)) == path.index(c) + 1
            edges.append((hot, c, (i, j)))
    for hot, (i0, j0), (i1, j1) in sorted(edges):
        d.line(x(i0 + j0), y(i0), x(i1 + j1), y(i1), "e-hot" if hot else "e")
    for (i, j) in sorted(ins):
        d.rect(x(i + j) - sq / 2, y(i) - sq / 2, sq, sq, "b-hot" if (i, j) in on else "b")
    for i in range(1, n):
        d.text(4, y(i) + 4, f"row {i}", "t-note")
    shape = path_words(path)
    d.text(4, h - 40, f"{len(ins)} full adders. Across: the carry to the next weight; down: the sum to the next row.",
           "t-note")
    d.text(4, h - 24, f"The accent marks a longest chain of adders, {len(path)} long:", "t-note")
    d.text(4, h - 8, f"{shape}.", "t-note")
    desc = (f"The array multiplier at N = {n}, drawn by weight (the top bit on the left): row 0 is the partial "
            f"product a & b[0]; each row below is {n} full adders that add the next partial-product row to the "
            f"previous row's sum, the carry rippling along the row. Product bit i leaves at row i's rightmost cell, "
            f"the top half at the last row. A longest chain of adders, {len(path)} long, is marked: {shape}.")
    return d, desc


# ---- the Dadda tree (dadda_rc.sv of record 707464b7)

def dadda_heights(limit):
    """The Dadda heights d(0) = 2, d(r+1) = floor(3 d(r) / 2): 2, 3, 4, 6, 9, 13, ... up to the first >= limit."""
    d = [2]
    while d[-1] < limit:
        d.append(3 * d[-1] // 2)
    return d


def dadda(n):
    """dadda_rc.sv: columns k = 0 .. 2N-1; before stage 0 column k holds min(k + 1, 2N - 1 - k) partial products;
    there are S stages, S = the number of Dadda heights below N; stage s brings every column down to t = d(S-1-s)
    bits (u = N at s = 0, else floor(3t / 2), the height before it), with, in column k (m = min(k, 2N - k)):
    f = max(0, min(m, u) - t) full adders (one fewer at s = 0, k = N) on bits 3q .. 3q+2, then h half adders (1 for
    t <= k < u and at s = 0, k = N) on bits 3f, 3f+1; the height after it is min(k + 1, t) for k <= 2N - t, else
    2N - 1 - k. Returns (the heights before stage 0, [{"t", "before", "adders": [(f, h) per column], "after"}])."""
    d = dadda_heights(n)
    stages_n = sum(1 for x in d if x < n)
    h0 = [min(k + 1, 2 * n - 1 - k) if k < 2 * n - 1 else 0 for k in range(2 * n)]
    stages, before = [], h0
    for s in range(stages_n):
        t = d[stages_n - 1 - s]
        u = n if s == 0 else 3 * t // 2
        adders = []
        for k in range(2 * n):
            m = min(k, 2 * n - k)
            f = max(0, min(m, u) - t) - (1 if s == 0 and k == n else 0)
            h = 1 if (t <= k < u) or (s == 0 and k == n) else 0
            adders.append((f, h))
        after = [min(k + 1, t) if k <= 2 * n - t else 2 * n - 1 - k for k in range(2 * n)]
        stages.append({"t": t, "before": before, "adders": adders, "after": after})
        before = after
    return h0, stages


def dadda_figure(n):
    h0, stages = dadda(n)
    cols = 2 * n
    dx, dy, r = 16, 11, 3.5
    left, top, gap = 104, 16, 26
    panels = [(("partial products" if i == 0 else f"after stage {i}"), s["before"], s["adders"], s["t"])
              for i, s in enumerate(stages)] + [(f"after stage {len(stages)}", stages[-1]["after"], None, None)]
    heights = [max(p[1]) for p in panels]
    w = left + cols * dx + 12
    h = top + sum(hh * dy + gap for hh in heights) + 56
    d = Drawing(w, h)
    x = lambda k: left + (cols - 1 - k) * dx + dx / 2      # noqa: E731
    y0 = top
    nfa = nha = 0
    for s, ((label, hs, adders, t), hh) in enumerate(zip(panels, heights)):
        d.text(4, y0 + 9, label, "t-note")
        if t is not None:
            d.text(4, y0 + 23, f"stage {s + 1}: to {t} rows", "t-note")
        if adders:                                  # the adders first, the dots over them
            for k, (f, ha) in enumerate(adders):
                for q in range(f):
                    d.rect(x(k) - 6, y0 + 3 * q * dy + 1, 12, 3 * dy - 2, "b-hot")
                    nfa += 1
                for q in range(ha):
                    d.rect(x(k) - 6, y0 + 3 * f * dy + 1, 12, 2 * dy - 2, "b-blue")
                    nha += 1
        for k in range(cols):
            for i in range(hs[k]):
                d.circle(x(k), y0 + i * dy + dy / 2, r, "n")
        y0 += hh * dy + gap
    d.text(4, y0 + 4, "then a ripple-carry adder on the two rows", "t-note")
    d.text(4, h - 24, "Accent: a full adder, three bits to a sum here and a carry into the next", "t-note")
    d.text(4, h - 8, "column on the left; blue: a half adder, two bits.", "t-note")
    desc = (f"The Dadda reduction at N = {n}, one dot diagram per stage, columns of weight 0 on the right to "
            f"{cols - 1} on the left: the partial products, then {len(stages)} stages that bring every column down to "
            + ", ".join(str(s["t"]) for s in stages)
            + f" bits. Each stage puts full adders (3 bits to a sum in the column and a carry into the next) and "
            f"half adders only where a column is over the stage's height: {nfa} full and {nha} half adders in all. "
            "The two rows left go to a ripple-carry adder.")
    return d, desc


def _make(fn, n, min_w):
    def make():
        d, desc = fn(n)
        return d, desc, min_w
    return make


DADDA = "e4d405a7efe7dc72a192166bf3409d033b90a673f52ed3cf581032c38d78a4bb"       # dadda_rc.sv, 707464b7
HEAP_42 = "9f7eb149ac237cd89d414f5de7f9e021bae46f339b13f5db8726e6f5a635bab5"     # solution.sv, 7d6d9bd9
ARRAY_BYHAND = "66686a9d4c60cc9484a7fc673c5a8e2b73f30e25f9f6ddaccccbf3d51bf3bd23"  # mul_n_byhand.sv (par), cc95273d

register("mul-heap-42", task="mul", designs=[HEAP_42], drawn_at=SCORED, scored_at=SCORED,
         make=_make(heap_figure, 16, 520))
register("mul-array", task="mul", designs=[ARRAY_BYHAND], drawn_at="N = 8", scored_at=SCORED,
         make=_make(array_figure, 8, 420))
register("mul-dadda", task="mul", designs=[DADDA], drawn_at="N = 8", scored_at=SCORED,
         make=_make(dadda_figure, 8, 330))
