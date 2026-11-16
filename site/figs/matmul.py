"""The matmul task's figures: each frontier design's schedule at the scoring point, cycle by cycle, and the spatial
pipeline's items in flight.

C = A·B with C[i][j] = sum over k of A[i][k]·B[k][j]: "step k" is the k-th term of every dot product. The models
restate the designs' always_ff bodies (the counter, the shifts, when `done` rises); tests/site/test_figures.py
simulates each design (Icarus Verilog, at the scoring point N = 4, W = 8, AccW = 32, on random matrices) and checks,
after every edge the figure shows, each entry of C (and P) against the steps the figure says it holds, and `done`.
"""

from . import register
from .svg import Drawing

N = 4
SCORED = "N = 4, W = 8, AccW = 32"


def schedule(variant, n=N):
    """[{"edge": t, "read": [steps whose products are formed in the cycle ending at edge t], "P": [steps the product
    register holds after edge t] or None, "C": [steps every C entry holds after edge t], "done": bool}] for the edges
    the figure shows, edge 0 being the start edge (A, B captured, C cleared).
      g1    matmul_g1.sv (par): one step per busy cycle, `k == N - 1` ends it; C holds afterwards.
      two   solution2.sv: two steps per cycle (`k + 2 >= N` ends it).
      four  solution.sv: four steps per cycle (`k + 4 >= N` ends it).
      free  f10.sv: one step per cycle with no hold multiplexer: after N steps b_sh is all zeros, so C keeps adding 0.
      reg   g2.sv: the product register P takes step t - 1 at edge t, C adds P; `k == N` ends it, one edge later."""
    per = {"g1": 1, "two": 2, "four": 4, "free": 1, "reg": 1}[variant]
    cycles = -(-n // per)                                  # busy cycles: ceil(N / steps per cycle)
    out = []
    if variant == "reg":
        for t in range(1, n + 2):
            step = t - 1
            out.append({"edge": t, "read": [step] if step < n else [], "P": [step] if step < n else [],
                        "C": list(range(min(t - 1, n))), "done": t >= n + 1, "zeros": step >= n})
        return out
    last = cycles + (1 if variant == "free" else 0)
    for t in range(1, last + 1):
        busy = t <= cycles
        read = [k for k in range(per * (t - 1), per * t) if k < n] if (busy or variant == "free") else []
        out.append({"edge": t, "read": read, "P": None, "C": list(range(min(per * t, n))) if busy else
                    list(range(n)), "done": t >= cycles, "zeros": variant == "free" and not busy})
    return out


def _grid(d, x, y, n, on, by_col, cls_on, sq=7):
    """A mini n x n matrix, the columns (by_col) or rows in `on` filled."""
    for r in range(n):
        for c in range(n):
            hit = (c if by_col else r) in on
            d.rect(x + c * (sq + 1), y + r * (sq + 1), sq, sq, cls_on if hit else "b")


def _steps(ks):
    if not ks:
        return "0"
    return f"k {ks[0]}" if len(ks) == 1 else f"k {ks[0]}–{ks[-1]}"


def schedule_figure(variant):
    rows = schedule(variant)
    has_p = variant == "reg"
    colw, left, top = 84, 92, 40
    w = left + (len(rows) + 1) * colw + 12
    labels = [("A columns,", "B rows read")] + ([("P holds",)] if has_p else []) + [("C holds",), ("done",)]
    rh = [40] + ([24] if has_p else []) + [24, 22]
    h = top + sum(rh) + 64
    d = Drawing(w, h)
    d.text(4, top - 18, "edge", "t-note")
    y = top
    for lab, hh in zip(labels, rh):
        for k, line in enumerate(lab):
            d.text(4, y + 16 + 14 * k, line, "t-note")
        y += hh
    x = left
    d.text(x + colw / 2 - 6, top - 18, "0", "t-mono", "middle")
    d.text(x, top + 22, "start:", "t-note")
    d.text(x, top + 36, "load A, B", "t-note")
    yc = top + rh[0] + (rh[1] if has_p else 0)
    if has_p:
        d.text(x, top + rh[0] + 16, "0", "t-mono")
    d.text(x, yc + 16, "0", "t-mono")
    d.text(x, yc + rh[-2] + 15, "0", "t-note")
    for c, s in enumerate(rows, 1):
        x = left + c * colw
        d.text(x + colw / 2 - 6, top - 18, str(s["edge"]), "t-mono", "middle")
        y = top + 4
        if s["read"]:
            _grid(d, x, y, N, s["read"], True, "b-hot")
            _grid(d, x + 36, y, N, s["read"], False, "b-blue")
        elif s.get("zeros"):
            d.text(x, y + 18, "b_sh = 0:", "t-note")
            d.text(x, y + 32, "product 0", "t-note")
        else:
            d.text(x, y + 18, "idle", "t-note")
        y = top + rh[0]
        if has_p:
            d.text(x, y + 16, _steps(s["P"]) if s["P"] else "0", "t-mono")
            y += rh[1]
        full = len(s["C"]) == N
        d.text(x, y + 16, "A·B" if full else _steps(s["C"]), "t-hot" if full else "t-mono")
        y += rh[-2]
        d.text(x, y + 15, "1" if s["done"] else "0", "t-hot" if s["done"] else "t-note")
    d.text(4, h - 40, "Left grid: A, its columns k read (accent); right grid: B, its rows k read (blue).",
           "t-note")
    d.text(4, h - 24, "\"k 0–1\": every C[i][j] holds the terms k = 0 and 1 of its dot product;",
           "t-note")
    d.text(4, h - 8, "\"A·B\": the whole product.", "t-note")
    lat = next(s["edge"] for s in rows if s["done"])
    steps = {"g1": "one step", "two": "two steps", "four": "four steps", "free": "one step", "reg": "one step"}
    desc = (f"The schedule at N = {N}, edge by edge after the start edge: in each busy cycle all {N * N} "
            f"multiply-accumulate units take {steps[variant]} of their dot products, reading column k of A and row k "
            f"of B. done rises on edge {lat}, so the product takes {lat} cycles."
            + (" The product register P holds step t - 1 after edge t and C adds it one edge later, so C is one step "
               "behind P." if variant == "reg" else "")
            + (" With no hold multiplexer the units keep adding after the last step, but B's shift register has "
               "shifted out to zeros, so they add 0." if variant == "free" else ""))
    return d, desc


# ---- the spatial pipeline (spatial_pipeline.sv of record d8a9cc68)

def pipeline(n=N):
    """spatial_pipeline.sv: the counter chain issues item m = (i, j) = divmod(m, N) after edge m (m < N², row-major;
    cc_run ends after the last); the stages are registered one after another: the operand registers pcu_va/pcu_vb
    (stage 0), the N lane products in the tree's leaves (stage 1), the L = $clog2(N) levels of the adder tree
    (stages 2 .. L+1, the root last), and the output shift of C when the root's valid bit is set. So after edge t
    stage s holds item t - 1 - s, and item m enters C on edge m + L + 3; done rises with the last. Returns (L,
    [stage names], {edge: [item per stage or None]}, {edge: item entering C}, the edge done rises)."""
    levels = (n - 1).bit_length()
    names = ["counter (i, j)", "operands"] + ["products"] + [f"tree level {k}" for k in range(1, levels)] + ["root"]
    items = n * n
    last = items - 1 + levels + 3
    table, into_c = {}, {}
    for t in range(0, last + 1):
        row = [t if t < items else None]                   # the counter's item after edge t
        for s in range(levels + 2):
            m = t - 1 - s
            row.append(m if 0 <= m < items else None)
        table[t] = row
        m = t - (levels + 3)
        if 0 <= m < items:
            into_c[t] = m
    return levels, names, table, into_c, last


def pipeline_figure():
    levels, names, table, into_c, done = pipeline()
    cw, rh = 21, 22
    left, top = 104, 40
    edges = sorted(table)
    w = left + len(edges) * cw + 12
    nrows = len(names) + 1
    h = top + nrows * rh + 58
    d = Drawing(w, h)
    d.text(4, top - 16, "edge", "t-note")
    for c, t in enumerate(edges):
        if t % 2 == 0 or t == done:
            d.text(left + c * cw + cw / 2, top - 16, str(t), "t-note", "middle")
    for r, name in enumerate(names + ["into C"]):
        d.text(4, top + r * rh + 15, name, "t-note")
    for c, t in enumerate(edges):
        x = left + c * cw
        for r in range(len(names)):
            m = table[t][r]
            if m is not None:
                d.rect(x + 1, top + r * rh + 2, cw - 2, rh - 4, "b-hot" if m == N * N - 1 else "b")
                d.text(x + cw / 2, top + r * rh + 15, f"{m // N}{m % N}", "t-mono", "middle")
        if t in into_c:
            m = into_c[t]
            r = len(names)
            d.rect(x + 1, top + r * rh + 2, cw - 2, rh - 4, "b-blue")
            d.text(x + cw / 2, top + r * rh + 15, f"{m // N}{m % N}", "t-mono", "middle")
    x = left + edges.index(done) * cw
    d.text(x + cw / 2, top + nrows * rh + 14, "done", "t-hot", "middle")
    d.text(4, h - 24, "\"ij\": the item C[i][j], issued one per cycle, row-major; the accent follows the last one.",
           "t-note")
    d.text(4, h - 8, f"Each result shifts into C {levels + 3} edges after its item is issued.", "t-note")
    desc = (f"The spatial pipeline at N = {N}: the counter issues one item (i, j) per cycle, row-major, and each "
            f"item moves one stage per edge: the operand registers, the {N} lane products, the adder tree's "
            f"{levels} levels, then into C. Up to {levels + 3} items are in flight at once; the {N * N}th result "
            f"enters C on edge {done}, when done rises.")
    return d, desc


G1 = "8dbb8b29b4ba583cf4b0660c3b5cd14d497a4ec400a3956a6aa98a44e6514ca7"       # matmul_g1.sv (par), c7773627
FOUR = "b6357f45fe9705bc9c9fabfb23bc720837ad203ff17ccb91cdf0aca5e4e8378a"     # solution.sv, 0ac973a1
TWO = "46a27216877db9ed64f86d202e02b0dec7117ed48e87a574d1d4d3e0b7ae2f4e"      # solution2.sv, f0b6b743
FREE = "73385c65005d82ccb977d186be60dc1b7facf38d205672c688dbc4eef384cca4"     # f10.sv, 688b1fea
REG = "dcc9612256623d5588699cbd0c93c9331f02927e1c960ddabe3a9774b1683fa8"      # g2.sv, bade2c48
PIPE = "308cf75fcf3041cee37886277a811731ba37dc04e7fabf345e57f152f257067d"     # spatial_pipeline.sv, d8a9cc68

for _name, _variant, _sha in (("matmul-schedule-g1", "g1", G1), ("matmul-schedule-four", "four", FOUR),
                              ("matmul-schedule-two", "two", TWO), ("matmul-schedule-free", "free", FREE),
                              ("matmul-schedule-reg", "reg", REG)):
    register(_name, task="matmul", designs=[_sha], drawn_at=SCORED, scored_at=SCORED,
             make=(lambda v: lambda: (*schedule_figure(v), 300))(_variant))
register("matmul-pipeline", task="matmul", designs=[PIPE], drawn_at=SCORED, scored_at=SCORED,
         make=lambda: (*pipeline_figure(), 440))
