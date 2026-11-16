"""The fdivp task's figures: the radix-4 SRT divider's digit selection, and the two quotient cores side by side.

The models restate the designs' constants and generate loops (quoted beside them); tests/site/test_figures.py
checks them against the designs: the selection by Yosys `eval` of the SRT design's own threshold and comparison
nets, the cores by the arithmetic cells of the netlists Yosys elaborates at binary16 (W = 5, P = 11).
"""

from . import register
from .svg import Drawing

SCORED = "W = 5, P = 11"

# fdivp_srt.sv's selection constants (Wally's mks2/mks1/mks0/mksm1 + 64), by the divisor's 3 bits after its leading
# one, da = 0..7 (the design's comment and its four ?: trees t2, t1, t0, tm)
THRESHOLDS = {
    2: (76, 78, 80, 81, 82, 84, 86, 87),
    1: (68, 68, 70, 70, 70, 72, 72, 72),
    0: (60, 60, 58, 58, 58, 56, 56, 56),
    -1: (51, 50, 48, 47, 46, 44, 42, 41),
}


def digit(yb, da):
    """The digit fdivp_srt.sv selects for the 7-bit estimate `yb` (sign bit flipped: yb - 64 is the estimate in
    eighths of the divisor's leading one) and the divisor bits `da`: `g2 = yb >= t2`, ..., `gm = yb >= tm`, and the
    multiple's priority chain `g2 ? 2 : g1 ? 1 : g0 ? 0 : gm ? -1 : -2`."""
    for q in (2, 1, 0, -1):
        if yb >= THRESHOLDS[q][da]:
            return q
    return -2


def selection_figure():
    left, top, cw, unit = 64, 24, 44, 40
    lo, hi = -3.5, 3.5
    w = left + 8 * cw + 70
    h = top + (hi - lo) * unit + 96
    d = Drawing(w, h)
    ys = lambda v: top + (hi - v) * unit                   # noqa: E731
    # the regions, column by column, from the design's thresholds
    for da in range(8):
        x = left + da * cw
        bounds = [hi] + [(THRESHOLDS[q][da] - 64) / 8 for q in (2, 1, 0, -1)] + [lo]
        for q, (b_hi, b_lo) in zip((2, 1, 0, -1, -2), zip(bounds, bounds[1:])):
            cls = {2: "b-on", 1: "b-soft", 0: None, -1: "b-soft", -2: "b-on"}[q]
            top_v, bot_v = min(b_hi, hi), max(b_lo, lo)
            if cls:
                d.rect(x, ys(top_v), cw, ys(bot_v) - ys(top_v), cls)
    # the thresholds as staircases
    for q in (2, 1, 0, -1):
        pts = []
        for da in range(8):
            v = (THRESHOLDS[q][da] - 64) / 8
            pts += [(left + da * cw, ys(v)), (left + (da + 1) * cw, ys(v))]
        d.poly(pts, "e-hot")
    # the digit labels in the middle column
    for q, v in ((2, 2.9), (1, 1.35), (0, 0.0), (-1, -1.35), (-2, -2.9)):
        d.text(left + 8 * cw + 8, ys(v) + 4, f"q = {q}", "t-head")
    # axes
    d.line(left, ys(lo), left + 8 * cw, ys(lo), "w")
    d.line(left, ys(lo), left, ys(hi), "w")
    for v in range(-3, 4):
        d.text(left - 6, ys(v) + 4, f"{v:+d}" if v else "0", "t-note", "end")
        d.line(left - 3, ys(v), left, ys(v), "w")
    for k in range(9):
        if k % 2 == 0:
            d.text(left + k * cw, ys(lo) + 16, f"{1 + k / 8:g}", "t-note", "middle")
    d.text(left + 4 * cw, ys(lo) + 34, "divisor d (its 3 bits after the leading one: 8 columns)", "t-note", "middle")
    d.text(4, top - 8, "remainder estimate (units of d's leading one)", "t-note")
    d.text(4, h - 24, "Accent: the design's four staircases of constants. At or above the top one", "t-note")
    d.text(4, h - 8, "the digit is 2; below the lowest, -2.", "t-note")
    desc = ("The radix-4 SRT digit selection of the divider: across, the divisor in [1, 2) in eight columns, one per "
            "value of its three bits after the leading one; up, the estimate of the partial remainder from the top "
            "bits of its carry-save form, in units of the divisor's leading one. Four staircases of constants, one value per "
            "column, split each column into the five digits 2, 1, 0, -1 and -2: an estimate at or above the top "
            "staircase gives 2, below the lowest -2. Choosing a digit takes an 8-bit estimate and four 7-bit "
            "comparisons with constants, never a full-width subtraction.")
    return d, desc


# ---- the two quotient cores at binary16

def cores(p):
    """fdivp.sv (par): `for (k = 0; k < P + 2; ...)`: step k compares and subtracts `rr[k] - nbx` on P + 1 bits and
    makes one quotient bit. fdivp_srt.sv: N = (P + 2) / 2 + 1 stages, `for (k = 0; k < N; ...)`: stage k adds the
    top 8 bits of the carry-save remainder (`es[k] = ws[k][P+5:P-2] + wc[k][P+5:P-2]`), compares the 7-bit estimate
    with four constants and makes one carry-save row (`sm`, `cy`) and one radix-4 digit, two quotient bits; then one
    adder of RW = P + 6 bits sums the remainder (`rs = ws[N] + wc[N]`) for the final correction and the sticky bit.
    Returns {"restoring": (steps, subtract width), "srt": (stages, estimate width, final adder width)}."""
    return {"restoring": (p + 2, p + 1), "srt": ((p + 2) // 2 + 1, 8, p + 6)}


def cores_figure(p):
    c = cores(p)
    steps, sw = c["restoring"]
    stages, ew, fw = c["srt"]
    bit = 30
    left, top = 12, 30
    w = left + max(steps, 2 * stages + 2) * bit + 24
    h = 250
    d = Drawing(w, h)
    y1, y2 = top + 22, top + 110
    d.text(left, top, f"restoring (par): {steps} steps, one quotient bit each", "t-head")
    for k in range(steps):
        x = left + k * bit
        d.rect(x + 1, y1, bit - 2, 30, "b")
        d.text(x + bit / 2, y1 + 19, "1", "t-mono", "middle")
        if k:
            d.line(x - 1, y1 + 15, x + 1, y1 + 15, "e")
    d.text(left, y1 + 48, f"each step: a {sw}-bit compare and a {sw}-bit subtraction, whose borrow ripples through "
           f"all {sw} bits", "t-note")
    d.text(left, y2 - 8, f"radix-4 SRT (the record): {stages} stages, two quotient bits each", "t-head")
    for k in range(stages):
        x = left + 2 * k * bit
        d.rect(x + 1, y2 + 14, 2 * bit - 2, 30, "b-hot")
        d.text(x + bit, y2 + 33, "2", "t-mono", "middle")
    x = left + 2 * stages * bit + 6
    d.rect(x, y2 + 14, 2 * bit - 8, 30, "b-blue")
    d.text(x + bit - 4, y2 + 33, "+", "t-head", "middle")
    d.text(left, y2 + 62, f"each stage: an {ew}-bit estimate add, four compares with constants and a carry-save row",
           "t-note")
    d.text(left, y2 + 78, "(no carry chain across the remainder); blue: one adder at the end, "
           f"{fw} bits, sums the", "t-note")
    d.text(left, y2 + 94, "remainder for the last correction and the sticky bit", "t-note")
    desc = (f"The two quotient cores at W = 5, P = {p}, drawn by the quotient bits they make. Par's restoring core "
            f"is {steps} steps in series, each a {sw}-bit comparison and subtraction making one quotient bit. The "
            f"SRT core is {stages} stages in series, each making a radix-4 digit, two bits, from an {ew}-bit "
            f"estimate addition, four comparisons with constants and a carry-save row with no carry chain; one "
            f"{fw}-bit adder at the end sums the carry-save remainder.")
    return d, desc


SRT = "8f051dea23f6ec7a652e104c8db81b2aac1ab5d803e79c40bfbc70bb15341c60"     # fdivp_srt.sv, 9aa52640
RESTORING = "6accce8480176a433638ac74ce597a3310aef2a72d2439f90f2abb7a16b72310"   # fdivp.sv (par), f5a6045c

register("fdivp-srt-selection", task="fdivp", designs=[SRT], drawn_at=SCORED, scored_at=SCORED,
         make=lambda: (*selection_figure(), 360))
register("fdivp-cores", task="fdivp", designs=[SRT, RESTORING], drawn_at=SCORED, scored_at=SCORED,
         make=lambda: (*cores_figure(11), 420))
