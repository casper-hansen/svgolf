import SvGolf.TaskSeq

/-!
# Task `matmul`: N×N signed matrix multiplication, wrapping at the accumulator width
# (TRUSTED text, final, decided 2026-11-08, amended 2026-11-09, 2026-11-14, 2026-11-16 and 2026-11-19; written 2026-11-04; contract C6 of `design/sequential/CONTRACT.md`)

Module (port order as written; `N`, `W`, `AccW` are the module's parameters, in this order):

```systemverilog
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
```

**Layout.** Flat, row-major, least significant entry first: entry `(i, k)` of `A` is
`A[(i*N+k)*W +: W]`, likewise `B`; entry `(i, j)` of `C` is `C[(i*N+j)*AccW +: AccW]`.

**Arithmetic (ruled 11/03).** The entries of `A` and `B` are SIGNED (two's complement,
`W` bits), products sign-extended; `C[i][j] = Σ_k A[i][k]·B[k][j]`, computed exactly in the
integers and then reduced mod `2^AccW` (wrap, as GPUs accumulate; order-independent, so every
summation order is legal). `C`'s entries are two's complement `AccW`-bit values.

**Protocol** (`TxTask`, `SvGolf/TaskSeq.lean`; C1 to C5): synchronous active-high reset `rst`;
claims from the cycle after its release; `start` a one-cycle pulse raised only when the design is
idle; `A` and `B` held from `start` until `done` rises; `done` rises within the declared latency
`lat` (cycles after the edge that samples `start`), then stays 1 with `C` = the product until the
next `start`. `done` is known in every cycle after the release, and 0 up to the first start
(`done` = 1 claims a result, and there is none before a start); `C` only where `done` = 1.

The declared latency `lat` is the submission's; the checker pins its value at the scoring point
`(4, 8, 32)` and the score uses it (C3, C7). Run-time `/ % **` are banned, as in every task (`task.json`).

**Range.** `1 ≤ N ≤ 256`, `1 ≤ W ≤ 127`, `1 ≤ AccW ≤ 64` (decided 2026-11-19: up to the largest
realistic matrix-multiply circuits, 256×256 matrices with entries of up to 127 bits and accumulators of up to
64 bits; it replaces the range of 2026-11-16, `N < 2^5`, `W < 2^10`, `AccW < 2^12`, and neither range contains
the other). The parameters are `int`s, and the range keeps the `int` arithmetic a design does on them below `2^31`,
where an `int` wraps: the port widths `N·N·W` and `N·N·AccW` (at most 8,323,072 and 4,194,304), every index of
the interface (`(i*N+k)*W`), and the larger widths the board's designs declare from them (a multiplier cube's
`N·N·(2N-1)·AccW`, at most 2,143,289,344, and a core mesh's `N·N·N·W`, at most 2,130,706,432: below
`2^31` = 2,147,483,648, by less than 1 %). There a real elaboration and ls-sv agree (`PDesign.int32Agrees`;
Task v2 decision 1, the `clmul` precedent).

**txtask-v2 (2026-11-05; final, decided 2026-11-08, amended 2026-11-09).** `Statement` is the v2
statement `TxTask.StatementV2`: txtask-v1's interface, clock discipline and latency bound; its claims
and termination from EVERY power-up state on every known stimulus (rule 2: an unreset register is an
unknown 0/1 value, not ls-sv's `x` start); Moore outputs (`MooreOutDep`, rule 1, nothing exempt: no
combinational path from `rst`, `start`, `A` or `B` to `done` or `C`); and no construct that creates an `x`
from known operands (`XSafe`, rule 3). `SvGolf/TaskSeq.lean`, last section, and
`design/soundness/TXTASK-V2-REVIEW.md`.
-/

namespace SvGolf.Tasks.Matmul

open SvGolf

/-- The parameters `(N, W, AccW)`. -/
abbrev Params := Nat × Nat × Nat

/-- Entry `idx` of a flat vector of `W`-bit signed entries, as an integer. -/
def entry (W : Nat) {n : Nat} (x : BitVec n) (idx : Nat) : Int :=
  (x.extractLsb' (idx * W) W).toInt

/-- `Σ_{k < N} A[i][k] · B[k][j]` in the integers. -/
def dot (N W : Nat) {n : Nat} (a b : BitVec n) (i j : Nat) : Int :=
  (List.range N).foldl (fun acc k => acc + entry W a (i * N + k) * entry W b (k * N + j)) 0

/-- The product `C = A·B`, each entry reduced mod `2^AccW`, packed flat row-major. -/
def product (N W AccW : Nat) {n : Nat} (a b : BitVec n) : BitVec (N * N * AccW) :=
  BitVec.ofNat (N * N * AccW)
    ((List.range (N * N)).foldl
      (fun acc ij =>
        acc + (BitVec.ofInt AccW (dot N W a b (ij / N) (ij % N))).toNat * 2 ^ (ij * AccW))
      0)

/-- **The task** (C6). -/
def task : TxTask Params where
  inRange p := 1 ≤ p.1 ∧ p.1 ≤ 256 ∧ 1 ≤ p.2.1 ∧ p.2.1 ≤ 127 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 64
  clk := "clk"
  rst := "rst"
  start := "start"
  operands p := [("A", p.1 * p.1 * p.2.1), ("B", p.1 * p.1 * p.2.1)]
  done := "done"
  payload p := [("C", p.1 * p.1 * p.2.2)]
  result p := fun (a, b, ()) => (product p.1 p.2.1 p.2.2 a b, ())

/-- **The challenge statement**, for the three-parameter design family `sem N W AccW` and the
latency function `lat N W AccW`. The checker's goal is `Statement design.sem lat ∧ lat 4 8 32 = n`
with the latency `lat` the proof file defines and the declared number `n` (C3). -/
abbrev Statement (sem : Nat → Nat → Nat → LeanModels.Sv.Design2) (lat : Nat → Nat → Nat → Nat) :
    Prop :=
  task.StatementV2 (fun p => sem p.1 p.2.1 p.2.2) (fun p => lat p.1 p.2.1 p.2.2)

/-! ## Sanity checks on the statement's data (proved; they add nothing to the trusted base) -/

/-- A 2×2 product with a negative entry: `A = [[-1, 2], [3, 4]]`, `B = [[5, 6], [7, 0]]` (W = 4)
gives `C = [[9, -6], [43, 18]]` (AccW = 8; `-6` is `0xFA`). -/
example : product 2 4 8 (0x432F#16) (0x0765#16) = 0x122BFA09#32 := by decide

/-- Wrap: `[[-8]]·[[-8]] = 64`, which is `0x40` in 8 bits and `0` in 6 bits (W = 4). -/
example : product 1 4 8 (0x8#4) (0x8#4) = 0x40#8 ∧ product 1 4 6 (0x8#4) (0x8#4) = 0#6 := by
  decide

/-- The off-points the extractor probes and the scoring point are in range (C6). -/
example : task.inRange (1, 1, 1) ∧ task.inRange (2, 3, 5) ∧ task.inRange (3, 4, 8) ∧
    task.inRange (4, 8, 32) := by
  simp [task]

/-- The range's ends (decided 2026-11-19): the corner `(256, 127, 64)` is in range, and one past it in each
parameter is not; neither is `0` in any parameter. -/
example : task.inRange (256, 127, 64) ∧ ¬ task.inRange (257, 127, 64) ∧ ¬ task.inRange (256, 128, 64) ∧
    ¬ task.inRange (256, 127, 65) ∧ ¬ task.inRange (0, 1, 1) ∧ ¬ task.inRange (1, 0, 1) ∧
    ¬ task.inRange (1, 1, 0) := by
  simp [task]

/-- Neither range contains the other (decided 2026-11-19): `N = 256` is new, and the former range's
`W = 2^10 - 1` and `AccW = 2^12 - 1` are no longer covered. -/
example : task.inRange (256, 1, 1) ∧ ¬ task.inRange (1, 2 ^ 10 - 1, 1) ∧ ¬ task.inRange (1, 1, 2 ^ 12 - 1) := by
  simp [task]

/-- The port names are distinct. -/
example (p : Params) :
    (["clk", "rst", "start"] ++ (task.operands p).map Prod.fst).Nodup ∧
      task.done ∉ (task.payload p).map Prod.fst := by
  simp [task]

end SvGolf.Tasks.Matmul
