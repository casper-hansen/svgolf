import SvGolf.Task
import LeanModels.SoftFloat.Binary.Defs

/-!
# Task `fdivp` (trusted statement): IEEE 754 division, PARAMETRIC in the format

**The function is IEEE 754-2019 division.** The output pattern `q` is `division(a, b)` (§5.4.1) of the two input
patterns in the binary interchange format with exponent width `W` and precision `P` (§3.3, §3.4), under the
rounding-direction attribute roundTiesToEven (§4.3.1), the default (§4.3.3). That function is not defined in this
task: it is `LeanModels.SoftFloat.Binary.divide`, from the IEEE 754 library of the pinned Proglib
(`LeanModels/SoftFloat/Binary/Defs.lean`, the only module of it this file imports: the definitions, no proofs). In the
library, every definition cites its clause:

* `decode` reads a pattern as `S ‖ E ‖ T` and gives its datum, the five cases of §3.4 (a)–(e): NaN, ±∞, a normal
  number, a subnormal number, ±0;
* `divide` takes the special cases of §6.1, §6.2, §6.3, §7.2 and §7.3 (a NaN operand, `0 / 0` and `∞ / ∞` give a
  NaN; `∞ / y` and `x / 0` give ±∞; `0 / y` and `x / ∞` give ±0; the sign of every non-NaN result is the XOR of
  the operands' signs), and otherwise rounds the exact quotient once (§4.3, §5.1);
* `round` is correct rounding with gradual underflow to subnormals (§3.3, §7.5, no flush to zero) and the overflow
  results of §7.4 (to ±∞ under roundTiesToEven).

The library proves that this `divide` is what the standard asks for, for every format
(`LeanModels/SoftFloat/Binary/Characterization.lean`): a quotient with a value is a nearest number of the format to
the exact quotient, ties to even (`divide_isNearestTiesToEven`, §4.3.1); it is an infinity exactly at the overflow
threshold (`divide_overflowsAtThreshold`, §4.3.1, §7.4); a quotient of two numbers is never a NaN
(`divide_ofNumbersIsNotNaN`, §7.2); its sign is the XOR of the operands' signs (`divide_signIsXor`, §6.3); and these
four properties leave exactly one possible pattern (`divide_isUniquelyCharacterized`).

Two things the standard leaves open or asks for beyond a bit pattern:

* **NaN results.** §6.2.3 says a NaN result *should* (not *shall*) carry an input's payload. `divide` gives every NaN
  result as the one canonical quiet NaN (sign 0, exponent field all ones, trailing significand `10…0`: `0x7E00` in
  binary16), as RISC-V and SMT-LIB do, so the result is a function of the operand bits. A design must produce that
  pattern; NaN payloads are not propagated.
* **Exception flags** (§7: invalid operation, division by zero, overflow, underflow, inexact) are not part of the
  task. The design has no flag outputs, and the result pattern does not depend on them.

Module (two parameters, in this order; port order as written):

```systemverilog
module fdiv #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
```

`W` is the width of the biased-exponent field and `P` the precision (the significand digits including the implicit
leading bit), so the trailing significand has `P - 1` bits and a pattern has `1 + W + (P - 1) = W + P` bits:
binary16 is `W = 5, P = 11`, bfloat16 `W = 8, P = 8`, binary32 `W = 8, P = 24`, binary64 `W = 11, P = 53`.

Statement: for every `W ≥ 2` and `P ≥ 2` (the library's own well-formedness of a format, `Format.hw`, `Format.hp`)
with `W + P < 2^20` (decided 2026-11-14: the range keeps the `int` arithmetic a design does on `W` and `P`, the
widths `W + P` and `W + P + 1` and the localparams it computes from them, below `2^31`, where an `int` wraps), the
design has exactly the ports `a`, `b` (inputs, `W + P` bits) and `q`
(output, `W + P` bits), no process is clocked, there is no combinational loop, every run terminates, and in every
cycle whose stimulus drives `a` and `b` with known values the snapshot's `q` is
`LeanModels.SoftFloat.Binary.divide ⟨W, P⟩ .nearestTiesToEven a b` (`.nearestTiesToEven` is the library's name for
roundTiesToEven). The two-parameter family is a family of fixed-size `CombTask`s, one per `(W, P)`, and the
statement quantifies over the pairs with `CombTask.StatementFixed` at each (`design/fdiv-param/TASK.md`, "Option C").
`REVIEW.md` lists the modelling choices.
-/

namespace SvGolf.Tasks.FdivP

open SvGolf LeanModels.SoftFloat

/-- The storage width of the format `⟨W, P⟩`: `1 + W + (P - 1) = W + P`. -/
theorem k_eq (W P : Nat) (hP : 1 ≤ P) : 1 + W + (P - 1) = W + P := by omega

/-- **The function of the task**: IEEE 754 division `Binary.divide ⟨W, P⟩ .nearestTiesToEven` (roundTiesToEven)
on `(W + P)`-bit patterns, for `2 ≤ W` and `2 ≤ P` (a `Binary.Format` requires both). The `BitVec.cast`s only
transport a pattern along the equation `Format.k = W + P` (they leave `toNat` unchanged: `fdivBits_toNat`);
outside the range the function is `0`, which no statement looks at. -/
def fdivBits (W P : Nat) (a b : BitVec (W + P)) : BitVec (W + P) :=
  if h : 2 ≤ W ∧ 2 ≤ P then
    let f : Binary.Format := ⟨W, P, h.1, h.2⟩
    have hk : f.k = W + P := k_eq W P (by omega)
    (Binary.divide f .nearestTiesToEven (a.cast hk.symm) (b.cast hk.symm)).cast hk
  else 0#(W + P)

/-- The task at the format `⟨W, P⟩`, as a fixed-size `CombTask` (its own parameter is ignored and
taken at `0`, as in `CombTask.StatementFixed`): inputs `a b : BitVec (W + P)`, output
`q = fdivBits W P a b`. -/
def task (W P : Nat) : CombTask where
  inRange K := K = 0
  inputs _ := [("a", W + P), ("b", W + P)]
  outputs _ := [("q", W + P)]
  fn _ := fun (a, b, ()) => (fdivBits W P a b, ())

/-- Which parameter pairs the statement covers: the library's own `Format` well-formedness, and
`W + P < 2^20` (decided 2026-11-14), so that the port width `W + P`, the exponent width `W + P + 1` a design
computes in and the localparams it computes from `W` and `P` (the ports' `[W+P-1:0]`, a
`localparam integer EW = W + P + 1`, `F = P + 4`, evaluated as `int`s) stay below `2^31`, where an `int`
wraps. -/
def inRange (W P : Nat) : Prop := 2 ≤ W ∧ 2 ≤ P ∧ W + P < 2 ^ 20

/-- **The challenge statement** for the two-parameter design family
`Submission.design.sem : Nat → Nat → Design2`: at every `W, P ≥ 2` in range the design satisfies the
fixed-size task at that format. A submission proves
`SvGolf.Tasks.FdivP.Statement Submission.design.sem`. -/
abbrev Statement (sem : Nat → Nat → LeanModels.Sv.Design2) : Prop :=
  ∀ W P, inRange W P → (task W P).StatementFixed (sem W P)

/-! Sanity checks on the statement's data (closed, by `decide`/`rfl`). -/

/-- binary16, bfloat16-like and binary32 are in range. -/
example : inRange 5 11 ∧ inRange 8 8 ∧ inRange 8 24 := by
  simp [inRange]

/-- The range ends where `W + P` reaches `2^20` (decided 2026-11-14). -/
example : inRange (2 ^ 20 - 3) 2 ∧ ¬ inRange (2 ^ 20 - 2) 2 ∧ inRange 2 (2 ^ 20 - 3) ∧
    ¬ inRange 2 (2 ^ 20 - 2) := by
  simp [inRange]

/-- The input names are distinct (the non-vacuity theorem `CombTask.SatisfiedAt.exists_run`
needs it), at every parameter pair. -/
example (W P : Nat) : (((task W P).inputs 0).map Prod.fst).Nodup := by
  simp [task]

/-- The casts do not change values: as numbers, `fdivBits W P a b` is the library's division of `a` and `b`. -/
theorem fdivBits_toNat (W P : Nat) (h : 2 ≤ W ∧ 2 ≤ P) (a b : BitVec (W + P)) :
    (fdivBits W P a b).toNat =
      (Binary.divide ⟨W, P, h.1, h.2⟩ .nearestTiesToEven
        (a.cast (k_eq W P (by omega)).symm) (b.cast (k_eq W P (by omega)).symm)).toNat := by
  simp [fdivBits, h]

/-- Golden vectors of the task's function: `1 / 3 = 0x3555` in binary16, `1 / 3 = 0x3EAAAAAB` in binary32, and
bfloat16-like `(8, 8)`: `1 / 3 = 0x3EAB`. -/
example : ((task 5 11).fn 0 (0x3C00#16, 0x4200#16, ())).1 = 0x3555#16 := by decide
example : ((task 8 24).fn 0 (0x3F800000#32, 0x40400000#32, ())).1 = 0x3EAAAAAB#32 := by decide
example : ((task 8 8).fn 0 (0x3F80#16, 0x4040#16, ())).1 = 0x3EAB#16 := by decide
/-- `0 / 0` is the canonical NaN of the format (`0x7E00` in binary16). -/
example : ((task 5 11).fn 0 (0x0000#16, 0x0000#16, ())).1 = 0x7E00#16 := by decide
/-- The smallest formats are in range: `W = 2, P = 2` is 4 bits. -/
example : ((task 2 2).fn 0 (0b0011#4, 0b0100#4, ())).1 = fdivBits 2 2 0b0011#4 0b0100#4 := rfl

end SvGolf.Tasks.FdivP
