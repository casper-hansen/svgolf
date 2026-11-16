# `fdivp`: review of the trusted statement

Hard gate of `PLAN2.md` for a new task: "reviewed trusted `Spec.lean`". The file under review is [Spec.lean](Spec.lean)
(in the `tasks` library: `lake build tasks.fdivp.Spec`); since 2026-11-14 its function is IEEE 754 division from
Proglib's library `LeanModels.SoftFloat.Binary` (below, "Changes"). From 2026-11-03 to 2026-11-14 the task also had a
trusted IEEE 754 spec of its own, `IEEE754.lean` (module `tasks.fdivp.IEEE754`; it was `svgolf/spec/IEEE754.lean`, reviewed for the former
16-bit task (binary16 alone), and moved into the task with its content unchanged: sha256
`4819c7290aa152f18c16706da82f086c0994cc285bde3fb6e6391449ae6c987b` before and after the move; renamed inside on 2026-11-04, below). The task is registered as READY: the word-level reference
`reference/fdivp.sv` is proved for every format (`reference/fdivp.lean`). The statement is "Option C" of
`design/fdiv-param/TASK.md`: no change to `SvGolf/Task.lean`. Changing the statement after your review is a small
follow-up for the names and the range; the proof is generated from the netlist and uses `a`, `b`, `q`, `W`, `P` and the
function `fdivBits`.

## The statement in plain words

A submission is one module with exactly these two parameters, in this order, and these ports, in this order:

```systemverilog
module fdiv #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
```

`W` is the width of the biased exponent field, `P` the precision (significand digits including the implicit bit), so a
pattern is `1 + W + (P - 1) = W + P` bits: binary16 is `(W, P) = (5, 11)`, bfloat16 `(8, 8)`, binary32 `(8, 24)`,
binary64 `(11, 53)`.

The task is satisfied when, **for every `W >= 2` and every `P >= 2` with `W + P < 2^20`**, the instance `fdiv #(W, P)` has
exactly the ports `a`, `b` (inputs) and `q` (output), each `W + P` bits; every run terminates; no process is clocked
(`Unclocked`); and in every cycle whose stimulus drives `a` and `b` with KNOWN values the snapshot's `q` equals
`LeanModels.SoftFloat.Binary.divide <W, P> .nearestTiesToEven a b`: IEEE 754 division under roundTiesToEven, from
Proglib's IEEE 754 library (`LeanModels/SoftFloat/Binary/Defs.lean` of the pinned revision; `.nearestTiesToEven` is
the library's name for roundTiesToEven). In Lean (`Spec.lean`):

```lean
def task (W P : Nat) : CombTask where
  inRange K := K = 0
  inputs _ := [("a", W + P), ("b", W + P)]
  outputs _ := [("q", W + P)]
  fn _ := fun (a, b, ()) => (fdivBits W P a b, ())

def inRange (W P : Nat) : Prop := 2 ≤ W ∧ 2 ≤ P ∧ W + P < 2 ^ 20

abbrev Statement (sem : Nat → Nat → Design2) : Prop :=
  ∀ W P, inRange W P → (task W P).StatementFixed (sem W P)
```

`fdivBits W P a b` is the library's `divide <W, P> .nearestTiesToEven a b` on `(W + P)`-bit patterns (casts along
`1 + W + (P - 1) = W + P`; the casts do not change a value, `fdivBits_toNat`). The rows of the function, in the order
tested (the library's `divide`, clause by clause): any NaN operand gives the canonical quiet NaN; `inf / inf` and `0 / 0` give it too; `inf / y` and `x / 0` (finite
nonzero `x`) give `±inf`; `x / inf` and `0 / y` give `±0`; finite nonzero over finite nonzero is the exact quotient
rounded to nearest, ties to even, with gradual underflow and overflow to `±inf`; the sign is `a[K-1] ^ b[K-1]`.

## Why the definition can be trusted (independent evidence, none of it part of the statement)

* **It is the library's binary16 and binary32 division.** At `(5, 11)` (IEEE binary16) and `(8, 24)` (binary32),
  `fdivBits` unfolds to `divide binary16 .nearestTiesToEven` and `divide binary32 .nearestTiesToEven`, which the library
  names `divBinary16` and `divBinary32`. The golden vectors of
  `Spec.lean` (`1 / 3` in binary16 `0x3555`, binary32 `0x3EAAAAAB`, bfloat16 `0x3EAB`; `0 / 0` the canonical NaN; the
  smallest format `(2, 2)`) are `decide`d there. The library's definitions (`LeanModels/SoftFloat/Binary/Defs.lean`,
  each citing its IEEE 754-2019 clause; `README.md`, "IEEE 754 division", says what they are, and `spec_validate/` has
  their differential validation) are generic in the format; `Format` requires `2 <= w` and `2 <= p` and nothing else.
* **The library proves its `divide` is the standard's division.** `LeanModels/SoftFloat/Binary/Characterization.lean`:
  a quotient with a value is a nearest number of the format, ties to even (`divide_isNearestTiesToEven`); it is an
  infinity exactly at the overflow threshold (`divide_overflowsAtThreshold`); a quotient of two numbers is never a NaN
  (`divide_ofNumbersIsNotNaN`); its sign is the XOR of the operands' signs (`divide_signIsXor`); and these four
  properties leave exactly one pattern (`divide_isUniquelyCharacterized`).
* **The function at every format is cross-validated THROUGH THE PROOF.** The reference is proved equal to this function
  for every format (`SvGolf.FdivParam.OutN_fdivBits`, section `DpU` of `reference/fdivp.lean`), and the reference is
  simulated (Verilator) against two
  independent implementations of the function, so every simulated pair is an indirect test of `divide` itself at that
  format: `oracle.py` (exact `fractions.Fraction` arithmetic, no floating point, no code from the spec's tooling `spec_validate/`) and
  `tests/fdivp/validate/oracle.h` (128-bit integers, the quotient rounded at the spacing of its binade). They agree with
  each other and with the reference on every pair of all 66 formats with `W + P <= 14` and of the two 32-bit
  formats `(5, 11)` and `(8, 8)`, and on 200,000 corner-rich vectors at each of 12 larger formats up to `(11, 53)` and
  `(2, 62)` (`tests/fdivp/results/`, README.md "Validation").
* **Golden values from the standards**: binary16 `1 / 3 = 0x3555`, binary32 `1 / 3 = 0x3EAAAAAB`, `0 / 0` and every NaN
  operand give the canonical NaN (`0x7E00`, `0x7FC00000`).

## The modelling choices to look at

1. **`inRange W P = 2 <= W /\ 2 <= P /\ W + P < 2^20`.** The first two are the library's own `Format` well-formedness: `W = 1` would have exponent
   bias `2^0 - 1 = 0` and no normal exponent below the all-ones one; `P = 1` would have no fraction bit, hence no quiet-NaN
   bit. Any larger lower bound would be a free choice. The statement is for every format in the range, so a design
   must be generic in `W` and `P`: a design specialized to `(5, 11)` has no proof of `forall W P`. Since 2026-11-14 the
   range also requires `W + P < 2^20`
   (below, "Changes"); from 2026-11-06 it required `W + P + 1 < 2^31`
   (decided 2026-11-06, README "The statement"): the port and exponent widths are `int` expressions of the module,
   and an `int` holds no value of `2^31` or more.
2. **The canonical quiet NaN, whatever the operands.** Every NaN result is `{0, all-ones exponent, fraction MSB set, rest 0}`
   (sign `0`): the payload and sign of an operand NaN are NOT propagated. That is the spec's choice at binary16 too (and
   `0x7E00` there). At `P = 2` the fraction has ONE bit, which is the quiet bit.
3. **Round to nearest, ties to even only.** No rounding-mode input, no status flags (a design with an extra port fails the
   interface conjunct: `tests/fdivp/negative/rm_pin.sv`, `status_flag.sv`, `wide_q.sv`).
4. **Full subnormals** (no flush to zero) and gradual underflow to `±0`; overflow to `±inf` (not to the largest finite).
5. **Storage `W + P` bits, ports `a`, `b`, `q`, module `fdiv`, parameters `W`, `P` in that order.** The names are the
   task's choice (the former 16-bit task had `a`, `b`, `q`); the checker requires the top to have exactly these overridable parameters by name
   and order.
6. **Option C**: the family of fixed-size tasks `task W P` at the placeholder parameter `0` (as the former 16-bit task's `StatementFixed`), not
   a two-parameter `CombTask`. It needs no change to the trusted `SvGolf/Task.lean`. The alternative (`CombTask2`,
   `design/fdiv-param/Task.lean.patch`, 35 lines) would rebuild every task library and is kept for a second two-parameter
   task. The one place `check.py` is not n-ary is the advisory `--tactics` probe (README.md of the task, "Findings").
7. **No region parameter.** Below `2^20` the statement does not bound `W + P`, so a design with a width limit (say
   `W + P <= 64`) is not a solution; the reference works for every `W, P >= 2` in the range because every width in it is
   an expression of the parameters.

## What it does NOT ban

Only `/ % **` (as the former 16-bit task): `+ - *`, shifts, comparisons, `$clog2` and every other construct the ls-sv subset accepts are
allowed. `task.json` `banlist.operators = ["/", "%", "**"]`.

## Cheating surfaces and which defence applies

| trick | defence | test |
|---|---|---|
| a design correct only up to some width (or at `(5, 11)` only) | the proof is for ALL `W, P >= 2`; the post-synthesis check is at the scoring point only, so it cannot catch it, the proof does | `tests/fdivp/attacks/` |
| a design correct on every format except one (or on a class of operands of every format) | the proof; the advisory oracle reports a mismatch at the scoring point only when it shows there | `tests/fdivp/attacks/` |
| run-time `/` or `%` (the operator that IS the task) | the banlist (front check and Yosys backstop `$div $mod`) | `tests/fdivp/negative/div_op.sv` |
| NaN payload or an unreachable arm as `'x` | source gate (x/z literals) and `fourstate` | the source gate's and `fourstate`'s own tests (`score/`) |
| extra port (rounding mode, flags) or a wider `q` | the interface conjunct | `tests/fdivp/negative/` |
| a constant output right on the NaN rows only | the proof | `tests/fdivp/negative/const_nan.sv`, refuted at `(2, 2)` in `Refute.lean` |

## Changes to the trusted statement since the review (to review)

* **2026-11-16: the proof of equivalence with the former statement is removed** (decided 2026-11-16: "You don't have to
  prove equiv to the old statement. Just update the statement and fix the proofs so they work wrt. the new
  statement."). `tests/fdivp/Equivalence.lean` (which proved the task's function equal to the former one, for every
  format and every pair of input patterns) and `tests/fdivp/OldIEEE754.lean` (the former definitions, kept as test
  material for that proof only) are deleted. No trusted file changes: `Spec.lean` is byte-identical, and the statement
  stands on its own as the library's IEEE 754 division. Every fdivp proof (the three references, the test baseline
  and the board's records) proves this statement directly.

* **2026-11-14: the range is reduced to `W + P < 2^20`** (decided 2026-11-14, for every family task whose
  designs compute `int` localparams from the parameters: the range is reduced so that this arithmetic never wraps).
  `inRange W P` was `2 ≤ W ∧ 2 ≤ P ∧ W + P + 1 < 2 ^ 31`; it is `2 ≤ W ∧ 2 ≤ P ∧ W + P < 2 ^ 20`. Under the exact
  32-bit `int` instantiation of the pinned ls-sv the Newton divider's `localparam integer F = P + 4` and the SRT
  divider's `RW = P + 6` wrapped at the top of the former range, so neither design was provable for the whole
  range by any proof; below `2^20` every localparam of the board's designs is its own value. `task`, `fdivBits` and
  the golden vectors are unchanged; the sanity check of the range's end moves to `2^20`. (Until 2026-11-16 a test
  file proved the statement the former one on the smaller range; removed, above.)

* **2026-11-14: the statement names IEEE 754 division from Proglib's library** (decided 2026-11-14: "Yes, repoint. Just
  make sure it feels clean for the user, so they can see it's nothing but the real IEEE spec, and not some obscure
  homegrown version"). `Spec.lean` imports `LeanModels.SoftFloat.Binary.Defs` (Proglib's IEEE 754 library, at the pinned
  revision) instead of `tasks.fdivp.IEEE754`, and `fdivBits W P` is `LeanModels.SoftFloat.Binary.divide ⟨W, P⟩
  .nearestTiesToEven` (the library's spelling of roundTiesToEven) instead of `SvGolf.IEEE754.divide ⟨W, P⟩
  .roundTiesToEven`; the module docstring now says, clause by clause, what that function is. `IEEE754.lean` leaves the
  trusted files (until 2026-11-16 it was kept as test material, with a proof that the task's function was the former
  one for every format and pair of patterns; both removed, above). `task`, `inRange`, `Statement`, the
  sanity checks and the golden vectors are textually unchanged. The trusted files are now `Spec.lean` and
  `SvGolf/Task.lean` (the library's `Defs.lean` is covered, like ls-sv's semantics, by the pinned Proglib revision a
  record names). What the library does not model is what the former spec did not: exception flags (§7) and NaN payloads
  (every NaN result is the canonical quiet NaN).

* **2026-11-03: the former 16-bit task (binary16 alone) is removed** (binary16 is this task's instance `(5, 11)`,
  the scoring point). `Spec.lean` loses the import of that task's `Spec` and its cross-link theorem (a design family
  satisfying this statement satisfies the 16-bit task's statement at `(5, 11)`): with that task gone it has no object.
  Nothing else changes: `task`, `fdivBits`, `inRange`, `Statement` and the checks are as reviewed.
* **2026-11-04: the two `rfl` guards are removed** (asked why they were needed, the answer was: "I really don't see what we need
  this for?"). They stated that `fdivBits` at `(5, 11)` and `(8, 24)` is the spec's binary16/binary32 instance; nothing
  used them, and the trusted text is smaller without them. `Statement` is unchanged.

* **2026-11-03: the IEEE 754 spec moves into the task** (the trusted spec is part of the task).
  `svgolf/spec/IEEE754.lean` is now `tasks/fdivp/IEEE754.lean` (module `tasks.fdivp.IEEE754`, namespace
  `SvGolf.IEEE754` unchanged), byte for byte (sha256 above). `Spec.lean` changes in two places: the import line
  (`import spec.IEEE754` -> `import tasks.fdivp.IEEE754`) and the path in its module docstring. The spec's facts
  (formerly `spec/IEEE754Proofs.lean`, the five characterization theorems included) are the section `IEEE754Proofs` of
  the reference proof `reference/fdivp.lean`, checked by `check.py` like any submission; its validation tooling is
  `spec_validate/`. The spec's docstrings still name `IEEE754Proofs.lean` and `README.md`: the section of the
  reference and this task's `README.md` ("The trusted spec") answer them; the move did not edit the file.

* **2026-11-04: the binary16 and binary32 instances are named after their formats** (the former 16-bit task's
  name is out of the Lean and the READMEs). A rename, in both trusted files, with no change to the function `divide` or
  to `Statement`. In `IEEE754.lean` the two abbreviations `divide binary16 .roundTiesToEven` and
  `divide binary32 .roundTiesToEven` are now `divBinary16` and `divBinary32` (bodies unchanged; every `#guard` golden
  vector and `decide` example kept, only the name in it changed), and the docstrings that named them (the module
  docstring, `RoundingMode`'s, the two definitions') say "the binary16 and binary32 instances" (the two definitions'
  also give the task's `(W, P)`). (The two `rfl` guards in `Spec.lean`, briefly renamed, were then removed; see the next entry.) `Format`,
  `decode`, `round`, `divide`, the characterization statements, `task`, `fdivBits`, `inRange` and `Statement` are
  unchanged. sha256 of `IEEE754.lean`: `4819c7290aa152f18c16706da82f086c0994cc285bde3fb6e6391449ae6c987b` before,
  `ea783e2a80d8cfc63b65087c7de0fac92ea584352817a0ea6e38239aa2726218` after.

## Questions for you

1. Port and module names `fdiv`, `a`, `b`, `q`, parameters `W`, `P` in that order (the former 16-bit task had `a`, `b`, `q`): acceptable?
2. `inRange = 2 <= W /\ 2 <= P` with no upper bound: confirmed? (The statement is for ALL formats, which the proof delivers.)
   Answered 2026-11-06: the range is `2 ≤ W ∧ 2 ≤ P ∧ W + P + 1 < 2^31`, so that every width stays an `int`.
   Since 2026-11-14 it is `2 ≤ W ∧ 2 ≤ P ∧ W + P < 2^20` ("Changes").
3. The canonical quiet NaN with sign 0 and no payload propagation, as in the former 16-bit task: confirmed for every format?
4. Round to nearest even only, no flags, full subnormals, overflow to infinity: confirmed?
5. Option C (`StatementFixed` family) rather than the `CombTask2` patch: confirmed?
6. Is it fine that the cross-validation of `divide` at formats other than binary16 is the one through the proof and the two
   independent oracles (above), rather than a separate run of `spec_validate/Run.lean` at those formats?
7. The 2026-11-03 change above (the cross-link theorem removed with the former 16-bit task): confirmed? (The `rfl` guards: removed 2026-11-04, decided.)
8. The move of the spec into the task (second trusted file `IEEE754.lean`, unchanged; its stale docstring pointers left
   as they are, above): confirmed?
9. The 2026-11-04 rename above (`divBinary16`/`divBinary32`; a rename only): confirmed?
