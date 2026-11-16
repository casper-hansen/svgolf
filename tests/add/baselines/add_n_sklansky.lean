import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombTaskTactic
import LeanModels.Sv.Lib.Prefix

/-!
# Task `add`: the Sklansky parallel-prefix adder `add_n_sklansky.sv`, proved with the `sv_comb` tactics

The design, as written: positions `0 … N` (position `0` is `cin` with propagate `0`, position `k + 1` is bit `k`),
`L = $clog2(N + 1)` levels of a 2-D array pair `g, p : [L:0][N:0]`, level `l + 1` combining position `i` whose bit `l`
is set (`((i >> l) & 1) == 1`, a conditional generate inside the nested level/node loops) with the top position of the
block below it, `((i >> l) << l) - 1`, and passing it through otherwise; `s[i] = x[i] ^ g[L][i]`, `cout = g[L][N]`.
Proved for every `N` with `1 ≤ N < 2^20`:

1. **Structure** (`skl_comb`, `skl_acyclic`): `sv_structure` proves `CombDesign` with the shared obligations
   (`SharedObl`), then `Acyclic` from them (the rank of level `l + 1` is `l + 1`, the sum and the carry out last).
2. **Ports** (`skl_interface`): `sv_interface`.
3. **Equations** (in `solution`): `CombTask.satisfiedAt_of_comb` reduces the statement to one settled-state lemma;
   `sv_equations` derives the netlist's equations over `Bool` from the semantics (the bit test and the shift atoms where
   the source has `>>`, `<<` and `& 1`) and the knownness of every driven bit; `sv_eq_nat` states them at `Nat` indices
   (the level count `clog2 (N + 1)` unwrapped from its 32-bit reading); the obligations close by `sv_obligations`.
4. **The prefix mathematics** (`sklRec_block`): after level `l` position `k` holds the generate/propagate pair of the
   block `[k / 2^l * 2^l, k]` of the adder's positions (`LeanModels.Sv.Lib.pgBlock`), so level `L` holds the carry into
   every bit, and `CombLib.add_spec` turns the ripple carries into the task's sum.

The route and the prefix lemma follow Proglib's `Examples/system-verilog/prefix_sklansky/add_proof.lean` (a clean-room
Sklansky design proved against the same statement restated over ls-sv); here the statement is svGolf's own, reached
through `CombTask.satisfiedAt_of_comb`. No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq LeanModels.Sv.Lib SvGolf

/-! ## 1. The prefix mathematics (plain `Bool`/`Nat`) -/

/-- The Sklansky recurrence as the design denotes it: level `0` is the positions `pos`; level `l + 1` at position `k`
joins `(l, k)` with `(l, k / 2^l * 2^l - 1)` where bit `l` of `k` is set, and copies `(l, k)` otherwise. -/
def sklRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, k => pos k
  | l + 1, k =>
    if k / 2 ^ l % 2 = 1 then pgOp (sklRec pos l k) (sklRec pos l (k / 2 ^ l * 2 ^ l - 1)) else sklRec pos l k

/-- After level `l`, position `k` holds the pair of the block `[k / 2^l * 2^l, k]`. -/
theorem sklRec_block (pos : Nat → Bool × Bool) : ∀ l k, sklRec pos l k = pgBlock pos (k / 2 ^ l * 2 ^ l) k
  | 0, k => by rw [sklRec, Nat.pow_zero, Nat.div_one, Nat.mul_one, pgBlock_self]
  | l + 1, k => by
    have hk : k / 2 ^ l * 2 ^ l ≤ k := Nat.div_mul_le_self k _
    have hP : 0 < 2 ^ l := Nat.two_pow_pos l
    rw [sklRec]
    split
    · next hb =>
      rw [sklRec_block pos l k, sklRec_block pos l (k / 2 ^ l * 2 ^ l - 1), Nat.pow_succ,
        ← Nat.div_div_eq_div_mul]
      generalize k / 2 ^ l = Q at *
      generalize 2 ^ l = P at *
      obtain ⟨h, rfl⟩ : ∃ h, Q = 2 * h + 1 := ⟨Q / 2, by omega⟩
      have e1 : (2 * h + 1) * P = 2 * (h * P) + P := by rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
      have e2 : (2 * (h * P) + P - 1) / P = 2 * h :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_assoc]; omega) (by rw [Nat.add_mul, Nat.mul_assoc]; omega)
      have e3 : (2 * h + 1) / 2 * (P * 2) = 2 * (h * P) := by
        rw [show (2 * h + 1) / 2 = h by omega, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm h 2,
          Nat.mul_assoc]
      rw [e1] at hk ⊢
      have hc := pgBlock_combine pos (j := 2 * (h * P)) (m := 2 * (h * P) + P - 1) (k := k) (by omega) (by omega)
      rw [show 2 * (h * P) + P - 1 + 1 = 2 * (h * P) + P by omega] at hc
      rw [e2, e3, Nat.mul_assoc]
      exact hc
    · next hb =>
      rw [sklRec_block pos l k, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      generalize k / 2 ^ l = Q at *
      generalize 2 ^ l = P at *
      obtain ⟨h, rfl⟩ : ∃ h, Q = 2 * h := ⟨Q / 2, by omega⟩
      rw [show 2 * h / 2 = h by omega, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm h 2]

/-! ## 2. Structure and ports -/

/-- `CombDesign` for every `N` in range, and the shared obligations (`auto`, `inRange`) that the rank and the equations
read from the context instead of normalizing them again. -/
theorem skl_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- `Acyclic` for every `N` in range: the rank of level `l + 1` is `l + 1`, the sum and the carry out come last. -/
theorem skl_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N))
    (hso : SharedObl design.pdesign [N]) : Acyclic (design.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (l.toNat + 1, 0, 0)
    | .fam "g_sum" _ _ => (40, 0, 0)
    | .plain 2 => (40, 0, 0)
    | _ => (0, 0, 0)) using hc
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- The task's interface: `a`, `b`, `cin` in, `s`, `cout` out, with the task's widths. -/
theorem skl_interface (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The statement -/

/-- **The Sklansky adder meets the `add` statement**, at every `N` with `1 ≤ N < 2^20`. -/
theorem solution : Goal := by
  intro N hN
  have hN1 : 1 ≤ N := hN.1
  have hR : N < 2 ^ 20 := hN.2
  obtain ⟨hc, hso⟩ := skl_comb N hN1 hR
  have ha := skl_acyclic N hN1 hR hc hso
  refine CombTask.satisfiedAt_of_comb (skl_interface N hN1 hR hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, LeanModels.Sv.CombTask.bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool] at hv ⊢
  obtain ⟨hA, hB, hC⟩ := hv
  have bit_a : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
  have bit_b : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
  have bit_cin : st.boolAt "cin" 0 = c0 :=
    (SvState.boolAt_ofBitVec hC (by decide)).trans (LeanModels.Sv.CombTask.getLsbD_ofBool_zero c0)
  sv_equations
  · sv_eq_nat
    -- every level holds the Sklansky recurrence
    have hlev : ∀ l, l ≤ clog2 (N + 1) → ∀ k, k ≤ N →
        (st.boolAt "g" (l * (N + 1) + k), st.boolAt "p" (l * (N + 1) + k)) =
          sklRec (addPos x.getLsbD y.getLsbD c0) l k := by
      intro l
      induction l with
      | zero =>
        intro _ k hk
        rcases k with _ | i
        · simp [sklRec, eq_g_plain_0, eq_p_plain_1, bit_cin]
        · simp [sklRec, eq_g_g_in_1 i (by omega), eq_p_g_in_2 i (by omega), bit_a i (by omega), bit_b i (by omega)]
      | succ l ih =>
        intro hl k hk
        rw [sklRec]
        split
        · next hg =>
          rw [eq_g_g_node_0 l (by omega) k (by omega) hg, eq_p_g_node_1 l (by omega) k (by omega) hg,
            ← ih (by omega) k hk,
            ← ih (by omega) (k / 2 ^ l * 2 ^ l - 1)
              (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.div_mul_le_self _ _) hk))]
          rfl
        · next hg =>
          rw [eq_g_g_node_2 l (by omega) k (by omega) hg, eq_p_g_node_3 l (by omega) k (by omega) hg,
            ← ih (by omega) k hk]
    -- the last level holds the carry into every bit
    have hcarry : ∀ k, k ≤ N →
        st.boolAt "g" (clog2 (N + 1) * (N + 1) + k) = rippleCarry x.getLsbD y.getLsbD c0 k := by
      intro k hk
      have h := hlev _ (Nat.le_refl _) k hk
      rw [sklRec_block, Nat.div_eq_of_lt (by have := le_two_pow_clog2 (N + 1); omega), Nat.zero_mul,
        pgBlock_addPos_zero] at h
      exact (Prod.mk.inj h).1
    -- the sum and the carry out, as `CombLib.add_spec` reads them, then the ports from their bits
    have hv : AddView N x y c0 (rippleCarry x.getLsbD y.getLsbD c0) (XF.bv N (st.boolAt "s")).getLsbD
        (st.boolAt "cout" 0) := by
      refine ⟨rfl, fun i _ => rfl, fun i hi => ?_, ?_⟩
      · rw [XF.getLsbD_bv hi, eq_s_g_sum_0 i hi, eq_x_g_in_0 i hi, bit_a i hi, bit_b i hi, hcarry i (by omega)]
      · rw [eq_cout_plain_2, hcarry N (Nat.le_refl N)]
    obtain ⟨h1, h2⟩ := add_spec hv
    rw [SvState.port_ofBitVec known_s_g_sum_0 (by omega) (by omega), SvState.port_ofBool known_cout_plain_2 rfl, h1, h2]
    exact ⟨rfl, rfl⟩
  sv_obligations

/-! ## Axioms -/

/-- info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
