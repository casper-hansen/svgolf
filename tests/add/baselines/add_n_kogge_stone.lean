import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombTaskTactic
import LeanModels.Sv.Lib.Prefix

/-!
# Task `add`: the Kogge-Stone parallel-prefix adder `add_n_kogge_stone.sv`, proved with the `sv_comb` tactics

The design, as written: positions `0 … N` (position `0` is `cin` with propagate `0`, position `k + 1` is bit `k`),
`L = $clog2(N + 1)` levels of a 2-D array pair `g, p : [L:0][N:0]`, level `l + 1` combining position `i` with
position `i - (1 << l)` when `i >= (1 << l)` (a conditional generate inside the nested level/node loops) and
passing it through otherwise; `s[i] = x[i] ^ g[L][i]`, `cout = g[L][N]`. Proved for every `N` with `1 ≤ N < 2^20`:

1. **Structure** (`ks_comb`, `ks_acyclic`): `sv_structure` proves `CombDesign` with the shared obligations
   (`SharedObl`), then `Acyclic` from them (the rank of level `l + 1` is `l + 1`, the sum and the carry out last).
2. **Ports** (`ks_interface`): `sv_interface`.
3. **Equations** (in `solution`): `CombTask.satisfiedAt_of_comb` reduces the statement to one settled-state lemma;
   `sv_equations` derives the netlist's equations over `Bool` from the semantics (the atom `2 ^ l` where the source
   has `1 << l`) and the knownness of every driven bit; `sv_eq_nat` states them at `Nat` indices (the level count
   `clog2 (N + 1)` unwrapped from its 32-bit reading); the obligations close by `sv_obligations`.
4. **The prefix mathematics** (`ksRec_block`): after level `l` position `k` holds the generate/propagate pair of the
   block `[k + 1 - 2^l, k]` of the adder's positions (`LeanModels.Sv.Lib.pgBlock`, natural subtraction), so level `L`
   holds the carry into every bit, and `CombLib.add_spec` turns the ripple carries into the task's sum.

The route and the prefix lemma follow Proglib's `Examples/system-verilog/prefix_ks/add_proof.lean` (a clean-room
Kogge-Stone design proved against the same statement restated over ls-sv); here the statement is svGolf's own, reached
through `CombTask.satisfiedAt_of_comb`. No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq LeanModels.Sv.Lib SvGolf

/-! ## 1. The prefix mathematics (plain `Bool`/`Nat`) -/

/-- The Kogge-Stone recurrence as the design denotes it: level `0` is the positions `pos`; level `l + 1` at position
`k` joins `(l, k)` with `(l, k - 2^l)` where `2^l ≤ k`, and copies `(l, k)` otherwise. -/
def ksRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, k => pos k
  | l + 1, k => if 2 ^ l ≤ k then pgOp (ksRec pos l k) (ksRec pos l (k - 2 ^ l)) else ksRec pos l k

/-- After level `l`, position `k` holds the pair of the block `[k + 1 - 2^l, k]` (natural subtraction). -/
theorem ksRec_block (pos : Nat → Bool × Bool) : ∀ l k, ksRec pos l k = pgBlock pos (k + 1 - 2 ^ l) k
  | 0, k => by rw [ksRec, Nat.pow_zero, Nat.add_sub_cancel, pgBlock_self]
  | l + 1, k => by
    have hP : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [ksRec, hP]
    split
    · rw [ksRec_block pos l k, ksRec_block pos l (k - 2 ^ l)]
      generalize 2 ^ l = Q at *
      have hc := pgBlock_combine pos (j := k + 1 - 2 * Q) (m := k - Q) (k := k) (by omega) (by omega)
      rw [show k - Q + 1 = k + 1 - Q by omega] at hc
      rw [show k - Q + 1 - Q = k + 1 - 2 * Q by omega]
      exact hc
    · rw [ksRec_block pos l k]
      generalize 2 ^ l = Q at *
      rw [show k + 1 - Q = 0 by omega, show k + 1 - 2 * Q = 0 by omega]

/-! ## 2. Structure and ports -/

/-- `CombDesign` for every `N` in range, and the shared obligations (`auto`, `inRange`) that the rank and the equations
read from the context instead of normalizing them again. -/
theorem ks_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- `Acyclic` for every `N` in range: the rank of level `l + 1` is `l + 1`, the sum and the carry out come last. -/
theorem ks_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N))
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
theorem ks_interface (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The statement -/

/-- **The Kogge-Stone adder meets the `add` statement**, at every `N` with `1 ≤ N < 2^20`. -/
theorem solution : Goal := by
  intro N hN
  have hN1 : 1 ≤ N := hN.1
  have hR : N < 2 ^ 20 := hN.2
  obtain ⟨hc, hso⟩ := ks_comb N hN1 hR
  have ha := ks_acyclic N hN1 hR hc hso
  refine CombTask.satisfiedAt_of_comb (ks_interface N hN1 hR hc) hc ha ?_
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
    -- every level holds the Kogge-Stone recurrence
    have hlev : ∀ l, l ≤ clog2 (N + 1) → ∀ k, k ≤ N →
        (st.boolAt "g" (l * (N + 1) + k), st.boolAt "p" (l * (N + 1) + k)) =
          ksRec (addPos x.getLsbD y.getLsbD c0) l k := by
      intro l
      induction l with
      | zero =>
        intro _ k hk
        rcases k with _ | i
        · simp [ksRec, eq_g_plain_0, eq_p_plain_1, bit_cin]
        · simp [ksRec, eq_g_g_in_1 i (by omega), eq_p_g_in_2 i (by omega), bit_a i (by omega), bit_b i (by omega)]
      | succ l ih =>
        intro hl k hk
        rw [ksRec]
        split
        · next hg =>
          rw [eq_g_g_node_0 l (by omega) k (by omega) hg, eq_p_g_node_1 l (by omega) k (by omega) hg,
            ← ih (by omega) k hk, ← ih (by omega) (k - 2 ^ l) (Nat.le_trans (Nat.sub_le _ _) hk)]
          rfl
        · next hg =>
          rw [eq_g_g_node_2 l (by omega) k (by omega) hg, eq_p_g_node_3 l (by omega) k (by omega) hg,
            ← ih (by omega) k hk]
    -- the last level holds the carry into every bit
    have hcarry : ∀ k, k ≤ N →
        st.boolAt "g" (clog2 (N + 1) * (N + 1) + k) = rippleCarry x.getLsbD y.getLsbD c0 k := by
      intro k hk
      have h := hlev _ (Nat.le_refl _) k hk
      rw [ksRec_block, show k + 1 - 2 ^ clog2 (N + 1) = 0 by have := le_two_pow_clog2 (N + 1); omega,
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
