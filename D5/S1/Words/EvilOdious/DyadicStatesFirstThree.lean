/- GID: D5/S1/Words/EvilOdious/DyadicStatesFirstThree
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/DyadicStatesFirstThree
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Sixfold Thue-Morse counts are controlled by dyadic coefficient states. -/

/-
admission_basis: escape-witness
Module escape_witness: state_word
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15228.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry bind-only as an organization label; no proof content is claimed for them.
state | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.h_seed, DyadicStatesFirstThree.stateZ_eq_state, DyadicStatesFirstThree.stateZ_step_1, DyadicStatesFirstThree.stateZ_step_2, DyadicStatesFirstThree.stateZ_step_3, DyadicStatesFirstThree.state_step_1, DyadicStatesFirstThree.state_step_2, DyadicStatesFirstThree.state_step_3, DyadicStatesLastThree.stateZ_step_4, DyadicStatesLastThree.stateZ_step_5, DyadicStatesLastThree.stateZ_step_6, DyadicStatesLastThree.state_step_4, DyadicStatesLastThree.state_step_5, DyadicStatesLastThree.state_step_6
recur_pos | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicStatesFirstThree.state_step_1, DyadicStatesFirstThree.state_step_2, DyadicStatesFirstThree.state_step_3, DyadicStatesLastThree.state_step_4, DyadicStatesLastThree.state_step_5, DyadicStatesLastThree.state_step_6
state_step_1 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicStatesFirstThree.stateZ_step_1
state_step_2 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicStatesFirstThree.stateZ_step_2
state_step_3 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicStatesFirstThree.stateZ_step_3
stateZ | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.h_state_step, DyadicStatesFirstThree.stateZ_eq_state, DyadicStatesFirstThree.stateZ_step_1, DyadicStatesFirstThree.stateZ_step_2, DyadicStatesFirstThree.stateZ_step_3, DyadicStatesFirstThree.state_word, DyadicStatesFirstThree.vector_prefix_bound, DyadicStatesLastThree.stateZ_step_4, DyadicStatesLastThree.stateZ_step_5, DyadicStatesLastThree.stateZ_step_6, DyadicStatesLastThree.state_dyadic_bound
stateZ_eq_state | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.h_seed, DyadicStatesFirstThree.stateZ_step_1, DyadicStatesFirstThree.stateZ_step_2, DyadicStatesFirstThree.stateZ_step_3, DyadicStatesLastThree.stateZ_step_4, DyadicStatesLastThree.stateZ_step_5, DyadicStatesLastThree.stateZ_step_6
stateZ_step_1 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_state_step
stateZ_step_2 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_state_step
stateZ_step_3 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_state_step
appendValue | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.appendValue_ge, DyadicPrefixBounds.c_dyadic, DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.h_dyadic, DyadicPrefixBounds.h_prefix, DyadicStatesFirstThree.appendValue_cons, DyadicStatesFirstThree.state_word, DyadicStatesFirstThree.vector_prefix_bound, DyadicStatesLastThree.appendValue_decompose, DyadicStatesLastThree.lowWord_bound, DyadicStatesLastThree.state_dyadic_bound, DyadicStatesLastThree.word_for_low, SixfoldMonotonicity.error_prefix, SixfoldMonotonicity.prefix_exists, SixfoldMonotonicity.prefix_scale_lower, SixfoldMonotonicity.tail_positive
appendValue_cons | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.appendValue_ge, DyadicStatesFirstThree.state_word, SixfoldMonotonicity.prefix_exists, SixfoldMonotonicity.prefix_scale_lower
state_word | proof_shape: content | frozen: none | escape_witness: state_word | consumers: DyadicStatesFirstThree.vector_prefix_bound
vector_prefix_bound | proof_shape: content | frozen: none | escape_witness: state_word | consumers: DyadicStatesLastThree.state_dyadic_bound
Content reason: state_word proves by word induction that one-bit transitions compose into a matrix product.
It supplies vector_prefix_bound and state_dyadic_bound; unfolding one transition does not prove an arbitrary word.
Utility none: these symbolic identities and estimates quantify over arbitrary indices.
-/

import D5.S1.Words.EvilOdious.MatrixBounds

namespace D5.S1.Words.EvilOdious.DyadicStatesFirstThree
open D5.S1.Words.EvilOdious.SequenceCoefficients
open D5.S1.Words.EvilOdious.MatrixBounds

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Finset Matrix

def state (d : ℕ) (q : List ℤ) (n : ℕ) : Fin d → ℤ := fun i => recur q (n - i)

theorem recur_pos (q : List ℤ) (N : ℕ) (hn : 0 < N) :
    recur q N = ∑ k ∈ Finset.range q.length,
      if k ≤ N ∧ 2 ∣ N - k then (List.getD q k 0) * recur q ((N - k) / 2) else 0 := by
  cases N with
  | zero => omega
  | succ n => rw [recur]



set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Finset Matrix

private theorem state_step_1 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 1) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 1) b).mulVec (state 5 (p 1) n) := by
  ext i
  fin_cases i <;> cases b
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n := by omega
    have hd0 : 2 ∣ (2 * n) := by omega
    have hq0 : ((2 * n)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n := by omega
    have hd1 : ¬ 2 ∣ (2 * n) - 1 := by omega
    have hl2 : 2 ≤ 2 * n := by omega
    have hd2 : 2 ∣ (2 * n) - 2 := by omega
    have hq2 : ((2 * n) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n := by omega
    have hd3 : ¬ 2 ∣ (2 * n) - 3 := by omega
    have hl4 : 4 ≤ 2 * n := by omega
    have hd4 : 2 ∣ (2 * n) - 4 := by omega
    have hq4 : ((2 * n) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n := by omega
    have hd5 : ¬ 2 ∣ (2 * n) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1) := by omega
    have hl1 : 1 ≤ 2 * n + 1 := by omega
    have hd1 : 2 ∣ (2 * n + 1) - 1 := by omega
    have hq1 : ((2 * n + 1) - 1) / 2 = n - 0 := by omega
    have hl2 : 2 ≤ 2 * n + 1 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 := by omega
    have hd3 : 2 ∣ (2 * n + 1) - 3 := by omega
    have hq3 : ((2 * n + 1) - 3) / 2 = n - 1 := by omega
    have hl4 : 4 ≤ 2 * n + 1 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 := by omega
    have hd5 : 2 ∣ (2 * n + 1) - 5 := by omega
    have hq5 : ((2 * n + 1) - 5) / 2 = n - 2 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 1 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 1) := by omega
    have hl1 : 1 ≤ 2 * n - 1 := by omega
    have hd1 : 2 ∣ (2 * n - 1) - 1 := by omega
    have hq1 : ((2 * n - 1) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 1 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 1 := by omega
    have hd3 : 2 ∣ (2 * n - 1) - 3 := by omega
    have hq3 : ((2 * n - 1) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n - 1 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 1 := by omega
    have hd5 : 2 ∣ (2 * n - 1) - 5 := by omega
    have hq5 : ((2 * n - 1) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 1 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 1) := by omega
    have hq0 : ((2 * n + 1 - 1)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 1 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 1) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 1 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 1) - 2 := by omega
    have hq2 : ((2 * n + 1 - 1) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 1 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 1) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 1 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 1) - 4 := by omega
    have hq4 : ((2 * n + 1 - 1) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 1 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 1) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 2 := by omega
    have hd0 : 2 ∣ (2 * n - 2) := by omega
    have hq0 : ((2 * n - 2)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n - 2 := by omega
    have hd1 : ¬ 2 ∣ (2 * n - 2) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 2 := by omega
    have hd2 : 2 ∣ (2 * n - 2) - 2 := by omega
    have hq2 : ((2 * n - 2) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 2 := by omega
    have hd3 : ¬ 2 ∣ (2 * n - 2) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 2 := by omega
    have hd4 : 2 ∣ (2 * n - 2) - 4 := by omega
    have hq4 : ((2 * n - 2) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n - 2 := by omega
    have hd5 : ¬ 2 ∣ (2 * n - 2) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 2 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1 - 2) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 2 := by omega
    have hd1 : 2 ∣ (2 * n + 1 - 2) - 1 := by omega
    have hq1 : ((2 * n + 1 - 2) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 2 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1 - 2) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 2 := by omega
    have hd3 : 2 ∣ (2 * n + 1 - 2) - 3 := by omega
    have hq3 : ((2 * n + 1 - 2) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 2 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1 - 2) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 2 := by omega
    have hd5 : 2 ∣ (2 * n + 1 - 2) - 5 := by omega
    have hq5 : ((2 * n + 1 - 2) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 3 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 3) := by omega
    have hl1 : 1 ≤ 2 * n - 3 := by omega
    have hd1 : 2 ∣ (2 * n - 3) - 1 := by omega
    have hq1 : ((2 * n - 3) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n - 3 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 3) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 3 := by omega
    have hd3 : 2 ∣ (2 * n - 3) - 3 := by omega
    have hq3 : ((2 * n - 3) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 3 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 3) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 3 := by omega
    have hd5 : 2 ∣ (2 * n - 3) - 5 := by omega
    have hq5 : ((2 * n - 3) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 3 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 3) := by omega
    have hq0 : ((2 * n + 1 - 3)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 3 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 3) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 3 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 3) - 2 := by omega
    have hq2 : ((2 * n + 1 - 3) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 3 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 3) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 3 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 3) - 4 := by omega
    have hq4 : ((2 * n + 1 - 3) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 3 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 3) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 4 := by omega
    have hd0 : 2 ∣ (2 * n - 4) := by omega
    have hq0 : ((2 * n - 4)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n - 4 := by omega
    have hd1 : ¬ 2 ∣ (2 * n - 4) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 4 := by omega
    have hd2 : 2 ∣ (2 * n - 4) - 2 := by omega
    have hq2 : ((2 * n - 4) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n - 4 := by omega
    have hd3 : ¬ 2 ∣ (2 * n - 4) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 4 := by omega
    have hd4 : 2 ∣ (2 * n - 4) - 4 := by omega
    have hq4 : ((2 * n - 4) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 4 := by omega
    have hd5 : ¬ 2 ∣ (2 * n - 4) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 4 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1 - 4) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 4 := by omega
    have hd1 : 2 ∣ (2 * n + 1 - 4) - 1 := by omega
    have hq1 : ((2 * n + 1 - 4) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 4 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1 - 4) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 4 := by omega
    have hd3 : 2 ∣ (2 * n + 1 - 4) - 3 := by omega
    have hq3 : ((2 * n + 1 - 4) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 4 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1 - 4) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 4 := by omega
    have hd5 : 2 ∣ (2 * n + 1 - 4) - 5 := by omega
    have hq5 : ((2 * n + 1 - 4) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring

private theorem state_step_2 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 2) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 2) b).mulVec (state 5 (p 2) n) := by
  ext i
  fin_cases i <;> cases b
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n := by omega
    have hd0 : 2 ∣ (2 * n) := by omega
    have hq0 : ((2 * n)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n := by omega
    have hd1 : ¬ 2 ∣ (2 * n) - 1 := by omega
    have hl2 : 2 ≤ 2 * n := by omega
    have hd2 : 2 ∣ (2 * n) - 2 := by omega
    have hq2 : ((2 * n) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n := by omega
    have hd3 : ¬ 2 ∣ (2 * n) - 3 := by omega
    have hl4 : 4 ≤ 2 * n := by omega
    have hd4 : 2 ∣ (2 * n) - 4 := by omega
    have hq4 : ((2 * n) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n := by omega
    have hd5 : ¬ 2 ∣ (2 * n) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1) := by omega
    have hl1 : 1 ≤ 2 * n + 1 := by omega
    have hd1 : 2 ∣ (2 * n + 1) - 1 := by omega
    have hq1 : ((2 * n + 1) - 1) / 2 = n - 0 := by omega
    have hl2 : 2 ≤ 2 * n + 1 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 := by omega
    have hd3 : 2 ∣ (2 * n + 1) - 3 := by omega
    have hq3 : ((2 * n + 1) - 3) / 2 = n - 1 := by omega
    have hl4 : 4 ≤ 2 * n + 1 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 := by omega
    have hd5 : 2 ∣ (2 * n + 1) - 5 := by omega
    have hq5 : ((2 * n + 1) - 5) / 2 = n - 2 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 1 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 1) := by omega
    have hl1 : 1 ≤ 2 * n - 1 := by omega
    have hd1 : 2 ∣ (2 * n - 1) - 1 := by omega
    have hq1 : ((2 * n - 1) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 1 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 1 := by omega
    have hd3 : 2 ∣ (2 * n - 1) - 3 := by omega
    have hq3 : ((2 * n - 1) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n - 1 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 1 := by omega
    have hd5 : 2 ∣ (2 * n - 1) - 5 := by omega
    have hq5 : ((2 * n - 1) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 1 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 1) := by omega
    have hq0 : ((2 * n + 1 - 1)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 1 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 1) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 1 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 1) - 2 := by omega
    have hq2 : ((2 * n + 1 - 1) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 1 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 1) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 1 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 1) - 4 := by omega
    have hq4 : ((2 * n + 1 - 1) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 1 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 1) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 2 := by omega
    have hd0 : 2 ∣ (2 * n - 2) := by omega
    have hq0 : ((2 * n - 2)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n - 2 := by omega
    have hd1 : ¬ 2 ∣ (2 * n - 2) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 2 := by omega
    have hd2 : 2 ∣ (2 * n - 2) - 2 := by omega
    have hq2 : ((2 * n - 2) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 2 := by omega
    have hd3 : ¬ 2 ∣ (2 * n - 2) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 2 := by omega
    have hd4 : 2 ∣ (2 * n - 2) - 4 := by omega
    have hq4 : ((2 * n - 2) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n - 2 := by omega
    have hd5 : ¬ 2 ∣ (2 * n - 2) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 2 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1 - 2) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 2 := by omega
    have hd1 : 2 ∣ (2 * n + 1 - 2) - 1 := by omega
    have hq1 : ((2 * n + 1 - 2) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 2 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1 - 2) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 2 := by omega
    have hd3 : 2 ∣ (2 * n + 1 - 2) - 3 := by omega
    have hq3 : ((2 * n + 1 - 2) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 2 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1 - 2) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 2 := by omega
    have hd5 : 2 ∣ (2 * n + 1 - 2) - 5 := by omega
    have hq5 : ((2 * n + 1 - 2) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 3 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 3) := by omega
    have hl1 : 1 ≤ 2 * n - 3 := by omega
    have hd1 : 2 ∣ (2 * n - 3) - 1 := by omega
    have hq1 : ((2 * n - 3) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n - 3 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 3) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 3 := by omega
    have hd3 : 2 ∣ (2 * n - 3) - 3 := by omega
    have hq3 : ((2 * n - 3) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 3 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 3) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 3 := by omega
    have hd5 : 2 ∣ (2 * n - 3) - 5 := by omega
    have hq5 : ((2 * n - 3) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 3 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 3) := by omega
    have hq0 : ((2 * n + 1 - 3)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 3 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 3) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 3 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 3) - 2 := by omega
    have hq2 : ((2 * n + 1 - 3) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 3 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 3) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 3 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 3) - 4 := by omega
    have hq4 : ((2 * n + 1 - 3) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 3 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 3) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 4 := by omega
    have hd0 : 2 ∣ (2 * n - 4) := by omega
    have hq0 : ((2 * n - 4)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n - 4 := by omega
    have hd1 : ¬ 2 ∣ (2 * n - 4) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 4 := by omega
    have hd2 : 2 ∣ (2 * n - 4) - 2 := by omega
    have hq2 : ((2 * n - 4) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n - 4 := by omega
    have hd3 : ¬ 2 ∣ (2 * n - 4) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 4 := by omega
    have hd4 : 2 ∣ (2 * n - 4) - 4 := by omega
    have hq4 : ((2 * n - 4) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 4 := by omega
    have hd5 : ¬ 2 ∣ (2 * n - 4) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 4 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1 - 4) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 4 := by omega
    have hd1 : 2 ∣ (2 * n + 1 - 4) - 1 := by omega
    have hq1 : ((2 * n + 1 - 4) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 4 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1 - 4) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 4 := by omega
    have hd3 : 2 ∣ (2 * n + 1 - 4) - 3 := by omega
    have hq3 : ((2 * n + 1 - 4) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 4 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1 - 4) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 4 := by omega
    have hd5 : 2 ∣ (2 * n + 1 - 4) - 5 := by omega
    have hq5 : ((2 * n + 1 - 4) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring

private theorem state_step_3 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 3) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 3) b).mulVec (state 5 (p 3) n) := by
  ext i
  fin_cases i <;> cases b
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n := by omega
    have hd0 : 2 ∣ (2 * n) := by omega
    have hq0 : ((2 * n)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n := by omega
    have hd1 : ¬ 2 ∣ (2 * n) - 1 := by omega
    have hl2 : 2 ≤ 2 * n := by omega
    have hd2 : 2 ∣ (2 * n) - 2 := by omega
    have hq2 : ((2 * n) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n := by omega
    have hd3 : ¬ 2 ∣ (2 * n) - 3 := by omega
    have hl4 : 4 ≤ 2 * n := by omega
    have hd4 : 2 ∣ (2 * n) - 4 := by omega
    have hq4 : ((2 * n) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n := by omega
    have hd5 : ¬ 2 ∣ (2 * n) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1) := by omega
    have hl1 : 1 ≤ 2 * n + 1 := by omega
    have hd1 : 2 ∣ (2 * n + 1) - 1 := by omega
    have hq1 : ((2 * n + 1) - 1) / 2 = n - 0 := by omega
    have hl2 : 2 ≤ 2 * n + 1 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 := by omega
    have hd3 : 2 ∣ (2 * n + 1) - 3 := by omega
    have hq3 : ((2 * n + 1) - 3) / 2 = n - 1 := by omega
    have hl4 : 4 ≤ 2 * n + 1 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 := by omega
    have hd5 : 2 ∣ (2 * n + 1) - 5 := by omega
    have hq5 : ((2 * n + 1) - 5) / 2 = n - 2 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 1 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 1) := by omega
    have hl1 : 1 ≤ 2 * n - 1 := by omega
    have hd1 : 2 ∣ (2 * n - 1) - 1 := by omega
    have hq1 : ((2 * n - 1) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 1 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 1 := by omega
    have hd3 : 2 ∣ (2 * n - 1) - 3 := by omega
    have hq3 : ((2 * n - 1) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n - 1 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 1 := by omega
    have hd5 : 2 ∣ (2 * n - 1) - 5 := by omega
    have hq5 : ((2 * n - 1) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 1 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 1) := by omega
    have hq0 : ((2 * n + 1 - 1)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 1 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 1) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 1 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 1) - 2 := by omega
    have hq2 : ((2 * n + 1 - 1) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 1 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 1) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 1 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 1) - 4 := by omega
    have hq4 : ((2 * n + 1 - 1) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 1 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 1) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 2 := by omega
    have hd0 : 2 ∣ (2 * n - 2) := by omega
    have hq0 : ((2 * n - 2)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n - 2 := by omega
    have hd1 : ¬ 2 ∣ (2 * n - 2) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 2 := by omega
    have hd2 : 2 ∣ (2 * n - 2) - 2 := by omega
    have hq2 : ((2 * n - 2) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 2 := by omega
    have hd3 : ¬ 2 ∣ (2 * n - 2) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 2 := by omega
    have hd4 : 2 ∣ (2 * n - 2) - 4 := by omega
    have hq4 : ((2 * n - 2) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n - 2 := by omega
    have hd5 : ¬ 2 ∣ (2 * n - 2) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 2 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1 - 2) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 2 := by omega
    have hd1 : 2 ∣ (2 * n + 1 - 2) - 1 := by omega
    have hq1 : ((2 * n + 1 - 2) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 2 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1 - 2) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 2 := by omega
    have hd3 : 2 ∣ (2 * n + 1 - 2) - 3 := by omega
    have hq3 : ((2 * n + 1 - 2) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 2 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1 - 2) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 2 := by omega
    have hd5 : 2 ∣ (2 * n + 1 - 2) - 5 := by omega
    have hq5 : ((2 * n + 1 - 2) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 3 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 3) := by omega
    have hl1 : 1 ≤ 2 * n - 3 := by omega
    have hd1 : 2 ∣ (2 * n - 3) - 1 := by omega
    have hq1 : ((2 * n - 3) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n - 3 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 3) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 3 := by omega
    have hd3 : 2 ∣ (2 * n - 3) - 3 := by omega
    have hq3 : ((2 * n - 3) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 3 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 3) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 3 := by omega
    have hd5 : 2 ∣ (2 * n - 3) - 5 := by omega
    have hq5 : ((2 * n - 3) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 3 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 3) := by omega
    have hq0 : ((2 * n + 1 - 3)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 3 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 3) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 3 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 3) - 2 := by omega
    have hq2 : ((2 * n + 1 - 3) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 3 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 3) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 3 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 3) - 4 := by omega
    have hq4 : ((2 * n + 1 - 3) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 3 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 3) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 4 := by omega
    have hd0 : 2 ∣ (2 * n - 4) := by omega
    have hq0 : ((2 * n - 4)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n - 4 := by omega
    have hd1 : ¬ 2 ∣ (2 * n - 4) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 4 := by omega
    have hd2 : 2 ∣ (2 * n - 4) - 2 := by omega
    have hq2 : ((2 * n - 4) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n - 4 := by omega
    have hd3 : ¬ 2 ∣ (2 * n - 4) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 4 := by omega
    have hd4 : 2 ∣ (2 * n - 4) - 4 := by omega
    have hq4 : ((2 * n - 4) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 4 := by omega
    have hd5 : ¬ 2 ∣ (2 * n - 4) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 4 := by omega
    have hd0 : ¬ 2 ∣ (2 * n + 1 - 4) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 4 := by omega
    have hd1 : 2 ∣ (2 * n + 1 - 4) - 1 := by omega
    have hq1 : ((2 * n + 1 - 4) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 4 := by omega
    have hd2 : ¬ 2 ∣ (2 * n + 1 - 4) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 4 := by omega
    have hd3 : 2 ∣ (2 * n + 1 - 4) - 3 := by omega
    have hq3 : ((2 * n + 1 - 4) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 4 := by omega
    have hd4 : ¬ 2 ∣ (2 * n + 1 - 4) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 4 := by omega
    have hd5 : 2 ∣ (2 * n + 1 - 4) - 5 := by omega
    have hq5 : ((2 * n + 1 - 4) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring




set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Finset Matrix

def stateZ (d : ℕ) (q : List ℤ) (n : ℕ) : Fin d → ℤ :=
  fun i => zrecur q ((n : ℤ) - (i : ℕ))

theorem stateZ_eq_state (d : ℕ) (hd : d ≤ 6) (q : List ℤ) (n : ℕ) (hn : 6 ≤ n) :
    stateZ d q n = state d q n := by
  ext i
  have hi := i.isLt
  simp only [stateZ, state, zrecur]
  rw [if_pos (by omega), Int.toNat_sub]

theorem stateZ_step_1 (n : ℕ) (b : Bool) :
    stateZ 5 (p 1) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 1) b).mulVec (stateZ 5 (p 1) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 1) n hl,
      stateZ_eq_state 5 (by decide) (p 1) _ (by omega)]
    exact state_step_1 n hl b

theorem stateZ_step_2 (n : ℕ) (b : Bool) :
    stateZ 5 (p 2) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 2) b).mulVec (stateZ 5 (p 2) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 2) n hl,
      stateZ_eq_state 5 (by decide) (p 2) _ (by omega)]
    exact state_step_2 n hl b

theorem stateZ_step_3 (n : ℕ) (b : Bool) :
    stateZ 5 (p 3) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 3) b).mulVec (stateZ 5 (p 3) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 3) n hl,
      stateZ_eq_state 5 (by decide) (p 3) _ (by omega)]
    exact state_step_3 n hl b

def appendValue (q : ℕ) (w : List Bool) : ℕ :=
  Nat.ofDigits 2 (w.map Bool.toNat ++ [q])


theorem appendValue_cons (q : ℕ) (b : Bool) (w : List Bool) :
    appendValue q (b :: w) = 2 * appendValue q w + (if b then 1 else 0) := by
  cases b <;> simp [appendValue, Nat.ofDigits_cons, Nat.add_comm]


theorem state_word {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n, ∀ b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (p : ℕ) (w : List Bool) :
    stateZ d q (appendValue p w) = (wordMatrix M w).mulVec (stateZ d q p) := by
  induction w with
  | nil => simp [appendValue, wordMatrix]
  | cons b w ih =>
    rw [appendValue_cons, step _, ih, Matrix.mulVec_mulVec]
    simp only [wordMatrix, List.map_cons, List.prod_cons]


theorem vector_prefix_bound {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n, ∀ b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (K : ℕ) (norm : ∀ w, matrixBound (wordMatrix M w) (K * 16 ^ w.length))
    (p : ℕ) (w : List Bool) (B : ℕ) (seed : vectorBound (stateZ d q p) B) :
    vectorBound (stateZ d q (appendValue p w)) (K * 16 ^ w.length * B) := by
  rw [state_word q M step p w]
  exact matrix_apply_bound _ _ _ _ (norm w) seed

end D5.S1.Words.EvilOdious.DyadicStatesFirstThree
