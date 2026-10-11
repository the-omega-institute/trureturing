/- GID: D5/S1/Words/EvilOdious/DyadicStatesLastThree
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/DyadicStatesLastThree
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Sixfold Thue-Morse counts are controlled by dyadic coefficient states. -/

/-
admission_basis: escape-witness
Module escape_witness: state_step_4
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15228.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry bind-only as an organization label; no proof content is claimed for them.
state_step_4 | proof_shape: content | frozen: none | escape_witness: state_step_4 | consumers: DyadicStatesLastThree.stateZ_step_4
state_step_5 | proof_shape: content | frozen: none | escape_witness: state_step_5 | consumers: DyadicStatesLastThree.stateZ_step_5
state_step_6 | proof_shape: content | frozen: none | escape_witness: state_step_6 | consumers: DyadicStatesLastThree.stateZ_step_6
stateZ_step_4 | proof_shape: content | frozen: none | escape_witness: stateZ_step_4 | consumers: DyadicPrefixBounds.h_state_step
stateZ_step_5 | proof_shape: content | frozen: none | escape_witness: stateZ_step_5 | consumers: DyadicPrefixBounds.h_state_step
stateZ_step_6 | proof_shape: content | frozen: none | escape_witness: stateZ_step_6 | consumers: DyadicPrefixBounds.c_prefix
Utility none: the declarations establish symbolic identities and recursions for arbitrary indices;
no standalone finite instance, numerical threshold reduction or certificate is asserted.
-/

import D5.S1.Words.EvilOdious.DyadicStatesFirstThree

namespace D5.S1.Words.EvilOdious.DyadicStatesLastThree
open D5.S1.Words.EvilOdious.SequenceCoefficients
open D5.S1.Words.EvilOdious.MatrixBounds
open D5.S1.Words.EvilOdious.DyadicStatesFirstThree

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Finset Matrix

private theorem state_step_4 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 4) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 4) b).mulVec (state 5 (p 4) n) := by
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

private theorem state_step_5 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 5) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 5) b).mulVec (state 5 (p 5) n) := by
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

private theorem state_step_6 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 6 (p 6) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 6 (p 6) b).mulVec (state 6 (p 6) n) := by
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
    have hl6 : 6 ≤ 2 * n := by omega
    have hd6 : 2 ∣ (2 * n) - 6 := by omega
    have hq6 : ((2 * n) - 6) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n + 1 := by omega
    have hd6 : ¬ 2 ∣ (2 * n + 1) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n - 1 := by omega
    have hd6 : ¬ 2 ∣ (2 * n - 1) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n + 1 - 1 := by omega
    have hd6 : 2 ∣ (2 * n + 1 - 1) - 6 := by omega
    have hq6 : ((2 * n + 1 - 1) - 6) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n - 2 := by omega
    have hd6 : 2 ∣ (2 * n - 2) - 6 := by omega
    have hq6 : ((2 * n - 2) - 6) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n + 1 - 2 := by omega
    have hd6 : ¬ 2 ∣ (2 * n + 1 - 2) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n - 3 := by omega
    have hd6 : ¬ 2 ∣ (2 * n - 3) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n + 1 - 3 := by omega
    have hd6 : 2 ∣ (2 * n + 1 - 3) - 6 := by omega
    have hq6 : ((2 * n + 1 - 3) - 6) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n - 4 := by omega
    have hd6 : 2 ∣ (2 * n - 4) - 6 := by omega
    have hq6 : ((2 * n - 4) - 6) / 2 = n - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
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
    have hl6 : 6 ≤ 2 * n + 1 - 4 := by omega
    have hd6 : ¬ 2 ∣ (2 * n + 1 - 4) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 5 := by omega
    have hd0 : ¬ 2 ∣ (2 * n - 5) := by omega
    have hl1 : 1 ≤ 2 * n - 5 := by omega
    have hd1 : 2 ∣ (2 * n - 5) - 1 := by omega
    have hq1 : ((2 * n - 5) - 1) / 2 = n - 3 := by omega
    have hl2 : 2 ≤ 2 * n - 5 := by omega
    have hd2 : ¬ 2 ∣ (2 * n - 5) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 5 := by omega
    have hd3 : 2 ∣ (2 * n - 5) - 3 := by omega
    have hq3 : ((2 * n - 5) - 3) / 2 = n - 4 := by omega
    have hl4 : 4 ≤ 2 * n - 5 := by omega
    have hd4 : ¬ 2 ∣ (2 * n - 5) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 5 := by omega
    have hd5 : 2 ∣ (2 * n - 5) - 5 := by omega
    have hq5 : ((2 * n - 5) - 5) / 2 = n - 5 := by omega
    have hl6 : 6 ≤ 2 * n - 5 := by omega
    have hd6 : ¬ 2 ∣ (2 * n - 5) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 5 := by omega
    have hd0 : 2 ∣ (2 * n + 1 - 5) := by omega
    have hq0 : ((2 * n + 1 - 5)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 5 := by omega
    have hd1 : ¬ 2 ∣ (2 * n + 1 - 5) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 5 := by omega
    have hd2 : 2 ∣ (2 * n + 1 - 5) - 2 := by omega
    have hq2 : ((2 * n + 1 - 5) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 5 := by omega
    have hd3 : ¬ 2 ∣ (2 * n + 1 - 5) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 5 := by omega
    have hd4 : 2 ∣ (2 * n + 1 - 5) - 4 := by omega
    have hq4 : ((2 * n + 1 - 5) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 5 := by omega
    have hd5 : ¬ 2 ∣ (2 * n + 1 - 5) - 5 := by omega
    have hl6 : 6 ≤ 2 * n + 1 - 5 := by omega
    have hd6 : 2 ∣ (2 * n + 1 - 5) - 6 := by omega
    have hq6 : ((2 * n + 1 - 5) - 6) / 2 = n - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring



theorem stateZ_step_4 (n : ℕ) (b : Bool) :
    stateZ 5 (p 4) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 4) b).mulVec (stateZ 5 (p 4) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 4) n hl,
      stateZ_eq_state 5 (by decide) (p 4) _ (by omega)]
    exact state_step_4 n hl b

theorem stateZ_step_5 (n : ℕ) (b : Bool) :
    stateZ 5 (p 5) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 5) b).mulVec (stateZ 5 (p 5) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 5) n hl,
      stateZ_eq_state 5 (by decide) (p 5) _ (by omega)]
    exact state_step_5 n hl b

theorem stateZ_step_6 (n : ℕ) (b : Bool) :
    stateZ 6 (p 6) (2*n+(if b then 1 else 0)) =
      (stateMatrix 6 (p 6) b).mulVec (stateZ 6 (p 6) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 6 (by decide) (p 6) n hl,
      stateZ_eq_state 6 (by decide) (p 6) _ (by omega)]
    exact state_step_6 n hl b

end D5.S1.Words.EvilOdious.DyadicStatesLastThree
