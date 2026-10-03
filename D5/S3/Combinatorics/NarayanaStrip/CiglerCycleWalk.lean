/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk
   mirror-E: none(waiver:external-conjecture-resolution)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Bool]
   utility: none
   digest: Signed even-strip Dyck sums equal the specified walk counts on the four-k cycle. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkFolding
import Mathlib.Logic.Equiv.Bool

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalk

open CiglerCycleWalkDefs CiglerCycleWalkTransfer CiglerCycleWalkFolding
open scoped BigOperators

theorem result : CiglerCycleWalkDefs.claim := by
  intro parameter size positive
  have doubled : 2 * (2 * parameter) = 4 * parameter := by omega
  have strip_bound : 2 * (2 * parameter - 1) = 4 * parameter - 2 := by omega
  have path_bound : 2 * parameter - 1 + 1 = 2 * parameter := by omega
  have change_bound (first second length : ℕ) (equal : first = second)
      (first_positive : 0 < first) (second_positive : 0 < second) :
      (foldedAdj first ^ length) ⟨0, first_positive⟩ ⟨0, first_positive⟩ =
        (foldedAdj second ^ length) ⟨0, second_positive⟩ ⟨0, second_positive⟩ := by
    subst second
    rfl
  have strip_moments (length : ℕ) :
      signedStrip (4 * parameter - 2) (length + 1) =
        (foldedAdj (2 * parameter) ^ (length + 1)) ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    have paired := strip_eq_folded (2 * parameter - 1) length (by omega) (by omega)
    rw [strip_bound] at paired
    exact paired.trans (change_bound _ _ _ path_bound (by omega) (by omega))
  have folded_moments (length : ℕ) :
      (foldedAdj (2 * parameter) ^ length) ⟨0, by omega⟩ ⟨0, by omega⟩ =
        (walkCount (4 * parameter) length 0 : ℤ) +
          walkCount (4 * parameter) length (-1) := by
    have folded := folded_moment_eq_walkCount (2 * parameter) length (by omega)
    rw [doubled] at folded
    exact folded
  have cycle_parity_reflection (vertices length : ℕ) :
      walkCount (2 * vertices) (2 * length + 1) 0 = 0 ∧
        walkCount (2 * vertices) (2 * length + 2) (-1) = 0 ∧
        walkCount (2 * vertices) (2 * length + 1) (-1) =
          walkCount (2 * vertices) (2 * length + 1) 1 ∧
        (walkCount (2 * vertices) (2 * length + 2) 0 : ℤ) =
          2 * (walkCount (2 * vertices) (2 * length + 1) 1 : ℤ) := by
    classical
    let parityHom : ZMod (2 * vertices) →+* ZMod 2 :=
      ZMod.castHom (show 2 ∣ 2 * vertices from dvd_mul_right 2 vertices) (ZMod 2)
    have negative_one : (-1 : ZMod 2) = 1 := by decide
    have two_zero : (2 : ZMod 2) = 0 := by decide
    have step_parity (label : Bool) :
        parityHom (if label then 1 else -1) = 1 := by
      cases label <;> simp [negative_one]
    have endpoint_parity (count : ℕ) (word : Fin count → Bool) :
        parityHom (∑ index, if word index then (1 : ZMod (2 * vertices)) else -1) =
          (count : ZMod 2) := by
      rw [map_sum]
      simp_rw [step_parity]
      simp
    have odd_zero : walkCount (2 * vertices) (2 * length + 1) 0 = 0 := by
      unfold walkCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro word member
      have endpoint := (Finset.mem_filter.mp member).2
      have mapped := congrArg parityHom endpoint
      rw [endpoint_parity] at mapped
      norm_num at mapped
      rw [two_zero] at mapped
      norm_num at mapped
    have even_neighbor : walkCount (2 * vertices) (2 * length + 2) (-1) = 0 := by
      unfold walkCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro word member
      have endpoint := (Finset.mem_filter.mp member).2
      have mapped := congrArg parityHom endpoint
      rw [endpoint_parity] at mapped
      norm_num [negative_one] at mapped
      rw [two_zero] at mapped
      norm_num at mapped
    have reflection (count : ℕ) :
        walkCount (2 * vertices) count (-1) = walkCount (2 * vertices) count 1 := by
      let reverseSteps : (Fin count → Bool) ≃ (Fin count → Bool) :=
        Equiv.piCongrRight fun _ => Equiv.boolNot
      have opposite (word : Fin count → Bool) :
          (∑ index, if reverseSteps word index then (1 : ZMod (2 * vertices)) else -1) =
            -(∑ index, if word index then (1 : ZMod (2 * vertices)) else -1) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro index _
        change (if !(word index) then (1 : ZMod (2 * vertices)) else -1) =
          -(if word index then 1 else -1)
        cases word index <;> simp
      unfold walkCount
      apply Finset.card_equiv reverseSteps
      intro word
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [opposite]
      exact neg_eq_iff_eq_neg.symm
    have recurrence (count : ℕ) :
        walkCount (2 * vertices) (count + 1) 0 =
          walkCount (2 * vertices) count 1 + walkCount (2 * vertices) count (-1) := by
      unfold walkCount
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [← (Fin.consEquiv fun _ : Fin (count + 1) => Bool).sum_comp]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.consEquiv, Equiv.coe_fn_mk,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true,
        if_true, if_false]
      have plus (total : ZMod (2 * vertices)) : 1 + total = 0 ↔ total = -1 := by
        rw [add_comm, add_eq_zero_iff_eq_neg]
      have minus (total : ZMod (2 * vertices)) : -1 + total = 0 ↔ total = 1 := by
        rw [add_comm, add_eq_zero_iff_eq_neg, neg_neg]
      simp_rw [plus, minus]
      exact add_comm _ _
    refine ⟨odd_zero, even_neighbor, reflection (2 * length + 1), ?_⟩
    have successor : 2 * length + 2 = (2 * length + 1) + 1 := by omega
    rw [successor, recurrence, reflection, Nat.cast_add]
    ring
  have parity := cycle_parity_reflection (2 * parameter) size
  rw [doubled] at parity
  have odd_equality := strip_moments (2 * size)
  rw [folded_moments, parity.1, Nat.cast_zero, zero_add, parity.2.2.1] at odd_equality
  have even_equality := strip_moments (2 * size + 1)
  have successor : 2 * size + 1 + 1 = 2 * size + 2 := by omega
  rw [successor, folded_moments, parity.2.1, Nat.cast_zero, add_zero] at even_equality
  refine ⟨odd_equality, even_equality, ?_⟩
  rw [odd_equality]
  exact parity.2.2.2

end D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalk
