/- GID: D5/S3/Combinatorics/Permutation/Verkama62Representation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Representation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One-based pattern notation and exact inversion-count transports for northeast ear runs. -/

import D5.S3.Combinatorics.Permutation.Verkama62Charge
import D5.S3.Combinatorics.IndecomposableInversion.FranklinInversionDefs
import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsWord
import Mathlib.Algebra.BigOperators.Fin

/-! Finite permutations, one-based words, and the rational coefficient seven quarters. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open D5.S3.Combinatorics.IndecomposableInversion

private theorem pattern_one_based (i : Fin 6) :
    (pattern i).val + 1 = (![3, 5, 1, 6, 2, 4] : Fin 6 → ℕ) i := by
  fin_cases i <;> rfl

/-- Classical 351624 in the printed one-based notation. -/
def ContainsOneBased {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ f : Fin 6 ↪o Fin n, ∀ i j,
    (![3, 5, 1, 6, 2, 4] : Fin 6 → ℕ) i < ![3, 5, 1, 6, 2, 4] j ↔
      (π (f i)).val + 1 < (π (f j)).val + 1

private theorem contains_one_based_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ContainsOneBased π ↔ Contains pattern π := by
  unfold ContainsOneBased Contains
  simp only [← pattern_one_based, Nat.add_lt_add_iff_right, Fin.val_fin_lt]

/-- Franklin's list inversion counter equals the increasing-position pair count. -/
theorem word_inversions {n : ℕ} (π : Equiv.Perm (Fin n)) :
    FranklinInversionDefs.inv (PSW.word π) = inversions π Finset.univ := by
  have hlength : (PSW.word π).length = n := by simp [PSW.word]
  have hget (i : Fin n) : (PSW.word π).getD i.val 0 = (π i).val + 1 := by
    simp [PSW.word, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
  unfold FranklinInversionDefs.inv
  rw [hlength]
  rw [← List.sum_toFinset _ (List.nodup_range (n := n))]
  simp only [List.toFinset_range, Finset.sum_range]
  unfold inversions
  apply Finset.sum_congr rfl
  intro i hi
  rw [← List.countP_eq_length_filter,
    ← (List.nodup_range (n := n)).card_eq_countP]
  simp only [List.toFinset_range, Finset.card_filter, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  change (if i.val < j.val ∧ (PSW.word π).getD j.val 0 <
    (PSW.word π).getD i.val 0 then 1 else 0) = _
  rw [hget i, hget j]
  simp only [Nat.add_lt_add_iff_right, Fin.val_fin_lt]

/-- The exact rational lower bound for every avoiding permutation supplied with
    a northeast ear run. The existence of the run is an explicit hypothesis. -/
theorem rational_bound_of_ear_run {n : ℕ} (π : Equiv.Perm (Fin n))
    (havoid : ¬ ContainsOneBased π) (run : EarRun π Finset.univ) :
    (7 / 4 : ℚ) * n - 3 ≤ (FranklinInversionDefs.inv (PSW.word π) : ℚ) := by
  have ha : ¬ Contains pattern π := by rwa [← contains_one_based_iff]
  have h := ear_run_bound run ha
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [← word_inversions π] at h
  have hq : (7 : ℚ) * n ≤ 4 * (FranklinInversionDefs.inv (PSW.word π) : ℚ) + 12 :=
    by exact_mod_cast h
  linarith

end D5.S3.Combinatorics.Permutation.Verkama62Local
