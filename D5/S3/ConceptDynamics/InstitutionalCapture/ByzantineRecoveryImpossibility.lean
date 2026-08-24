/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryImpossibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryImpossibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: At or below the half-honest threshold, no deterministic rule always recovers truth. -/

import D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery
import Mathlib.Data.Fintype.Fin

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit `ByzantineMajorityRecovery.byzantineCount`
     supplies the family single source of truth for the number of reports that
     disagree with the common honest Boolean value.
   * Exact pinned-Mathlib hits `Fin.card_filter_val_lt` and
     `Finset.card_filter_add_card_filter_not` count the two parts of the
     adversarial report vector constructed below.
   * Searches for the `n ≤ 2 * f` deterministic-recovery impossibility found
     no complete declaration. `loogle` and `leansearch` were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineRecoveryImpossibility

open D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery

/-- If at most half the reporters are guaranteed honest, one report vector is
compatible with both Boolean truths under the allowed Byzantine bound. -/
theorem deterministic_recovery_impossible
    {n f : Nat} (threshold : n ≤ 2 * f) :
    ¬∃ recovery : (Fin n → Bool) → Bool,
      ∀ truth reports, byzantineCount reports truth ≤ f →
        recovery reports = truth := by
  rintro ⟨recovery, correct⟩
  by_cases small : n ≤ f
  · let reports : Fin n → Bool := fun _ => false
    have recovers_false : recovery reports = false := by
      apply correct false reports
      simp [byzantineCount, reports]
    have recovers_true : recovery reports = true := by
      apply correct true reports
      simpa [byzantineCount, reports] using small
    exact Bool.false_ne_true (recovers_false.symm.trans recovers_true)
  · have f_lt_n : f < n := Nat.lt_of_not_ge small
    let reports : Fin n → Bool := fun reporter => decide (reporter < f)
    have true_count :
        (Finset.univ.filter fun reporter => reports reporter = true).card = f := by
      simp [reports, Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt f_lt_n)]
    have false_bound : byzantineCount reports false ≤ f := by
      simpa [byzantineCount] using true_count.le
    have partition :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (fun reporter => reports reporter = true)
    have partition_count :
        (Finset.univ.filter fun reporter => reports reporter = true).card +
          (Finset.univ.filter fun reporter => ¬reports reporter = true).card = n := by
      simpa using partition
    have true_bound : byzantineCount reports true ≤ f := by
      have mismatch_count : byzantineCount reports true = n - f := by
        simp only [byzantineCount, ne_eq]
        omega
      omega
    have recovers_false : recovery reports = false :=
      correct false reports false_bound
    have recovers_true : recovery reports = true :=
      correct true reports true_bound
    exact Bool.false_ne_true (recovers_false.symm.trans recovers_true)

/- Two reporters and one allowed Byzantine reporter satisfy the threshold. -/
example :
    ¬∃ recovery : (Fin 2 → Bool) → Bool,
      ∀ truth reports, byzantineCount reports truth ≤ 1 →
        recovery reports = truth := by
  apply deterministic_recovery_impossible
  decide

example : Fin 2 := 0

#print axioms deterministic_recovery_impossible

end D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineRecoveryImpossibility
