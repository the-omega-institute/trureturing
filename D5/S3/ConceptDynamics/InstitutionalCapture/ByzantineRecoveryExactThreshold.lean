/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryExactThreshold
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryExactThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Universal deterministic Boolean recovery holds exactly above twice the fault bound. -/

import D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineRecoveryImpossibility

/- Library-search audit trail (2026-08-27):
   * Exact D5 primitives `byzantineCount` and `strictMajority` supply the
     report-disagreement count and the canonical strict-majority rule.
   * Exact D5 theorem `deterministic_recovery_impossible` supplies necessity
     at `n <= 2 * f`; `strict_majority_recovers` supplies sufficiency above it.
   * Searches found no existing theorem joining both directions into the exact
     threshold. Pinned Mathlib contributes only core option simplification;
     `loogle` and `leansearch` were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineRecoveryExactThreshold

open D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery
open D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineRecoveryImpossibility

/-- A deterministic rule recovers every Boolean truth from every report vector
with at most `f` disagreements exactly when the population is larger than twice
the allowed fault bound. -/
theorem deterministic_recovery_exact_threshold (n f : Nat) :
    (∃ recovery : (Fin n -> Bool) -> Bool,
      ∀ truth reports, byzantineCount reports truth ≤ f ->
        recovery reports = truth) ↔
      n > 2 * f := by
  constructor
  · intro recovery
    by_contra notThreshold
    exact deterministic_recovery_impossible
      (Nat.le_of_not_gt notThreshold) recovery
  · intro threshold
    refine ⟨fun reports => (strictMajority reports).getD false, ?_⟩
    intro truth reports byzantineBound
    have recovered :=
      strict_majority_recovers truth reports threshold byzantineBound
    simp [recovered]

/-- Three reports with one allowed disagreement lie on the recoverable side of
the exact threshold. -/
example :
    ∃ recovery : (Fin 3 -> Bool) -> Bool,
      ∀ truth reports, byzantineCount reports truth ≤ 1 ->
        recovery reports = truth := by
  exact (deterministic_recovery_exact_threshold 3 1).mpr (by decide)

/-- Two reports with one allowed disagreement lie on the impossible side. -/
example :
    ¬∃ recovery : (Fin 2 -> Bool) -> Bool,
      ∀ truth reports, byzantineCount reports truth ≤ 1 ->
        recovery reports = truth := by
  exact deterministic_recovery_impossible (by decide)

#print axioms deterministic_recovery_exact_threshold

end D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineRecoveryExactThreshold
