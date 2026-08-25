/- GID: D5/S3/ConceptDynamics/DecisionValueScale/OptimalAcceptanceThreshold
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/OptimalAcceptanceThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary expected-loss comparison is equivalent to the optimal acceptance threshold. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-25):
   * Repository searches for optimal acceptance, false-positive and
     false-negative costs, the source loss comparison, and the threshold
     quotient found no exact theorem. `OptimalBinaryAbstention` has a different
     three-action loss model.
   * Body-shape searches for `(1 - p) * c` and `c / (c + c')` found no
     source-shaped canonical decision primitive to import.
   * Pinned Mathlib supplies `div_le_iff₀` and ordered-field arithmetic, but no
     theorem packaging this expected-loss comparison and threshold. The
     `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.OptimalAcceptanceThreshold

/-- Positive false-positive and false-negative costs are jointly satisfiable
on the source real carrier. -/
example : ∃ p cFP cFN : Real, p = 1 / 2 ∧ 0 < cFP ∧ 0 < cFN := by
  exact ⟨1 / 2, 1, 1, rfl, by norm_num, by norm_num⟩

/-- Accepting has no larger expected loss than rejecting exactly when the
posterior reaches the source cost threshold. -/
theorem optimal_acceptance_threshold
    (p cFP cFN : Real) (cFPPositive : 0 < cFP) (cFNPositive : 0 < cFN) :
    (1 - p) * cFP ≤ p * cFN ↔
      p ≥ cFP / (cFP + cFN) := by
  have sumPositive : 0 < cFP + cFN := add_pos cFPPositive cFNPositive
  constructor
  · intro lossComparison
    apply (div_le_iff₀ sumPositive).2
    nlinarith
  · intro threshold
    have scaledThreshold := (div_le_iff₀ sumPositive).1 threshold
    nlinarith

#print axioms optimal_acceptance_threshold

end D5.S3.ConceptDynamics.DecisionValueScale.OptimalAcceptanceThreshold
