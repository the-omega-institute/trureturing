/- GID: D5/S3/DivergenceSupport/LandauerIdentity
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/LandauerIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive the exact heat-entropy-information identity from the reservoir and unitary entropy balances. -/

/- Library-search audit trail (2026-08-12):
   * Pinned-mathlib searches for `Landauer`, `heat-entropy`, `entropy-heat`,
     `reservoir entropy`, and `mutual reservoir` found no matching theorem.
   * Mathlib provides the `linarith` tactic in `Mathlib/Tactic/Linarith/Frontend.lean`
     and `linear_combination` in `Mathlib/Tactic/LinearCombination.lean`.
   * A repository search found no exact heat-entropy-information identity. The separate
     lower-bound result discards nonnegative remainder terms and is not this equality.
-/

import Mathlib

namespace D5.S3.DivergenceSupport.LandauerIdentity

/-- The reservoir balance and unitary entropy balance imply the exact identity relating heat,
system entropy change, final mutual information, and reservoir divergence. -/
theorem landauer_identity_from_balances
    (beta heat systemEntropyChange reservoirEntropyChange
      mutualInformation reservoirDivergence : Real)
    (hReservoir :
      beta * heat = reservoirEntropyChange + reservoirDivergence)
    (hUnitary :
      mutualInformation = systemEntropyChange + reservoirEntropyChange) :
    beta * heat =
      -systemEntropyChange + mutualInformation + reservoirDivergence := by
  fail_if_success rfl
  fail_if_success assumption
  linarith

/- A concrete inhabitant of the six-real domain. -/
example : Real × Real × Real × Real × Real × Real :=
  (0, 0, 0, 0, 0, 0)

/- The two balance hypotheses are jointly satisfiable. -/
example :
    ∃ beta heat systemEntropyChange reservoirEntropyChange
        mutualInformation reservoirDivergence : Real,
      beta * heat = reservoirEntropyChange + reservoirDivergence ∧
      mutualInformation = systemEntropyChange + reservoirEntropyChange := by
  exact ⟨0, 0, 0, 0, 0, 0, by norm_num, by norm_num⟩

/- With the unitary balance retained but the reservoir balance omitted, the conclusion can fail. -/
example :
    (0 : Real) = 1 + (-1) ∧
      ¬((0 : Real) * 0 = -(1 : Real) + 0 + 0) := by
  norm_num

/- With the reservoir balance retained but the unitary balance omitted, the conclusion can fail. -/
example :
    (0 : Real) * 0 = 0 + 0 ∧
      ¬((0 : Real) * 0 = -(1 : Real) + 0 + 0) := by
  norm_num

#print axioms landauer_identity_from_balances

end D5.S3.DivergenceSupport.LandauerIdentity
