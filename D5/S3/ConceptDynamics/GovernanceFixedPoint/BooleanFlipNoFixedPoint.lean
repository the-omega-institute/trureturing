/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/BooleanFlipNoFixedPoint
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/BooleanFlipNoFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical exchange of two Boolean statuses has no fixed point. -/

import D5.S3.ConceptDynamics.GovernanceFixedPoint.Core

/- Library-search audit trail (2026-08-30):
   * Exact searches for `bool_flip_has_no_fixed_point` found no declaration in
     D5 or pinned Mathlib.
   * Shape searches found only distinct Boolean negation and general
     fixed-point-free results, not the canonical GFPT `boolFlip` statement.
   * The proof therefore closes the two constructors of `Bool` directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- Exchanging the two Boolean statuses leaves neither status fixed. -/
theorem bool_flip_has_no_fixed_point :
    ¬ ∃ status : Bool, status = boolFlip status := by
  rintro ⟨status, fixed⟩
  cases status <;> cases fixed

#print axioms bool_flip_has_no_fixed_point

-- Concrete elaboration witnesses for the nonempty two-status carrier.
example : Bool := false

example : boolFlip false = true := rfl

example : boolFlip true = false := rfl

end D5.S3.ConceptDynamics.GovernanceFixedPoint
