/- GID: D5/S3/ConceptDynamics/Topology/UniversalT0QuotientComplete
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/UniversalT0QuotientComplete
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical separation quotient is T0 and has its unique continuous factorization. -/

import D5.S3.ConceptDynamics.Topology.UniversalT0Quotient

/- Library-search audit trail (2026-08-27):
   * The frozen `universal_t0_quotient` theorem is the exact unique continuous
     factorization clause and is imported directly.
   * Pinned Mathlib supplies the canonical
     `SeparationQuotient.instT0Space` instance for the quotient itself.
   * `rg -n "T0Space \\(SeparationQuotient|SeparationQuotient.*exists unique"
     across D5 and pinned Mathlib found no declaration conjoining both public
     clauses of the source theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.UniversalT0QuotientComplete

open D5.S3.ConceptDynamics.Topology.UniversalT0Quotient

/-- The canonical separation quotient is a T0 space and every continuous map
to a T0 target descends through it by a unique continuous factor. -/
theorem universal_t0_quotient_complete
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space Y]
    (f : X -> Y) (hContinuous : Continuous f) :
    T0Space (SeparationQuotient X) ∧
      ∃! bar_f : SeparationQuotient X -> Y,
        Continuous bar_f ∧ f = bar_f ∘ SeparationQuotient.mk := by
  exact ⟨inferInstance, universal_t0_quotient f hContinuous⟩

#print axioms universal_t0_quotient_complete

end D5.S3.ConceptDynamics.Topology.UniversalT0QuotientComplete
