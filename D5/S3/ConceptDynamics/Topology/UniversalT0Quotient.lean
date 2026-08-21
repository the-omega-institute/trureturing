/- GID: D5/S3/ConceptDynamics/Topology/UniversalT0Quotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/UniversalT0Quotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The separation quotient has the universal property for continuous maps to T0 spaces. -/

import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n "SeparationQuotient.*lift|continuous_lift_iff" .lake/packages/mathlib/Mathlib`
     found `SeparationQuotient.lift`, `continuous_lift`, and `lift_comp_mk`.
   * `rg -n "T0Space.*Inseparable|Inseparable.*eq" .lake/packages/mathlib/Mathlib/Topology`
     found `Inseparable.eq` and `Inseparable.map`; these show a continuous map into a T0
     space is constant on inseparable pairs.
   * `rg -n "injective_comp_right" .lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean`
     found `Function.Surjective.injective_comp_right`, used for uniqueness through the
     surjective quotient map.
   * Repository search found no accepted theorem packaging this universal property.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.UniversalT0Quotient

/- The quotient is the canonical T0 reflection of the source topology. -/
theorem universal_t0_quotient
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space Y]
    (f : X -> Y) (h_continuous : Continuous f) :
    ∃! bar_f : SeparationQuotient X -> Y,
      Continuous bar_f ∧ f = bar_f ∘ SeparationQuotient.mk := by
  have h_respects : ∀ x y, Inseparable x y -> f x = f y := by
    intro x y hxy
    exact (hxy.map h_continuous).eq
  let bar_f : SeparationQuotient X -> Y := SeparationQuotient.lift f h_respects
  have h_cont_bar : Continuous bar_f := by
    exact SeparationQuotient.continuous_lift (f := f) (hf := h_respects) h_continuous
  have h_factor : f = bar_f ∘ SeparationQuotient.mk := by
    exact (SeparationQuotient.lift_comp_mk h_respects).symm
  refine ⟨bar_f, ⟨h_cont_bar, h_factor⟩, ?_⟩
  intro candidate h_candidate
  apply SeparationQuotient.surjective_mk.injective_comp_right
  exact h_candidate.2.symm.trans h_factor

#print axioms universal_t0_quotient

end D5.S3.ConceptDynamics.Topology.UniversalT0Quotient
