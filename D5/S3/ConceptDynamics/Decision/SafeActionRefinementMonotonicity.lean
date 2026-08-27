/- GID: D5/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining a readout enlarges the actions legal throughout its current fiber. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-27):
   * Repository body-shape searches found the direct fiber-wide legality predicate in
     `EpistemicCompulsionWitness`, but no named safe-action primitive or exact theorem.
   * The source safe-action objects are constructed below as bounded intersections of
     full-state legal-action sets over the two readout fibers; no sibling definition is added.
   * Exact pinned-Mathlib helper `Set.biInter_subset_biInter_left` in
     `Mathlib.Data.Set.Lattice` supplies antitonicity of the bounded intersection. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.SafeActionRefinementMonotonicity

/-- If `q` factors through the finer readout `r`, every action legal throughout the
current `q`-fiber is legal throughout the smaller current `r`-fiber. -/
theorem safe_action_refinement_monotonicity
    {X Q R Action : Type*}
    (q : X -> Q) (r : X -> R) (legal : X -> Action -> Prop)
    (f : R -> Q) (refines : q = f ∘ r) (x : X) :
    (⋂ state ∈ {candidate | q candidate = q x},
        {action | legal state action}) ⊆
      ⋂ state ∈ {candidate | r candidate = r x},
        {action | legal state action} := by
  apply Set.biInter_subset_biInter_left
  intro state sameFineReadout
  change r state = r x at sameFineReadout
  change q state = q x
  simpa only [refines, Function.comp_apply] using congrArg f sameFineReadout

#print axioms safe_action_refinement_monotonicity

end D5.S3.ConceptDynamics.Decision.SafeActionRefinementMonotonicity
