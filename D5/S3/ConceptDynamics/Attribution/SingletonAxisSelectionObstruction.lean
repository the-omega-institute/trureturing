/- GID: D5/S3/ConceptDynamics/Attribution/SingletonAxisSelectionObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/SingletonAxisSelectionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No equivariant axis selector exists on a globally fixed singleton state. -/

import Mathlib.GroupTheory.GroupAction.SubMulAction
import D5.S3.ConceptDynamics.Attribution.StabilizerSelectorObstruction

/- Library-search audit trail (2026-08-29):
   * The frozen family owner
     `no_equivariant_selector_of_stabilizer_without_fixed_action` gives the
     general admissible-selector obstruction and is instantiated below.
   * Repository name and body-shape searches found no theorem whose selector
     domain is the invariant singleton of one globally fixed state.
   * Pinned Mathlib supplies the canonical `SubMulAction` construction for an
     invariant subset, but no packaged no-selector theorem. -/

namespace D5.S3.ConceptDynamics.Attribution.SingletonAxisSelectionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.Attribution.StabilizerSelectorObstruction

/-- The singleton of a state fixed by the whole group is an invariant
subaction. If the axis action has no global fixed point, no deterministic map
from that singleton can be equivariant. -/
theorem no_equivariant_singleton_axis_selector
    {G State Axis : Type*} [Group G] [MulAction G State] [MulAction G Axis]
    (omega : State) (hfixed : forall g : G, g • omega = omega)
    (hnoFixedAxis : forall axis : Axis, exists g : G, Ne (g • axis) axis) :
    let fixedState : SubMulAction G State :=
      { carrier := {omega}
        smul_mem' := by
          intro g state hstate
          simp only [Set.mem_singleton_iff] at hstate |-
          rw [hstate, hfixed g] }
    Not (exists selector : fixedState -> Axis,
      forall (g : G) (state : fixedState),
        selector (g • state) = g • selector state) := by
  let fixedState : SubMulAction G State :=
    { carrier := {omega}
      smul_mem' := by
        intro g state hstate
        simp only [Set.mem_singleton_iff] at hstate |-
        rw [hstate, hfixed g] }
  change Not (exists selector : fixedState -> Axis,
    forall (g : G) (state : fixedState),
      selector (g • state) = g • selector state)
  intro hselector
  apply no_equivariant_selector_of_stabilizer_without_fixed_action
    (fun _ : fixedState => Set.univ) ⟨omega, Set.mem_singleton omega⟩
    (fun axis _ => by
      obtain ⟨g, hmoves⟩ := hnoFixedAxis axis
      refine ⟨g, ?_, hmoves⟩
      apply Subtype.ext
      exact hfixed g)
  obtain ⟨selector, hequivariant⟩ := hselector
  exact ⟨selector, (fun _ => Set.mem_univ _), hequivariant⟩

#print axioms no_equivariant_singleton_axis_selector

end D5.S3.ConceptDynamics.Attribution.SingletonAxisSelectionObstruction
