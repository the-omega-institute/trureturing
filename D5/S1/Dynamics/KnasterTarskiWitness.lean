/- GID: D5/S1/Dynamics/KnasterTarskiWitness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Frozen proofs assemble the extremal fixed-point theorem with its three-state instance. -/

import D5.S1.Dynamics.KnasterTarski

open Function (fixedPoints)

namespace D5.S1.Dynamics.KnasterTarskiWitness

open D5.S1.Dynamics.KnasterTarski

/-- The general Knaster–Tarski extremal fixed points together with the
three-state successor-cycle instance, assembled from their frozen proofs. -/
theorem knaster_tarski_with_three_cycle_instance :
    (∀ {α : Type*} [CompleteLattice α] (f : α →o α),
        IsLeast (fixedPoints f) f.lfp ∧ IsGreatest (fixedPoints f) f.gfp)
      ∧ (threeCycleOperator.lfp = ∅ ∧ threeCycleOperator.gfp = Set.univ) :=
  ⟨fun f => knaster_tarski_extremal_fixed_points f,
    three_cycle_extremal_fixed_points⟩

end D5.S1.Dynamics.KnasterTarskiWitness
