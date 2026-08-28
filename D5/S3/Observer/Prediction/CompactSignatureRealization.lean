/- GID: D5/S3/Observer/Prediction/CompactSignatureRealization
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/CompactSignatureRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite compatibility on a compact state space has a global realization. -/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/- Library-search audit trail (2026-08-28):
   * The current D5 tree has no theorem constructing a global state from finite compatibility of
     a protocol-indexed continuous signature. Searches by `iInter_nonempty`, `CompactSpace`,
     finite-intersection, readout, and signature shapes found no complete repository declaration.
   * The pinned Mathlib exact supporting hit `CompactSpace.iInter_nonempty` proves nonemptiness of
     a closed family intersection from nonemptiness of every finite subintersection.
   * Pinned Mathlib's `isClosed_eq` proves that each continuous coordinate fiber is closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Prediction.CompactSignatureRealization

/-- A finitely compatible family of continuous protocol values on a compact state space is
realized by one state at every protocol. -/
theorem finite_compatibility_global_realization
    {P X : Type*} {Lambda : P -> Type*}
    [TopologicalSpace X] [CompactSpace X]
    [(p : P) -> TopologicalSpace (Lambda p)]
    [(p : P) -> T2Space (Lambda p)]
    (readout : (p : P) -> C(X, Lambda p))
    (signature : (p : P) -> Lambda p)
    (finite_compatible :
      forall protocols : Set P, protocols.Finite ->
        exists x : X, forall p, p ∈ protocols -> readout p x = signature p) :
    exists x : X, forall p : P, readout p x = signature p := by
  classical
  let compatibleState : P -> Set X :=
    fun p => {x | readout p x = signature p}
  have compatibleState_closed : forall p, IsClosed (compatibleState p) := by
    intro p
    exact isClosed_eq (readout p).continuous continuous_const
  have finite_intersections_nonempty :
      forall protocols : Finset P,
        (⋂ p ∈ protocols, compatibleState p).Nonempty := by
    intro protocols
    obtain ⟨x, realizes⟩ :=
      finite_compatible (protocols : Set P) protocols.finite_toSet
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro p p_mem
    change readout p x = signature p
    exact realizes p p_mem
  obtain ⟨x, realizes⟩ :=
    CompactSpace.iInter_nonempty compatibleState_closed finite_intersections_nonempty
  refine ⟨x, ?_⟩
  intro p
  exact Set.mem_iInter.1 realizes p

/- The identity readout on a finite discrete space witnesses that the hypotheses are inhabited. -/
example :
    exists x : Bool, forall _p : Bool,
      ({ toFun := id, continuous_toFun := continuous_id } : C(Bool, Bool)) x = true := by
  apply finite_compatibility_global_realization
    (P := Bool) (X := Bool) (Lambda := fun _ : Bool => Bool)
    (readout := fun _ : Bool =>
      ({ toFun := id, continuous_toFun := continuous_id } : C(Bool, Bool)))
    (signature := fun _ : Bool => true)
  intro _ _
  exact ⟨true, by simp⟩

example : Bool := false

#print axioms finite_compatibility_global_realization

end D5.S3.Observer.Prediction.CompactSignatureRealization
