/- GID: D5/S1/Solenoid/Connectivity/FiniteNameInverseLimitNoGo
   generality: G
   mirror-B: D5/B/S1/Solenoid/Connectivity/FiniteNameInverseLimitNoGo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous names from a connected space into a finite-name inverse limit are constant. -/

/- Library-search audit trail (2026-09-02):
   * Repository searches found rigidity theorems for a single discrete target
     and for particular profinite products, but no theorem about the canonical
     inverse limit of an arbitrary sequential system of finite discrete names.
   * Pinned Mathlib supplies `Profinite.limitCone`, the finite-discrete functor
     `FintypeCat.toProfinite`, and the exact connected-to-totally-disconnected
     engine `TotallyDisconnectedSpace.eq_of_continuous`; all are used directly.
   * No new definition is introduced: the target is Mathlib's canonical limit
     cone point for the supplied finite-name functor. -/

import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

namespace D5.S1.Solenoid.Connectivity.FiniteNameInverseLimitNoGo

open CategoryTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A continuous compatible family of finite discrete names cannot distinguish
points of a connected space. Its image is one point, and injectivity is possible
only when the source itself has at most one point. -/
theorem finite_name_inverse_limit_no_go
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (finiteNames : ℕᵒᵖ ⥤ FintypeCat)
    (name : X → (Profinite.limitCone (finiteNames ⋙ FintypeCat.toProfinite)).pt)
    (hname : Continuous name) :
    (∀ x y : X, name x = name y) ∧
      (∀ x₀ : X, Set.range name = {name x₀}) ∧
      (Function.Injective name → Subsingleton X) := by
  have hconstant : ∀ x y : X, name x = name y :=
    TotallyDisconnectedSpace.eq_of_continuous name hname
  refine ⟨hconstant, ?_, ?_⟩
  · intro x₀
    exact Set.range_eq_singleton (fun x => hconstant x x₀)
  · intro hinjective
    constructor
    intro x y
    exact hinjective (hconstant x y)

example : Unit := ()

#print axioms finite_name_inverse_limit_no_go

end D5.S1.Solenoid.Connectivity.FiniteNameInverseLimitNoGo
