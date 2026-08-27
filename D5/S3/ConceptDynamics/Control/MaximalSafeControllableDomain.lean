/- GID: D5/S3/ConceptDynamics/Control/MaximalSafeControllableDomain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/MaximalSafeControllableDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The semantic indefinitely safe domain is the greatest controlled-safe fixed point. -/

import D5.S3.ConceptDynamics.Control.FiniteHorizonReachability
import Mathlib.Order.FixedPoints

/- Library-search audit trail (2026-08-27):
   * Repository searches for maximal safe controllable domains, viability
     kernels, and controlled-safe greatest fixed points found no exact theorem.
   * Exact family hits `ControlSystem` and `controlPredecessor` provide the
     source's state-dependent actions and adversarial successor semantics and
     are imported rather than redeclared.
   * `finite_horizon_reachability` is adjacent but characterizes least-fixed-
     point reachability, not the indefinitely safe greatest fixed point.
   * Exact pinned Mathlib hits `OrderHom.map_gfp` and `OrderHom.le_gfp` provide
     the fixed-point and maximality steps and are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.MaximalSafeControllableDomain

open D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

/-- The states contained in some controlled invariant subset of the safe set
are exactly the greatest fixed point of `K ↦ safe ∩ CPre(K)`. Every greatest-
fixed-point state has a safe action, and the two public inclusions state
indefinite safety and maximality separately. -/
theorem maximal_safe_controllable_domain
    {State : Type*} (system : ControlSystem State) (safe : Set State) :
    let safetyOperator : Set State →o Set State :=
      { toFun := fun domain => safe ∩ controlPredecessor system domain
        monotone' := by
          intro smaller larger inclusion state stateSafe
          exact ⟨stateSafe.1, by
            rcases stateSafe.2 with ⟨action, successors⟩
            exact ⟨action, fun next isSuccessor =>
              inclusion (successors isSuccessor)⟩⟩ }
    let foreverSafe : Set State :=
      {state | ∃ invariant : Set State,
        state ∈ invariant ∧
          invariant ⊆ safe ∧
          ∀ current ∈ invariant,
            ∃ action : system.Action current,
              system.successor action ⊆ invariant}
    foreverSafe = safetyOperator.gfp ∧
      (∀ state ∈ safetyOperator.gfp,
        ∃ action : system.Action state,
          system.successor action ⊆ safetyOperator.gfp) ∧
      safetyOperator.gfp ⊆ foreverSafe ∧
      foreverSafe ⊆ safetyOperator.gfp := by
  let safetyOperator : Set State →o Set State :=
    { toFun := fun domain => safe ∩ controlPredecessor system domain
      monotone' := by
        intro smaller larger inclusion state stateSafe
        exact ⟨stateSafe.1, by
          rcases stateSafe.2 with ⟨action, successors⟩
          exact ⟨action, fun next isSuccessor =>
            inclusion (successors isSuccessor)⟩⟩ }
  let foreverSafe : Set State :=
    {state | ∃ invariant : Set State,
      state ∈ invariant ∧
        invariant ⊆ safe ∧
        ∀ current ∈ invariant,
          ∃ action : system.Action current,
            system.successor action ⊆ invariant}
  change foreverSafe = safetyOperator.gfp ∧
    (∀ state ∈ safetyOperator.gfp,
      ∃ action : system.Action state,
        system.successor action ⊆ safetyOperator.gfp) ∧
    safetyOperator.gfp ⊆ foreverSafe ∧
    foreverSafe ⊆ safetyOperator.gfp
  have fixedPoint : safetyOperator safetyOperator.gfp = safetyOperator.gfp :=
    safetyOperator.map_gfp
  have greatestIsSafe : safetyOperator.gfp ⊆ safe := by
    intro state inGreatest
    have inOperator : state ∈ safetyOperator safetyOperator.gfp := by
      rw [fixedPoint]
      exact inGreatest
    exact inOperator.1
  have greatestHasAction :
      ∀ state ∈ safetyOperator.gfp,
        ∃ action : system.Action state,
          system.successor action ⊆ safetyOperator.gfp := by
    intro state inGreatest
    have inOperator : state ∈ safetyOperator safetyOperator.gfp := by
      rw [fixedPoint]
      exact inGreatest
    exact inOperator.2
  have greatestSubsetForever : safetyOperator.gfp ⊆ foreverSafe := by
    intro state inGreatest
    exact ⟨safetyOperator.gfp, inGreatest, greatestIsSafe,
      greatestHasAction⟩
  have foreverSubsetGreatest : foreverSafe ⊆ safetyOperator.gfp := by
    rintro state ⟨invariant, inInvariant, invariantSafe, invariantControlled⟩
    apply safetyOperator.le_gfp (a := invariant) at inInvariant
    · exact inInvariant
    · intro current currentInInvariant
      exact ⟨invariantSafe currentInInvariant,
        invariantControlled current currentInInvariant⟩
  exact ⟨Set.Subset.antisymm foreverSubsetGreatest greatestSubsetForever,
    greatestHasAction, greatestSubsetForever, foreverSubsetGreatest⟩

#print axioms maximal_safe_controllable_domain

end D5.S3.ConceptDynamics.Control.MaximalSafeControllableDomain
