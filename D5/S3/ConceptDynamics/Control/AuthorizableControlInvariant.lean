/- GID: D5/S3/ConceptDynamics/Control/AuthorizableControlInvariant
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/AuthorizableControlInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Componentwise preservation makes authorizable control dynamically invariant. -/

import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-09-01):
   * Repository searches found separate theorems for robust viability, repeated
     renewal, public recovery, visible autonomy, provenance, and control
     closure, but no theorem assembling the source's nine named requirements
     into one dynamic invariant.
   * The only in-flight ConceptDynamics declaration was
     `InformationRefinementGovernance`; it concerns refinement monotonicity and
     does not state a dynamic-invariance assembly.
   * Exact pinned-Mathlib hits `Set.MapsTo.inter_inter` and
     `Set.MapsTo.iterate` supply conjunction and finite-time transport. They are
     applied directly below, so no third-party or local reconstruction of those
     generic facts is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.AuthorizableControlInvariant

/-- The nine state predicates that the source identifies as jointly necessary
for maintaining authorizable future control. -/
structure AutonomyConditions (State : Type*) where
  viability : Set State
  liveness : Set State
  recoverability : Set State
  observationRate : Set State
  causalControl : Set State
  provenance : Set State
  identityCorrection : Set State
  revisionGovernance : Set State
  expandability : Set State

/-- States satisfying every component of authorizable future control. -/
def AutonomyConditions.core {State : Type*}
    (conditions : AutonomyConditions State) : Set State :=
  ((((((((conditions.viability ∩ conditions.liveness) ∩
    conditions.recoverability) ∩ conditions.observationRate) ∩
    conditions.causalControl) ∩ conditions.provenance) ∩
    conditions.identityCorrection) ∩ conditions.revisionGovernance) ∩
    conditions.expandability)

/-- If one closed-loop update preserves each of the nine named requirements,
then every finite iterate preserves their joint core. Thus the source's
authorizable control capacity is a dynamic invariant under that update. -/
theorem authorizable_control_dynamic_invariant
    {State : Type*} (step : State → State)
    (conditions : AutonomyConditions State)
    (viabilityPreserved :
      Set.MapsTo step conditions.viability conditions.viability)
    (livenessPreserved :
      Set.MapsTo step conditions.liveness conditions.liveness)
    (recoverabilityPreserved :
      Set.MapsTo step conditions.recoverability conditions.recoverability)
    (observationRatePreserved :
      Set.MapsTo step conditions.observationRate conditions.observationRate)
    (causalControlPreserved :
      Set.MapsTo step conditions.causalControl conditions.causalControl)
    (provenancePreserved :
      Set.MapsTo step conditions.provenance conditions.provenance)
    (identityCorrectionPreserved :
      Set.MapsTo step conditions.identityCorrection conditions.identityCorrection)
    (revisionGovernancePreserved :
      Set.MapsTo step conditions.revisionGovernance conditions.revisionGovernance)
    (expandabilityPreserved :
      Set.MapsTo step conditions.expandability conditions.expandability) :
    ∀ time, Set.MapsTo (step^[time]) conditions.core conditions.core := by
  intro time
  have firstTwo := viabilityPreserved.inter_inter livenessPreserved
  have firstThree := firstTwo.inter_inter recoverabilityPreserved
  have firstFour := firstThree.inter_inter observationRatePreserved
  have firstFive := firstFour.inter_inter causalControlPreserved
  have firstSix := firstFive.inter_inter provenancePreserved
  have firstSeven := firstSix.inter_inter identityCorrectionPreserved
  have firstEight := firstSeven.inter_inter revisionGovernancePreserved
  have allPreserved := firstEight.inter_inter expandabilityPreserved
  exact allPreserved.iterate time

/-- The constant state `3` gives a concrete nonempty instance: every named
condition holds, and every finite identity update keeps the state at `3`. -/
example :
    let conditions : AutonomyConditions Nat :=
      { viability := {3}
        liveness := {3}
        recoverability := {3}
        observationRate := {3}
        causalControl := {3}
        provenance := {3}
        identityCorrection := {3}
        revisionGovernance := {3}
        expandability := {3} }
    3 ∈ conditions.core ∧
      (id : Nat → Nat) 3 = 3 ∧
      ∀ time, Set.MapsTo ((id : Nat → Nat)^[time])
        conditions.core conditions.core := by
  let conditions : AutonomyConditions Nat :=
    { viability := {3}
      liveness := {3}
      recoverability := {3}
      observationRate := {3}
      causalControl := {3}
      provenance := {3}
      identityCorrection := {3}
      revisionGovernance := {3}
      expandability := {3} }
  change 3 ∈ conditions.core ∧
    (id : Nat → Nat) 3 = 3 ∧
    ∀ time, Set.MapsTo ((id : Nat → Nat)^[time])
      conditions.core conditions.core
  have singletonPreserved :
      Set.MapsTo (id : Nat → Nat) ({3} : Set Nat) {3} := by
    intro state membership
    exact membership
  refine ⟨?_, rfl, ?_⟩
  · simp [conditions, AutonomyConditions.core]
  · exact authorizable_control_dynamic_invariant (id : Nat → Nat) conditions
      singletonPreserved singletonPreserved singletonPreserved
      singletonPreserved singletonPreserved singletonPreserved
      singletonPreserved singletonPreserved singletonPreserved

/-- For the successor update, state `0` moves to `1`. If viability requires
remaining at `0`, that component premise and the joint dynamic invariant both
fail, while the other eight conditions remain unrestricted. -/
example :
    let conditions : AutonomyConditions Nat :=
      { viability := {0}
        liveness := Set.univ
        recoverability := Set.univ
        observationRate := Set.univ
        causalControl := Set.univ
        provenance := Set.univ
        identityCorrection := Set.univ
        revisionGovernance := Set.univ
        expandability := Set.univ }
    let step := Nat.succ
    0 ∈ conditions.core ∧
      step 0 = 1 ∧
      ¬Set.MapsTo step conditions.viability conditions.viability ∧
      ¬∀ time, Set.MapsTo (step^[time]) conditions.core conditions.core := by
  let conditions : AutonomyConditions Nat :=
    { viability := {0}
      liveness := Set.univ
      recoverability := Set.univ
      observationRate := Set.univ
      causalControl := Set.univ
      provenance := Set.univ
      identityCorrection := Set.univ
      revisionGovernance := Set.univ
      expandability := Set.univ }
  let step := Nat.succ
  change 0 ∈ conditions.core ∧
    step 0 = 1 ∧
    ¬Set.MapsTo step conditions.viability conditions.viability ∧
    ¬∀ time, Set.MapsTo (step^[time]) conditions.core conditions.core
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [conditions, AutonomyConditions.core]
  · intro viabilityInvariant
    have moved := viabilityInvariant (show 0 ∈ conditions.viability by simp [conditions])
    simpa [conditions, step] using moved
  · intro dynamicInvariant
    have moved := dynamicInvariant 1
      (show 0 ∈ conditions.core by simp [conditions, AutonomyConditions.core])
    simpa [conditions, step, AutonomyConditions.core] using moved

#print axioms authorizable_control_dynamic_invariant

end D5.S3.ConceptDynamics.Control.AuthorizableControlInvariant
