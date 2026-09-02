/- GID: D5/S3/ConceptDynamics/Dialectics/OneStepClosureFivefoldEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/OneStepClosureFivefoldEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five one-step closure criteria are equivalent, and carry detects strict refinement. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-09-03):
   * Repository searches found the canonical `depthZeroKernel`, `depthOneKernel`,
     `InterfaceCongruence`, `EffectiveDescent`, `IsCarryWitness`, and
     `completeItinerary` primitives; they are reused rather than redeclared.
   * `deterministic_interface_sixfold_equivalence` supplies four of the five
     equivalences, but does not state complete-itinerary kernel equality or the
     strict-refinement witness clause, so it is applied rather than rebound.
   * Pinned Mathlib and installed-package searches found no exact theorem
     combining all five conditions with the strict-refinement characterization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.OneStepClosureFivefoldEquivalence

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/-- Equality of the first two kernels, forward invariance, equality with the
complete behavior kernel, exact descent, and absence of carry are equivalent.
Moreover, a carry exists exactly when the first refinement is strict. -/
theorem one_step_closure_fivefold_equivalence
    {X B : Type*} (q : X → B) (F : X → X) :
    List.TFAE [
      depthZeroKernel q = depthOneKernel q F,
      InterfaceCongruence q F,
      Setoid.ker q = Setoid.ker (completeItinerary F q),
      EffectiveDescent q F,
      ∀ x y, ¬IsCarryWitness q F q x y] ∧
    ((∃ x y, IsCarryWitness q F q x y) ↔
      depthOneKernel q F < depthZeroKernel q) := by
  constructor
  · tfae_have 1 ↔ 2 :=
      (deterministic_interface_sixfold_equivalence q F).out 5 1
    tfae_have 2 ↔ 3 := by
      constructor
      · intro congruence
        apply le_antisymm
        · intro x y sameReadout
          funext n
          induction n with
          | zero => simpa [completeItinerary] using sameReadout
          | succ n ih =>
              simpa only [completeItinerary, Function.iterate_succ_apply'] using
                congruence ((F^[n]) x) ((F^[n]) y)
                  (by simpa [completeItinerary] using ih)
        · intro x y sameItinerary
          simpa [completeItinerary] using congrFun sameItinerary 0
      · intro sameKernels x y sameReadout
        have sameItinerary : completeItinerary F q x = completeItinerary F q y := by
          change Setoid.ker (completeItinerary F q) x y
          rw [← sameKernels]
          exact sameReadout
        simpa [completeItinerary, Function.iterate_succ_apply'] using
          congrFun sameItinerary 1
    tfae_have 2 ↔ 4 :=
      (deterministic_interface_sixfold_equivalence q F).out 1 0
    tfae_have 2 ↔ 5 :=
      (deterministic_interface_sixfold_equivalence q F).out 1 2
    tfae_finish
  · constructor
    · rintro ⟨x, y, carry⟩
      constructor
      · intro left right sameAtOneStep
        exact sameAtOneStep.1
      · intro reverseInclusion
        exact carry.2 (reverseInclusion x y carry.1).2
    · intro strictRefinement
      by_contra noCarry
      apply strictRefinement.2
      intro x y sameReadout
      constructor
      · exact sameReadout
      · by_contra separated
        apply noCarry
        exact ⟨x, y, ⟨sameReadout, separated⟩⟩

example : Nonempty Bool := ⟨false⟩

example :
    IsCarryWitness
      (fun pair : Bool × Bool ↦ pair.1)
      (fun pair ↦ (pair.2, pair.1))
      (fun pair ↦ pair.1)
      (false, false) (false, true) :=
  ⟨rfl, Bool.false_ne_true⟩

example :
    List.TFAE [
      depthZeroKernel (id : Bool → Bool) = depthOneKernel id Bool.not,
      InterfaceCongruence (id : Bool → Bool) Bool.not,
      Setoid.ker (id : Bool → Bool) =
        Setoid.ker (completeItinerary Bool.not id),
      EffectiveDescent (id : Bool → Bool) Bool.not,
      ∀ x y, ¬IsCarryWitness (id : Bool → Bool) Bool.not id x y] ∧
    ((∃ x y, IsCarryWitness (id : Bool → Bool) Bool.not id x y) ↔
      depthOneKernel (id : Bool → Bool) Bool.not < depthZeroKernel id) :=
  one_step_closure_fivefold_equivalence id Bool.not

#print axioms one_step_closure_fivefold_equivalence

end D5.S3.ConceptDynamics.Dialectics.OneStepClosureFivefoldEquivalence
