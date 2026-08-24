/- GID: D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The full control-profile quotient is the universal coarsest action-complete concept. -/

import D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality
import D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization
import Mathlib.Algebra.Group.Action.Defs

/- Library-search audit trail (2026-08-24):
   * Current-tree searches found the canonical `Concept`, `Refines`, and `DynClosure`
     family primitives; they are imported rather than redeclared. The nearby
     `actionIdentity` uses a subtype of a set of actions, while `futureBehavior`
     is restricted to an anchor-relative reachable orbit, so neither is the source's
     full-state monoid-indexed control profile.
   * Exact current-tree hit
     `realized_image_unique_factorization_iff_reverse_kernel` turns the proved
     candidate-kernel inclusion into the required unique factor and is applied directly.
   * Exact pinned-Mathlib hits `Quotient.lift`, `Quotient.map`, `Quotient.sound`,
     `Setoid.kerLift`, and `Set.rangeFactorization_surjective` provide the canonical
     quotient operations and their universal behavior. No theorem already packages all
     three public control clauses with the monoid dynamic-closure identification.
   * External `loogle` and `leansearch` executables were unavailable on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.ControlQuotientUniversalMinimality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality
open D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

universe u

/-- The complete control profile records the public outcome after every monoid action. -/
def controlProfile {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) : Concept X (M -> O) :=
  fun state action => readout (action • state)

/-- States modulo equality of their complete control profiles. -/
abbrev ControlQuotient {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) :=
  Quotient (Setoid.ker (controlProfile (M := M) readout))

/-- The canonical projection onto complete control profiles. -/
def controlProjection {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) : X -> ControlQuotient (M := M) readout :=
  Quotient.mk _

/-- The current public readout recovered from a complete control profile. -/
def controlReadout {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) : ControlQuotient (M := M) readout -> O :=
  Quotient.lift readout (by
    intro first second sameProfile
    simpa only [controlProfile, one_smul] using congrFun sameProfile 1)

/-- A monoid action induced on complete control profiles. -/
def controlAction {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) (action : M) :
    ControlQuotient (M := M) readout -> ControlQuotient (M := M) readout :=
  Quotient.map (fun state => action • state) (by
    intro first second sameProfile
    funext continuation
    simpa only [controlProfile, mul_smul] using
      congrFun sameProfile (continuation * action))

/-- The public consequence of one action, decided from the current control value. -/
def controlOutcome {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) (action : M) :
    ControlQuotient (M := M) readout -> O :=
  Quotient.lift (fun state => readout (action • state)) (by
    intro first second sameProfile
    exact congrFun sameProfile action)

/-- The complete control-profile quotient recovers the present readout, carries every
action, and decides every action consequence. Every other concept with all three
properties uniquely factors onto its realized quotient image, and the control-profile
kernel is exactly the finite-intervention dynamic-closure kernel. -/
theorem control_quotient_universal_minimality
    {M X O : Type u} [Monoid M] [MulAction M X] (readout : Concept X O) :
    readout = controlReadout (M := M) readout ∘
        controlProjection (M := M) readout ∧
      (forall action : M,
        controlProjection (M := M) readout ∘ (fun state => action • state) =
          controlAction readout action ∘ controlProjection (M := M) readout) ∧
      (forall action : M,
        (fun state => readout (action • state)) =
          controlOutcome readout action ∘ controlProjection (M := M) readout) ∧
      (forall {B : Type u} (candidate : Concept X B),
        (exists recover : B -> O, readout = recover ∘ candidate) ->
        (forall action : M, exists close : B -> B,
          candidate ∘ (fun state => action • state) = close ∘ candidate) ->
        (forall action : M, exists consequence : B -> O,
          (fun state => readout (action • state)) = consequence ∘ candidate) ->
        ∃! factor : Set.range candidate ->
            Set.range (controlProjection (M := M) readout),
          Set.rangeFactorization (controlProjection (M := M) readout) =
            factor ∘ Set.rangeFactorization candidate) ∧
      Setoid.ker (controlProfile (M := M) readout) =
        Setoid.ker
          (DynClosure readout (fun action : M => fun state => action • state)) := by
  constructor
  · funext state
    rfl
  constructor
  · intro action
    funext state
    rfl
  constructor
  · intro action
    funext state
    rfl
  constructor
  · intro B candidate _recovers _closes consequences
    apply (realized_image_unique_factorization_iff_reverse_kernel
      (controlProjection (M := M) readout) candidate).2
    intro first second sameCandidate
    apply Quotient.sound
    funext action
    obtain ⟨consequence, consequenceFactors⟩ := consequences action
    calc
      readout (action • first) = consequence (candidate first) :=
        congrFun consequenceFactors first
      _ = consequence (candidate second) := congrArg consequence sameCandidate
      _ = readout (action • second) :=
        (congrFun consequenceFactors second).symm
  · apply Setoid.ext
    intro first second
    constructor
    · intro sameProfile
      funext word
      induction word generalizing first second with
      | nil =>
          simpa only [DynClosure, controlledBehavior, runWord, controlProfile,
            one_smul] using congrFun sameProfile 1
      | cons action word inductionHypothesis =>
          simp only [DynClosure, controlledBehavior, runWord]
          apply inductionHypothesis
          funext continuation
          simpa only [controlProfile, mul_smul] using
            congrFun sameProfile (continuation * action)
    · intro sameDynamicProfile
      funext action
      simpa only [DynClosure, controlledBehavior, runWord, controlProfile] using
        congrFun sameDynamicProfile [action]

#print axioms control_quotient_universal_minimality

end D5.S3.ConceptDynamics.Control.ControlQuotientUniversalMinimality
