/- GID: D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorCore
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/ReachableBehaviorCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reachable future-behavior classes form a separated protocol-stable universal quotient. -/

import D5.S3.ObserverMemory.PredictionFactors.CanonicalReachableBehaviorFactor
import D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorClassSurjectivity

/- Library-search audit trail (2026-09-03):
   * Exact family primitives `ReachableOrbit`, `futureBehavior`,
     `ReachableBehaviorQuotient`, `orbitPoint`, and `behaviorClass` construct the
     source carrier; they are imported rather than redeclared.
   * Exact family theorems `every_reachable_behavior_class_is_reachable` and
     `canonical_reachable_behavior_factor` supply the reachability and universal
     unique-surjection clauses and are applied directly.
   * Pinned Mathlib's exact `Setoid.kerLift_injective` separates distinct
     behavior classes. `Quotient.map` constructs each protocol-prefix update.
   * Body-shape searches for a prefix update on `ReachableBehaviorQuotient`
     found no existing declaration. The nearby `controlAction` acts on a
     full-state control quotient rather than the anchor-relative reachable carrier. -/

noncomputable section

namespace D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorCore

open D5.S3.ObserverMemory.PredictionFactors.CanonicalReachableBehaviorFactor
open D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorClassSurjectivity
open D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The quotient of reachable states by all future readouts has four canonical
properties: every class is reached, distinct classes are separated by a future
protocol, every protocol prefix induces a unique update, and every reachable
realization of the same behavior maps uniquely and surjectively onto it. -/
theorem reachable_behavior_core
    {M X B : Type*} [Monoid M] [MulAction M X]
    (anchor : X) (readout : X -> B) :
    Function.Surjective
        (behaviorClass (M := M) (X := X) (B := B) anchor readout) /\
      (forall first second : ReachableBehaviorQuotient (M := M) anchor readout,
        first ≠ second ->
          exists continuation : M,
            Setoid.kerLift (futureBehavior (M := M) anchor readout) first continuation ≠
              Setoid.kerLift (futureBehavior (M := M) anchor readout) second continuation) /\
      (forall protocolPrefix : M,
        ExistsUnique fun coreUpdate :
            ReachableBehaviorQuotient (M := M) anchor readout ->
              ReachableBehaviorQuotient (M := M) anchor readout =>
          forall action : M,
            coreUpdate (behaviorClass anchor readout action) =
              behaviorClass anchor readout (protocolPrefix * action)) /\
      (forall {X' : Type*} [MulAction M X']
          (candidateAnchor : X') (candidateReadout : X' -> B),
        (forall state : X', exists action : M, action • candidateAnchor = state) ->
        (forall action : M,
          candidateReadout (action • candidateAnchor) = readout (action • anchor)) ->
        ExistsUnique fun factor :
            X' -> ReachableBehaviorQuotient (M := M) anchor readout =>
          Function.Surjective factor /\
            forall action : M,
              factor (action • candidateAnchor) =
                behaviorClass anchor readout action) := by
  classical
  have classesReachable :
      Function.Surjective
        (behaviorClass (M := M) (X := X) (B := B) anchor readout) :=
    every_reachable_behavior_class_is_reachable anchor readout
  refine ⟨classesReachable, ?_, ?_, ?_⟩
  · intro first second distinct
    have profilesDistinct :
        Setoid.kerLift (futureBehavior (M := M) anchor readout) first ≠
          Setoid.kerLift (futureBehavior (M := M) anchor readout) second := by
      intro profilesEqual
      exact distinct (Setoid.kerLift_injective _ profilesEqual)
    by_contra noContinuation
    apply profilesDistinct
    funext continuation
    by_contra valuesDistinct
    exact noContinuation ⟨continuation, valuesDistinct⟩
  · intro protocolPrefix
    let prefixState : ReachableOrbit (M := M) anchor -> ReachableOrbit (M := M) anchor :=
      fun state =>
        ⟨protocolPrefix • state.1, by
          rcases state.2 with ⟨action, actionReaches⟩
          refine ⟨protocolPrefix * action, ?_⟩
          rw [mul_smul, actionReaches]⟩
    have prefixStateRespects :
        forall first second : ReachableOrbit (M := M) anchor,
          Setoid.ker (futureBehavior (M := M) anchor readout) first second ->
            Setoid.ker (futureBehavior (M := M) anchor readout)
              (prefixState first) (prefixState second) := by
      intro first second sameBehavior
      change futureBehavior (M := M) anchor readout first =
        futureBehavior (M := M) anchor readout second at sameBehavior
      funext continuation
      change readout (continuation • (protocolPrefix • first.1)) =
        readout (continuation • (protocolPrefix • second.1))
      simpa only [futureBehavior, mul_smul] using
        congrFun sameBehavior (continuation * protocolPrefix)
    let coreUpdate :
        ReachableBehaviorQuotient (M := M) anchor readout ->
          ReachableBehaviorQuotient (M := M) anchor readout :=
      Quotient.map prefixState prefixStateRespects
    have coreUpdateOnClass : forall action : M,
        coreUpdate (behaviorClass anchor readout action) =
          behaviorClass anchor readout (protocolPrefix * action) := by
      intro action
      change Quotient.mk _ (prefixState (orbitPoint anchor action)) =
        Quotient.mk _ (orbitPoint anchor (protocolPrefix * action))
      apply Quotient.sound
      exact congrArg (futureBehavior (M := M) anchor readout)
        (Subtype.ext (mul_smul protocolPrefix action anchor).symm)
    refine ⟨coreUpdate, coreUpdateOnClass, ?_⟩
    intro other otherOnClass
    funext state
    rcases classesReachable state with ⟨action, rfl⟩
    exact (otherOnClass action).trans (coreUpdateOnClass action).symm
  · intro X' _ candidateAnchor candidateReadout candidateReachable sameBehavior
    exact canonical_reachable_behavior_factor anchor candidateAnchor readout
      candidateReadout candidateReachable sameBehavior

#print axioms reachable_behavior_core

end D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorCore
