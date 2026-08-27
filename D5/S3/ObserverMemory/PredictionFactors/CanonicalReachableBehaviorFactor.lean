/- GID: D5/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every reachable realization of the same anchor behavior maps uniquely and surjectively to the canonical reachable behavior quotient. -/

import D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality

/- Library-search audit trail (2026-08-27):
   * Exact repository primitives `ReachableOrbit`, `futureBehavior`,
     `ReachableBehaviorQuotient`, `orbitPoint`, and `behaviorClass` construct the
     source carrier and canonical classes; they are imported rather than forked.
   * The close theorem `finite_state_minimality` adds finiteness hypotheses and
     the later cardinal-minimality clause, so it does not cover this unrestricted
     unique-surjection theorem.
   * `canonical_minimal_realization` is adjacent but concerns unary dynamics and
     realized images rather than an anchor-relative monoid orbit.
   * Pinned Mathlib provides quotient soundness and classical choice, but no
     theorem packages this reachable equal-external-behavior factorization. -/

noncomputable section

namespace D5.S3.ObserverMemory.PredictionFactors.CanonicalReachableBehaviorFactor

open D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every state of a reachable competing realization has a unique canonical
behavior class. The resulting map is surjective and sends each competing orbit
point to the class of the corresponding source orbit point. -/
theorem canonical_reachable_behavior_factor
    {M X X' B : Type*} [Monoid M] [MulAction M X] [MulAction M X']
    (anchor : X) (candidateAnchor : X')
    (readout : X -> B) (candidateReadout : X' -> B)
    (candidate_reachable : forall x' : X',
      exists m : M, m • candidateAnchor = x')
    (same_external_behavior : forall m : M,
      candidateReadout (m • candidateAnchor) = readout (m • anchor)) :
    ExistsUnique fun factor :
        X' -> ReachableBehaviorQuotient (M := M) anchor readout =>
      Function.Surjective factor /\
        forall m : M,
          factor (m • candidateAnchor) = behaviorClass anchor readout m := by
  classical
  let chosenAction : X' -> M := fun x' => Classical.choose (candidate_reachable x')
  have chosenAction_spec : forall x' : X',
      chosenAction x' • candidateAnchor = x' := by
    intro x'
    exact Classical.choose_spec (candidate_reachable x')
  let factor : X' -> ReachableBehaviorQuotient (M := M) anchor readout :=
    fun x' => behaviorClass anchor readout (chosenAction x')
  have factor_on_orbit : forall m : M,
      factor (m • candidateAnchor) = behaviorClass anchor readout m := by
    intro m
    change Quotient.mk _ (orbitPoint anchor (chosenAction (m • candidateAnchor))) =
      Quotient.mk _ (orbitPoint anchor m)
    apply Quotient.sound
    funext continuation
    change readout (continuation • (chosenAction (m • candidateAnchor) • anchor)) =
      readout (continuation • (m • anchor))
    calc
      readout (continuation • (chosenAction (m • candidateAnchor) • anchor)) =
          readout ((continuation * chosenAction (m • candidateAnchor)) • anchor) := by
        rw [mul_smul]
      _ = candidateReadout
          ((continuation * chosenAction (m • candidateAnchor)) • candidateAnchor) :=
        (same_external_behavior _).symm
      _ = candidateReadout
          (continuation • (chosenAction (m • candidateAnchor) • candidateAnchor)) := by
        rw [mul_smul]
      _ = candidateReadout (continuation • (m • candidateAnchor)) :=
        congrArg (fun x' => candidateReadout (continuation • x'))
          (chosenAction_spec (m • candidateAnchor))
      _ = candidateReadout ((continuation * m) • candidateAnchor) := by
        rw [mul_smul]
      _ = readout ((continuation * m) • anchor) := same_external_behavior _
      _ = readout (continuation • (m • anchor)) := by
        rw [mul_smul]
  have factor_surjective : Function.Surjective factor := by
    intro state
    refine Quotient.inductionOn state ?_
    rintro ⟨x, m, hm⟩
    refine ⟨m • candidateAnchor, ?_⟩
    rw [factor_on_orbit]
    change Quotient.mk _ (orbitPoint anchor m) = Quotient.mk _ ⟨x, ⟨m, hm⟩⟩
    apply Quotient.sound
    exact congrArg (futureBehavior (M := M) anchor readout) (Subtype.ext hm)
  refine ⟨factor, ⟨factor_surjective, factor_on_orbit⟩, ?_⟩
  intro other other_property
  funext x'
  rcases candidate_reachable x' with ⟨m, hm⟩
  rw [← hm, other_property.2 m, factor_on_orbit]

/-- The hypotheses and carrier are jointly inhabited by the one-state action. -/
example :
    ExistsUnique fun factor :
        PUnit.{1} -> ReachableBehaviorQuotient (M := Nat)
          (PUnit.unit : PUnit.{1}) (id : PUnit.{1} -> PUnit.{1}) =>
      Function.Surjective factor /\
        forall m : Nat,
          factor (m • (PUnit.unit : PUnit.{1})) =
            behaviorClass (M := Nat) (X := PUnit.{1}) (B := PUnit.{1})
              PUnit.unit id m := by
  exact canonical_reachable_behavior_factor
    (M := Nat) (X := PUnit.{1}) (X' := PUnit.{1}) (B := PUnit.{1})
    PUnit.unit PUnit.unit id id
    (fun x => ⟨1, Subsingleton.elim _ x⟩) (fun _ => rfl)

/-- The actual anchor carrier used by the witness is inhabited. -/
example : Unit := ()

#print axioms canonical_reachable_behavior_factor

end D5.S3.ObserverMemory.PredictionFactors.CanonicalReachableBehaviorFactor
