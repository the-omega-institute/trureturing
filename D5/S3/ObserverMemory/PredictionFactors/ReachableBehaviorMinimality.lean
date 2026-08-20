/- GID: D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The reachable future-behavior quotient is the canonical smallest finite realization. -/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.PUnit
import Mathlib.SetTheory.Cardinal.NatCard

/- Library-search audit trail (2026-08-20):
   * Repository and pinned-Mathlib searches found no theorem deriving the
     anchor-relative factor from only reachability and equal external behavior.
   * The close repository theorem `controlled_behavior_universal_property`
     instead assumes a supplied surjective realization and commuting structure.
   * Exact pinned-Mathlib hit `Nat.card_le_card_of_surjective` is applied below.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

noncomputable section

namespace D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- States produced from the actual anchor by an allowed monoid action. -/
def ReachableOrbit {M X : Type*} [SMul M X] (anchor : X) :=
  {x : X // exists m : M, m • anchor = x}

/-- The complete public readout obtained after every allowed continuation. -/
def futureBehavior {M X B : Type*} [SMul M X]
    (anchor : X) (readout : X -> B) : ReachableOrbit (M := M) anchor -> M -> B :=
  fun state continuation => readout (continuation • state.1)

/-- The actual reachable states modulo equality of all future public readouts. -/
abbrev ReachableBehaviorQuotient {M X B : Type*} [SMul M X]
    (anchor : X) (readout : X -> B) :=
  Quotient (Setoid.ker (futureBehavior (M := M) anchor readout))

/-- The reachable state produced by one allowed action. -/
def orbitPoint {M X : Type*} [Monoid M] [MulAction M X]
    (anchor : X) (action : M) : ReachableOrbit (M := M) anchor :=
  ⟨action • anchor, ⟨action, rfl⟩⟩

/-- The behavior class produced by one allowed action at the actual anchor. -/
def behaviorClass {M X B : Type*} [Monoid M] [MulAction M X]
    (anchor : X) (readout : X -> B) (action : M) :
    ReachableBehaviorQuotient (M := M) anchor readout :=
  Quotient.mk (Setoid.ker (futureBehavior (M := M) anchor readout))
    (orbitPoint anchor action)

/-- For finite state carriers, every reachable implementation with the same
anchor behavior maps uniquely and surjectively onto the actual reachable
future-behavior quotient, which gives the sharp cardinal lower bound. -/
theorem finite_state_minimality
    {M X X' B : Type*} [Monoid M] [MulAction M X] [MulAction M X']
    [Finite X] [Finite X']
    (anchor : X) (candidateAnchor : X')
    (readout : X -> B) (candidateReadout : X' -> B)
    (candidate_reachable : forall x' : X',
      exists m : M, m • candidateAnchor = x')
    (same_external_behavior : forall m : M,
      candidateReadout (m • candidateAnchor) = readout (m • anchor)) :
    Nat.card (ReachableBehaviorQuotient (M := M) anchor readout) <= Nat.card X' /\
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
    exact congrArg (futureBehavior (M := M) anchor readout)
      (Subtype.ext hm)
  constructor
  · exact Nat.card_le_card_of_surjective factor factor_surjective
  · refine ⟨factor, ⟨factor_surjective, factor_on_orbit⟩, ?_⟩
    intro other hother
    funext x'
    rcases candidate_reachable x' with ⟨m, hm⟩
    rw [← hm, hother.2 m, factor_on_orbit]

/-- The hypotheses are jointly inhabited by the one-state trivial action. -/
example :
    Nat.card (ReachableBehaviorQuotient (M := Nat)
        (PUnit.unit : PUnit.{1}) (id : PUnit.{1} -> PUnit.{1})) <=
      Nat.card PUnit.{1} /\
      ExistsUnique fun factor :
          PUnit.{1} -> ReachableBehaviorQuotient (M := Nat)
            (PUnit.unit : PUnit.{1}) (id : PUnit.{1} -> PUnit.{1}) =>
        Function.Surjective factor /\
          forall m : Nat,
            factor (m • (PUnit.unit : PUnit.{1})) =
              behaviorClass (M := Nat) (X := PUnit.{1}) (B := PUnit.{1})
                PUnit.unit id m := by
  exact finite_state_minimality (M := Nat) (X := PUnit.{1}) (X' := PUnit.{1})
    (B := PUnit.{1}) PUnit.unit PUnit.unit id id
    (fun x => ⟨1, Subsingleton.elim _ x⟩) (fun _ => rfl)

/-- The actual anchor used by the witness is inhabited. -/
example : Unit := ()

#print axioms finite_state_minimality

end D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality
