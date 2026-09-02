/- GID: D5/S3/Observer/HyperbolicTransport/GoldenImageRecoveryObstruction
   generality: I
   mirror-B: D5/B/S3/Observer/HyperbolicTransport/GoldenImageRecoveryObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The projective golden boundary image forgets every observer rapidity. -/

import D5.S3.Observer.HyperbolicTransport.ObserverEventNullDirections
import Mathlib.LinearAlgebra.Projectivization.Basic

/- Library-search audit trail (2026-09-02):
   * The exact D5 predecessor `golden_observer_event_null_directions` constructs
     the source's two null directions, observer event, genuine tangent, and
     positive scale identities. It is imported and applied on that carrier.
   * D5 searches for the event and tangent names together with projectivization,
     injectivity, boundary images, and recovery found no projective observer map
     or recovery obstruction.
   * Pinned Mathlib supplies the canonical `Projectivization` quotient together
     with `Projectivization.mk_eq_mk_iff'`; both are used directly.
   * Searches of the installed non-Mathlib Lean packages found no theorem about
     golden null directions, rapidity, or projective reconstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HyperbolicTransport.GoldenImageRecoveryObstruction

open D5.S3.Observer.HyperbolicTransport.ObserverEventNullDirections
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The projective class of the positive golden null direction. -/
def goldenFutureBoundaryPoint : ℙ ℝ (ℝ × ℝ) :=
  Projectivization.mk ℝ goldenFutureNullDirection (by
    intro zeroDirection
    have secondCoordinate := congrArg Prod.snd zeroDirection
    norm_num [goldenFutureNullDirection] at secondCoordinate)

/-- The projective class of the conjugate golden null direction. -/
def goldenPastBoundaryPoint : ℙ ℝ (ℝ × ℝ) :=
  Projectivization.mk ℝ goldenPastNullDirection (by
    intro zeroDirection
    have secondCoordinate := congrArg Prod.snd zeroDirection
    norm_num [goldenPastNullDirection] at secondCoordinate)

/-- The future boundary vector is nonzero along the observer orbit. -/
private theorem futureBoundaryVector_ne_zero (eta : ℝ) :
    goldenObserverEvent eta + goldenObserverTangent eta ≠ 0 := by
  rcases golden_observer_event_null_directions.2.2.2.2 eta with
    ⟨_, _, _, _, futureDirection, _, futurePositive, _⟩
  have futureNullNonzero : goldenFutureNullDirection ≠ 0 := by
    intro zeroDirection
    have secondCoordinate := congrArg Prod.snd zeroDirection
    norm_num [goldenFutureNullDirection] at secondCoordinate
  rw [futureDirection]
  exact smul_ne_zero (ne_of_gt futurePositive) futureNullNonzero

/-- The past boundary vector is nonzero along the observer orbit. -/
private theorem pastBoundaryVector_ne_zero (eta : ℝ) :
    goldenObserverTangent eta - goldenObserverEvent eta ≠ 0 := by
  rcases golden_observer_event_null_directions.2.2.2.2 eta with
    ⟨_, _, _, _, _, pastDirection, _, pastPositive⟩
  have pastNullNonzero : goldenPastNullDirection ≠ 0 := by
    intro zeroDirection
    have secondCoordinate := congrArg Prod.snd zeroDirection
    norm_num [goldenPastNullDirection] at secondCoordinate
  rw [pastDirection]
  exact smul_ne_zero (ne_of_gt pastPositive) pastNullNonzero

/-- The concrete event-tangent states on the golden observer orbit. -/
def GoldenObserverOrbit :=
  {state : (ℝ × ℝ) × (ℝ × ℝ) //
    ∃ eta : ℝ,
      state = (goldenObserverEvent eta, goldenObserverTangent eta)}

/-- The concrete observer state at a given rapidity. -/
def goldenObserverAt (eta : ℝ) : GoldenObserverOrbit :=
  ⟨(goldenObserverEvent eta, goldenObserverTangent eta), eta, rfl⟩

/-- The future boundary vector of an orbit state is nonzero. -/
private theorem orbitFutureBoundaryVector_ne_zero
    (state : GoldenObserverOrbit) : state.1.1 + state.1.2 ≠ 0 := by
  rcases state.2 with ⟨eta, stateAtEta⟩
  rw [stateAtEta]
  exact futureBoundaryVector_ne_zero eta

/-- The past boundary vector of an orbit state is nonzero. -/
private theorem orbitPastBoundaryVector_ne_zero
    (state : GoldenObserverOrbit) : state.1.2 - state.1.1 ≠ 0 := by
  rcases state.2 with ⟨eta, stateAtEta⟩
  rw [stateAtEta]
  exact pastBoundaryVector_ne_zero eta

/-- The source boundary projection on concrete observer states. Its two
coordinates are the projective classes of event plus tangent and tangent minus
event, respectively. -/
def goldenBoundaryProjection (state : GoldenObserverOrbit) :
    ℙ ℝ (ℝ × ℝ) × ℙ ℝ (ℝ × ℝ) :=
  (Projectivization.mk ℝ
      (state.1.1 + state.1.2)
      (orbitFutureBoundaryVector_ne_zero state),
    Projectivization.mk ℝ
      (state.1.2 - state.1.1)
      (orbitPastBoundaryVector_ne_zero state))

/-- The boundary projection evaluated along the rapidity parameterization. -/
def goldenBoundaryImage (eta : ℝ) :
    ℙ ℝ (ℝ × ℝ) × ℙ ℝ (ℝ × ℝ) :=
  goldenBoundaryProjection (goldenObserverAt eta)

/-- Every observer rapidity has the same pair of projective golden boundary
points. Distinct rapidities nevertheless have distinct event-tangent states,
so the boundary map is non-injective and neither rapidity nor the concrete
observer state can be reconstructed from its image. -/
theorem golden_image_recovery_obstruction :
    (∀ eta : ℝ,
      goldenBoundaryImage eta =
        (goldenFutureBoundaryPoint, goldenPastBoundaryPoint)) ∧
      (∀ eta₁ eta₂ : ℝ, eta₁ ≠ eta₂ →
        goldenBoundaryImage eta₁ = goldenBoundaryImage eta₂ ∧
          (goldenObserverEvent eta₁, goldenObserverTangent eta₁) ≠
            (goldenObserverEvent eta₂, goldenObserverTangent eta₂)) ∧
      ¬ Function.Injective goldenBoundaryProjection ∧
      (∀ recoverRapidity :
          (ℙ ℝ (ℝ × ℝ) × ℙ ℝ (ℝ × ℝ)) → ℝ,
        ¬ ∀ eta : ℝ, recoverRapidity (goldenBoundaryImage eta) = eta) ∧
      ∀ recoverObserver :
          (ℙ ℝ (ℝ × ℝ) × ℙ ℝ (ℝ × ℝ)) →
            (ℝ × ℝ) × (ℝ × ℝ),
        ¬ ∀ eta : ℝ,
          recoverObserver (goldenBoundaryImage eta) =
            (goldenObserverEvent eta, goldenObserverTangent eta) := by
  have fixedImage : ∀ eta : ℝ,
      goldenBoundaryImage eta =
        (goldenFutureBoundaryPoint, goldenPastBoundaryPoint) := by
    intro eta
    rcases golden_observer_event_null_directions.2.2.2.2 eta with
      ⟨_, _, _, _, futureDirection, pastDirection, _, _⟩
    unfold goldenBoundaryImage goldenBoundaryProjection goldenObserverAt
      goldenFutureBoundaryPoint goldenPastBoundaryPoint
    apply Prod.ext
    · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      exact ⟨2 * Real.exp eta / Real.sqrt 5, futureDirection.symm⟩
    · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      exact ⟨2 * Real.exp (-eta) / Real.sqrt 5, pastDirection.symm⟩
  have sameImage : ∀ eta₁ eta₂ : ℝ,
      goldenBoundaryImage eta₁ = goldenBoundaryImage eta₂ := by
    intro eta₁ eta₂
    exact (fixedImage eta₁).trans (fixedImage eta₂).symm
  have distinctObserverStates : ∀ eta₁ eta₂ : ℝ, eta₁ ≠ eta₂ →
      (goldenObserverEvent eta₁, goldenObserverTangent eta₁) ≠
        (goldenObserverEvent eta₂, goldenObserverTangent eta₂) := by
    intro eta₁ eta₂ rapiditiesDistinct statesEqual
    rcases golden_observer_event_null_directions.2.2.2.2 eta₁ with
      ⟨_, _, _, _, futureDirection₁, _, _, _⟩
    rcases golden_observer_event_null_directions.2.2.2.2 eta₂ with
      ⟨_, _, _, _, futureDirection₂, _, _, _⟩
    have futureVectorsEqual := congrArg
      (fun state : (ℝ × ℝ) × (ℝ × ℝ) => state.1 + state.2) statesEqual
    rw [futureDirection₁, futureDirection₂] at futureVectorsEqual
    have amplitudesEqual := congrArg Prod.snd futureVectorsEqual
    have scaledExponentialsEqual :
        2 * Real.exp eta₁ / Real.sqrt 5 =
          2 * Real.exp eta₂ / Real.sqrt 5 := by
      simpa only [Prod.smul_snd, goldenFutureNullDirection, smul_eq_mul,
        mul_one] using amplitudesEqual
    have sqrtFiveNonzero : Real.sqrt 5 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have doubledExponentialsEqual :
        2 * Real.exp eta₁ = 2 * Real.exp eta₂ :=
      (div_left_inj' sqrtFiveNonzero).mp scaledExponentialsEqual
    apply rapiditiesDistinct
    apply Real.exp_injective
    linarith
  refine ⟨fixedImage, ?_, ?_, ?_, ?_⟩
  · intro eta₁ eta₂ rapiditiesDistinct
    exact ⟨sameImage eta₁ eta₂,
      distinctObserverStates eta₁ eta₂ rapiditiesDistinct⟩
  · intro injectiveProjection
    have projectedStatesEqual :
        goldenBoundaryProjection (goldenObserverAt 0) =
          goldenBoundaryProjection (goldenObserverAt 1) := by
      simpa only [goldenBoundaryImage] using sameImage 0 1
    have orbitStatesEqual := injectiveProjection projectedStatesEqual
    have concreteStatesEqual := congrArg Subtype.val orbitStatesEqual
    exact distinctObserverStates 0 1 (by norm_num) concreteStatesEqual
  · intro recoverRapidity recoversEveryRapidity
    have falseEquality : (0 : ℝ) = 1 := calc
      (0 : ℝ) = recoverRapidity (goldenBoundaryImage 0) :=
        (recoversEveryRapidity 0).symm
      _ = recoverRapidity (goldenBoundaryImage 1) :=
        congrArg recoverRapidity (sameImage 0 1)
      _ = 1 := recoversEveryRapidity 1
    norm_num at falseEquality
  · intro recoverObserver recoversEveryObserver
    apply distinctObserverStates 0 1 (by norm_num)
    calc
      (goldenObserverEvent 0, goldenObserverTangent 0) =
          recoverObserver (goldenBoundaryImage 0) :=
        (recoversEveryObserver 0).symm
      _ = recoverObserver (goldenBoundaryImage 1) :=
        congrArg recoverObserver (sameImage 0 1)
      _ = (goldenObserverEvent 1, goldenObserverTangent 1) :=
        recoversEveryObserver 1

#print axioms goldenFutureBoundaryPoint
#print axioms goldenPastBoundaryPoint
#print axioms GoldenObserverOrbit
#print axioms goldenObserverAt
#print axioms goldenBoundaryProjection
#print axioms goldenBoundaryImage
#print axioms golden_image_recovery_obstruction

end

end D5.S3.Observer.HyperbolicTransport.GoldenImageRecoveryObstruction
