/- GID: D5/S3/Observer/HyperbolicTransport/ObserverEventNullDirections
   generality: I
   mirror-B: D5/B/S3/Observer/HyperbolicTransport/ObserverEventNullDirections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden observer events and their tangents recover two fixed null directions. -/

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Current-tree searches for observer events, rapidity, null bases, tangent vectors,
     and light cones found no theorem with this continuous golden parameterization.
   * `GoldenHyperbolicInflation` treats discrete spectral transport, while
     `GoldenLorentzUpdate` treats the Fibonacci substitution's action on the same
     quadratic form; neither states the event-tangent decomposition below.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`, `Real.goldenConj_sq`,
     `Real.goldenRatio_add_goldenConj`, `Real.goldenRatio_mul_goldenConj`,
     `Real.goldenRatio_sub_goldenConj`, `Real.sq_sqrt`, `Real.hasDerivAt_exp`,
     and `HasDerivAt.prodMk`; these components are reused directly.
   * Searches in the other pinned Lean packages found no golden null-basis or
     rapidity theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.HyperbolicTransport.ObserverEventNullDirections

/-- The positive golden null direction. -/
def goldenFutureNullDirection : ℝ × ℝ :=
  (Real.goldenRatio, 1)

/-- The conjugate golden null direction. -/
def goldenPastNullDirection : ℝ × ℝ :=
  (Real.goldenConj, 1)

/-- The golden Lorentz form `Q(x,y) = x² - xy - y²`. -/
def goldenLorentzForm (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 - v.1 * v.2 - v.2 ^ 2

/-- The unit golden hyperbola parameterized by rapidity. -/
def goldenObserverEvent (eta : ℝ) : ℝ × ℝ :=
  ((Real.exp eta * Real.goldenRatio - Real.exp (-eta) * Real.goldenConj) /
      Real.sqrt 5,
    (Real.exp eta - Real.exp (-eta)) / Real.sqrt 5)

/-- The rapidity tangent of the golden observer event. -/
def goldenObserverTangent (eta : ℝ) : ℝ × ℝ :=
  ((Real.exp eta * Real.goldenRatio + Real.exp (-eta) * Real.goldenConj) /
      Real.sqrt 5,
    (Real.exp eta + Real.exp (-eta)) / Real.sqrt 5)

/-- Every golden observer event has unit Lorentz value, and adding or subtracting
its genuine tangent recovers the same two null directions with positive amplitudes. -/
theorem golden_observer_event_null_directions :
    (∀ v : ℝ × ℝ, ∃! weights : ℝ × ℝ,
      v = weights.1 • goldenFutureNullDirection +
        weights.2 • goldenPastNullDirection) ∧
      (∀ a b : ℝ,
        goldenLorentzForm
            (a • goldenFutureNullDirection + b • goldenPastNullDirection) =
          -5 * a * b) ∧
      goldenLorentzForm goldenFutureNullDirection = 0 ∧
      goldenLorentzForm goldenPastNullDirection = 0 ∧
      ∀ eta : ℝ,
        goldenObserverEvent eta =
            (Real.exp eta / Real.sqrt 5) • goldenFutureNullDirection +
              (-Real.exp (-eta) / Real.sqrt 5) • goldenPastNullDirection ∧
          goldenObserverTangent eta =
            (Real.exp eta / Real.sqrt 5) • goldenFutureNullDirection +
              (Real.exp (-eta) / Real.sqrt 5) • goldenPastNullDirection ∧
          HasDerivAt goldenObserverEvent (goldenObserverTangent eta) eta ∧
          goldenLorentzForm (goldenObserverEvent eta) = 1 ∧
          goldenObserverEvent eta + goldenObserverTangent eta =
            (2 * Real.exp eta / Real.sqrt 5) • goldenFutureNullDirection ∧
          goldenObserverTangent eta - goldenObserverEvent eta =
            (2 * Real.exp (-eta) / Real.sqrt 5) • goldenPastNullDirection ∧
          0 < 2 * Real.exp eta / Real.sqrt 5 ∧
          0 < 2 * Real.exp (-eta) / Real.sqrt 5 := by
  have sqrtFivePos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have sqrtFiveNe : Real.sqrt 5 ≠ 0 := ne_of_gt sqrtFivePos
  have sqrtFiveSquare : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have basisDecomposition :
      ∀ v : ℝ × ℝ, ∃! weights : ℝ × ℝ,
        v = weights.1 • goldenFutureNullDirection +
          weights.2 • goldenPastNullDirection := by
    intro v
    let difference := Real.goldenRatio - Real.goldenConj
    have differenceNe : difference ≠ 0 := by
      dsimp only [difference]
      rw [Real.goldenRatio_sub_goldenConj]
      exact sqrtFiveNe
    let weights : ℝ × ℝ :=
      ((v.1 - Real.goldenConj * v.2) / difference,
        (Real.goldenRatio * v.2 - v.1) / difference)
    refine ⟨weights, ?_, ?_⟩
    · ext <;>
        simp [weights, difference, goldenFutureNullDirection,
          goldenPastNullDirection, smul_eq_mul] <;>
        field_simp [differenceNe] <;>
        ring
    · intro candidate candidateExpansion
      have firstCoordinate := congrArg Prod.fst candidateExpansion
      have secondCoordinate := congrArg Prod.snd candidateExpansion
      simp [goldenFutureNullDirection, goldenPastNullDirection, smul_eq_mul]
        at firstCoordinate secondCoordinate
      apply Prod.ext
      · dsimp only [weights]
        apply (eq_div_iff differenceNe).2
        rw [firstCoordinate, secondCoordinate]
        dsimp only [difference]
        ring
      · dsimp only [weights]
        apply (eq_div_iff differenceNe).2
        rw [firstCoordinate, secondCoordinate]
        dsimp only [difference]
        ring
  have coordinateForm (a b : ℝ) :
      goldenLorentzForm
          (a • goldenFutureNullDirection + b • goldenPastNullDirection) =
        -5 * a * b := by
    calc
      goldenLorentzForm
            (a • goldenFutureNullDirection + b • goldenPastNullDirection) =
          a ^ 2 *
              (Real.goldenRatio ^ 2 - Real.goldenRatio - 1) +
            b ^ 2 * (Real.goldenConj ^ 2 - Real.goldenConj - 1) +
            a * b *
              (2 * (Real.goldenRatio * Real.goldenConj) -
                (Real.goldenRatio + Real.goldenConj) - 2) := by
        simp [goldenLorentzForm, goldenFutureNullDirection,
          goldenPastNullDirection, smul_eq_mul]
        ring_nf
        rw [sqrtFiveSquare]
        ring
      _ = -5 * a * b := by
        rw [Real.goldenRatio_sq, Real.goldenConj_sq,
          Real.goldenRatio_mul_goldenConj,
          Real.goldenRatio_add_goldenConj]
        ring
  refine ⟨basisDecomposition, coordinateForm, ?_, ?_, ?_⟩
  · simpa using coordinateForm 1 0
  · simpa using coordinateForm 0 1
  · intro eta
    have eventExpansion :
        goldenObserverEvent eta =
          (Real.exp eta / Real.sqrt 5) • goldenFutureNullDirection +
            (-Real.exp (-eta) / Real.sqrt 5) • goldenPastNullDirection := by
      ext <;>
        simp [goldenObserverEvent, goldenFutureNullDirection,
          goldenPastNullDirection, smul_eq_mul] <;>
        ring
    have tangentExpansion :
        goldenObserverTangent eta =
          (Real.exp eta / Real.sqrt 5) • goldenFutureNullDirection +
            (Real.exp (-eta) / Real.sqrt 5) • goldenPastNullDirection := by
      ext <;>
        simp [goldenObserverTangent, goldenFutureNullDirection,
          goldenPastNullDirection, smul_eq_mul] <;>
        ring
    have negativeExpDerivative :
        HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-eta)) eta := by
      simpa only [Function.comp_def, mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-eta)).comp eta (hasDerivAt_neg eta)
    have firstCoordinateDerivative :
        HasDerivAt
          (fun x : ℝ =>
            (Real.exp x * Real.goldenRatio -
                Real.exp (-x) * Real.goldenConj) / Real.sqrt 5)
          ((Real.exp eta * Real.goldenRatio +
              Real.exp (-eta) * Real.goldenConj) / Real.sqrt 5)
          eta := by
      simpa using (((Real.hasDerivAt_exp eta).mul_const Real.goldenRatio).sub
          (negativeExpDerivative.mul_const Real.goldenConj)).div_const
          (Real.sqrt 5)
    have secondCoordinateDerivative :
        HasDerivAt
          (fun x : ℝ =>
            (Real.exp x - Real.exp (-x)) / Real.sqrt 5)
          ((Real.exp eta + Real.exp (-eta)) / Real.sqrt 5)
          eta := by
      simpa using ((Real.hasDerivAt_exp eta).sub negativeExpDerivative).div_const
        (Real.sqrt 5)
    have tangentDerivative :
        HasDerivAt goldenObserverEvent (goldenObserverTangent eta) eta := by
      change HasDerivAt
        (fun x : ℝ =>
          ((Real.exp x * Real.goldenRatio -
                Real.exp (-x) * Real.goldenConj) / Real.sqrt 5,
            (Real.exp x - Real.exp (-x)) / Real.sqrt 5))
        ((Real.exp eta * Real.goldenRatio +
              Real.exp (-eta) * Real.goldenConj) / Real.sqrt 5,
          (Real.exp eta + Real.exp (-eta)) / Real.sqrt 5)
        eta
      exact firstCoordinateDerivative.prodMk secondCoordinateDerivative
    have exponentialProduct :
        Real.exp eta * Real.exp (-eta) = 1 := by
      rw [← Real.exp_add]
      simp
    have eventUnit : goldenLorentzForm (goldenObserverEvent eta) = 1 := by
      rw [eventExpansion, coordinateForm]
      field_simp [sqrtFiveNe]
      nlinarith [exponentialProduct, sqrtFiveSquare]
    have futureDirection :
        goldenObserverEvent eta + goldenObserverTangent eta =
          (2 * Real.exp eta / Real.sqrt 5) • goldenFutureNullDirection := by
      ext <;>
        simp [goldenObserverEvent, goldenObserverTangent,
          goldenFutureNullDirection, smul_eq_mul] <;>
        ring
    have pastDirection :
        goldenObserverTangent eta - goldenObserverEvent eta =
          (2 * Real.exp (-eta) / Real.sqrt 5) • goldenPastNullDirection := by
      ext <;>
        simp [goldenObserverEvent, goldenObserverTangent,
          goldenPastNullDirection, smul_eq_mul] <;>
        ring
    refine ⟨eventExpansion, tangentExpansion, tangentDerivative, eventUnit,
      futureDirection, pastDirection, ?_, ?_⟩
    · exact div_pos (mul_pos (by norm_num) (Real.exp_pos eta)) sqrtFivePos
    · exact div_pos (mul_pos (by norm_num) (Real.exp_pos (-eta))) sqrtFivePos

/- At zero rapidity the theorem supplies a concrete event satisfying all eight laws. -/
example :
    goldenObserverEvent 0 =
        (Real.exp 0 / Real.sqrt 5) • goldenFutureNullDirection +
          (-Real.exp 0 / Real.sqrt 5) • goldenPastNullDirection ∧
      goldenObserverTangent 0 =
        (Real.exp 0 / Real.sqrt 5) • goldenFutureNullDirection +
          (Real.exp 0 / Real.sqrt 5) • goldenPastNullDirection ∧
      HasDerivAt goldenObserverEvent (goldenObserverTangent 0) 0 ∧
      goldenLorentzForm (goldenObserverEvent 0) = 1 ∧
      goldenObserverEvent 0 + goldenObserverTangent 0 =
        (2 * Real.exp 0 / Real.sqrt 5) • goldenFutureNullDirection ∧
      goldenObserverTangent 0 - goldenObserverEvent 0 =
        (2 * Real.exp 0 / Real.sqrt 5) • goldenPastNullDirection ∧
      0 < 2 * Real.exp 0 / Real.sqrt 5 ∧
      0 < 2 * Real.exp 0 / Real.sqrt 5 := by
  simpa using golden_observer_event_null_directions.2.2.2.2 (0 : ℝ)

/- Replacing the genuine tangent by the zero vector already breaks the future-null
identity at zero rapidity. -/
example :
    goldenObserverEvent 0 + (0, 0) ≠
      (2 * Real.exp 0 / Real.sqrt 5) • goldenFutureNullDirection := by
  intro falseIdentity
  have secondCoordinate := congrArg Prod.snd falseIdentity
  have nonzeroAmplitude : (2 : ℝ) / Real.sqrt 5 ≠ 0 :=
    div_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  apply nonzeroAmplitude
  simpa [goldenObserverEvent, goldenFutureNullDirection, smul_eq_mul] using
    secondCoordinate.symm

#print axioms golden_observer_event_null_directions

end D5.S3.Observer.HyperbolicTransport.ObserverEventNullDirections
