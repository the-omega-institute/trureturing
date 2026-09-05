/- GID: D5/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection
   generality: G
   mirror-B: D5/B/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Symmetry forces every second-order scalar regulator mode to be radial. -/

import D5.S3.CompletionDynamics.ObserverJet.PairedOddJetCancellation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.ObserverJet.ScalarCouplingSelection

open scoped BigOperators
open D5.S3.CompletionDynamics.ObserverJet.PairedOddJetCancellation

/-- A real two-coordinate nontrivial regulator mode. -/
abbrev RegulatorMode := EuclideanSpace ℝ (Fin 2)

/-- The standard regulator rotation. -/
def regulatorRotation (theta : ℝ) (u : RegulatorMode) : RegulatorMode :=
  !₂[Real.cos theta * u 0 - Real.sin theta * u 1,
    Real.sin theta * u 0 + Real.cos theta * u 1]

/-- A generating regulator reflection. -/
def regulatorReflection (u : RegulatorMode) : RegulatorMode :=
  !₂[u 0, -u 1]

/-- The general real degree-at-most-two contribution of one regulator mode,
with its constant term kept globally outside the mode. -/
def secondOrderMode
    (linearX linearY quadraticXX quadraticXY quadraticYY : ℝ)
    (u : RegulatorMode) : ℝ :=
  linearX * u 0 + linearY * u 1 +
    quadraticXX * (u 0) ^ 2 + quadraticXY * u 0 * u 1 +
      quadraticYY * (u 1) ^ 2

/-- Every rotation-invariant and reflection-invariant real polynomial mode of
degree at most two and with zero constant term is a radial quadratic mode. -/
theorem invariant_second_order_mode_is_radial
    (linearX linearY quadraticXX quadraticXY quadraticYY : ℝ)
    (hRotation : ∀ (theta : ℝ) (u : RegulatorMode),
      secondOrderMode linearX linearY quadraticXX quadraticXY quadraticYY
          (regulatorRotation theta u) =
        secondOrderMode linearX linearY quadraticXX quadraticXY quadraticYY u)
    (hReflection : ∀ u : RegulatorMode,
      secondOrderMode linearX linearY quadraticXX quadraticXY quadraticYY
          (regulatorReflection u) =
        secondOrderMode linearX linearY quadraticXX quadraticXY quadraticYY u) :
    ∀ u : RegulatorMode,
      secondOrderMode linearX linearY quadraticXX quadraticXY quadraticYY u =
        quadraticXX * ‖u‖ ^ 2 := by
  have hLinearX := hRotation Real.pi (!₂[1, 0] : RegulatorMode)
  have hLinearY := hRotation Real.pi (!₂[0, 1] : RegulatorMode)
  have hLinearXZero : linearX = 0 := by
    norm_num [secondOrderMode, regulatorRotation, Real.cos_pi,
      Real.sin_pi] at hLinearX
    linarith
  have hLinearYZero : linearY = 0 := by
    norm_num [secondOrderMode, regulatorRotation, Real.cos_pi,
      Real.sin_pi] at hLinearY
    linarith
  have hMixed := hReflection (!₂[1, 1] : RegulatorMode)
  have hMixedZero : quadraticXY = 0 := by
    norm_num [secondOrderMode, regulatorReflection, hLinearXZero,
      hLinearYZero] at hMixed
    linarith
  have hDiagonal :=
    hRotation (Real.pi / 2) (!₂[1, 0] : RegulatorMode)
  have hDiagonalEqual : quadraticYY = quadraticXX := by
    norm_num [secondOrderMode, regulatorRotation, Real.cos_pi_div_two,
      Real.sin_pi_div_two, hLinearXZero, hLinearYZero, hMixedZero] at hDiagonal
    linarith
  intro u
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [secondOrderMode, hLinearXZero, hLinearYZero, hMixedZero,
    hDiagonalEqual, Fin.sum_univ_two]
  ring

/-- A completed scalar whose second-order modal part and higher-order remainder
preserve regulator rotations and reflections has only radial quadratic modal
terms. A nonzero reflected displacement has zero signed first moment and
strictly positive second moment. -/
theorem scalar_coupling_selection_rule
    (F0 : ℝ)
    (linearX linearY quadraticXX quadraticXY quadraticYY : ℕ+ → ℝ)
    (higherInvariant : ℕ+ → RegulatorMode → ℝ)
    (hCompletedRotation : ∀ (n : ℕ+) (theta : ℝ) (u : RegulatorMode),
      secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) (regulatorRotation theta u) +
          higherInvariant n (regulatorRotation theta u) =
        secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) u + higherInvariant n u)
    (hHigherRotation : ∀ (n : ℕ+) (theta : ℝ) (u : RegulatorMode),
      higherInvariant n (regulatorRotation theta u) = higherInvariant n u)
    (hCompletedReflection : ∀ (n : ℕ+) (u : RegulatorMode),
      secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) (regulatorReflection u) +
          higherInvariant n (regulatorReflection u) =
        secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) u + higherInvariant n u)
    (hHigherReflection : ∀ (n : ℕ+) (u : RegulatorMode),
      higherInvariant n (regulatorReflection u) = higherInvariant n u)
    (delta gamma : ℝ) (hDelta : delta ≠ 0) :
    ∃ kappa : ℕ+ → ℝ,
      (∀ modes : ℕ+ → RegulatorMode,
        F0 + ∑' n : ℕ+,
            (secondOrderMode (linearX n) (linearY n) (quadraticXX n)
                (quadraticXY n) (quadraticYY n) (modes n) +
              higherInvariant n (modes n)) =
          F0 + ∑' n : ℕ+,
            (kappa n * ‖modes n‖ ^ 2 + higherInvariant n (modes n))) ∧
      let right : ℂ :=
        (1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (gamma : ℂ)
      let left : ℂ :=
        (1 / 2 : ℂ) - (delta : ℂ) + Complex.I * (gamma : ℂ)
      let center : ℂ :=
        (1 / 2 : ℂ) + Complex.I * (gamma : ℂ)
      (right + left) / 2 = center ∧
      (delta + (-delta)) / 2 = 0 ∧
      (delta ^ 2 + (-delta) ^ 2) / 2 = delta ^ 2 ∧
      0 < (delta ^ 2 + (-delta) ^ 2) / 2 := by
  have hModeRotation (n : ℕ+) (theta : ℝ) (u : RegulatorMode) :
      secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) (regulatorRotation theta u) =
        secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) u := by
    have hCompleted := hCompletedRotation n theta u
    rw [hHigherRotation n theta u] at hCompleted
    linarith
  have hModeReflection (n : ℕ+) (u : RegulatorMode) :
      secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) (regulatorReflection u) =
        secondOrderMode (linearX n) (linearY n) (quadraticXX n)
          (quadraticXY n) (quadraticYY n) u := by
    have hCompleted := hCompletedReflection n u
    rw [hHigherReflection n u] at hCompleted
    linarith
  refine ⟨quadraticXX, ?_, ?_⟩
  · intro modes
    congr 1
    apply tsum_congr
    intro n
    rw [invariant_second_order_mode_is_radial
      (linearX n) (linearY n) (quadraticXX n) (quadraticXY n)
      (quadraticYY n) (hModeRotation n) (hModeReflection n)]
  · dsimp
    refine ⟨by ring, paired_tangent_average_zero delta,
      paired_tangent_second_moment delta, ?_⟩
    rw [paired_tangent_second_moment]
    positivity

/-- The regulator-mode domain is inhabited. -/
example : RegulatorMode := 0

/-- The symmetry and nonzero-displacement hypotheses are jointly satisfiable. -/
example :
    let zeroCoefficient : ℕ+ → ℝ := fun _ => 0
    let zeroHigher : ℕ+ → RegulatorMode → ℝ := fun _ _ => 0
    (∀ (n : ℕ+) (theta : ℝ) (u : RegulatorMode),
      secondOrderMode (zeroCoefficient n) (zeroCoefficient n)
          (zeroCoefficient n) (zeroCoefficient n) (zeroCoefficient n)
          (regulatorRotation theta u) + zeroHigher n (regulatorRotation theta u) =
        secondOrderMode (zeroCoefficient n) (zeroCoefficient n)
          (zeroCoefficient n) (zeroCoefficient n) (zeroCoefficient n) u + zeroHigher n u) ∧
    (∀ (n : ℕ+) (theta : ℝ) (u : RegulatorMode),
      zeroHigher n (regulatorRotation theta u) = zeroHigher n u) ∧
    (∀ (n : ℕ+) (u : RegulatorMode),
      secondOrderMode (zeroCoefficient n) (zeroCoefficient n)
          (zeroCoefficient n) (zeroCoefficient n) (zeroCoefficient n)
          (regulatorReflection u) + zeroHigher n (regulatorReflection u) =
        secondOrderMode (zeroCoefficient n) (zeroCoefficient n)
          (zeroCoefficient n) (zeroCoefficient n) (zeroCoefficient n) u + zeroHigher n u) ∧
    (∀ (n : ℕ+) (u : RegulatorMode),
      zeroHigher n (regulatorReflection u) = zeroHigher n u) ∧
    (1 : ℝ) ≠ 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, one_ne_zero⟩
  · intro n theta u
    simp only [secondOrderMode, zero_mul, add_zero]
  · intro n theta u
    rfl
  · intro n u
    simp only [secondOrderMode, zero_mul, add_zero]
  · intro n u
    rfl

#print axioms invariant_second_order_mode_is_radial
#print axioms scalar_coupling_selection_rule

end D5.S3.CompletionDynamics.ObserverJet.ScalarCouplingSelection
