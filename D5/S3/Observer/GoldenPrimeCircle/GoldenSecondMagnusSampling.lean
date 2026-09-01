/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden Mellin sample times make second-Magnus curvature descend through whole golden shell shifts. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling
import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Golden second-Magnus sampling

The golden logarithmic scale has period `2 * log phi`; its integral Fourier
modes therefore sample Mellin time at integer multiples of
`pi / log phi`. This file turns that normalization into a complex unit-circle
character, identifies it with the existing prime-frequency Fourier phase, and
shows that multiplication by any whole power of `phi^2` is invisible to every
integral golden mode.

The existing second-Magnus swap kernel is then evaluated at two golden sample
times. It becomes exactly the alternating determinant of the two golden scale
characters. Consequently both the pairwise kernel and every finite
second-Magnus energy descend through independent whole-shell shifts of the two
scale inputs.

This is a quotient-compatibility and sampling theorem. It does not prove that
prime log-frequency ratios have a uniform nonresonance gap, establish Cesaro
recovery of holonomy energy, construct a topological winding or Chern class,
control an infinite prime family, dominate zero-side odd energy, locate zeta
zeros, or prove RH.
-/

/- Library-search audit trail (2026-09-01):
   * `GoldenScaleCircle` owns the unwrapped logarithmic coordinate and its
     whole-shell translation law under multiplication by `phi^2`.
   * `GoldenVerticalSampling` owns the exact equality between integral golden
     Fourier frequency and vertical Mellin frequency.
   * `PrimeFrequencyPhaseFlow` owns the unitary Fourier character.
   * `SecondMagnusSwapCurvature` owns the alternating two-slot kernel and its
     finite energy. This file specializes and transports those owners instead
     of defining parallel phase or curvature objects.
   * Pinned Mathlib supplies `Circle.exp`, `Circle.exp_eq_exp`, and the complex
     coercion of circle phases. Repository search found no existing owner of
     the combined golden-shell descent theorem below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenSecondMagnusSampling

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle
open D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling
open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

noncomputable section

universe u

/-- The vertical Mellin time sampled by an integral mode of the golden scale
circle. -/
def goldenSampleTime (mode : ℤ) : ℝ :=
  (mode : ℝ) * goldenAngularFrequency

/-- The point of the unit additive circle represented by the unwrapped golden
scale coordinate. -/
def goldenScaleCirclePoint (x : ℝ) : AddCircle (1 : ℝ) :=
  (goldenScaleCoordinate x : AddCircle (1 : ℝ))

/-- The integral Fourier character of the golden scale coordinate. -/
def goldenScaleFourierPhase (x : ℝ) (mode : ℤ) : ℂ :=
  (Circle.exp
    (-2 * Real.pi * (mode : ℝ) * goldenScaleCoordinate x) : ℂ)

/-- Multiplication of positive scales becomes addition on the visible golden
scale circle. -/
theorem golden_scale_circle_point_mul
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    goldenScaleCirclePoint (x * y) =
      goldenScaleCirclePoint x + goldenScaleCirclePoint y := by
  unfold goldenScaleCirclePoint
  rw [golden_scale_coordinate_mul hx hy, AddCircle.coe_add]

/-- Every whole golden shell shift has the same visible scale-circle point. -/
theorem golden_scale_circle_point_phi_even_pow_mul
    (shell : ℕ) {x : ℝ} (hx : 0 < x) :
    goldenScaleCirclePoint ((Real.goldenRatio ^ 2) ^ shell * x) =
      goldenScaleCirclePoint x := by
  unfold goldenScaleCirclePoint
  rw [golden_scale_coordinate_phi_even_pow_mul shell hx]
  change
    ((goldenScaleCoordinate x + (shell : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
      (goldenScaleCoordinate x : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  have hShell : (((shell : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨(shell : ℤ), ?_⟩
    simp
  rw [hShell, add_zero]

/-- The golden scale-circle Fourier character is exactly the existing
log-frequency Fourier phase at the corresponding golden Mellin sample time. -/
theorem golden_scale_fourier_phase_eq_log_frequency
    (x : ℝ) (mode : ℤ) :
    goldenScaleFourierPhase x mode =
      fourierPhase (Real.log x) (goldenSampleTime mode) := by
  unfold goldenScaleFourierPhase goldenSampleTime fourierPhase
  rw [Circle.coe_exp]
  apply congrArg Complex.exp
  have hVertical :=
    golden_phase_vertical_frequency_identity x mode
  have hVerticalCast :
      ((2 * Real.pi * (mode : ℝ) * goldenScaleCoordinate x : ℝ) : ℂ) =
        ((((mode : ℝ) * goldenAngularFrequency) * Real.log x : ℝ) : ℂ) :=
    congrArg (fun value : ℝ => (value : ℂ)) hVertical
  calc
    (((-2 * Real.pi * (mode : ℝ) * goldenScaleCoordinate x : ℝ) : ℂ) *
        Complex.I) =
      -Complex.I *
        ((2 * Real.pi * (mode : ℝ) * goldenScaleCoordinate x : ℝ) : ℂ) := by
          push_cast
          ring
    _ = -Complex.I *
        ((((mode : ℝ) * goldenAngularFrequency) * Real.log x : ℝ) : ℂ) := by
          rw [hVerticalCast]
    _ = -Complex.I *
        (((mode : ℝ) * goldenAngularFrequency : ℝ) : ℂ) *
          ((Real.log x : ℝ) : ℂ) := by
          push_cast
          ring

/-- Every golden scale character has unit norm. -/
theorem golden_scale_fourier_phase_norm
    (x : ℝ) (mode : ℤ) :
    ‖goldenScaleFourierPhase x mode‖ = 1 := by
  rw [golden_scale_fourier_phase_eq_log_frequency]
  exact
    (fourier_phase_character_laws
      (Real.log x) 0 (goldenSampleTime mode) 0).2.2.2.1

/-- At a fixed integral mode, the golden scale phase is multiplicative on
positive scales. -/
theorem golden_scale_fourier_phase_mul
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (mode : ℤ) :
    goldenScaleFourierPhase (x * y) mode =
      goldenScaleFourierPhase x mode *
        goldenScaleFourierPhase y mode := by
  rw [golden_scale_fourier_phase_eq_log_frequency,
    golden_scale_fourier_phase_eq_log_frequency,
    golden_scale_fourier_phase_eq_log_frequency,
    Real.log_mul hx.ne' hy.ne']
  exact
    (fourier_phase_character_laws
      (Real.log x) (Real.log y) (goldenSampleTime mode) 0).2.2.1

/-- Integral golden modes are invariant under every whole golden shell shift. -/
theorem golden_scale_fourier_phase_phi_even_pow_mul
    (shell : ℕ) {x : ℝ} (hx : 0 < x) (mode : ℤ) :
    goldenScaleFourierPhase ((Real.goldenRatio ^ 2) ^ shell * x) mode =
      goldenScaleFourierPhase x mode := by
  unfold goldenScaleFourierPhase
  rw [golden_scale_coordinate_phi_even_pow_mul shell hx]
  have hCircle :
      Circle.exp
          (-2 * Real.pi * (mode : ℝ) *
            (goldenScaleCoordinate x + (shell : ℝ))) =
        Circle.exp
          (-2 * Real.pi * (mode : ℝ) * goldenScaleCoordinate x) := by
    rw [Circle.exp_eq_exp]
    refine ⟨-(mode * (shell : ℤ)), ?_⟩
    push_cast
    ring
  exact congrArg Subtype.val hCircle

/-- At golden Mellin sample times, the existing second-Magnus kernel is exactly
the alternating determinant of golden scale Fourier characters. -/
theorem second_magnus_kernel_at_golden_samples
    (x y : ℝ) (mode1 mode2 : ℤ) :
    secondMagnusSwapKernel
        (Real.log x) (Real.log y)
        (goldenSampleTime mode1) (goldenSampleTime mode2) =
      goldenScaleFourierPhase x mode1 *
          goldenScaleFourierPhase y mode2 -
        goldenScaleFourierPhase y mode1 *
          goldenScaleFourierPhase x mode2 := by
  unfold secondMagnusSwapKernel
  rw [golden_scale_fourier_phase_eq_log_frequency,
    golden_scale_fourier_phase_eq_log_frequency,
    golden_scale_fourier_phase_eq_log_frequency,
    golden_scale_fourier_phase_eq_log_frequency]

/-- Independent whole-shell shifts of two positive scales leave the sampled
second-Magnus kernel unchanged. -/
theorem golden_second_magnus_shell_orbit_invariance
    (shellX shellY : ℕ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (mode1 mode2 : ℤ) :
    secondMagnusSwapKernel
        (Real.log ((Real.goldenRatio ^ 2) ^ shellX * x))
        (Real.log ((Real.goldenRatio ^ 2) ^ shellY * y))
        (goldenSampleTime mode1) (goldenSampleTime mode2) =
      secondMagnusSwapKernel
        (Real.log x) (Real.log y)
        (goldenSampleTime mode1) (goldenSampleTime mode2) := by
  rw [second_magnus_kernel_at_golden_samples,
    second_magnus_kernel_at_golden_samples,
    golden_scale_fourier_phase_phi_even_pow_mul shellX hx,
    golden_scale_fourier_phase_phi_even_pow_mul shellY hy,
    golden_scale_fourier_phase_phi_even_pow_mul shellY hy,
    golden_scale_fourier_phase_phi_even_pow_mul shellX hx]

/-- Every finite second-Magnus energy sampled on the golden Mellin lattice
depends only on the whole-shell orbit of each positive scale channel. -/
theorem finite_second_magnus_energy_golden_shell_invariant
    {ι : Type u} [Fintype ι]
    (scale : ι → ℝ) (shell : ι → ℕ)
    (curvature : ι → ι → ℂ)
    (hScale : ∀ p, 0 < scale p)
    (mode1 mode2 : ℤ) :
    finiteSecondMagnusEnergy
        (fun p =>
          Real.log ((Real.goldenRatio ^ 2) ^ shell p * scale p))
        curvature (goldenSampleTime mode1) (goldenSampleTime mode2) =
      finiteSecondMagnusEnergy
        (fun p => Real.log (scale p))
        curvature (goldenSampleTime mode1) (goldenSampleTime mode2) := by
  classical
  unfold finiteSecondMagnusEnergy
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [golden_second_magnus_shell_orbit_invariance
    (shell p) (shell q) (hScale p) (hScale q) mode1 mode2]

#print axioms golden_scale_circle_point_mul
#print axioms golden_scale_circle_point_phi_even_pow_mul
#print axioms golden_scale_fourier_phase_eq_log_frequency
#print axioms golden_scale_fourier_phase_norm
#print axioms golden_scale_fourier_phase_mul
#print axioms golden_scale_fourier_phase_phi_even_pow_mul
#print axioms second_magnus_kernel_at_golden_samples
#print axioms golden_second_magnus_shell_orbit_invariance
#print axioms finite_second_magnus_energy_golden_shell_invariant

end

end D5.S3.Observer.GoldenPrimeCircle.GoldenSecondMagnusSampling
