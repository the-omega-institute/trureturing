/- GID: D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate
   generality: I
   mirror-B: D5/B/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The complex golden exponential is a nonvanishing additive-to-multiplicative Prony character whose radius records signed critical displacement. -/

import D5.S3.Weil.GoldenCriticalSpectrum.GoldenSamplingAtom
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Golden exponential Prony coordinate

The existing golden sampling atom separates a real radial displacement from a
real phase frequency. This owner packages the same atom as one complex
coordinate

`G(z) = exp(-goldenScalePeriod * z)`.

Addition of complex displacements becomes multiplication of nodes, and natural
iteration becomes ordinary powers. The norm records exactly the real part, so
equality of nodes can only alias points at the same radial displacement.

This is a coordinate theorem. It does not identify any zeta zero or prove that
a family of sampled nodes is globally injective in the imaginary direction.
-/

/- Library-search audit trail (2026-09-03):
   * `GoldenSamplingAtom.goldenSamplingAtom` already owns the split radial and
     phase representation and its exact golden-ratio norm.
   * `GoldenCriticalRadius` and `GoldenReflectionTransfer` already own radial
     reflection and unit-radius characterizations.
   * No current D5 declaration packages those facts as one complex character,
     proves its additive law, or proves the natural-time power law needed by
     the finite Prony interfaces.
   * Pinned Mathlib supplies `Complex.exp_add`, `Complex.exp_neg`,
     `Complex.exp_nat_mul`, `Complex.exp_conj`, and `Complex.norm_exp`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.GoldenCriticalSpectrum.GoldenExponentialPronyCoordinate

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle
open D5.S3.Weil.GoldenCriticalSpectrum.GoldenReflectionTransfer
open D5.S3.Weil.GoldenCriticalSpectrum.GoldenSamplingAtom

/-- The common complex exponential coordinate used by both prime-scale and
zero-scale Prony nodes. -/
def goldenExponentialPronyCoordinate (z : ℂ) : ℂ :=
  Complex.exp (-(goldenScalePeriod : ℂ) * z)

/-- The complex coordinate is exactly the existing split radial-phase golden
sampling atom. -/
theorem golden_exponential_prony_coordinate_eq_sampling_atom (z : ℂ) :
    goldenExponentialPronyCoordinate z = goldenSamplingAtom z.im z.re := by
  unfold goldenExponentialPronyCoordinate goldenSamplingAtom goldenTransferGain
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp
    ring
  · simp
    ring

@[simp]
theorem golden_exponential_prony_coordinate_zero :
    goldenExponentialPronyCoordinate 0 = 1 := by
  simp [goldenExponentialPronyCoordinate]

/-- Golden exponential nodes never vanish. -/
theorem golden_exponential_prony_coordinate_ne_zero (z : ℂ) :
    goldenExponentialPronyCoordinate z ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- Addition in the lifted complex coordinate becomes multiplication of Prony
nodes. -/
theorem golden_exponential_prony_coordinate_add (z w : ℂ) :
    goldenExponentialPronyCoordinate (z + w) =
      goldenExponentialPronyCoordinate z *
        goldenExponentialPronyCoordinate w := by
  unfold goldenExponentialPronyCoordinate
  rw [show -(goldenScalePeriod : ℂ) * (z + w) =
      -(goldenScalePeriod : ℂ) * z +
        -(goldenScalePeriod : ℂ) * w by ring,
    Complex.exp_add]

/-- Sign reversal in the lifted coordinate becomes inversion of the Prony
node. -/
theorem golden_exponential_prony_coordinate_neg (z : ℂ) :
    goldenExponentialPronyCoordinate (-z) =
      (goldenExponentialPronyCoordinate z)⁻¹ := by
  unfold goldenExponentialPronyCoordinate
  rw [show -(goldenScalePeriod : ℂ) * (-z) =
      -(-(goldenScalePeriod : ℂ) * z) by ring,
    Complex.exp_neg]

/-- Natural translation depth becomes the corresponding ordinary power of one
Prony node. -/
theorem golden_exponential_prony_coordinate_nat_mul
    (time : ℕ) (z : ℂ) :
    goldenExponentialPronyCoordinate ((time : ℂ) * z) =
      goldenExponentialPronyCoordinate z ^ time := by
  unfold goldenExponentialPronyCoordinate
  rw [show -(goldenScalePeriod : ℂ) * ((time : ℂ) * z) =
      (time : ℂ) * (-(goldenScalePeriod : ℂ) * z) by ring,
    Complex.exp_nat_mul]

/-- Complex conjugation of the lifted coordinate conjugates the node. -/
theorem golden_exponential_prony_coordinate_conj (z : ℂ) :
    goldenExponentialPronyCoordinate (starRingEnd ℂ z) =
      starRingEnd ℂ (goldenExponentialPronyCoordinate z) := by
  unfold goldenExponentialPronyCoordinate
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The radius is the real exponential of the signed radial displacement. -/
theorem golden_exponential_prony_coordinate_norm_exp (z : ℂ) :
    ‖goldenExponentialPronyCoordinate z‖ =
      Real.exp (-goldenScalePeriod * z.re) := by
  unfold goldenExponentialPronyCoordinate
  rw [Complex.norm_exp]
  congr 1
  simp
  ring

/-- The same radius in the canonical golden-ratio normalization. -/
theorem golden_exponential_prony_coordinate_norm (z : ℂ) :
    ‖goldenExponentialPronyCoordinate z‖ =
      Real.goldenRatio ^ (-2 * z.re) := by
  rw [golden_exponential_prony_coordinate_eq_sampling_atom]
  exact (golden_sampling_atom_modulus_and_location z.im z.re).1

/-- Unit radius is exactly zero real displacement. -/
theorem golden_exponential_prony_coordinate_norm_eq_one_iff (z : ℂ) :
    ‖goldenExponentialPronyCoordinate z‖ = 1 ↔ z.re = 0 := by
  rw [golden_exponential_prony_coordinate_eq_sampling_atom]
  exact (golden_sampling_atom_modulus_and_location z.im z.re).2.1

/-- Positive real displacement lies strictly inside the unit disk. -/
theorem golden_exponential_prony_coordinate_inside
    {z : ℂ} (hz : 0 < z.re) :
    ‖goldenExponentialPronyCoordinate z‖ < 1 := by
  rw [golden_exponential_prony_coordinate_eq_sampling_atom]
  exact (golden_sampling_atom_modulus_and_location z.im z.re).2.2 hz

/-- Equality of golden exponential nodes forces equality of their real
coordinates. Any remaining aliasing is purely vertical phase aliasing. -/
theorem golden_exponential_prony_coordinate_eq_implies_re_eq
    {z w : ℂ}
    (h : goldenExponentialPronyCoordinate z =
      goldenExponentialPronyCoordinate w) :
    z.re = w.re := by
  have hNorm := congrArg norm h
  rw [golden_exponential_prony_coordinate_norm_exp,
    golden_exponential_prony_coordinate_norm_exp] at hNorm
  have hArg := Real.exp_injective hNorm
  have hMul : goldenScalePeriod * (z.re - w.re) = 0 := by
    nlinarith
  have hDifference : z.re - w.re = 0 :=
    (mul_eq_zero.mp hMul).resolve_left golden_scale_period_ne_zero
  exact sub_eq_zero.mp hDifference

example : Nonempty ℂ := ⟨0⟩

#print axioms golden_exponential_prony_coordinate_eq_sampling_atom
#print axioms golden_exponential_prony_coordinate_add
#print axioms golden_exponential_prony_coordinate_neg
#print axioms golden_exponential_prony_coordinate_nat_mul
#print axioms golden_exponential_prony_coordinate_norm_eq_one_iff
#print axioms golden_exponential_prony_coordinate_eq_implies_re_eq

end D5.S3.Weil.GoldenCriticalSpectrum.GoldenExponentialPronyCoordinate
