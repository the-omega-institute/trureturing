/- GID: D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom
   generality: I
   mirror-B: D5/B/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden sampling places positive-height atoms inside the unit disk. -/

import D5.S3.Weil.GoldenCriticalSpectrum.GoldenReflectionTransfer

/-!
# Golden sampling atoms

The golden sampling period is `2 * log phi`. A mode with real frequency
`gamma` and positive height `height` acquires a unitary phase and the radial
gain at displacement `-height`. Its norm is therefore `phi ^ (-2 * height)`.

The inverse-Fourier residue identity in the source depends on a transform
normalization and contour convention. This module isolates the convention-free
conclusion about each sampled atom; it does not assert an inverse-transform
formula.
-/

/- Library-search audit trail (2026-09-01):
   * The target atom and its two chain neighbors remain residual-open with no
     formalization receipt or coverage GID.
   * Repository search found `GoldenScaleCircle.goldenScalePeriod` and
     `GoldenReflectionTransfer.goldenTransferGain`. The latter already owns
     positivity and the unit-gain characterization, and is reused below.
   * No existing D5 declaration combines that radial owner with the complex
     frequency phase or proves the resulting norm and unit-disk location.
   * Pinned Mathlib supplies `Complex.norm_exp`,
     `Real.rpow_def_of_pos`, and `Real.rpow_lt_one_iff_of_pos`.
   * A NyxID-proxied public ecosystem search found Mathlib's complex
     exponential documentation but no exact golden sampling theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.GoldenCriticalSpectrum.GoldenSamplingAtom

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle
open D5.S3.Weil.GoldenCriticalSpectrum.GoldenReflectionTransfer

/-- The complex atom obtained by sampling a mode at one negative golden
period. The first factor is its radial damping and the second is its phase. -/
def goldenSamplingAtom (gamma height : ℝ) : ℂ :=
  (goldenTransferGain (-height) : ℂ) *
    Complex.exp (((-goldenScalePeriod * gamma : ℝ) : ℂ) * Complex.I)

/-- A golden sampling atom has radius `phi ^ (-2h)`. It lies on the unit
circle exactly at the birth boundary `h = 0`, and every positive height lies
strictly inside the unit disk. -/
theorem golden_sampling_atom_modulus_and_location (gamma height : ℝ) :
    ‖goldenSamplingAtom gamma height‖ =
        Real.goldenRatio ^ (-2 * height) ∧
      (‖goldenSamplingAtom gamma height‖ = 1 ↔ height = 0) ∧
      (0 < height → ‖goldenSamplingAtom gamma height‖ < 1) := by
  have hNorm :
      ‖goldenSamplingAtom gamma height‖ = goldenTransferGain (-height) := by
    unfold goldenSamplingAtom
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (golden_transfer_gain_pos (-height)), Complex.norm_exp]
    simp [Complex.mul_re]
  have hPower :
      goldenTransferGain (-height) = Real.goldenRatio ^ (-2 * height) := by
    unfold goldenTransferGain goldenScalePeriod
    rw [Real.rpow_def_of_pos Real.goldenRatio_pos]
    congr 1
    ring
  refine ⟨hNorm.trans hPower, ?_, ?_⟩
  · rw [hNorm]
    simpa using (golden_transfer_gain_eq_one_iff (-height))
  · intro hHeight
    rw [hNorm, hPower]
    exact (Real.rpow_lt_one_iff_of_pos Real.goldenRatio_pos).2
      (Or.inl ⟨Real.one_lt_goldenRatio, by linarith⟩)

/-- At frequency zero and height one, the atom has the exact radius
`phi ^ (-2)` and is strictly inside the unit disk. -/
theorem golden_sampling_atom_inside_witness :
    ‖goldenSamplingAtom 0 1‖ = Real.goldenRatio ^ (-2 : ℝ) ∧
      ‖goldenSamplingAtom 0 1‖ < 1 := by
  have h := golden_sampling_atom_modulus_and_location 0 1
  constructor
  · simpa using h.1
  · exact h.2.2 (by norm_num)

/-- Height zero violates the positive-height premise: the frequency-zero atom
has norm exactly one, so the strict unit-disk conclusion is false. -/
theorem golden_sampling_atom_boundary_counterexample :
    ‖goldenSamplingAtom 0 0‖ = 1 ∧
      ¬ ‖goldenSamplingAtom 0 0‖ < 1 := by
  have h := golden_sampling_atom_modulus_and_location 0 0
  have hUnit : ‖goldenSamplingAtom 0 0‖ = 1 := h.2.1.mpr rfl
  refine ⟨hUnit, ?_⟩
  rw [hUnit]
  exact lt_irrefl (1 : ℝ)

#print axioms golden_sampling_atom_modulus_and_location
#print axioms golden_sampling_atom_inside_witness
#print axioms golden_sampling_atom_boundary_counterexample

end D5.S3.Weil.GoldenCriticalSpectrum.GoldenSamplingAtom
