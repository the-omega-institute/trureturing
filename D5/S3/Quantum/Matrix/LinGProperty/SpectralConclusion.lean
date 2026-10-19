/- GID: D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/SpectralConclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation, D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound, D5/S3/Quantum/Matrix/LinGProperty/Normalization, D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound]
   utility: none
   digest: Combining trace-overlap bounds with the quantitative geometric mean estimate. -/

import D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
import D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
import D5.S3.Quantum.Matrix.LinGProperty.Normalization
import D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound
import Mathlib.Tactic.Module

/-! The normalized spectral estimates combine uniformly for parameters at least one. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinGProperty
open D5.S3.Quantum.Schatten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The trace-corrected arithmetic estimate implies the normalized geometric-mean comparison. -/
theorem normalized_conclusion {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (hA : A.trace = 1) (hB : B.trace = 1) {c : ℝ} (hc : 1 ≤ c)
    (j : Fin (Fintype.card (Fin n)))
    (hAp : A.PosSemidef) (hBp : B.PosSemidef)
    (hL1 : 2 * singularValuesSorted X j ≤
      (hAp.isHermitian.add hBp.isHermitian).eigenvalues₀ j + 1 - ‖X.trace‖)
    (hG : (geometricMean (phi c A) (phi c B)).IsHermitian) :
    singularValuesSorted (phi c X) j ≤ hG.eigenvalues₀ j := by
  let t := ‖X.trace‖
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := normalized_trace_norm_le_one hW hA hB
  have hc0 : 0 < c := by linarith
  have hAn : A ≠ 0 := by intro hz; simpa [hz] using hA
  have hBn : B ≠ 0 := by intro hz; simpa [hz] using hB
  have hP := phi_posDef hAp hAn hc
  have hQ := phi_posDef hBp hBn hc
  have hPa : phi c A = A + c • 1 := by simp [phi, hA]
  have hQb : phi c B = B + c • 1 := by simp [phi, hB]
  let H := (1 / 2 : ℝ) • (A + B)
  have hH : H.IsHermitian :=
    (hAp.isHermitian.add hBp.isHermitian).smul (by simp)
  have hH0 : 0 ≤ H := (hAp.add hBp).smul (by norm_num : (0 : ℝ) ≤ 1/2) |>.nonneg
  have hfloor : c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
      (1 / 2 : ℝ) • (phi c A + phi c B) := by
    have he : (1 / 2 : ℝ) • (phi c A + phi c B) = c • 1 + H := by
      rw [hPa, hQb]; dsimp [H]; module
    rw [he]
    exact le_add_of_nonneg_right hH0
  have hsquare : ((1 / 2 : ℝ) • (phi c A - phi c B)) *
      ((1 / 2 : ℝ) • (phi c A - phi c B)) ≤ ((1-t^2)/4) • 1 := by
    have hd : phi c A - phi c B = A - B := by rw [hPa, hQb]; abel
    rw [hd]
    have hsq : (A-B)*(A-B) ≤ (1-t^2) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.le_iff.mpr (normalized_difference_square_le hW hA hB)
    have hh := smul_le_smul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 1/4)
    convert hh using 1 <;> simp [smul_mul_smul, smul_smul, div_eq_mul_inv, mul_assoc]
  have hmean := arithmetic_sub_le_geometricMean hP hQ hc0 hfloor hsquare
  let r := c - (1-t^2)/(4*c)
  let L := H + (r : ℂ) • 1
  have hL : L.IsHermitian := hH.add (Matrix.isHermitian_one.smul (by simp))
  have he : (1 / 2 : ℝ) • (phi c A + phi c B) -
      (((1-t^2)/4)/c) • (1 : Matrix (Fin n) (Fin n) ℂ) = L := by
    rw [hPa, hQb]
    dsimp [L, H, r]
    rw [show (1-t^2)/(4*c) = ((1-t^2)/4)/c by ring]
    module
  rw [he] at hmean
  have heig := eigenvalues_zero_mono hL hG (Matrix.le_iff.mp hmean) j
  have hshift := eigenvalues_zero_add_scalar H hH r hL j
  have hscale := eigenvalues_zero_smul (A+B)
    (hAp.isHermitian.add hBp.isHermitian) (1/2) (by norm_num) hH j
  have hpert := singularValuesSorted_add_scalar X ((c : ℂ) * X.trace) j
  have hcnorm : ‖(c : ℂ) * X.trace‖ = c*t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  change singularValuesSorted (phi c X) j ≤ singularValuesSorted X j +
    ‖(c : ℂ) * X.trace‖ at hpert
  rw [hcnorm] at hpert
  have hnum : (1-t^2)/(4*c) ≤ (c-1/2)*(1-t) := by
    have hfrac : (1+t)/(4*c) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*c)).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hfrac (by linarith : 0 ≤ 1-t)
    have hid : ((1+t)/(4*c))*(1-t) = (1-t^2)/(4*c) := by ring
    rw [hid] at hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ 1-t by linarith)]
  change 2 * singularValuesSorted X j ≤ _ + 1 - t at hL1
  dsimp [L, r] at hshift
  change hH.eigenvalues₀ j = _ at hscale
  linarith

end D5.S3.Quantum.Matrix.LinGProperty
