/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original shifted theta inversion and finite negative Fourier Weil operators. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Group.Integral

/-! # The original discriminant theta transformation and Weil operators -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Matrix MeasureTheory

namespace D5.S3.VertexAlgebra.LatticeDiscriminantWeil
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeDiscriminantTheta
open D5.S3.Fourier.MatrixGaussian
open private class_representative shift_eq phase_mk pairRaw pairing_mk pairing_symm
  pairing_add pairing_neg pairing_zero character_orthogonality zero_sector
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

noncomputable section

private def translatedGaussian {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (s : Fin r → ℝ) : C(Fin r → ℝ, ℂ) :=
  (gaussianMap A b).comp (ContinuousMap.addRight s)

private lemma translated_integrable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ) :
    Integrable (translatedGaussian A b s) := by
  have hf : Integrable (gaussianMap A b) := by
    convert integrable_gaussian_linear A hA ((Real.pi : ℂ) * b)
      (by simpa using mul_pos Real.pi_pos hb) 0 0 using 1
    funext x
    simp [gaussianMap, neg_mul]
  exact hf.comp_add_right s

private lemma translated_locally_summable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ)
    (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
    Summable (fun a : Fin r → ℤ =>
      ‖((translatedGaussian A b s).comp
        (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖) := by
  let Ks := K.map (fun x => x + s) (continuous_id.add continuous_const)
  refine (locally_summable_norm_gaussian A hA b hb Ks).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun a => ?_)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  let y : Ks := ⟨(x : Fin r → ℝ) + s, ⟨x, x.property, rfl⟩⟩
  have h := ContinuousMap.norm_coe_le_norm
    (((gaussianMap A b).comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict Ks) y
  convert h using 1
  congr 2
  ext i
  simp [translatedGaussian, y, add_assoc, add_comm, add_left_comm]

private lemma dot_fourier {r : ℕ} (f : (Fin r → ℝ) → ℂ) (w : Fin r → ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar volume
      (1 : Matrix (Fin r) (Fin r) ℝ).toBilin' f w =
      ∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) * f x := by
  unfold VectorFourier.fourierIntegral
  congr 1
  funext x
  simp only [Matrix.toBilin'_apply', one_mulVec, Circle.smul_def,
    smul_eq_mul, Real.fourierChar_apply]
  congr 2
  rw [dotProduct_comm]
  push_cast
  ring

private lemma translated_fourier {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s w : Fin r → ℝ) :
    (∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      translatedGaussian A b s x) =
      Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) *
        ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ))) := by
  rw [← dot_fourier]
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    volume (1 : Matrix (Fin r) (Fin r) ℝ).toBilin' (gaussianMap A b) s) w
  change VectorFourier.fourierIntegral _ _ _ (translatedGaussian A b s) w = _ at h
  rw [h, dot_fourier]
  simp only [Matrix.toBilin'_apply', one_mulVec, Circle.smul_def, smul_eq_mul,
    Real.fourierChar_apply]
  rw [show Complex.exp (((2 * Real.pi * (s ⬝ᵥ w) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) by
    congr 1; rw [dotProduct_comm]; push_cast; ring]
  congr 1
  exact integral_fourier_gaussian A hA b hb w

private lemma translation_phase_norm {r : ℕ} (w s : Fin r → ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma translated_poisson {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ) :
    (∑' n : Fin r → ℤ, Complex.exp
      (-Real.pi * b * (quadratic A ((fun i => (n i : ℝ)) + s) : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
      ∑' k : Fin r → ℤ, Complex.exp
        (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ)) := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  have hs : Summable (fun k : Fin r → ℤ =>
      Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := by
    apply Summable.of_norm
    simpa only [norm_mul, translation_phase_norm, one_mul, div_eq_mul_inv, neg_mul] using
      summable_norm_gaussian A⁻¹ hA.inv b⁻¹ hbi
  have hFT (k : Fin r → ℤ) := translated_fourier A hA b hb s (fun i => (k i : ℝ))
  have hsf := hs.mul_left ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2))
  have hp := D5.S3.Fourier.CoordinatePoisson.tsum_eq_tsum_integral
    (translated_integrable A hA b hb s) (translated_locally_summable A hA b hb s)
    (hsf.congr (fun k => by simpa only [mul_left_comm, dotProduct] using (hFT k).symm))
  calc
    _ = ∑' k : Fin r → ℤ, ∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i, (k i : ℝ) * x i : ℝ)) * translatedGaussian A b s x := hp
    _ = ∑' k : Fin r → ℤ, (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        (Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := by
      apply tsum_congr
      intro k
      simpa only [dotProduct, mul_left_comm] using hFT k
    _ = _ := tsum_mul_left

end
end D5.S3.VertexAlgebra.LatticeDiscriminantWeil
