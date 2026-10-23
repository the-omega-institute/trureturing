/- GID: D5/S3/Fourier/MatrixGaussian
   generality: G
   mirror-B: D5/B/S3/Fourier/MatrixGaussian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate Lebesgue normalization for positive matrix Gaussian integrals. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder

namespace D5.S3.Fourier.MatrixGaussian
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real quadratic form in the given coordinates. -/
def quadratic (A : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ A *ᵥ x

private lemma integral_mulVec (M : Matrix n n ℝ) (hM : M.det ≠ 0)
    (f : (n → ℝ) → ℂ) :
    (∫ x : n → ℝ, f (M *ᵥ x)) = |M.det|⁻¹ • ∫ y : n → ℝ, f y := by
  let e := (M.mulVecLin.equivOfDetNeZero (by simpa [← Matrix.toLin'_apply'] using hM)).toContinuousLinearEquiv
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := M.mulVecLin) (by simpa [← Matrix.toLin'_apply'] using hM)
  have hi := e.toHomeomorph.isClosedEmbedding.integral_map (μ := volume) f
  change (∫ y, f y ∂Measure.map M.mulVecLin volume) = ∫ x, f (M *ᵥ x) at hi
  rw [hm, integral_smul_measure] at hi
  simpa [← Matrix.toLin'_apply', ENNReal.toReal_ofReal, abs_nonneg] using hi.symm

private lemma integrable_mulVec_iff (M : Matrix n n ℝ) (hM : M.det ≠ 0)
    (f : (n → ℝ) → ℂ) :
    Integrable (fun x : n → ℝ => f (M *ᵥ x)) ↔ Integrable f := by
  let e := (M.mulVecLin.equivOfDetNeZero (by simpa [← Matrix.toLin'_apply'] using hM)).toContinuousLinearEquiv
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := M.mulVecLin) (by simpa [← Matrix.toLin'_apply'] using hM)
  have hi := e.toHomeomorph.isClosedEmbedding.measurableEmbedding.integrable_map_iff
    (μ := volume) (g := f)
  change Integrable f (Measure.map M.mulVecLin volume) ↔
    Integrable (fun x => f (M *ᵥ x)) at hi
  rw [hm, integrable_smul_measure] at hi
  · exact hi.symm
  · simp [← Matrix.toLin'_apply', hM]
  · exact ENNReal.ofReal_ne_top

private lemma sqrt_transpose (A : Matrix n n ℝ) : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
  have h := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h

private lemma sqrt_quadratic (A : Matrix n n ℝ) (hA : A.PosDef) (x : n → ℝ) :
    ∑ i, ((CFC.sqrt A *ᵥ x) i) ^ 2 = quadratic A x := by
  rw [show (∑ i, ((CFC.sqrt A *ᵥ x) i) ^ 2) =
      (CFC.sqrt A *ᵥ x) ⬝ᵥ (CFC.sqrt A *ᵥ x) by simp [dotProduct, pow_two]]
  rw [← dotProduct_transpose_mulVec, sqrt_transpose, mulVec_mulVec,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  rfl

private lemma sqrt_inverse_quadratic (A : Matrix n n ℝ) (hA : A.PosDef)
    (w : n → ℝ) :
    ∑ i, (((CFC.sqrt A)⁻¹ *ᵥ w) i) ^ 2 = quadratic A⁻¹ w := by
  rw [hA.posSemidef.inv_sqrt]
  exact sqrt_quadratic A⁻¹ hA.inv w

private lemma sqrt_det (A : Matrix n n ℝ) (hA : A.PosDef) :
    (CFC.sqrt A).det = Real.sqrt A.det := by
  simpa using hA.posSemidef.det_sqrt

private lemma sqrt_det_ne_zero (A : Matrix n n ℝ) (hA : A.PosDef) :
    (CFC.sqrt A).det ≠ 0 := by
  rw [sqrt_det A hA]
  exact (Real.sqrt_pos.2 hA.det_pos).ne'

private lemma sqrt_linear (A : Matrix n n ℝ) (hA : A.PosDef) (w x : n → ℝ) :
    ((CFC.sqrt A)⁻¹ *ᵥ w) ⬝ᵥ (CFC.sqrt A *ᵥ x) = w ⬝ᵥ x := by
  have hs := sqrt_det_ne_zero A hA
  rw [← dotProduct_transpose_mulVec (CFC.sqrt A) x ((CFC.sqrt A)⁻¹ *ᵥ w),
    sqrt_transpose, mulVec_mulVec,
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec, dotProduct_comm]

private lemma gaussian_sqrt_coordinates (A : Matrix n n ℝ) (hA : A.PosDef)
    (b c : ℂ) (w x : n → ℝ) :
    -b * (quadratic A x : ℂ) + c * (w ⬝ᵥ x : ℝ) =
      -b * ∑ i, ((CFC.sqrt A *ᵥ x) i : ℂ)^2 +
        ∑ i, (c * (((CFC.sqrt A)⁻¹ *ᵥ w) i : ℂ)) * (CFC.sqrt A *ᵥ x) i := by
  simp_rw [← Complex.ofReal_pow, ← Complex.ofReal_sum, sqrt_quadratic A hA]
  congr 1
  simp only [mul_assoc, ← Finset.mul_sum, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  rw [show (∑ i, ((CFC.sqrt A)⁻¹ *ᵥ w) i * (CFC.sqrt A *ᵥ x) i) =
    w ⬝ᵥ x from sqrt_linear A hA w x]

/-- A matrix Gaussian with an arbitrary complex linear phase is integrable for
coordinate Lebesgue measure. The zero-dimensional product is included. -/
theorem integrable_gaussian_linear (A : Matrix n n ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (c : ℂ) (w : n → ℝ) :
    Integrable (fun x : n → ℝ =>
      Complex.exp (-b * (quadratic A x : ℂ) + c * (w ⬝ᵥ x : ℝ))) := by
  let d := (CFC.sqrt A)⁻¹ *ᵥ w
  have hi := GaussianFourier.integrable_cexp_neg_mul_sum_add hb
    (fun i => c * (d i : ℂ))
  have ht := (integrable_mulVec_iff (CFC.sqrt A) (sqrt_det_ne_zero A hA)
    (fun y : n → ℝ => Complex.exp
      (-b * ∑ i, (y i : ℂ)^2 + ∑ i, (c * (d i : ℂ)) * y i))).2 hi
  convert ht using 1
  funext x
  congr 1
  exact gaussian_sqrt_coordinates A hA b c w x

/-- The determinant factor is computed in coordinate Lebesgue measure. -/
theorem integral_gaussian_linear (A : Matrix n n ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (c : ℂ) (w : n → ℝ) :
    (∫ x : n → ℝ, Complex.exp
      (-b * (quadratic A x : ℂ) + c * (w ⬝ᵥ x : ℝ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * (Real.pi / b) ^ ((Fintype.card n : ℂ) / 2) *
        Complex.exp (c ^ 2 * (quadratic A⁻¹ w : ℂ) / (4 * b)) := by
  let d := (CFC.sqrt A)⁻¹ *ᵥ w
  let f := fun y : n → ℝ => Complex.exp
    (-b * ∑ i, (y i : ℂ)^2 + ∑ i, (c * (d i : ℂ)) * y i)
  have he (x : n → ℝ) : Complex.exp
      (-b * (quadratic A x : ℂ) + c * (w ⬝ᵥ x : ℝ)) = f (CFC.sqrt A *ᵥ x) := by
    congr 1
    exact gaussian_sqrt_coordinates A hA b c w x
  simp_rw [he]
  rw [integral_mulVec (CFC.sqrt A) (sqrt_det_ne_zero A hA) f]
  dsimp [f]
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add hb]
  rw [sqrt_det A hA, abs_of_pos (Real.sqrt_pos.2 hA.det_pos)]
  simp only [Complex.real_smul, Complex.ofReal_inv, mul_assoc]
  congr 2
  simp_rw [mul_pow, ← Finset.mul_sum, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
  rw [show (∑ i, d i ^ 2) = quadratic A⁻¹ w from sqrt_inverse_quadratic A hA w]

/-- The coordinate Fourier kernel has the inverse quadratic form and the principal
complex power in every finite dimension, including dimension zero. -/
theorem integral_fourier_gaussian (A : Matrix n n ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (w : n → ℝ) :
    (∫ x : n → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      Complex.exp (-Real.pi * b * (quadratic A x : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(Fintype.card n : ℂ) / 2) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ)) := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have harg : b.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hi := integral_gaussian_linear A hA ((Real.pi : ℂ) * b)
    (by simpa using mul_pos Real.pi_pos hb) (-2 * Real.pi * Complex.I) w
  have he (x : n → ℝ) :
      Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
        Complex.exp (-Real.pi * b * (quadratic A x : ℂ)) =
      Complex.exp (-((Real.pi : ℂ) * b) * (quadratic A x : ℂ) +
        (-2 * Real.pi * Complex.I) * (w ⬝ᵥ x : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [hi, show (Real.pi : ℂ) / (Real.pi * b) = b⁻¹ by field_simp,
    Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  congr 2
  · congr 1
    ring
  · congr 1
    field_simp
    simp [Complex.I_sq]
    <;> ring

#print axioms integral_fourier_gaussian

end
end D5.S3.Fourier.MatrixGaussian
