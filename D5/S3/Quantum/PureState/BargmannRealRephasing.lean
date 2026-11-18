/- GID: D5/S3/Quantum/PureState/BargmannRealRephasing
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/BargmannRealRephasing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Hermitian matrix with a nonvanishing row is real up to phases iff triples are real. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Real rephasing and three-point Bargmann products

For a square complex matrix `G`, rephasing by real angles `θ` replaces the entry `G i j`
by `exp (θ i * I) * G i j * exp (-(θ j) * I)`; for the Gram matrix of a family of pure
states this is the Gram matrix of the same states with each vector multiplied by a phase.
Cyclic products `G i j * G j k * G k i` are unchanged by rephasing, so a rephasing to a real
matrix forces every such product to be real.

When `G` is Hermitian and some row `i₀` has no zero entry, the converse holds. Taking `i₀`
as a base, the phases `θ j = arg (G i₀ j)` turn the entry `(i, j)` into
`G i₀ i * G i j * G j i₀ / (‖G i₀ i‖ * ‖G i₀ j‖)`, a positive multiple of a cyclic
product.
Other entries of `G` may vanish.
For a positive semidefinite `G`, the rephased real matrix is then a real positive
semidefinite matrix and factors as `Bᵀ * B` with `B` real: the columns of `B` are real
vectors with the rephased Gram matrix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace D5.S3.Quantum.PureState.BargmannRealRephasing

private theorem exp_mul_exp_neg (t : ℝ) :
    Complex.exp (t * I) * Complex.exp (-(t : ℂ) * I) = 1 := by
  rw [← Complex.exp_add]
  simp

/-- Rephasing leaves cyclic products unchanged, so a real rephasing makes them real. -/
private theorem triple_im_eq_zero_of_rephasing {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ)
    (θ : Fin N → ℝ)
    (h : ∀ i j, (Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I)).im = 0)
    (i j k : Fin N) : (G i j * G j k * G k i).im = 0 := by
  have hprod : G i j * G j k * G k i =
      (Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I)) *
        (Complex.exp (θ j * I) * G j k * Complex.exp (-(θ k) * I)) *
        (Complex.exp (θ k * I) * G k i * Complex.exp (-(θ i) * I)) := by
    calc G i j * G j k * G k i
        = G i j * G j k * G k i *
            ((Complex.exp (θ i * I) * Complex.exp (-(θ i : ℂ) * I)) *
              (Complex.exp (θ j * I) * Complex.exp (-(θ j : ℂ) * I)) *
              (Complex.exp (θ k * I) * Complex.exp (-(θ k : ℂ) * I))) := by
          rw [exp_mul_exp_neg, exp_mul_exp_neg, exp_mul_exp_neg]
          ring
      _ = _ := by ring
  have h1 := h i j
  have h2 := h j k
  have h3 := h k i
  rw [hprod]
  generalize Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I) = a at h1 ⊢
  generalize Complex.exp (θ j * I) * G j k * Complex.exp (-(θ k) * I) = b at h2 ⊢
  generalize Complex.exp (θ k * I) * G k i * Complex.exp (-(θ i) * I) = c at h3 ⊢
  simp [Complex.mul_im, Complex.mul_re, h1, h2, h3]

private theorem exp_arg_mul_I {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (arg z * I) = z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [eq_div_iff hn, mul_comm]
  exact norm_mul_exp_arg_mul_I z

private theorem exp_neg_arg_mul_I {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (-(arg z : ℂ) * I) = conj z / (‖z‖ : ℂ) := by
  have hc : -(arg z : ℂ) * I = conj ((arg z : ℂ) * I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [hc, Complex.exp_conj, exp_arg_mul_I hz, map_div₀, Complex.conj_ofReal]

/-- A Hermitian complex matrix with a row `i₀` free of zero entries can be rephased by real
angles to a matrix with real entries if and only if every cyclic product
`G i j * G j k * G k i` is real. -/
theorem exists_real_rephasing_iff_triple_products_real {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.IsHermitian) (i₀ : Fin N)
    (hne : ∀ j, G i₀ j ≠ 0) :
    (∃ θ : Fin N → ℝ, ∀ i j,
        (Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I)).im = 0) ↔
      ∀ i j k, (G i j * G j k * G k i).im = 0 := by
  constructor
  · rintro ⟨θ, hθ⟩
    exact triple_im_eq_zero_of_rephasing G θ hθ
  · intro htri
    refine ⟨fun j => arg (G i₀ j), fun i j => ?_⟩
    have hstar : conj (G i₀ j) = G j i₀ := hG.apply j i₀
    have hni : (‖G i₀ i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hne i)
    have hnj : (‖G i₀ j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hne j)
    have hentry : Complex.exp (arg (G i₀ i) * I) * G i j *
          Complex.exp (-(arg (G i₀ j) : ℂ) * I) =
        (G i₀ i * G i j * G j i₀) * (((‖G i₀ i‖ * ‖G i₀ j‖)⁻¹ : ℝ) : ℂ) := by
      rw [exp_arg_mul_I (hne i), exp_neg_arg_mul_I (hne j), hstar]
      push_cast
      field_simp
    rw [hentry, Complex.mul_im, htri i₀ i j, Complex.ofReal_im]
    ring

/-- A positive semidefinite complex matrix with a row `i₀` free of zero entries is, after
rephasing by real angles, the Gram matrix `Bᵀ * B` of real vectors if and only if every cyclic
product `G i j * G j k * G k i` is real. -/
theorem exists_real_gram_rephasing_iff_triple_products_real {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) (i₀ : Fin N)
    (hne : ∀ j, G i₀ j ≠ 0) :
    (∃ θ : Fin N → ℝ, ∃ B : Matrix (Fin N) (Fin N) ℝ, ∀ i j,
        Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I) = ((Bᵀ * B) i j : ℂ)) ↔
      ∀ i j k, (G i j * G j k * G k i).im = 0 := by
  rw [← exists_real_rephasing_iff_triple_products_real G hG.isHermitian i₀ hne]
  constructor
  · rintro ⟨θ, B, hB⟩
    exact ⟨θ, fun i j => by rw [hB i j, Complex.ofReal_im]⟩
  · rintro ⟨θ, hθ⟩
    let D : Matrix (Fin N) (Fin N) ℂ := diagonal fun i => Complex.exp (θ i * I)
    let G' : Matrix (Fin N) (Fin N) ℂ := D * G * Dᴴ
    have hG'entry : ∀ i j,
        G' i j = Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I) := by
      intro i j
      have hc : conj (Complex.exp (θ j * I)) = Complex.exp (-(θ j : ℂ) * I) := by
        rw [← Complex.exp_conj]
        congr 1
        simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp [G', D, mul_diagonal, diagonal_mul, hc]
    have hG'psd : G'.PosSemidef := hG.mul_mul_conjTranspose_same D
    let R : Matrix (Fin N) (Fin N) ℝ := G'.map Complex.re
    have hreal : ∀ i j, G' i j = ((R i j : ℝ) : ℂ) := by
      intro i j
      apply Complex.ext
      · simp [R]
      · rw [Complex.ofReal_im, hG'entry]
        exact hθ i j
    have hRherm : R.IsHermitian := by
      refine IsHermitian.ext fun i j => ?_
      have h := hG'psd.isHermitian.apply i j
      simp only [star_trivial, R, map_apply]
      rw [← h]
      simp
    have hRpsd : R.PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg hRherm fun x => ?_
      have hx := hG'psd.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
      have hform : star (fun i => (x i : ℂ)) ⬝ᵥ (G' *ᵥ fun i => (x i : ℂ)) =
          ((star x ⬝ᵥ (R *ᵥ x) : ℝ) : ℂ) := by
        simp only [dotProduct, mulVec, hreal, Pi.star_apply, star_trivial,
          Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]
      rw [hform] at hx
      exact_mod_cast hx
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hRpsd.nonneg
    refine ⟨θ, B, fun i j => ?_⟩
    rw [← hG'entry, hreal, hB, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

end D5.S3.Quantum.PureState.BargmannRealRephasing
