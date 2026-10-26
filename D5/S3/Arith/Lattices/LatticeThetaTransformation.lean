/- GID: D5/S3/Arith/Lattices/LatticeThetaTransformation
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/LatticeThetaTransformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive even unimodular lattice theta inversion with integer inverse reindexing. -/

import D5.S3.Fourier.MatrixGaussianTheta
import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

/-! # The theta series of an even unimodular lattice

The coordinates are the actual integral charge lattice. Positivity is an analytic
hypothesis on this series and imposes no restriction on the local lattice algebra.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix

namespace D5.S3.Arith.Lattices.LatticeThetaTransformation
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.Fourier.MatrixGaussian
noncomputable section

/-- The ordinary theta series, with every integral charge counted. -/
def latticeTheta (D : LatticeData) (τ : ℂ) : ℂ :=
  ∑' a : Charge D, Complex.exp (Real.pi * Complex.I * τ * (bilinear D a a : ℂ))

private abbrev realGram (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  D.G.map (Int.castRingHom ℝ)

private lemma quadratic_realGram (D : LatticeData) (a : Charge D) :
    quadratic (realGram D) (fun i => (a i : ℝ)) = (bilinear D a a : ℝ) := by
  simp [quadratic, bilinear, dotProduct, Matrix.mulVec, realGram, Finset.mul_sum,
    mul_assoc]

private lemma latticeTheta_eq (D : LatticeData) (τ : ℂ) :
    latticeTheta D τ = theta (realGram D) τ := by
  simp [latticeTheta, theta, quadratic_realGram]

private def gramEquiv {r : ℕ} (G : Matrix (Fin r) (Fin r) ℤ) (hu : IsUnit G.det) :
    (Fin r → ℤ) ≃ (Fin r → ℤ) where
  toFun := G.mulVec
  invFun := G⁻¹.mulVec
  left_inv a := by rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  right_inv a := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

private lemma cast_gram_mulVec {r : ℕ} (G : Matrix (Fin r) (Fin r) ℤ)
    (a : Fin r → ℤ) :
    (fun i => ((G *ᵥ a) i : ℝ)) = G.map (Int.castRingHom ℝ) *ᵥ (fun i => (a i : ℝ)) := by
  funext i
  exact RingHom.map_mulVec (Int.castRingHom ℝ) G a i

private lemma inverse_quadratic_gram {r : ℕ} (G : Matrix (Fin r) (Fin r) ℤ)
    (hG : (G.map (Int.castRingHom ℝ)).PosDef) (a : Fin r → ℤ) :
    quadratic (G.map (Int.castRingHom ℝ))⁻¹ (fun i => ((G *ᵥ a) i : ℝ)) =
      quadratic (G.map (Int.castRingHom ℝ)) (fun i => (a i : ℝ)) := by
  rw [cast_gram_mulVec, quadratic, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG.det_pos.ne'), one_mulVec, dotProduct_comm]
  rfl

/-- Integral unimodularity supplies a genuine bijection of all integer vectors,
which identifies the inverse-form theta series with the original theta series. -/
theorem theta_inverse_integer_reindex {r : ℕ} (G : Matrix (Fin r) (Fin r) ℤ)
    (hG : (G.map (Int.castRingHom ℝ)).PosDef) (hu : IsUnit G.det) (τ : ℂ) :
    theta (G.map (Int.castRingHom ℝ))⁻¹ τ = theta (G.map (Int.castRingHom ℝ)) τ := by
  have h := (gramEquiv G hu).tsum_eq (fun a : Fin r → ℤ =>
    Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (G.map (Int.castRingHom ℝ))⁻¹ (fun i => (a i : ℝ)) : ℂ)))
  simpa only [theta, gramEquiv, Equiv.coe_fn_mk, inverse_quadratic_gram G hG] using h.symm

private lemma gram_det_one (D : LatticeData) (hD : (realGram D).PosDef)
    (hu : IsUnit D.G.det) : (realGram D).det = 1 := by
  have hc : (realGram D).det = (D.G.det : ℝ) := (Int.castRingHom ℝ).map_det D.G |>.symm
  rcases Int.isUnit_eq_one_or hu with h | h
  · simpa [hc, h]
  · have hp := hD.det_pos
    rw [hc, h] at hp
    norm_num at hp

/-- The actual all-charge theta series converges absolutely and obeys the S law
for a positive even unimodular Gram matrix of rank `m + m`, including rank zero. -/
theorem lattice_theta_S (D : LatticeData) (hD : (D.G.map (Int.castRingHom ℝ)).PosDef)
    (hu : IsUnit D.G.det) (m : ℕ) (hr : D.rank = m + m)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun a : Charge D =>
      ‖Complex.exp (Real.pi * Complex.I * τ * (bilinear D a a : ℂ))‖) ∧
      latticeTheta D (-1 / τ) = (-Complex.I * τ) ^ m * latticeTheta D τ := by
  refine ⟨?_, ?_⟩
  · simpa only [quadratic_realGram, Complex.ofReal_intCast] using
      summable_norm_theta (realGram D) hD τ hτ
  · have h := theta_inversion (realGram D) hD τ hτ
    rw [theta_inverse_integer_reindex D.G hD hu, gram_det_one D hD hu, Real.sqrt_one,
      Complex.ofReal_one, div_one] at h
    have he : (D.rank : ℂ) / 2 = (m : ℂ) := by rw [hr]; push_cast; ring
    rw [he, Complex.cpow_natCast] at h
    simpa only [latticeTheta_eq] using h

#print axioms theta_inverse_integer_reindex
#print axioms lattice_theta_S

example (τ : ℂ) (hτ : 0 < τ.im) :
    let D : LatticeData := {
      rank := 0
      G := 1
      symmetric := fun i => Fin.elim0 i
      even_diagonal := fun i => Fin.elim0 i }
    latticeTheta D (-1 / τ) = (-Complex.I * τ) ^ (0 : ℕ) * latticeTheta D τ := by
  exact (lattice_theta_S {
      rank := 0
      G := 1
      symmetric := fun i => Fin.elim0 i
      even_diagonal := fun i => Fin.elim0 i }
    (by simpa using (Matrix.PosDef.one : (1 : Matrix (Fin 0) (Fin 0) ℝ).PosDef))
    (by simp) 0 rfl τ hτ).2

example (τ : ℂ) : theta (1 : Matrix (Fin 0) (Fin 0) ℝ) τ = 1 := by
  simp [theta, quadratic, dotProduct]

example (τ : ℂ) :
    theta ((!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))⁻¹ τ =
      theta ((!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  apply theta_inverse_integer_reindex
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
    · intro x hx
      have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (by ext i; fin_cases i <;> simp [h])
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      rcases hn with h | h
      · by_cases hh : x 1 = 0
        · simp only [hh, add_zero, zero_mul]
          nlinarith [sq_pos_of_ne_zero h]
        · nlinarith [sq_pos_of_ne_zero hh, sq_nonneg (x 0 + x 1)]
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1)]
  · norm_num [Matrix.det_fin_two]

end
end D5.S3.Arith.Lattices.LatticeThetaTransformation
