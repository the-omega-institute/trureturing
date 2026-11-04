/- GID: D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The absolute-product spectral objective has orthogonal minimum one. -/

import D5.S1.Digit.Infinite.ResetCodebookOrder
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! The exact spectral objective of MathOverflow 515549 and an attaining orthogonal basis. -/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum

noncomputable section

/-- Entrywise absolute value, rather than an operator absolute value. -/
def entryAbs {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => |A i j|

/-- The usual complex spectral radius of a real matrix, as a real number. -/
def radius {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  (spectralRadius ℂ (Complex.ofRealHom.mapMatrix A)).toReal

/-- Both orthogonality identities are explicit. -/
def Orthogonal {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) : Prop :=
  Qᵀ * Q = 1 ∧ Q * Qᵀ = 1

/-- The exact objective of MathOverflow question 515549. -/
def objective {K : ℕ} (P Q : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  radius (entryAbs (P * Q) * entryAbs (Qᵀ * P⁻¹))

private theorem abs_product_ge_one {K : ℕ} (A B : Matrix (Fin K) (Fin K) ℝ)
    (hAB : A * B = 1) : ∀ i j, (1 : Matrix (Fin K) (Fin K) ℝ) i j ≤
      (entryAbs A * entryAbs B) i j := by
  intro i j
  have h := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun k => A i k * B k j)
  have hid : |(A * B) i j| = (1 : Matrix (Fin K) (Fin K) ℝ) i j := by
    rw [hAB]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.mul_apply] at hid
  rw [← hid]
  simpa only [Matrix.mul_apply, entryAbs, abs_mul] using h

private theorem lower_mul_diag {K : ℕ} (A B : Matrix (Fin K) (Fin K) ℝ)
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : Fin K) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hB hj, mul_zero]
    · rw [hA hj, zero_mul]
  · simp

private theorem triangular_radius {K : ℕ} (hK : 0 < K)
    (N : Matrix (Fin K) (Fin K) ℝ) (hN : N.IsLowerTriangular)
    (hd : ∀ i, N i i = 1) : radius N = 1 := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let C : Matrix (Fin K) (Fin K) ℂ := Complex.ofRealHom.mapMatrix N
  have ht : Cᵀ.IsUpperTriangular := by
    intro i j hij
    change (N j i : ℂ) = 0
    rw [hN hij, Complex.ofReal_zero]
  have hc : C.charpoly = (Polynomial.X - 1) ^ K := by
    rw [← Matrix.charpoly_transpose, Matrix.charpoly_of_isUpperTriangular _ ht]
    simp [C, RingHom.mapMatrix_apply, Matrix.transpose_apply, hd]
  have hs : spectrum ℂ C = {1} := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hc]
    simp [Polynomial.IsRoot, hK.ne', sub_eq_zero]
  change (spectralRadius ℂ C).toReal = 1
  rw [spectralRadius_eq_of_unital, hs]
  simp

/-- The complete universal bound and an actual attaining orthogonal matrix. -/
theorem result (K : ℕ) (hK : 0 < K) (P : Matrix (Fin K) (Fin K) ℝ)
    (hP : P.det ≠ 0) :
    (∀ Q : Matrix (Fin K) (Fin K) ℝ, Orthogonal Q → 1 ≤ objective P Q) ∧
      ∃ Q : Matrix (Fin K) (Fin K) ℝ, Orthogonal Q ∧ objective P Q = 1 := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hprod (Q : Matrix (Fin K) (Fin K) ℝ) (hQ : Orthogonal Q) :
      (P * Q) * (Qᵀ * P⁻¹) = 1 := by
    calc
      (P * Q) * (Qᵀ * P⁻¹) = P * (Q * Qᵀ) * P⁻¹ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hQ.2, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
  constructor
  · intro Q hQ
    have h := D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_mono
      (1 : Matrix (Fin K) (Fin K) ℝ)
      (entryAbs (P * Q) * entryAbs (Qᵀ * P⁻¹))
      (by intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
      (abs_product_ge_one _ _ (hprod Q hQ))
    simpa [objective, radius, map_one] using h
  · let f : Fin K → EuclideanSpace ℝ (Fin K) := fun i => WithLp.toLp 2 (P i)
    let e := InnerProductSpace.gramSchmidtOrthonormalBasis
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin K)) = Fintype.card (Fin K)) f
    let a := EuclideanSpace.basisFun (Fin K) ℝ
    let Q : Matrix (Fin K) (Fin K) ℝ := a.toBasis.toMatrix e
    have hQ : Orthogonal Q := by
      constructor
      · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          a.toMatrix_orthonormalBasis_conjTranspose_mul_self e
      · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          a.toMatrix_orthonormalBasis_self_mul_conjTranspose e
    have hQentry (i j : Fin K) : Q i j = e j i := by
      simp [Q, Module.Basis.toMatrix_apply, a, OrthonormalBasis.coe_toBasis_repr_apply]
    have hT : (P * Q).IsLowerTriangular := by
      intro i j hij
      have hzero := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular
        (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin K)) = Fintype.card (Fin K)) f (i := i) (j := j) (show i < j from hij)
      simpa only [Matrix.mul_apply, hQentry, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial, f, e, PiLp.toLp_apply, mul_comm] using hzero
    let T := P * Q
    have hT' : T.IsLowerTriangular := hT
    have hi : T⁻¹ = Qᵀ * P⁻¹ := Matrix.inv_eq_right_inv (hprod Q hQ)
    letI : Invertible T := (isUnit_iff_exists_inv.mpr ⟨Qᵀ * P⁻¹, hprod Q hQ⟩).invertible
    have hTi : T⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hT'
    have hAT : (entryAbs T).IsLowerTriangular := by
      intro i j hij
      simp only [entryAbs, hT' hij, abs_zero]
    have hATi : (entryAbs T⁻¹).IsLowerTriangular := by
      intro i j hij
      simp [entryAbs, hTi hij]
    refine ⟨Q, hQ, ?_⟩
    change radius (entryAbs T * entryAbs (Qᵀ * P⁻¹)) = 1
    rw [← hi]
    apply triangular_radius hK _ (hAT.mul hATi)
    intro i
    rw [lower_mul_diag _ _ hAT hATi]
    change |T i i| * |T⁻¹ i i| = 1
    rw [← abs_mul, ← lower_mul_diag _ _ hT' hTi]
    have htprod : T * T⁻¹ = 1 := Matrix.mul_inv_of_invertible T
    rw [htprod]
    simp

end
end D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum
