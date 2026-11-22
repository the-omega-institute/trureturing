/- GID: D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full Cartesian product of n quaternion readings has least real feature dimension five to the n. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic.FinCases


open scoped InnerProductSpace Quaternion
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
namespace D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank

/-- Entrywise formula for the Kronecker power on the Cartesian grid. -/
private def matrixPower (n : ℕ) {s : Type*} (A : Matrix s s ℝ) :
    Matrix (Fin n → s) (Fin n → s) ℝ :=
  Matrix.of fun x y => ∏ i, A (x i) (y i)

private theorem matrixPower_mul (n : ℕ) {s : Type*} [Fintype s] [DecidableEq s]
    (A B : Matrix s s ℝ) :
    matrixPower n (A * B) = matrixPower n A * matrixPower n B := by
  classical
  ext x y
  simp only [matrixPower, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib

private theorem matrixPower_one (n : ℕ) {s : Type*} [Fintype s] [DecidableEq s] :
    matrixPower n (1 : Matrix s s ℝ) = 1 := by
  classical
  ext x y
  simp only [matrixPower, Matrix.of_apply, Matrix.one_apply, Finset.prod_boole,
    Finset.mem_univ, forall_const]
  by_cases h : x = y
  · simp [h]
  · simp [h, show ¬ ∀ i, x i = y i from fun hx => h (funext hx)]

private theorem matrixPower_isUnit (n : ℕ) {s : Type*} [Fintype s] [DecidableEq s]
    {A : Matrix s s ℝ} (h : IsUnit A) : IsUnit (matrixPower n A) := by
  classical
  let f : Matrix s s ℝ →* Matrix (Fin n → s) (Fin n → s) ℝ := {
    toFun := matrixPower n, map_one' := matrixPower_one n, map_mul' := matrixPower_mul n }
  exact h.map f

private def points : Fin 5 → unitary ℍ[ℝ] :=
  ![1, -1, unitI, unitJ, unitI * unitJ]

private noncomputable def G : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun i j => quaternionModel.kappa (points i) (points j)

/-- The five feature vectors are independent, as witnessed by their Gram determinant. -/
private theorem five_gram : G.det = 1/8 := by
  let A : Matrix (Fin 5) (Fin 5) ℝ := !![1,0,1/2,1/2,1/2;
    0,1,1/2,1/2,1/2; 1/2,1/2,1,1/2,1/2;
    1/2,1/2,1/2,1,1/2; 1/2,1/2,1/2,1/2,1]
  have h : G = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, A, points, quaternionModel, inner_eq_components, unitI, unitJ,
        Unitary.coe_neg, OneMemClass.coe_one, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
        Matrix.cons_val_succ, Matrix.cons_val_zero]
  rw [h]
  norm_num [A, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique,
    Matrix.submatrix_apply, Fin.succAbove]

/-- Readings multiply across all factors, including the empty product. -/
noncomputable def productReading (n : ℕ) (x y : Fin n → unitary ℍ[ℝ]) : ℝ :=
  ∏ i, quaternionModel.kappa (x i) (y i)

/-- The full Cartesian product of n quaternion readings has least real feature dimension 5^n. -/
theorem least_feature_rank (n : ℕ) : IsLeast
    {r : ℕ | ∃ φ : (Fin n → unitary ℍ[ℝ]) → EuclideanSpace ℝ (Fin r),
      ∀ x y, productReading n x y = ⟪φ x, φ y⟫_ℝ} (5^n) := by
  classical
  let e : (Fin n → Fin 5) ≃ Fin (5^n) := (Fintype.equivFin _).trans
    (finCongr (by simp))
  constructor
  · obtain ⟨ψ, hψ⟩ := quaternionModel_hasFeatureRank_five
    refine ⟨fun x => WithLp.toLp 2 fun j => ∏ i, (ψ (x i)).ofLp (e.symm j i), ?_⟩
    intro x y
    simp only [productReading, hψ,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    rw [Fintype.prod_sum, ← e.sum_comp]
    apply Finset.sum_congr rfl
    intro z _
    simp [Finset.prod_mul_distrib]
  · intro r hr
    obtain ⟨φ,hφ⟩ := hr
    let samples (z : Fin n → Fin 5) := fun i => points (z i)
    have hG : matrixPower n G = Matrix.gram ℝ (φ ∘ samples) := by
      ext i j
      simpa [productReading, matrixPower, G, samples, Matrix.gram_apply] using hφ (samples i) (samples j)
    have unitG : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 (isUnit_iff_ne_zero.2 (by rw [five_gram]; norm_num))
    have hunit := matrixPower_isUnit n unitG
    rw [hG, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
    have hind := Matrix.det_gram_ne_zero_iff_linearIndependent.mp hunit
    have hbound := hind.fintype_card_le_finrank
    simpa only [Fintype.card_fun, Fintype.card_fin, finrank_euclideanSpace] using hbound

end D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank
