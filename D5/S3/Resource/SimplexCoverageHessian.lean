/- GID: D5/S3/Resource/SimplexCoverageHessian
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoverageHessian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Connected nonnegative Hessian normalization implies transverse nonpositivity. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoverageHessian

open Matrix WithLp
open scoped BigOperators RealInnerProductSpace

theorem quadratic_nonpos_of_connected_normalization
    {Index : Type*} [Fintype Index] [Nonempty Index]
    (matrix : Matrix Index Index ℝ) (positiveVector : Index → ℝ)
    (symmetric : matrix.IsSymm)
    (nonnegative : ∀ row column, 0 ≤ matrix row column)
    (positive : ∀ index, 0 < positiveVector index)
    (fixed : matrix *ᵥ positiveVector = positiveVector)
    (connected : ∀ support : Finset Index, support.Nonempty → support ≠ Finset.univ →
      ∃ row ∈ support, ∃ column ∉ support, 0 < matrix row column)
    (quadratic : ∀ vector : Index → ℝ,
      vector ⬝ᵥ (matrix *ᵥ vector) ≤ vector ⬝ᵥ ((matrix * matrix) *ᵥ vector))
    (vector : Index → ℝ) (perpendicular : vector ⬝ᵥ positiveVector = 0) :
    vector ⬝ᵥ (matrix *ᵥ vector) ≤ 0 := by
  classical
  have eigenvalue_bound : ∀ (eigenvalue : ℝ) (eigenvector : Index → ℝ),
      eigenvector ≠ 0 → matrix *ᵥ eigenvector = eigenvalue • eigenvector →
      |eigenvalue| ≤ 1 := by
    intro eigenvalue eigenvector nonzero eigen
    obtain ⟨pivot, _, maximal⟩ := Finset.exists_max_image Finset.univ
      (fun index => |eigenvector index| / positiveVector index) Finset.univ_nonempty
    let ratio := |eigenvector pivot| / positiveVector pivot
    have bounds : ∀ index, |eigenvector index| ≤ ratio * positiveVector index := by
      intro index
      exact (div_le_iff₀ (positive index)).mp (maximal index (Finset.mem_univ index))
    have pivot_nonzero : eigenvector pivot ≠ 0 := by
      intro zero
      have all_zero : eigenvector = 0 := by
        funext index
        have bound : |eigenvector index| ≤ 0 := by
          simpa only [ratio, zero, abs_zero, zero_div, zero_mul] using bounds index
        exact abs_eq_zero.mp (le_antisymm bound (abs_nonneg _))
      exact nonzero all_zero
    have pivot_pos : 0 < |eigenvector pivot| := abs_pos.mpr pivot_nonzero
    have estimate : |eigenvalue| * |eigenvector pivot| ≤ |eigenvector pivot| := by
      calc
        |eigenvalue| * |eigenvector pivot| = |(matrix *ᵥ eigenvector) pivot| := by
          rw [eigen, Pi.smul_apply, smul_eq_mul, abs_mul]
        _ ≤ ∑ index, |matrix pivot index * eigenvector index| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ index, matrix pivot index * |eigenvector index| := by
          simp_rw [abs_mul, abs_of_nonneg (nonnegative pivot _)]
        _ ≤ ∑ index, matrix pivot index * (ratio * positiveVector index) := by
          exact Finset.sum_le_sum fun index _ =>
            mul_le_mul_of_nonneg_left (bounds index) (nonnegative pivot index)
        _ = ratio * (matrix *ᵥ positiveVector) pivot := by
          simp only [mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index _
          ring
        _ = |eigenvector pivot| := by
          rw [fixed]
          exact div_mul_cancel₀ _ (ne_of_gt (positive pivot))
    nlinarith
  have fixed_unique : ∀ eigenvector : Index → ℝ,
      matrix *ᵥ eigenvector = eigenvector →
      ∃ scalar : ℝ, eigenvector = scalar • positiveVector := by
    intro eigenvector eigen
    obtain ⟨pivot, _, maximal⟩ := Finset.exists_max_image Finset.univ
      (fun index => eigenvector index / positiveVector index) Finset.univ_nonempty
    let scalar := eigenvector pivot / positiveVector pivot
    have bounds : ∀ index, eigenvector index ≤ scalar * positiveVector index := by
      intro index
      exact (div_le_iff₀ (positive index)).mp (maximal index (Finset.mem_univ index))
    let support := Finset.univ.filter
      (fun index => eigenvector index / positiveVector index = scalar)
    have member_iff : ∀ index,
        index ∈ support ↔ eigenvector index = scalar * positiveVector index := by
      intro index
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact div_eq_iff (ne_of_gt (positive index))
    have support_nonempty : support.Nonempty := by
      refine ⟨pivot, (member_iff pivot).mpr ?_⟩
      exact (div_mul_cancel₀ _ (ne_of_gt (positive pivot))).symm
    have full : support = Finset.univ := by
      by_contra proper
      obtain ⟨row, row_mem, column, column_not_mem, edge⟩ :=
        connected support support_nonempty proper
      have row_eq := (member_iff row).mp row_mem
      have sum_zero : ∑ index, matrix row index *
          (scalar * positiveVector index - eigenvector index) = 0 := by
        calc
          _ = scalar * (matrix *ᵥ positiveVector) row - (matrix *ᵥ eigenvector) row := by
            simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro index _
            ring
          _ = 0 := by rw [fixed, eigen, row_eq]; ring
      have term_zero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun index (_ : index ∈ Finset.univ) =>
          mul_nonneg (nonnegative row index) (sub_nonneg.mpr (bounds index)))).mp sum_zero
        column (Finset.mem_univ column)
      have column_eq : eigenvector column = scalar * positiveVector column := by
        have difference := (mul_eq_zero.mp term_zero).resolve_left (ne_of_gt edge)
        linarith
      exact column_not_mem ((member_iff column).mpr column_eq)
    refine ⟨scalar, ?_⟩
    funext index
    exact (member_iff index).mp (full.symm ▸ Finset.mem_univ index)
  have hermitian : matrix.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr symmetric
  let basis := hermitian.eigenvectorBasis
  let euclideanVector : EuclideanSpace ℝ Index := toLp 2 vector
  have eigen : ∀ index, matrix *ᵥ (ofLp (basis index)) =
      hermitian.eigenvalues index • ofLp (basis index) :=
    hermitian.mulVec_eigenvectorBasis
  have positive_eigenvalue : ∀ index, 0 < hermitian.eigenvalues index →
      hermitian.eigenvalues index = 1 := by
    intro index eigenvalue_pos
    have nonzero : ofLp (basis index) ≠ 0 := by
      exact (ofLp_eq_zero 2).ne.mpr (basis.orthonormal.ne_zero index)
    have norm_pos : 0 < ofLp (basis index) ⬝ᵥ ofLp (basis index) := by
      have norm_nonnegative : 0 ≤ ofLp (basis index) ⬝ᵥ ofLp (basis index) :=
        Finset.sum_nonneg fun coordinate _ => mul_self_nonneg _
      have norm_nonzero := (dotProduct_self_eq_zero (v := ofLp (basis index))).not.mpr nonzero
      exact lt_of_le_of_ne norm_nonnegative (Ne.symm norm_nonzero)
    have bound := eigenvalue_bound _ _ nonzero (eigen index)
    have quadratic_eigen := quadratic (ofLp (basis index))
    rw [← mulVec_mulVec, eigen index, mulVec_smul, eigen index,
      dotProduct_smul, dotProduct_smul, dotProduct_smul] at quadratic_eigen
    simp only [smul_eq_mul] at quadratic_eigen
    have lower : hermitian.eigenvalues index ≤ (hermitian.eigenvalues index) ^ 2 := by
      nlinarith
    have upper : hermitian.eigenvalues index ≤ 1 := le_trans (le_abs_self _) bound
    nlinarith
  have coefficient_zero : ∀ index, 0 < hermitian.eigenvalues index →
      ⟪basis index, euclideanVector⟫ = (0 : ℝ) := by
    intro index eigenvalue_pos
    have fixed_eigen : matrix *ᵥ ofLp (basis index) = ofLp (basis index) := by
      rw [eigen index, positive_eigenvalue index eigenvalue_pos, one_smul]
    obtain ⟨scalar, scalar_eq⟩ := fixed_unique _ fixed_eigen
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [euclideanVector, star_trivial, scalar_eq, dotProduct_smul,
      perpendicular, smul_zero]
  have inner_eigen : ∀ index,
      ⟪basis index, toLp 2 (matrix *ᵥ vector)⟫ =
        hermitian.eigenvalues index * ⟪basis index, euclideanVector⟫ := by
    intro index
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      euclideanVector]
    calc
      (matrix *ᵥ vector) ⬝ᵥ ofLp (basis index) =
          ofLp (basis index) ⬝ᵥ (matrixᵀ *ᵥ vector) := by
        rw [symmetric, dotProduct_comm]
      _ = vector ⬝ᵥ (matrix *ᵥ ofLp (basis index)) :=
        dotProduct_transpose_mulVec _ _ _
      _ = _ := by rw [eigen index, dotProduct_smul, smul_eq_mul]
  calc
    vector ⬝ᵥ (matrix *ᵥ vector) =
        ⟪euclideanVector, toLp 2 (matrix *ᵥ vector)⟫ := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, euclideanVector,
        star_trivial, dotProduct_comm]
    _ = ∑ index, ⟪euclideanVector, basis index⟫ *
        ⟪basis index, toLp 2 (matrix *ᵥ vector)⟫ :=
      (basis.sum_inner_mul_inner _ _).symm
    _ ≤ 0 := by
      apply Finset.sum_nonpos
      intro index _
      rw [inner_eigen, real_inner_comm (basis index) euclideanVector]
      by_cases eigenvalue_pos : 0 < hermitian.eigenvalues index
      · rw [coefficient_zero index eigenvalue_pos]; simp
      · have eigenvalue_nonpos := le_of_not_gt eigenvalue_pos
        nlinarith [sq_nonneg (⟪basis index, euclideanVector⟫ : ℝ)]

end D5.S3.Resource.SimplexCoverageHessian
