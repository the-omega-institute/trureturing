/- GID: D5/S3/Geometry/PersistentLaplacianHeatStability
   generality: G
   mirror-B: D5/B/S3/Geometry/PersistentLaplacianHeatStability
   mirror-E: none(waiver:finite-hodge-operators)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none -/

import Mathlib.Algebra.Category.ModuleCat.Products
import D5.S3.Geometry.FiniteSimplicialSingularHomology
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Degree-zero persistent heat operators from weighted simplicial boundary rows. -/

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped InnerProduct InnerProductSpace Matrix
open ContinuousLinearMap

namespace D5.S3.Geometry.PersistentLaplacianHeatStability

open FiniteSimplicialSingularHomology

variable {V : Type} [Fintype V] [LinearOrder V]

private def coordinates (L : PreAbstractSimplicialComplex V) (p : ℕ) :
    orderedGroup L p →ₗ[ℤ] (Face L p → ℤ) := by
  classical
  exact (DirectSum.linearEquivFunOnFintype ℤ (Face L p) (fun _ => ℤ)).toLinearMap.comp
    (ModuleCat.coprodIsoDirectSum (fun _ : Face L p => Z)).hom.hom

private theorem coordinates_faceι (L : PreAbstractSimplicialComplex V) {p : ℕ}
    (f : Face L p) (a : ℤ) :
    coordinates L p ((faceι L f).hom a) = Pi.single f a := by
  classical
  change (DirectSum.linearEquivFunOnFintype ℤ (Face L p) (fun _ => ℤ))
    ((faceι L f ≫ (ModuleCat.coprodIsoDirectSum (fun _ : Face L p => Z)).hom).hom a) = _
  rw [faceι, ModuleCat.ι_coprodIsoDirectSum_hom]
  exact DirectSum.linearEquivFunOnFintype_lof (R := ℤ) (M := fun _ : Face L p => ℤ) f a

/-- Real incidence entries obtained from the integer ordered simplicial boundary. -/
def edgeIncidence (L : PreAbstractSimplicialComplex V) :
    Matrix (Face L 0) (Face L 1) ℝ :=
  fun v e => (coordinates L 0 ((faceι L e ≫ orderedBoundary L 0).hom (1 : ℤ)) v : ℝ)

private theorem edgeIncidence_apply (L : PreAbstractSimplicialComplex V)
    (v : Face L 0) (e : Face L 1) :
    letI := Classical.decEq (Face L 0)
    edgeIncidence L v e = ∑ a : e.val, (-1 : ℝ) ^
      (e.val.filter (fun b => b < a.val)).card * (if eraseFace L e a = v then (1 : ℝ) else 0) := by
  classical
  have hcomp : faceι L e ≫ orderedBoundary L 0 =
      ∑ a : e.val, ((-1 : ℤ) ^ (e.val.filter (fun b => b < a.val)).card) •
        faceι L (eraseFace L e a) := by
    rw [faceι, orderedBoundary, Sigma.ι_comp_desc]
  simp only [edgeIncidence, hcomp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, map_sum, Finset.sum_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  change ((coordinates L 0 (((-1 : ℤ) ^ _ : ℤ) •
    (faceι L (eraseFace L e a)).hom (1 : ℤ)) v : ℤ) : ℝ) = _
  rw [map_zsmul, coordinates_faceι]
  change ((((-1 : ℤ) ^ _ : ℤ) •
    (Pi.single (M := fun _ : Face L 0 => ℤ) (eraseFace L e a) 1 v) : ℤ) : ℝ) = _
  rw [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
  norm_num only [Int.cast_neg, Int.cast_one]
  by_cases ha : v = eraseFace L e a
  · subst v
    simp
  · simp only [Pi.single_eq_of_ne ha, Int.cast_zero, ite_eq_right (Ne.symm ha), mul_zero]

/-- Hidden vertices are the zero-faces of the larger complex missing from the smaller one. -/
abbrev HiddenVertex (K L : PreAbstractSimplicialComplex V) :=
  {v : Face L 0 // v.val ∉ K}

instance (K L : PreAbstractSimplicialComplex V) : Fintype (HiddenVertex K L) := by
  classical
  unfold HiddenVertex
  infer_instance

private def retainedInclusion {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L)
    (v : Face K 0) : Face L 0 := ⟨v.val, hKL v.property.1, v.property.2⟩

local notation "Euc" => EuclideanSpace ℝ

private def asOperator {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    Euc n →L[ℝ] Euc m :=
  letI : DecidableEq n := Classical.decEq n
  (Matrix.toEuclideanLin A).toContinuousLinearMap

private def diagonalOperator {n : Type} [Fintype n] (d : n → ℝ) :
    Euc n →L[ℝ] Euc n := by
  classical
  exact asOperator (Matrix.diagonal d)

private theorem diagonalOperator_apply {n : Type} [Fintype n]
    (d : n → ℝ) (x : Euc n) (i : n) :
    diagonalOperator d x i = d i * x i := by
  classical
  change (Matrix.diagonal d *ᵥ WithLp.ofLp x) i = _
  rw [Matrix.mulVec_diagonal]

private theorem diagonalOperator_adjoint {n : Type} [Fintype n] (d : n → ℝ) :
    (diagonalOperator d)† = diagonalOperator d := by
  classical
  symm
  apply (eq_adjoint_iff _ _).2
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, diagonalOperator_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

private def edgeScale {n : Type} [Fintype n] (w : n → ℝ) : Euc n →L[ℝ] Euc n :=
  diagonalOperator fun i => Real.sqrt (w i)

private def rowScale {n : Type} [Fintype n] (v : n → ℝ) : Euc n →L[ℝ] Euc n :=
  diagonalOperator fun i => (Real.sqrt (v i))⁻¹

private def retainedIncidence {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    Euc (Face L 1) →L[ℝ] Euc (Face K 0) :=
  asOperator fun v e => edgeIncidence L (retainedInclusion hKL v) e

private def hiddenIncidence (K L : PreAbstractSimplicialComplex V) :
    Euc (Face L 1) →L[ℝ] Euc (HiddenVertex K L) :=
  asOperator fun v e => edgeIncidence L v.val e

private def retainedBoundary {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L)
    (v : Face K 0 → ℝ) (w : Face L 1 → ℝ) :
    Euc (Face L 1) →L[ℝ] Euc (Face K 0) :=
  rowScale v ∘L retainedIncidence hKL ∘L edgeScale w

private def hiddenBoundary (K L : PreAbstractSimplicialComplex V)
    (v : HiddenVertex K L → ℝ) (w : Face L 1 → ℝ) :
    Euc (Face L 1) →L[ℝ] Euc (HiddenVertex K L) :=
  rowScale v ∘L hiddenIncidence K L ∘L edgeScale w

/-- The unaugmented degree-zero weighted persistent Laplacian in orthonormal coordinates.
The weighted edge boundary is restricted to the kernel of its hidden rows. -/
def persistentLaplacian {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L)
    (v : Face K 0 → ℝ) (hidden : HiddenVertex K L → ℝ) (w : Face L 1 → ℝ) :
    Euc (Face K 0) →L[ℝ] Euc (Face K 0) :=
  let B := retainedBoundary hKL v w
  let C := hiddenBoundary K L hidden w
  let T := B ∘L C.ker.subtypeL
  T ∘L T†

private theorem persistentLaplacian_projection {K L : PreAbstractSimplicialComplex V}
    (hKL : K ≤ L) (v : Face K 0 → ℝ) (hidden : HiddenVertex K L → ℝ) (w : Face L 1 → ℝ) :
    persistentLaplacian hKL v hidden w =
      retainedBoundary hKL v w ∘L (hiddenBoundary K L hidden w).ker.starProjection ∘L
        (retainedBoundary hKL v w)† := by
  simp only [persistentLaplacian, adjoint_comp, Submodule.adjoint_subtypeL]
  rfl

private theorem persistentLaplacian_positive {K L : PreAbstractSimplicialComplex V}
    (hKL : K ≤ L) (v : Face K 0 → ℝ) (hidden : HiddenVertex K L → ℝ) (w : Face L 1 → ℝ) :
    (persistentLaplacian hKL v hidden w).IsPositive :=
  isPositive_self_comp_adjoint _

private theorem rowScale_surjective {n : Type} [Fintype n] {v : n → ℝ}
    (hv : ∀ i, 0 < v i) : Function.Surjective (rowScale v) := by
  intro y
  refine ⟨diagonalOperator (fun i => Real.sqrt (v i)) y, ?_⟩
  ext i
  simp only [rowScale, diagonalOperator_apply]
  rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 (hv i)).ne', one_mul]

private def trial {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L)
    (v : Face K 0 → ℝ) (x : Euc (Face K 0)) (y : Euc (HiddenVertex K L)) :
    Euc (Face L 1) :=
  ((retainedIncidence hKL)†) (rowScale v x) - ((hiddenIncidence K L)†) y

private theorem boundary_residual {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L)
    (v : Face K 0 → ℝ) (hidden : HiddenVertex K L → ℝ) (w : Face L 1 → ℝ)
    (x : Euc (Face K 0)) (y : Euc (HiddenVertex K L)) :
    ((retainedBoundary hKL v w)†) x - ((hiddenBoundary K L hidden w)†) y =
      edgeScale w (trial hKL v x (rowScale hidden y)) := by
  simp only [retainedBoundary, hiddenBoundary, trial, adjoint_comp, ContinuousLinearMap.comp_apply,
    rowScale, edgeScale, diagonalOperator_adjoint, map_sub]

private theorem edgeEnergy {n : Type} [Fintype n] {w : n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (z : Euc n) : ‖edgeScale w z‖ ^ 2 = ∑ i, w i * (z i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [edgeScale, diagonalOperator_apply, mul_pow, Real.sq_sqrt (hw i)]

private theorem persistentLaplacian_minimum {K L : PreAbstractSimplicialComplex V}
    (hKL : K ≤ L) (v : Face K 0 → ℝ) {hidden : HiddenVertex K L → ℝ}
    (hh : ∀ i, 0 < hidden i) {w : Face L 1 → ℝ} (hw : ∀ i, 0 ≤ w i) (x : Euc (Face K 0)) :
    let q := ⟪persistentLaplacian hKL v hidden w x, x⟫_ℝ
    (∃ y, q = ∑ i, w i * (trial hKL v x y i) ^ 2) ∧
      ∀ y, q ≤ ∑ i, w i * (trial hKL v x y i) ^ 2 := by
  dsimp only
  let B := retainedBoundary hKL v w
  let C := hiddenBoundary K L hidden w
  let z := (B†) x
  let U := C.kerᗮ
  have hU : U = (C†).range := by
    change C.kerᗮ = (C†).range
    rw [C.orthogonal_ker, (C†).range.closed_of_finiteDimensional.submodule_topologicalClosure_eq]
  have hq : ⟪persistentLaplacian hKL v hidden w x, x⟫_ℝ =
      ‖z - U.starProjection z‖ ^ 2 := by
    rw [persistentLaplacian_projection]
    change ⟪B (C.ker.starProjection z), x⟫_ℝ = _
    rw [← adjoint_inner_right]
    change ⟪C.ker.starProjection z, z⟫_ℝ = _
    rw [show z - U.starProjection z = C.ker.starProjection z by
      simp [U, Submodule.starProjection_orthogonal']]
    simpa only [RCLike.re_to_real, Submodule.starProjection_apply, Submodule.norm_coe] using
      C.ker.re_inner_starProjection_eq_normSq z
  rw [hq]
  have hmem : U.starProjection z ∈ (C†).range :=
    hU ▸ Submodule.starProjection_apply_mem _ _
  obtain ⟨y, hy⟩ := hmem
  refine ⟨⟨rowScale hidden y, ?_⟩, ?_⟩
  · rw [← edgeEnergy hw, ← boundary_residual, ← hy]
    rfl
  · intro y'
    obtain ⟨y, rfl⟩ := rowScale_surjective hh y'
    rw [← edgeEnergy hw, ← boundary_residual (hidden := hidden)]
    change ‖z - U.starProjection z‖ ^ 2 ≤ ‖z - (C†) y‖ ^ 2
    have hy' : (C†) y ∈ U := hU.symm ▸ ⟨y, rfl⟩
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro _ ⟨a, rfl⟩; positivity⟩ (⟨(C†) y, hy'⟩ : U)

private theorem persistentLaplacian_order {K L : PreAbstractSimplicialComplex V}
    (hKL : K ≤ L) (v : Face K 0 → ℝ)
    {hidden hidden' : HiddenVertex K L → ℝ} (hh : ∀ i, 0 < hidden i) (hh' : ∀ i, 0 < hidden' i)
    {w w' : Face L 1 → ℝ} (hw : ∀ i, 0 ≤ w i) (hw' : ∀ i, 0 ≤ w' i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ i, a * w i ≤ b * w' i) :
    a • persistentLaplacian hKL v hidden w ≤ b • persistentLaplacian hKL v hidden' w' := by
  rw [ContinuousLinearMap.le_def, isPositive_iff']
  refine ⟨?_, fun x => ?_⟩
  · exact ((persistentLaplacian_positive hKL v hidden' w').smul_of_nonneg hb).isSelfAdjoint.sub
      ((persistentLaplacian_positive hKL v hidden w).smul_of_nonneg ha).isSelfAdjoint
  · simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left, sub_nonneg]
    obtain ⟨⟨y, hy⟩, _⟩ := persistentLaplacian_minimum hKL v hh' hw' x
    have htrial := (persistentLaplacian_minimum hKL v hh hw x).2 y
    rw [hy]
    calc
      _ ≤ a * ∑ i, w i * (trial hKL v x y i) ^ 2 := mul_le_mul_of_nonneg_left htrial ha
      _ ≤ _ := by
        simp only [Finset.mul_sum, ← mul_assoc]
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

end D5.S3.Geometry.PersistentLaplacianHeatStability
