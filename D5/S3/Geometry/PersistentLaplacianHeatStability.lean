/- GID: D5/S3/Geometry/PersistentLaplacianHeatStability
   generality: G
   mirror-B: D5/B/S3/Geometry/PersistentLaplacianHeatStability
   mirror-E: none(waiver:finite-hodge-operators)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none -/

import Mathlib.Algebra.Category.ModuleCat.Products
import D5.S3.Geometry.FiniteSimplicialSingularHomology
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
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

/-- Real incidence entries obtained from the integer ordered simplicial boundary. -/
def edgeIncidence (L : PreAbstractSimplicialComplex V) :
    Matrix (Face L 0) (Face L 1) ℝ :=
  fun v e => (coordinates L 0 ((faceι L e ≫ orderedBoundary L 0).hom (1 : ℤ)) v : ℝ)

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

section RelativeHeat

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "End" => H →L[ℝ] H
local notation "exp" => NormedSpace.exp

omit [CompleteSpace H] in
/-- The mixed form bound in squared form. The quadratic is the sum of the two positive
forms obtained from the Löwner inequalities, evaluated on differently scaled pairs. -/
private theorem mixedForm_sq {A B : End} {M : ℝ} (hM : 1 ≤ M)
    (hlo : M⁻¹ • A ≤ B) (hhi : B ≤ M • A) (x y : H) :
    M * ⟪(B - A) x, y⟫_ℝ ^ 2 ≤
      (M - 1) ^ 2 * (⟪A x, x⟫_ℝ * ⟪B y, y⟫_ℝ) := by
  have hMp : 0 < M := by linarith
  let P : End := M • B - A
  let R : End := M • A - B
  have hP : P.IsPositive := by
    have hp := (ContinuousLinearMap.le_def.mp hlo).smul_of_nonneg hMp.le
    simpa only [smul_sub, smul_smul, mul_inv_cancel₀ hMp.ne', one_smul] using hp
  have hR : R.IsPositive := ContinuousLinearMap.le_def.mp hhi
  let a := ⟪A x, x⟫_ℝ
  let b := ⟪(B - A) x, y⟫_ℝ
  let c := ⟪B y, y⟫_ℝ
  have hp (r : ℝ) : 0 ≤ (M ^ 2 - 1) * a * (r * r) +
      (2 * M * (M + 1) * b) * r + M * (M ^ 2 - 1) * c := by
    have h := add_nonneg (hP.inner_nonneg_left (M • y + r • x))
      (mul_nonneg hMp.le (hR.inner_nonneg_left (y - r • x)))
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, real_inner_smul_left, real_inner_smul_right, hP.inner_left_eq_inner_right y x,
      hR.inner_left_eq_inner_right y x, real_inner_comm (P x) y,
      real_inner_comm (R x) y] at h
    dsimp only [P, R] at h
    simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] at h
    dsimp only [a, b, c]
    simp only [sub_apply, inner_sub_left]
    convert h using 1
    ring
  have hd := discrim_le_zero hp
  rw [show discrim ((M ^ 2 - 1) * a) (2 * M * (M + 1) * b)
      (M * (M ^ 2 - 1) * c) =
      (4 * M * (M + 1) ^ 2) * (M * b ^ 2 - (M - 1) ^ 2 * (a * c)) by
        unfold discrim
        ring] at hd
  have hfac : 0 < 4 * M * (M + 1) ^ 2 := by positivity
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hd hfac)

private def heat (A : End) (s : ℝ) : End := exp (s • (-A))

omit [CompleteSpace H] in
private theorem heat_zero (A : End) : heat A 0 = 1 := by simp [heat]

private theorem heat_selfAdjoint {A : End} (hA : IsSelfAdjoint A) (s : ℝ) :
    IsSelfAdjoint (heat A s) := by
  rw [IsSelfAdjoint, heat, NormedSpace.star_exp]
  simp [hA.star_eq]

private theorem heat_deriv (A : End) (s : ℝ) :
    HasDerivAt (heat A) (-(A * heat A s)) s := by
  change HasDerivAt (fun r : ℝ => exp (r • (-A))) (-(A * exp (s • (-A)))) s
  simpa only [neg_mul] using hasDerivAt_exp_smul_const' (-A) s

private theorem heat_reverse_deriv (A : End) (s : ℝ) :
    HasDerivAt (fun r : ℝ => heat A (1 - r)) (heat A (1 - s) * A) s := by
  have hs : HasDerivAt (fun r : ℝ => 1 - r) (-1) s :=
    (hasDerivAt_id' s).const_sub 1
  have h := (hasDerivAt_exp_smul_const (-A) (1 - s)).scomp s hs
  simpa only [Function.comp_def, heat, mul_neg, neg_one_smul, neg_neg] using h

private theorem heat_apply_deriv (A : End) (x : H) (s : ℝ) :
    HasDerivAt (fun r => heat A r x) (-(A (heat A s x))) s := by
  simpa [mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using
    (heat_deriv A s).clm_apply (hasDerivAt_const s x)

private theorem heat_apply_continuous (A : End) (x : H) : Continuous (fun s => heat A s x) :=
  continuous_iff_continuousAt.2 fun s => (heat_apply_deriv A x s).continuousAt

private def heatEnergy (A : End) (x : H) (s : ℝ) : ℝ :=
  ⟪A (heat A s x), heat A s x⟫_ℝ

private theorem continuous_heatEnergy (A : End) (x : H) : Continuous (heatEnergy A x) :=
  (A.continuous.comp (heat_apply_continuous A x)).inner (heat_apply_continuous A x)

private theorem heatEnergy_integral (A : End) (x : H) :
    (∫ s in (0 : ℝ)..1, heatEnergy A x s) = (‖x‖ ^ 2 - ‖heat A 1 x‖ ^ 2) / 2 := by
  have hderiv (s : ℝ) : HasDerivAt (fun r => -‖heat A r x‖ ^ 2 / 2) (heatEnergy A x s) s := by
    convert ((heat_apply_deriv A x s).norm_sq.neg.div_const 2) using 1
    simp only [heatEnergy, inner_neg_right]
    rw [real_inner_comm (A (heat A s x)) (heat A s x)]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      ((continuous_heatEnergy A x).intervalIntegrable 0 1), heat_zero, one_apply_eq_self]
  ring

private theorem heat_pair_integral {A B : End} (hB : IsSelfAdjoint B) (x y : H) :
    (∫ s in (0 : ℝ)..1, ⟪(B - A) (heat A s x), heat B (1 - s) y⟫_ℝ) =
      ⟪(heat A 1 - heat B 1) x, y⟫_ℝ := by
  have hderiv (s : ℝ) : HasDerivAt
      (fun r => ⟪heat B (1 - r) (heat A r x), y⟫_ℝ)
      ⟪(B - A) (heat A s x), heat B (1 - s) y⟫_ℝ s := by
    have h := ((heat_reverse_deriv B s).clm_apply (heat_apply_deriv A x s)).inner ℝ
      (hasDerivAt_const s y)
    have hadj : (heat B (1 - s))† = heat B (1 - s) := (heat_selfAdjoint hB _).star_eq
    convert h using 1
    simp only [mul_apply_eq_comp, map_neg, inner_zero_right, zero_add, ← map_sub,
      sub_apply, ← sub_eq_add_neg]
    rw [← adjoint_inner_right, hadj]
  have hc : Continuous (fun s : ℝ => ⟪(B - A) (heat A s x), heat B (1 - s) y⟫_ℝ) :=
    ((B - A).continuous.comp (heat_apply_continuous A x)).inner
      ((heat_apply_continuous B y).comp (continuous_const.sub continuous_id))
  simpa [heat_zero, one_apply_eq_self, sub_apply, inner_sub_left] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hc.intervalIntegrable 0 1))

open MeasureTheory Set

private theorem interval_cauchy {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf₀ : ∀ s, 0 ≤ f s) (hg₀ : ∀ s, 0 ≤ g s) :
    (∫ s in (0 : ℝ)..1, f s * g s) ≤
      Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..1, g s ^ 2) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have mem (k : ℝ → ℝ) (hk : Continuous k) : MemLp k (ENNReal.ofReal 2) μ := by
    obtain ⟨c, hc⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (0 : ℝ) 1) hk.continuousOn
    apply MemLp.of_bound hk.aestronglyMeasurable c
    exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hc s (Ioc_subset_Icc_self hs)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf₀) (Filter.Eventually.of_forall hg₀) (mem f hf) (mem g hg)
  simpa only [μ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Real.rpow_two, ← Real.sqrt_eq_rpow] using h

private theorem heat_expectation_nonneg {A : End} (hA : IsSelfAdjoint A) (x : H) :
    0 ≤ ⟪heat A 1 x, x⟫_ℝ := by
  let T := heat A (1 / 2)
  have hT : T† = T := (heat_selfAdjoint hA _).star_eq
  have hTT : heat A 1 = T ∘L T := by
    change exp ((1 : ℝ) • (-A)) = exp ((1 / 2 : ℝ) • (-A)) * exp ((1 / 2 : ℝ) • (-A))
    have hmem : (1 / 2 : ℝ) • (-A) ∈ Metric.eball 0
        (NormedSpace.expSeries ℝ End).radius := by
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.refl _) hmem hmem, ← add_smul]
    norm_num
  rw [hTT]
  simpa only [hT] using (isPositive_self_comp_adjoint T).inner_nonneg_left x

private theorem heat_gap_sq {A B : End} {M : ℝ} (hM : 1 ≤ M)
    (hA : A.IsPositive) (hB : B.IsPositive) (hlo : M⁻¹ • A ≤ B) (hhi : B ≤ M • A)
    (x y : H) :
    4 * M * ⟪(heat A 1 - heat B 1) x, y⟫_ℝ ^ 2 ≤ (M - 1) ^ 2 *
      ((‖x‖ ^ 2 - ‖heat A 1 x‖ ^ 2) * (‖y‖ ^ 2 - ‖heat B 1 y‖ ^ 2)) := by
  have hMp : 0 < M := by linarith
  let f (s : ℝ) := Real.sqrt (heatEnergy A x s)
  let g (s : ℝ) := Real.sqrt (heatEnergy B y (1 - s))
  have hf : Continuous f := (continuous_heatEnergy A x).sqrt
  have hg : Continuous g :=
    (continuous_heatEnergy B y |>.comp (continuous_const.sub continuous_id)).sqrt
  have hf₂ (s : ℝ) : f s ^ 2 = heatEnergy A x s :=
    Real.sq_sqrt (hA.inner_nonneg_left _)
  have hg₂ (s : ℝ) : g s ^ 2 = heatEnergy B y (1 - s) :=
    Real.sq_sqrt (hB.inner_nonneg_left _)
  let k (s : ℝ) := ⟪(B - A) (heat A s x), heat B (1 - s) y⟫_ℝ
  have hk : Continuous k := ((B - A).continuous.comp (heat_apply_continuous A x)).inner
    ((heat_apply_continuous B y).comp (continuous_const.sub continuous_id))
  let c := (M - 1) / Real.sqrt M
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.2 hM) (Real.sqrt_nonneg _)
  have hpoint (s : ℝ) : |k s| ≤ c * (f s * g s) := by
    have h := mixedForm_sq hM hlo hhi (heat A s x) (heat B (1 - s) y)
    change M * (k s) ^ 2 ≤ _ at h
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hc
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).1
    rw [sq_abs, mul_pow, mul_pow, hf₂, hg₂]
    have hc₂ : c ^ 2 = (M - 1) ^ 2 / M := by
      dsimp [c]
      rw [div_pow, Real.sq_sqrt hMp.le]
    rw [hc₂, div_mul_eq_mul_div, le_div_iff₀ hMp]
    exact mul_comm (k s ^ 2) M ▸ h
  have hle : |⟪(heat A 1 - heat B 1) x, y⟫_ℝ| ≤
      c * (Real.sqrt (∫ s in (0 : ℝ)..1, heatEnergy A x s) *
        Real.sqrt (∫ s in (0 : ℝ)..1, heatEnergy B y s)) := by
    rw [← heat_pair_integral hB.isSelfAdjoint]
    calc
      |∫ s in (0 : ℝ)..1, k s| ≤ ∫ s in (0 : ℝ)..1, |k s| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ s in (0 : ℝ)..1, c * (f s * g s) :=
        intervalIntegral.integral_mono_on (by norm_num) (hk.abs.intervalIntegrable 0 1)
          ((continuous_const.mul (hf.mul hg)).intervalIntegrable 0 1) (fun s _ => hpoint s)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        apply mul_le_mul_of_nonneg_left _ hc
        have h := interval_cauchy hf hg (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
        simp_rw [hf₂, hg₂] at h
        rw [intervalIntegral.integral_comp_sub_left (heatEnergy B y) 1] at h
        simpa using h
  have hnonneg (C : End) (hC : C.IsPositive) (z : H) :
      0 ≤ ∫ s in (0 : ℝ)..1, heatEnergy C z s :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => hC.inner_nonneg_left _
  have hs := pow_le_pow_left₀ (abs_nonneg _) hle 2
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (hnonneg A hA x), Real.sq_sqrt (hnonneg B hB y),
    heatEnergy_integral, heatEnergy_integral] at hs
  dsimp [c] at hs
  rw [div_pow, Real.sq_sqrt hMp.le, div_mul_eq_mul_div, le_div_iff₀ hMp] at hs
  linarith only [mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)]

private theorem unit_heat_gap {A B : End} {M : ℝ} (hM : 1 ≤ M)
    (hA : A.IsPositive) (hB : B.IsPositive) (hlo : M⁻¹ • A ≤ B) (hhi : B ≤ M • A)
    {x : H} (hx : ‖x‖ = 1) :
    |⟪(heat A 1 - heat B 1) x, x⟫_ℝ| ≤ (M - 1) / (M + 1) := by
  let d := |⟪(heat A 1 - heat B 1) x, x⟫_ℝ|
  let a := ‖heat A 1 x‖
  let b := ‖heat B 1 x‖
  have energy_le (C : End) (hC : C.IsPositive) : ‖heat C 1 x‖ ^ 2 ≤ 1 := by
    have h : 0 ≤ ∫ s in (0 : ℝ)..1, heatEnergy C x s :=
      intervalIntegral.integral_nonneg (by norm_num) fun _ _ => hC.inner_nonneg_left _
    rw [heatEnergy_integral, hx, one_pow] at h
    linarith
  have ha : a ^ 2 ≤ 1 := energy_le A hA
  have hb : b ^ 2 ≤ 1 := energy_le B hB
  have hr : d ≤ max a b := by
    have hope (C : End) : ⟪heat C 1 x, x⟫_ℝ ≤ ‖heat C 1 x‖ := by
      simpa [hx] using real_inner_le_norm (heat C 1 x) x
    have ha₀ := heat_expectation_nonneg hA.isSelfAdjoint x
    have hb₀ := heat_expectation_nonneg hB.isSelfAdjoint x
    dsimp only [d]
    rw [sub_apply, inner_sub_left, abs_le]
    constructor
    · linarith [hope B, le_max_right a b]
    · linarith [hope A, le_max_left a b]
  have hd : 0 ≤ d := abs_nonneg _
  have hab : (1 - a ^ 2) * (1 - b ^ 2) ≤ 1 - d ^ 2 := by
    rcases le_total a b with h | h
    · rw [max_eq_right h] at hr
      calc
        _ ≤ 1 - b ^ 2 := by
          nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hb)]
        _ ≤ _ := by linarith [pow_le_pow_left₀ hd hr 2]
    · rw [max_eq_left h] at hr
      calc
        _ ≤ 1 - a ^ 2 := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg b)]
        _ ≤ _ := by linarith [pow_le_pow_left₀ hd hr 2]
  have h := heat_gap_sq hM hA hB hlo hhi x x
  rw [hx, one_pow] at h
  have h' : 4 * M * d ^ 2 ≤ (M - 1) ^ 2 * (1 - d ^ 2) := by
    have hleft : 4 * M * d ^ 2 ≤ (M - 1) ^ 2 * ((1 - a ^ 2) * (1 - b ^ 2)) := by
      simpa only [d, sq_abs, a, b] using h
    exact hleft.trans (mul_le_mul_of_nonneg_left hab (sq_nonneg _))
  have hMp : 0 < M + 1 := by linarith
  change d ≤ _
  apply (le_div_iff₀ hMp).2
  apply (sq_le_sq₀ (mul_nonneg hd hMp.le) (sub_nonneg.2 hM)).1
  nlinarith only [h']

private theorem relative_heat {A B : End} {M : ℝ} (hM : 1 ≤ M)
    (hA : A.IsPositive) (hB : B.IsPositive) (hlo : M⁻¹ • A ≤ B) (hhi : B ≤ M • A) :
    ‖exp (-B) - exp (-A)‖ ≤ (M - 1) / (M + 1) := by
  let T := heat A 1 - heat B 1
  have hT : T.IsSymmetric :=
    isSelfAdjoint_iff_isSymmetric.mp ((heat_selfAdjoint hA.isSelfAdjoint _).sub
      (heat_selfAdjoint hB.isSelfAdjoint _))
  have nonneg : 0 ≤ (M - 1) / (M + 1) := by
    exact div_nonneg (sub_nonneg.2 hM) (by linarith)
  have hnorm : ‖T‖ ≤ (M - 1) / (M + 1) := by
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simpa [hx, ContinuousLinearMap.rayleighQuotient] using nonneg
    let z := ‖x‖⁻¹ • x
    have hz : ‖z‖ = 1 := by simp [z, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
    have hq : |T.rayleighQuotient x| = |⟪T z, z⟫_ℝ| := by
      congr 1
      simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
        RCLike.re_to_real, z, map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp [norm_ne_zero_iff.2 hx]
    rw [hq]
    exact unit_heat_gap hM hA hB hlo hhi hz
  simpa only [T, heat, one_smul, norm_sub_rev] using hnorm

end RelativeHeat

/-- Pairwise stability of the unaugmented degree-zero weighted persistent heat operator.
The retained vertex weights are fixed, and the two hidden vertex weight systems may differ. -/
theorem weighted_persistent_heat_stability {K L : PreAbstractSimplicialComplex V}
    (hKL : K ≤ L) (v : Face K 0 → ℝ) (_hv : ∀ i, 0 < v i)
    {hidden hidden' : HiddenVertex K L → ℝ}
    (hh : ∀ i, 0 < hidden i) (hh' : ∀ i, 0 < hidden' i)
    {w w' : Face L 1 → ℝ} (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    {M t u : ℝ} (hM : 1 ≤ M) (ht : 0 < t) (hu : 0 < u)
    (hlo : ∀ i, M⁻¹ * (t * w i) ≤ u * w' i) (hhi : ∀ i, u * w' i ≤ M * (t * w i)) :
    ‖NormedSpace.exp (-(u • persistentLaplacian hKL v hidden' w')) -
      NormedSpace.exp (-(t • persistentLaplacian hKL v hidden w))‖ ≤ (M - 1) / (M + 1) := by
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have hw₀ : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hw'₀ : ∀ i, 0 ≤ w' i := fun i => (hw' i).le
  apply relative_heat hM
    ((persistentLaplacian_positive hKL v hidden w).smul_of_nonneg ht.le)
    ((persistentLaplacian_positive hKL v hidden' w').smul_of_nonneg hu.le)
  · rw [smul_smul]
    exact persistentLaplacian_order hKL v hh hh' hw₀ hw'₀
      (mul_nonneg (inv_nonneg.mpr hM₀) ht.le) hu.le
      (fun i => by simpa only [mul_assoc] using hlo i)
  · rw [smul_smul]
    exact persistentLaplacian_order hKL v hh' hh hw'₀ hw₀ hu.le
      (mul_nonneg hM₀ ht.le) (fun i => by simpa only [mul_assoc] using hhi i)

end D5.S3.Geometry.PersistentLaplacianHeatStability
