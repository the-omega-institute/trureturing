/- GID: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic simplex curvature formula and positive T-transform chain. -/

/-

admission_basis: escape-witness
escape_witness: positive_sorted_chain
Direct frozen dependencies: none; all prerequisites are pinned Mathlib or this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15483
Per-declaration judgement form (definitions carry no new-content claim):
proof_shape: rankOneMetric: bind-only; consumer=PositiveSimplexGeometryAndMixing.rankOne_inverse; witness=none
proof_shape: rankOneInverse: bind-only; consumer=PositiveSimplexGeometryAndMixing.rankOne_inverse; witness=none
proof_shape: rankOne_inverse: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_inverse; witness=none
proof_shape: simplex: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_positive_chain; witness=none
proof_shape: chart: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: metric: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel; witness=none
proof_shape: christoffel: bind-only; consumer=PositiveSimplexGeometryAndMixing.ricci; witness=none
proof_shape: ricci: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature; witness=none
proof_shape: scalarCurvature: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: scalInfty: bind-only; consumer=LogScalarCurvatureMonotone.scalInfty_eq_formula; witness=none
proof_shape: desc: bind-only; consumer=LogScalarCurvatureMonotone.sorted_list_eq_desc; witness=none
proof_shape: prefixSum: bind-only; consumer=LogScalarCurvatureMonotone.vector_prefix_eq_list; witness=none
proof_shape: moreMixed: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_sorted_prefix; witness=none
proof_shape: remain: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: chartDomain: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: sumCLM: bind-only; consumer=PositiveSimplexGeometryAndMixing.sumCLM_apply; witness=none
proof_shape: sumCLM_apply: bind-only; consumer=PositiveSimplexGeometryAndMixing.log_chart_last_partial; witness=none
proof_shape: chart_castSucc: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: chart_last: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: hasFDerivAt_remain: bind-only; consumer=PositiveSimplexGeometryAndMixing.log_chart_last_partial; witness=none
proof_shape: log_chart_castSucc_partial: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_entry; witness=none
proof_shape: log_chart_last_partial: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_entry; witness=none
proof_shape: metric_entry: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_diagonal_rankOne; witness=none
proof_shape: metric_diagonal_rankOne: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_inverse; witness=none
proof_shape: chartS2: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: remain_pos: bind-only; consumer=PositiveSimplexGeometryAndMixing.chartS2_pos; witness=none
proof_shape: chartS2_pos: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: metric_inverse: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_inverse_entry; witness=none
proof_shape: chartDomain_open: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_metric_entry; witness=none
proof_shape: hasFDerivAt_metric_entry: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_partial; witness=none
proof_shape: metric_partial: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_partial_combination; witness=none
proof_shape: weight: bind-only; consumer=PositiveSimplexGeometryAndMixing.gamma; witness=none
proof_shape: shape: bind-only; consumer=PositiveSimplexGeometryAndMixing.gamma; witness=none
proof_shape: gamma: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_eq_gamma; witness=none
proof_shape: metric_inverse_entry: bind-only; consumer=PositiveSimplexGeometryAndMixing.metric_inverse_rowSum; witness=none
proof_shape: metric_inverse_rowSum: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_eq_gamma; witness=none
proof_shape: metric_partial_combination: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_eq_gamma; witness=none
proof_shape: sum_partial_contract: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_eq_gamma; witness=none
proof_shape: christoffel_eq_gamma: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_partial; witness=none
proof_shape: s2Deriv: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_chartS2; witness=none
proof_shape: hasFDerivAt_chartS2: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_weight; witness=none
proof_shape: s2Deriv_single: bind-only; consumer=PositiveSimplexGeometryAndMixing.gammaDeriv_single; witness=none
proof_shape: weightDeriv: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_weight; witness=none
proof_shape: hasFDerivAt_weight: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_gamma; witness=none
proof_shape: hasFDerivAt_remain_inverse: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_shape; witness=none
proof_shape: hasFDerivAt_coord_inverse: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_shape; witness=none
proof_shape: shapeDeriv: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_shape; witness=none
proof_shape: hasFDerivAt_shape: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_gamma; witness=none
proof_shape: gammaDeriv: bind-only; consumer=PositiveSimplexGeometryAndMixing.hasFDerivAt_gamma; witness=none
proof_shape: hasFDerivAt_gamma: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_partial; witness=none
proof_shape: gammaPartial: bind-only; consumer=PositiveSimplexGeometryAndMixing.gammaDeriv_single; witness=none
proof_shape: gammaDeriv_single: bind-only; consumer=PositiveSimplexGeometryAndMixing.christoffel_partial; witness=none
proof_shape: christoffel_partial: bind-only; consumer=PositiveSimplexGeometryAndMixing.ricci_eq_gauss; witness=none
proof_shape: shape_weight_sum: bind-only; consumer=PositiveSimplexGeometryAndMixing.gamma_product_sum; witness=none
proof_shape: gamma_product_sum: bind-only; consumer=PositiveSimplexGeometryAndMixing.coordinate_gauss; witness=none
proof_shape: weightPartial: bind-only; consumer=PositiveSimplexGeometryAndMixing.gamma_partial_difference; witness=none
proof_shape: gamma_partial_difference: bind-only; consumer=PositiveSimplexGeometryAndMixing.coordinate_gauss; witness=none
proof_shape: metricShapeProduct: bind-only; consumer=PositiveSimplexGeometryAndMixing.coordinate_gauss; witness=none
proof_shape: coordinate_gauss: bind-only; consumer=PositiveSimplexGeometryAndMixing.ricci_eq_gauss; witness=none
proof_shape: metricShapeProduct_eq_mul: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_eq_trace; witness=none
proof_shape: ricci_eq_gauss: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_eq_trace; witness=none
proof_shape: trace_diagonal_rankOne: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums; witness=none
proof_shape: trace_diagonal_mul_rankOne: bind-only; consumer=PositiveSimplexGeometryAndMixing.trace_diagonal_rankOne_square; witness=none
proof_shape: trace_rankOne_square: bind-only; consumer=PositiveSimplexGeometryAndMixing.trace_diagonal_rankOne_square; witness=none
proof_shape: trace_diagonal_rankOne_square: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums; witness=none
proof_shape: contraction_eq_trace: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_eq_trace; witness=none
proof_shape: metric_inverse_symm: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_eq_trace; witness=none
proof_shape: scalarCurvature_eq_trace: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums; witness=none
proof_shape: metricShapeProduct_rankOne: bind-only; consumer=PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums; witness=none
proof_shape: scalarCurvature_powerSums: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: PositiveT: bind-only; consumer=LogScalarCurvatureMonotone.permutation_positive_chain; witness=none
proof_shape: ttransform_positive: bind-only; consumer=LogScalarCurvatureMonotone.permutation_positive_chain; witness=none
proof_shape: ttransform_sum: bind-only; consumer=LogScalarCurvatureMonotone.permutation_positive_chain; witness=none
proof_shape: eq_of_pointwise_le_sum_eq: bind-only; consumer=PositiveSimplexGeometryAndMixing.positive_sorted_chain; witness=none
proof_shape: positive_sorted_chain: content; consumer=LogScalarCurvatureMonotone.moreMixed_positive_chain; witness=positive_sorted_chain
proof_shape: positiveT_simplex: bind-only; consumer=LogScalarCurvatureMonotone.formula_oneT; witness=none
-/

import D5.S3.Geometry.AlphaGeometry.MajorizationTransfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.InformationTheory.Hamming


noncomputable section
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector
private def rankOneMetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (c : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (d i)⁻¹) + Matrix.of (fun _ _ => c)
private def rankOneInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (c : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal d - Matrix.of (fun i j => c * d i * d j / (1 + c * ∑ k, d k))
private lemma rankOne_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (c : ℝ) (hd : ∀ i, d i ≠ 0) (hc : c ≠ 0)
    (hden : 1 + c * ∑ k, d k ≠ 0) :
    (rankOneMetric d c)⁻¹ = rankOneInverse d c := by
  let A : Matrix ι ι ℝ := Matrix.diagonal (fun i => (d i)⁻¹)
  let U : Matrix ι (Fin 1) ℝ := Matrix.of fun _ _ => 1
  let C : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => c
  let V : Matrix (Fin 1) ι ℝ := Matrix.of fun _ _ => 1
  have hA : IsUnit A := by
    apply Matrix.isUnit_diagonal.mpr
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (hd i))
  have hC : IsUnit C := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa [C, Matrix.det_unique] using (isUnit_iff_ne_zero.mpr hc)
  have hAi : A⁻¹ = Matrix.diagonal d := by
    apply Matrix.inv_eq_right_inv
    ext i j
    by_cases hij : i = j
    · subst j; simp [A, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply, hd i]
    · simp [A, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hCi : C⁻¹ = Matrix.of (fun _ _ => c⁻¹) := by
    ext i j
    simp [C, Matrix.inv_subsingleton, Matrix.diagonal_apply,
      Subsingleton.elim i j, Ring.inverse_eq_inv]
  have hmid : C⁻¹ + V * A⁻¹ * U = Matrix.of (fun _ _ => c⁻¹ + ∑ i, d i) := by
    rw [hAi, hCi]
    ext i j
    simp [V, U, Matrix.mul_apply, Matrix.diagonal_apply]
  have hmidne : c⁻¹ + ∑ i, d i ≠ 0 := by
    intro h
    apply hden
    field_simp [hc] at h
    linear_combination h
  have hmidunit : IsUnit (C⁻¹ + V * A⁻¹ * U) := by
    rw [hmid]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa [Matrix.det_unique] using isUnit_iff_ne_zero.mpr hmidne
  have hmidi : (C⁻¹ + V * A⁻¹ * U)⁻¹ = Matrix.of (fun _ _ => (c⁻¹ + ∑ i, d i)⁻¹) := by
    rw [hmid]
    ext i j
    simp [Matrix.inv_subsingleton, Matrix.diagonal_apply,
      Subsingleton.elim i j, Ring.inverse_eq_inv]
  have hupdate : A + U * C * V = rankOneMetric d c := by
    ext i j
    simp [A, U, C, V, rankOneMetric, Matrix.mul_apply]
  rw [← hupdate, Matrix.add_mul_mul_inv_eq_sub A U C V hA hC hmidunit, hmidi, hAi]
  ext i j
  simp [rankOneInverse, U, V, Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp [hc, hmidne, hden]
  <;> ring
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ (∑ i, x i = 1)}
def chart {n : ℕ} (t : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun k => if h : k.val < n - 1 then t ⟨k.val, h⟩ else 1 - ∑ i, t i
def metric {n : ℕ} (t : Fin (n - 1) → ℝ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  fun i j => ∑ k,
    (fderiv ℝ (fun s => Real.log (chart s k)) t (Pi.single i 1)) *
      (fderiv ℝ (fun s => Real.log (chart s k)) t (Pi.single j 1))
def christoffel {n : ℕ} (t : Fin (n - 1) → ℝ) (k i j : Fin (n - 1)) : ℝ :=
  (1 / 2 : ℝ) * ∑ l,
    (metric t)⁻¹ k l *
      (fderiv ℝ (fun s => metric s l j) t (Pi.single i 1) +
       fderiv ℝ (fun s => metric s l i) t (Pi.single j 1) -
       fderiv ℝ (fun s => metric s i j) t (Pi.single l 1))
def ricci {n : ℕ} (t : Fin (n - 1) → ℝ) (i j : Fin (n - 1)) : ℝ :=
  ∑ k,
    (fderiv ℝ (fun s => christoffel s k i j) t (Pi.single k 1) -
       fderiv ℝ (fun s => christoffel s k i k) t (Pi.single j 1) +
       (∑ l, (christoffel t k k l * christoffel t l i j -
         christoffel t k j l * christoffel t l i k)))
def scalarCurvature {n : ℕ} (t : Fin (n - 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, (metric t)⁻¹ i j * ricci t i j
def scalInfty {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  scalarCurvature (fun i => x (Fin.castLE (Nat.sub_le n 1) i))
def desc {n : ℕ} (x : Fin n → ℝ) : List ℝ :=
  (List.ofFn x).mergeSort (fun a b => decide (b ≤ a))
def prefixSum (xs : List ℝ) (k : ℕ) : ℝ := (xs.take k).sum
def moreMixed {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  (∀ k < n, prefixSum (desc x) k ≤ prefixSum (desc y) k) ∧
    prefixSum (desc x) n = prefixSum (desc y) n
abbrev remain {m : ℕ} (t : Fin m → ℝ) : ℝ := 1 - ∑ i, t i
def chartDomain (m : ℕ) : Set (Fin m → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ (∑ i, t i < 1)}
private def sumCLM (m : ℕ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)
private lemma sumCLM_apply {m : ℕ} (v : Fin m → ℝ) : sumCLM m v = ∑ i, v i := by
  simp [sumCLM]
lemma chart_castSucc {m : ℕ} (t : Fin m → ℝ) (i : Fin m) :
    @chart (m + 1) t i.castSucc = t i := by
  simp [chart, i.isLt]
lemma chart_last {m : ℕ} (t : Fin m → ℝ) :
    @chart (m + 1) t (Fin.last m) = remain t := by
  simp [chart, remain]
private lemma hasFDerivAt_remain {m : ℕ} (t : Fin m → ℝ) :
    HasFDerivAt remain (-sumCLM m) t := by
  have hsum : HasFDerivAt (fun s : Fin m → ℝ => ∑ i, s i) (sumCLM m) t := by
    apply HasFDerivAt.fun_sum
    intro i hi
    exact hasFDerivAt_apply i t
  convert! (hasFDerivAt_const (1 : ℝ) t).sub hsum using 1
  <;> simp [remain]
private lemma log_chart_castSucc_partial {m : ℕ} (t : Fin m → ℝ)
    (ht : t ∈ chartDomain m) (i j : Fin m) :
    fderiv ℝ (fun s => Real.log (@chart (m + 1) s i.castSucc)) t (Pi.single j 1) =
      if i = j then (t i)⁻¹ else 0 := by
  simp_rw [chart_castSucc]
  have h : HasFDerivAt (fun s : Fin m → ℝ => Real.log (s i))
      ((t i)⁻¹ • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) t :=
    (hasFDerivAt_apply i t).log (ne_of_gt (ht.1 i))
  have hf : fderiv ℝ (fun s : Fin m → ℝ => Real.log (s i)) t =
      (t i)⁻¹ • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) := by
    convert! h.fderiv
  convert! congrArg (fun f : (Fin m → ℝ) →L[ℝ] ℝ => f (Pi.single j 1)) hf using 1
  simp [Pi.single_apply, eq_comm]
private lemma log_chart_last_partial {m : ℕ} (t : Fin m → ℝ)
    (ht : t ∈ chartDomain m) (j : Fin m) :
    fderiv ℝ (fun s => Real.log (@chart (m + 1) s (Fin.last m))) t (Pi.single j 1) =
      -(remain t)⁻¹ := by
  simp only [chart, Fin.val_last, Nat.add_sub_cancel, lt_self_iff_false, dif_neg]
  have hf : fderiv ℝ (fun s : Fin m → ℝ => Real.log (remain s)) t =
      (remain t)⁻¹ • (-sumCLM m) := by
    convert! ((hasFDerivAt_remain t).log (ne_of_gt (sub_pos.mpr ht.2))).fderiv
  convert! congrArg (fun f : (Fin m → ℝ) →L[ℝ] ℝ => f (Pi.single j 1)) hf using 1
  simp [sumCLM_apply, Pi.single_apply]
private lemma metric_entry {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (i j : Fin m) :
    @metric (m + 1) t i j = (if i = j then (t i ^ 2)⁻¹ else 0) +
      (remain t ^ 2)⁻¹ := by
  unfold metric
  rw [Fin.sum_univ_castSucc]
  simp_rw [log_chart_castSucc_partial t ht, log_chart_last_partial t ht]
  by_cases hij : i = j
  · subst j
    simp [Pi.single_apply, inv_pow, ← pow_two]
  · simp [hij, eq_comm, inv_pow, ← pow_two]
private lemma metric_diagonal_rankOne {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    @metric (m + 1) t = Matrix.diagonal (fun i => (t i ^ 2)⁻¹) +
      (Matrix.of (fun _ _ => (remain t ^ 2)⁻¹)) := by
  ext i j
  simpa [Matrix.diagonal_apply] using metric_entry t ht i j
def chartS2 {m : ℕ} (t : Fin m → ℝ) : ℝ := remain t ^ 2 + ∑ i, t i ^ 2
private lemma remain_pos {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) : 0 < remain t :=
  sub_pos.mpr ht.2
lemma chartS2_pos {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) : 0 < chartS2 t := by
  apply add_pos_of_pos_of_nonneg (sq_pos_of_pos (remain_pos t ht))
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
private lemma metric_inverse {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    (@metric (m + 1) t)⁻¹ = Matrix.diagonal (fun i => t i ^ 2) -
      Matrix.of (fun i j => t i ^ 2 * t j ^ 2 / chartS2 t) := by
  have hden : 1 + (remain t ^ 2)⁻¹ * (∑ i, t i ^ 2) ≠ 0 := by
    have hb := sq_pos_of_pos (remain_pos t ht)
    have hs : 0 ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hd : ∀ i, t i ^ 2 ≠ 0 := fun i => pow_ne_zero _ (ht.1 i).ne'
  rw [metric_diagonal_rankOne t ht]
  change (rankOneMetric (fun i => t i ^ 2) (remain t ^ 2)⁻¹)⁻¹ = _
  rw [rankOne_inverse _ _ hd (inv_ne_zero (pow_ne_zero _ (remain_pos t ht).ne')) hden]
  ext i j
  simp only [rankOneInverse, Matrix.sub_apply, Matrix.of_apply]
  congr 1
  have hbne : remain t ^ 2 ≠ 0 := pow_ne_zero _ (remain_pos t ht).ne'
  apply (div_eq_div_iff hden (chartS2_pos t ht).ne').mpr
  unfold chartS2
  have hbcan := inv_mul_cancel₀ hbne
  linear_combination (t i ^ 2 * t j ^ 2) * hbcan
private lemma chartDomain_open (m : ℕ) : IsOpen (chartDomain m) := by
  have h₁ : IsOpen {t : Fin m → ℝ | ∀ i, 0 < t i} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have h₂ : IsOpen {t : Fin m → ℝ | (∑ i, t i) < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h₁.inter h₂
private lemma hasFDerivAt_metric_entry {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (i j : Fin m) :
    HasFDerivAt (fun s : Fin m → ℝ => @metric (m + 1) s i j)
      ((if i = j then (-2 / t i ^ 3) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) else 0) +
        (2 / remain t ^ 3) • sumCLM m) t := by
  have hbase : HasFDerivAt (fun s : Fin m → ℝ => (s i ^ 2)⁻¹)
      ((-2 / t i ^ 3) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) t := by
    have hx : HasFDerivAt (fun s : Fin m → ℝ => s i) ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) t :=
      hasFDerivAt_apply i t
    convert! (hasDerivAt_inv (pow_ne_zero 2 (ht.1 i).ne')).comp_hasFDerivAt t (hx.pow 2) using 1
    ext v
    simp
    field_simp [(ht.1 i).ne', (remain_pos t ht).ne']
    <;> ring
  have hb : HasFDerivAt (fun s : Fin m → ℝ => (remain s ^ 2)⁻¹)
      ((2 / remain t ^ 3) • sumCLM m) t := by
    convert! (hasDerivAt_inv (pow_ne_zero 2 (remain_pos t ht).ne')).comp_hasFDerivAt t
      ((hasFDerivAt_remain t).pow 2) using 1
    ext v
    simp
    field_simp [(remain_pos t ht).ne']
    <;> ring
  have he : (fun s : Fin m → ℝ => @metric (m + 1) s i j) =ᶠ[𝓝 t]
      fun s => (if i = j then (s i ^ 2)⁻¹ else 0) + (remain s ^ 2)⁻¹ := by
    filter_upwards [(chartDomain_open m).mem_nhds ht] with s hs
    exact metric_entry s hs i j
  apply HasFDerivAt.congr_of_eventuallyEq _ he
  by_cases hij : i = j
  · convert! hbase.add hb using 1 <;> simp [hij] <;> rfl
  · convert! hb using 1 <;> simp [hij]
private lemma metric_partial {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (i j h : Fin m) :
    fderiv ℝ (fun s : Fin m → ℝ => @metric (m + 1) s i j) t (Pi.single h 1) =
      (if i = j ∧ i = h then -2 / t i ^ 3 else 0) + 2 / remain t ^ 3 := by
  have hf := (hasFDerivAt_metric_entry t ht i j).fderiv
  convert! congrArg (fun f : (Fin m → ℝ) →L[ℝ] ℝ => f (Pi.single h 1)) hf using 1
  simp [sumCLM_apply, Pi.single_apply]
  split_ifs <;> simp_all
private def weight {m : ℕ} (t : Fin m → ℝ) (k : Fin m) : ℝ := t k ^ 2 / chartS2 t
private def shape {m : ℕ} (t : Fin m → ℝ) (i j : Fin m) : ℝ :=
  (remain t)⁻¹ + if i = j then (t i)⁻¹ else 0
private def gamma {m : ℕ} (t : Fin m → ℝ) (k i j : Fin m) : ℝ :=
  weight t k * shape t i j - (if k = i ∧ i = j then (t i)⁻¹ else 0)
private lemma metric_inverse_entry {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (k i : Fin m) :
    (@metric (m+1) t)⁻¹ k i = (if k = i then t k ^ 2 else 0) -
      t k ^ 2 * t i ^ 2 / chartS2 t := by
  rw [metric_inverse t ht]
  simp [Matrix.diagonal_apply]
private lemma metric_inverse_rowSum {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (k : Fin m) :
    (∑ l, (@metric (m+1) t)⁻¹ k l) = t k ^ 2 * remain t ^ 2 / chartS2 t := by
  simp_rw [metric_inverse_entry t ht]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change t k ^ 2 - t k ^ 2 * (∑ i : Fin m, t i ^ 2) / chartS2 t = _
  apply (eq_div_iff (chartS2_pos t ht).ne').mpr
  change (t k ^ 2 - t k ^ 2 * (∑ i : Fin m, t i ^ 2) / chartS2 t) * chartS2 t = _
  rw [sub_mul,div_mul_cancel₀ _ (chartS2_pos t ht).ne']
  change t k ^ 2 * (remain t ^ 2 + ∑ i : Fin m, t i ^ 2) - t k ^ 2 * (∑ i : Fin m, t i ^ 2) = _
  ring
private lemma metric_partial_combination {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (l i j : Fin m) :
    fderiv ℝ (fun s : Fin m → ℝ => @metric (m+1) s l j) t (Pi.single i 1) +
      fderiv ℝ (fun s : Fin m → ℝ => @metric (m+1) s l i) t (Pi.single j 1) -
      fderiv ℝ (fun s : Fin m → ℝ => @metric (m+1) s i j) t (Pi.single l 1) =
    2 * ((remain t ^ 3)⁻¹ - (if i = j ∧ l = i then (t i ^ 3)⁻¹ else 0)) := by
  rw [metric_partial t ht,metric_partial t ht,metric_partial t ht]
  by_cases hli : l = i <;> by_cases hlj : l = j <;> by_cases hij : i = j
  <;> simp_all [div_eq_mul_inv,eq_comm] <;> ring
private lemma sum_partial_contract {m : ℕ} (F : Fin m → ℝ) (b a : ℝ) (i j : Fin m) :
    (∑ l, F l * (b⁻¹ - (if i = j ∧ l = i then a⁻¹ else 0))) =
      (∑ l, F l) / b - (if i = j then F i / a else 0) := by
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  by_cases hij : i = j
  · simp [hij,mul_ite,div_eq_mul_inv]
  · simp [hij,div_eq_mul_inv]
private lemma christoffel_eq_gamma {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m)
    (k i j : Fin m) : @christoffel (m+1) t k i j = gamma t k i j := by
  change (1 / 2 : ℝ) * (∑ l : Fin m, (@metric (m+1) t)⁻¹ k l *
    (fderiv ℝ (fun s : Fin m → ℝ => @metric (m+1) s l j) t (Pi.single i 1) +
     fderiv ℝ (fun s : Fin m → ℝ => @metric (m+1) s l i) t (Pi.single j 1) -
     fderiv ℝ (fun s : Fin m → ℝ => @metric (m+1) s i j) t (Pi.single l 1))) = _
  simp_rw [metric_partial_combination t ht]
  have hfactor : (1 / 2 : ℝ) * (∑ l, (@metric (m+1) t)⁻¹ k l *
      (2 * ((remain t ^ 3)⁻¹ - (if i = j ∧ l = i then (t i ^ 3)⁻¹ else 0)))) =
      ∑ l, (@metric (m+1) t)⁻¹ k l *
      ((remain t ^ 3)⁻¹ - (if i = j ∧ l = i then (t i ^ 3)⁻¹ else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  erw [hfactor]
  erw [sum_partial_contract (fun l : Fin m => (@metric (m+1) t)⁻¹ k l)
    (remain t ^ 3) (t i ^ 3) i j]
  erw [metric_inverse_rowSum t ht k,metric_inverse_entry t ht k i]
  unfold gamma weight shape
  have hbne := (remain_pos t ht).ne'
  have hsne := (chartS2_pos t ht).ne'
  generalize hbdef : remain t = b at *
  generalize hsdef : chartS2 t = S at *
  split_ifs <;> simp_all
  <;> field_simp [(ht.1 i).ne',(ht.1 j).ne',(ht.1 k).ne',hbne,hsne]
  <;> ring
private def s2Deriv {m : ℕ} (t : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  (2 * remain t) • (-sumCLM m) + ∑ i, (2 * t i) • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)
private lemma hasFDerivAt_chartS2 {m : ℕ} (t : Fin m → ℝ) :
    HasFDerivAt chartS2 (s2Deriv t) t := by
  have hsum : HasFDerivAt (fun s : Fin m → ℝ => ∑ i, s i ^ 2)
      (∑ i, (2 * t i) • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) t := by
    apply HasFDerivAt.fun_sum
    intro i hi
    have hx : HasFDerivAt (fun s : Fin m → ℝ => s i) ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) t := hasFDerivAt_apply i t
    convert! hx.pow 2 using 1 <;> simp
  convert! ((hasFDerivAt_remain t).pow 2).add hsum using 1
  <;> simp [chartS2,s2Deriv]
  <;> rfl
private lemma s2Deriv_single {m : ℕ} (t : Fin m → ℝ) (h : Fin m) :
    s2Deriv t (Pi.single h 1) = 2 * (t h - remain t) := by
  simp [s2Deriv,sumCLM_apply,Pi.single_apply]
  ring
private def weightDeriv {m : ℕ} (t : Fin m → ℝ) (k : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ :=
  (2 * t k / chartS2 t) • (ContinuousLinearMap.proj k : (Fin m → ℝ) →L[ℝ] ℝ) - (t k ^ 2 / chartS2 t ^ 2) • s2Deriv t
private lemma hasFDerivAt_weight {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (k : Fin m) :
    HasFDerivAt (fun s => weight s k) (weightDeriv t k) t := by
  have hpow : HasFDerivAt (fun s : Fin m → ℝ => s k ^ 2)
      ((2 * t k) • (ContinuousLinearMap.proj k : (Fin m → ℝ) →L[ℝ] ℝ)) t := by
    have hx : HasFDerivAt (fun s : Fin m → ℝ => s k) ((ContinuousLinearMap.proj k : (Fin m → ℝ) →L[ℝ] ℝ)) t := hasFDerivAt_apply k t
    convert! hx.pow 2 using 1 <;> simp
  have hinv := (hasDerivAt_inv (chartS2_pos t ht).ne').comp_hasFDerivAt t (hasFDerivAt_chartS2 t)
  convert! hpow.mul hinv using 1
  ext v
  simp [weightDeriv,div_eq_mul_inv]
  ring
private lemma hasFDerivAt_remain_inverse {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    HasFDerivAt (fun s : Fin m → ℝ => (remain s)⁻¹)
      ((remain t ^ 2)⁻¹ • sumCLM m) t := by
  convert! (hasDerivAt_inv (remain_pos t ht).ne').comp_hasFDerivAt t (hasFDerivAt_remain t) using 1
  ext v
  simp
private lemma hasFDerivAt_coord_inverse {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (i : Fin m) :
    HasFDerivAt (fun s : Fin m → ℝ => (s i)⁻¹) (-(t i ^ 2)⁻¹ • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) t := by
  have hx : HasFDerivAt (fun s : Fin m → ℝ => s i) ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) t := hasFDerivAt_apply i t
  convert! (hasDerivAt_inv (ht.1 i).ne').comp_hasFDerivAt t hx using 1
private def shapeDeriv {m : ℕ} (t : Fin m → ℝ) (i j : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ :=
  (remain t ^ 2)⁻¹ • sumCLM m +
    if i = j then -(t i ^ 2)⁻¹ • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) else 0
private lemma hasFDerivAt_shape {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (i j : Fin m) :
    HasFDerivAt (fun s => shape s i j) (shapeDeriv t i j) t := by
  by_cases hij : i = j
  · convert! (hasFDerivAt_remain_inverse t ht).add (hasFDerivAt_coord_inverse t ht i) using 1
    <;> simp [shape,shapeDeriv,hij]
    <;> rfl
  · convert! hasFDerivAt_remain_inverse t ht using 1
    <;> simp [shape,shapeDeriv,hij]
private def gammaDeriv {m : ℕ} (t : Fin m → ℝ) (k i j : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ :=
  shape t i j • weightDeriv t k + weight t k • shapeDeriv t i j -
    if k = i ∧ i = j then -(t i ^ 2)⁻¹ • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) else 0
private lemma hasFDerivAt_gamma {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (k i j : Fin m) :
    HasFDerivAt (fun s => gamma s k i j) (gammaDeriv t k i j) t := by
  have hr : HasFDerivAt (fun s : Fin m → ℝ => if k = i ∧ i = j then (s i)⁻¹ else 0)
      (if k = i ∧ i = j then -(t i ^ 2)⁻¹ • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) else 0) t := by
    by_cases hij : k = i ∧ i = j
    · simpa only [if_pos hij] using hasFDerivAt_coord_inverse t ht i
    · simpa only [if_neg hij] using hasFDerivAt_const (0 : ℝ) t
  convert! ((hasFDerivAt_weight t ht k).mul (hasFDerivAt_shape t ht i j)).sub hr using 1
  simp [gammaDeriv,add_comm]
private def gammaPartial {m : ℕ} (t : Fin m → ℝ) (k i j h : Fin m) : ℝ :=
  ((if k = h then 2 * t k / chartS2 t else 0) -
    2 * t k ^ 2 * (t h - remain t) / chartS2 t ^ 2) * shape t i j +
    weight t k * ((remain t ^ 2)⁻¹ - (if i = j ∧ i = h then (t i ^ 2)⁻¹ else 0)) +
    (if k = i ∧ i = j ∧ i = h then (t i ^ 2)⁻¹ else 0)
private lemma gammaDeriv_single {m : ℕ} (t : Fin m → ℝ) (k i j h : Fin m) :
    gammaDeriv t k i j (Pi.single h 1) = gammaPartial t k i j h := by
  simp [gammaDeriv,weightDeriv,shapeDeriv,s2Deriv_single,sumCLM_apply,
    Pi.single_apply,gammaPartial]
  by_cases hkh : k = h <;> by_cases hij : i = j
  <;> by_cases hih : i = h <;> by_cases hki : k = i
  <;> simp_all [Pi.single_apply,eq_comm] <;> ring
private lemma christoffel_partial {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (k i j h : Fin m) :
    fderiv ℝ (fun s : Fin m → ℝ => @christoffel (m+1) s k i j) t (Pi.single h 1) =
      gammaPartial t k i j h := by
  have he : (fun s : Fin m → ℝ => @christoffel (m+1) s k i j) =ᶠ[𝓝 t]
      fun s => gamma s k i j := by
    filter_upwards [(chartDomain_open m).mem_nhds ht] with s hs
    exact christoffel_eq_gamma s hs k i j
  have hda := (hasFDerivAt_gamma t ht k i j).congr_of_eventuallyEq he
  convert! congrArg (fun f : (Fin m → ℝ) →L[ℝ] ℝ => f (Pi.single h 1)) hda.fderiv using 1
  exact (gammaDeriv_single t k i j h).symm
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
private lemma shape_weight_sum {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (h : Fin m) :
    (∑ l, weight t l * shape t h l) =
      (∑ l, t l ^ 2) / (remain t * chartS2 t) + t h / chartS2 t := by
  unfold shape
  simp only [mul_add, mul_ite,mul_zero,Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold weight
  rw [← Finset.sum_div]
  have hbne := (remain_pos t ht).ne'
  have hsne := (chartS2_pos t ht).ne'
  have htne := (ht.1 h).ne'
  generalize hbdef : remain t = b at *
  generalize hsdef : chartS2 t = S at *
  field_simp [hbne,hsne,htne]
  <;> ring
private lemma gamma_product_sum {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (k h i j : Fin m) :
    (∑ l, gamma t k h l * gamma t l i j) =
      weight t k * shape t i j * ((∑ l, t l ^ 2) / (remain t * chartS2 t) + t h / chartS2 t) -
      (if i = j then weight t k * shape t h i / t i else 0) -
      (if k = h then weight t h * shape t i j / t h else 0) +
      (if k = h ∧ h = i ∧ i = j then (t h)⁻¹ * (t i)⁻¹ else 0) := by
  have h₁ : (∑ l, weight t k * shape t h l * (weight t l * shape t i j)) =
      weight t k * shape t i j * (∑ l, weight t l * shape t h l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have h₂ : (∑ l, weight t k * shape t h l * (if l = i ∧ i = j then (t i)⁻¹ else 0)) =
      if i = j then weight t k * shape t h i / t i else 0 := by
    by_cases hij : i = j
    · simp [hij,mul_ite,div_eq_mul_inv]
    · simp [hij]
  have h₃ : (∑ l, (if k = h ∧ h = l then (t h)⁻¹ else 0) * (weight t l * shape t i j)) =
      if k = h then weight t h * shape t i j / t h else 0 := by
    by_cases hkh : k = h
    · simp [hkh,ite_mul,div_eq_mul_inv,mul_comm]
    · simp [hkh]
  have h₄ : (∑ l, (if k = h ∧ h = l then (t h)⁻¹ else 0) *
      (if l = i ∧ i = j then (t i)⁻¹ else 0)) =
      if k = h ∧ h = i ∧ i = j then (t h)⁻¹ * (t i)⁻¹ else 0 := by
    by_cases hkh : k = h <;> by_cases hhi : h = i <;> by_cases hij : i = j
    <;> simp_all [ite_mul,mul_ite]
  simp only [gamma,mul_sub,sub_mul,Finset.sum_sub_distrib]
  rw [h₁,h₂,h₃,h₄,shape_weight_sum t ht h]
  ring
private def weightPartial {m : ℕ} (t : Fin m → ℝ) (k h : Fin m) : ℝ :=
  (if k = h then 2 * t k / chartS2 t else 0) -
    2 * t k ^ 2 * (t h - remain t) / chartS2 t ^ 2
private lemma gamma_partial_difference {m : ℕ} (t : Fin m → ℝ) (k i h j : Fin m) :
    gammaPartial t k i j h - gammaPartial t k i h j =
      weightPartial t k h * shape t i j - weightPartial t k j * shape t i h := by
  simp only [gammaPartial,weightPartial,and_comm,and_left_comm,and_assoc]
  ring
private def metricShapeProduct {m : ℕ} (t : Fin m → ℝ) (k h : Fin m) : ℝ :=
  (if k = h then t k else 0) + weight t k * (remain t - t h)
private lemma coordinate_gauss {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (k i h j : Fin m) :
    gammaPartial t k i j h - gammaPartial t k i h j +
      (∑ l, (gamma t k h l * gamma t l i j - gamma t k j l * gamma t l i h)) =
      (metricShapeProduct t k h * shape t i j -
        metricShapeProduct t k j * shape t i h) / chartS2 t := by
  rw [gamma_partial_difference,Finset.sum_sub_distrib,gamma_product_sum t ht,
    gamma_product_sum t ht]
  have hB : (∑ l, t l ^ 2) = chartS2 t - remain t ^ 2 := by unfold chartS2; ring
  rw [hB]
  unfold metricShapeProduct weightPartial weight shape
  have hbne := (remain_pos t ht).ne'
  have hsne := (chartS2_pos t ht).ne'
  generalize hbdef : remain t = b at *
  generalize hsdef : chartS2 t = S at *
  have htn : ∀ q, t q ≠ 0 := fun q => (ht.1 q).ne'
  clear hB hbdef hsdef ht
  by_cases hkh : k = h <;> by_cases hkj : k = j <;> by_cases hhi : h = i
  <;> by_cases hij : i = j <;> by_cases hih : i = h
  <;> subst_vars
  <;> split_ifs
  <;> (try (exfalso; aesop (config := { enableSimp := false, maxRuleApplications := 40, terminal := true })))
  <;> (try field_simp [htn,hbne,hsne])
  <;> ring
private lemma metricShapeProduct_eq_mul {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    Matrix.of (metricShapeProduct t) = ((@metric (m + 1) t)⁻¹ : Matrix (Fin m) (Fin m) ℝ) * Matrix.of (shape t) := by
  ext k h
  change metricShapeProduct t k h = ∑ l : Fin m, (@metric (m+1) t)⁻¹ k l * shape t l h
  simp_rw [metric_inverse_entry t ht]
  unfold shape
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
  have hr := metric_inverse_rowSum t ht k
  simp_rw [metric_inverse_entry t ht] at hr
  erw [hr]
  have hdiag : (∑ l, ((if k = l then t k ^ 2 else 0) -
      t k ^ 2 * t l ^ 2 / chartS2 t) * (if l = h then (t l)⁻¹ else 0)) =
      ((if k = h then t k ^ 2 else 0) - t k ^ 2 * t h ^ 2 / chartS2 t) * (t h)⁻¹ := by
    simp [mul_ite]
  erw [hdiag]
  unfold metricShapeProduct weight
  have hbne := (remain_pos t ht).ne'
  have hsne := (chartS2_pos t ht).ne'
  generalize hbdef : remain t = b at *
  generalize hsdef : chartS2 t = S at *
  by_cases hkh : k = h <;> simp_all
  <;> field_simp [(ht.1 h).ne',hbne,hsne]
  <;> ring
private lemma ricci_eq_gauss {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) (i j : Fin m) :
    @ricci (m+1) t i j =
      (Matrix.trace (Matrix.of (metricShapeProduct t)) * shape t i j -
        (Matrix.of (shape t) * Matrix.of (metricShapeProduct t)) i j) / chartS2 t := by
  change (∑ k : Fin m,
    (fderiv ℝ (fun s : Fin m → ℝ => @christoffel (m+1) s k i j) t (Pi.single k 1) -
     fderiv ℝ (fun s : Fin m → ℝ => @christoffel (m+1) s k i k) t (Pi.single j 1) +
     ∑ l : Fin m, (@christoffel (m+1) t k k l * @christoffel (m+1) t l i j -
       @christoffel (m+1) t k j l * @christoffel (m+1) t l i k))) =
    ((∑ k : Fin m, metricShapeProduct t k k) * shape t i j -
     ∑ k : Fin m, shape t i k * metricShapeProduct t k j) / chartS2 t
  simp_rw [christoffel_partial t ht,christoffel_eq_gamma t ht,coordinate_gauss t ht]
  rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul]
  simp [mul_comm]
private lemma trace_diagonal_rankOne {m : ℕ} (d u v : Fin m → ℝ) (c : ℝ) :
    Matrix.trace (Matrix.diagonal d - c • Matrix.vecMulVec u v) =
      (∑ i, d i) - c * (∑ i, u i * v i) := by
  simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_diagonal,
    Matrix.trace_vecMulVec, dotProduct]
private lemma trace_diagonal_mul_rankOne {m : ℕ} (d u v : Fin m → ℝ) :
    Matrix.trace (Matrix.diagonal d * Matrix.vecMulVec u v) = ∑ i, d i * u i * v i := by
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Matrix.vecMulVec_apply, mul_assoc]
private lemma trace_rankOne_square {m : ℕ} (u v : Fin m → ℝ) :
    Matrix.trace (Matrix.vecMulVec u v * Matrix.vecMulVec u v) = (∑ i, u i * v i)^2 := by
  rw [Matrix.vecMulVec_mul_vecMulVec,Matrix.trace_vecMulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (u _) (∑ _, _)]
  rw [← Finset.mul_sum]
  simp_rw [mul_comm (v _) (u _)]
  ring
private lemma trace_diagonal_rankOne_square {m : ℕ} (d u v : Fin m → ℝ) (c : ℝ) :
    Matrix.trace ((Matrix.diagonal d - c • Matrix.vecMulVec u v) *
      (Matrix.diagonal d - c • Matrix.vecMulVec u v)) =
      (∑ i, d i ^ 2) - 2*c*(∑ i, d i * u i * v i) +
        c^2*(∑ i, u i * v i)^2 := by
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,Matrix.trace_sub,
    Matrix.trace_sub,Matrix.trace_sub,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.smul_mul,Matrix.mul_smul]
  simp only [Matrix.trace_smul,smul_eq_mul]
  rw [Matrix.trace_mul_comm (Matrix.vecMulVec u v),
    trace_diagonal_mul_rankOne,trace_rankOne_square,Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp only [← pow_two]
  ring
private lemma contraction_eq_trace {m : ℕ} (H R : Matrix (Fin m) (Fin m) ℝ) (hH : H.IsSymm) :
    (∑ i, ∑ j, H i j * R i j) = Matrix.trace (H * R) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hH.apply]
private lemma metric_inverse_symm {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    ((@metric (m+1) t)⁻¹).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [metric_inverse_entry t ht,metric_inverse_entry t ht]
  by_cases hij : i = j <;> simp_all [eq_comm]
  ring
private lemma scalarCurvature_eq_trace {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    @scalarCurvature (m+1) t =
      (Matrix.trace (Matrix.of (metricShapeProduct t)) ^ 2 -
        Matrix.trace (Matrix.of (metricShapeProduct t) * Matrix.of (metricShapeProduct t))) /
        chartS2 t := by
  let H : Matrix (Fin m) (Fin m) ℝ := ((@metric (m + 1) t)⁻¹ : Matrix (Fin m) (Fin m) ℝ)
  let Q : Matrix (Fin m) (Fin m) ℝ := Matrix.of (shape t)
  let M : Matrix (Fin m) (Fin m) ℝ := Matrix.of (metricShapeProduct t)
  have hM : H*Q=M := (metricShapeProduct_eq_mul t ht).symm
  have hR : Matrix.of (@ricci (m+1) t) = (chartS2 t)⁻¹ • (Matrix.trace M • Q - Q*M) := by
    ext i j
    rw [Matrix.of_apply,ricci_eq_gauss t ht]
    simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
    dsimp only [M,Q]
    simp only [Matrix.of_apply]
    ring
  change (∑ i : Fin m, ∑ j : Fin m, H i j * Matrix.of (@ricci (m+1) t) i j) = _
  rw [contraction_eq_trace H _ (metric_inverse_symm t ht),hR,Matrix.mul_smul,
    Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_smul,Matrix.trace_sub,Matrix.trace_smul]
  rw [← Matrix.mul_assoc,hM]
  dsimp only [M]
  simp only [smul_eq_mul]
  ring
private lemma metricShapeProduct_rankOne {m : ℕ} (t : Fin m → ℝ) :
    Matrix.of (metricShapeProduct t) = Matrix.diagonal t -
      (chartS2 t)⁻¹ • Matrix.vecMulVec (fun i => t i ^ 2) (fun j => t j - remain t) := by
  ext i j
  simp [metricShapeProduct,weight,Matrix.diagonal_apply,Matrix.vecMulVec,div_eq_mul_inv]
  ring
lemma scalarCurvature_powerSums {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    @scalarCurvature (m+1) t =
      ((∑ i, t i) ^ 2 - (∑ i, t i ^ 2) -
        2*(∑ i, t i)*(∑ i, t i ^ 2*(t i-remain t))/chartS2 t +
        2*(∑ i, t i ^ 3*(t i-remain t))/chartS2 t) / chartS2 t := by
  rw [scalarCurvature_eq_trace t ht,metricShapeProduct_rankOne,
    trace_diagonal_rankOne,trace_diagonal_rankOne_square]
  have he : (∑ i, t i * t i ^ 2 * (t i - remain t)) =
      ∑ i, t i ^ 3 * (t i - remain t) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  simp only [div_eq_mul_inv]
  ring
def PositiveT {n : ℕ} (y q : Fin n → ℝ) : Prop :=
  IsTTransform y q ∧ (∀ i, 0 < y i) ∧ (∀ i, 0 < q i) ∧ (∑ i, q i) = ∑ i, y i
lemma ttransform_positive {n : ℕ} {y q : Fin n → ℝ}
    (ht : IsTTransform y q) (hy : ∀ i, 0 < y i) : ∀ i, 0 < q i := by
  rcases ht with ⟨j,l,c,hc0,hc1,rfl⟩
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  have h₁ := hy i
  have h₂ := hy (Equiv.swap j l i)
  by_cases hc : c = 0
  · simp [hc, h₁]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) h₁.le)
      (mul_pos (lt_of_le_of_ne hc0 (Ne.symm hc)) h₂)
lemma ttransform_sum {n : ℕ} {y q : Fin n → ℝ} (ht : IsTTransform y q) :
    (∑ i, q i) = ∑ i, y i := by
  rcases ht with ⟨j,l,c,hc0,hc1,rfl⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Equiv.sum_comp (Equiv.swap j l) y]
  ring
private lemma eq_of_pointwise_le_sum_eq {n : ℕ} {x y : Fin n → ℝ}
    (hxy : ∀ i, x i ≤ y i) (hsum : (∑ i, x i) = ∑ i, y i) : x = y := by
  funext i
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hxy j)).mp hsum i (Finset.mem_univ i)
lemma positive_sorted_chain {n : ℕ} {z y : Fin n → ℝ}
    (hz : Antitone z) (hz0 : ∀ i, 0 < z i) (hy0 : ∀ i, 0 < y i)
    (hpre : ∀ k, D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k z ≤ D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k y)
    (hsum : (∑ i, z i) = ∑ i, y i) :
    Relation.ReflTransGen PositiveT y z := by
  classical
  suffices H : ∀ d (q : Fin n → ℝ), hammingDist z q ≤ d →
      (∀ i, 0 < q i) → (∀ k, D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k z ≤ D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k q) →
      (∑ i, z i) = (∑ i, q i) → Relation.ReflTransGen PositiveT q z from
    H _ y le_rfl hy0 hpre hsum
  intro d
  induction d with
  | zero =>
    intro q hcard hq0 hqpre hsum
    have heq : z = q := eq_of_hammingDist_eq_zero (Nat.le_zero.mp hcard)
    subst q
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro q hcard hq0 hqpre hsum
    by_cases hall : ∀ i, z i ≤ q i
    · have heq := eq_of_pointwise_le_sum_eq hall hsum
      subst q
      exact Relation.ReflTransGen.refl
    obtain ⟨q',htr,hq'0,hq'pre,hcard'⟩ :=
      exists_isTTransform_of_not_forall_le hz (fun i => (hz0 i).le)
        (fun i => (hq0 i).le) hqpre hall
    have hp := ttransform_positive htr hq0
    have hs := ttransform_sum htr
    exact (Relation.ReflTransGen.single ⟨htr,hq0,hp,hs⟩).trans
      (ih q' (by change hammingDist z q' < hammingDist z q at hcard'; omega) hp hq'pre (hsum.trans hs.symm))
lemma positiveT_simplex {n : ℕ} {y q : Fin n → ℝ}
    (ht : PositiveT y q) (hy : y ∈ simplex n) : q ∈ simplex n :=
  ⟨ht.2.2.1,ht.2.2.2.trans hy.2⟩

end D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
