/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/HaarColumnChart
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/HaarColumnChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Haar.HaarColumnChart. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Haar/HaarColumnChart.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar.CompactDualMeasure
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Splitting a skew matrix into one column and block; Jacobian of column chart. -/


open Haar Matrix MeasureTheory Complex Fintype Module LinearMap Norms.L2Operator MatMul
variable {n} [Fintype n] (k₀ : n)
set_option synthInstance.maxSize 999

omit [Fintype n] in
@[scoped simp] lemma Haar.val_ne_and_ne_val (i : Subtype (· ≠ k₀)) : i ≠ k₀ ∧ k₀ ≠ i := by lia

/-- A volume-preserving real linear homeomorphism onto real n×n matrices, inverse to y ↦
((y_{k₀k₀}, column k₀ of `skewOfReal` y without its diagonal entry), block of y off k₀). -/
noncomputable def skewColumnEquiv := (HasGaussianIntegral.exists_measurePreserving_equiv ⟨⟨fun y ↦
  ((y k₀ k₀, (skewOfReal y ·.1 k₀ : Subtype (· ≠ k₀) → ℂ)),
  y.toBlock (· ≠ k₀) (· ≠ k₀)), by aesop⟩, by aesop⟩ (by simp [add_assoc, skewOfReal,
  div_pow, sum_eq_add_sum_subtype_ne _ k₀, ← Finset.sum_add_distrib, RCLike.norm_sq_eq_def]; grind)
  (by simp [finrank_matrix]; zify [@card_pos _ _ ⟨k₀⟩]; lia)).choose.toContinuousLinearEquiv

@[simp] lemma skewColumnEquiv_spec : MeasurePreserving (skewColumnEquiv k₀) ∧ ∀ y, (skewColumnEquiv
  k₀).symm y = ((y k₀ k₀, (skewOfReal y ·.1 k₀)), y.toBlock _ _) := by simp [skewColumnEquiv]; grind

@[simp] lemma skewOfReal_skewColumnEquiv : ∀ p, letI S := skewOfReal (skewColumnEquiv k₀ p)
  S k₀ k₀ = p.1.1 * I ∧ ∀ i, S i.1 k₀ = p.1.2 i ∧ S k₀ i = -star (p.1.2 i) ∧ ∀ j, S i j.1 =
    skewOfReal p.2 i j := by simp [↓reindex_equiv
  (skewColumnEquiv _).symm, -skewColumnEquiv_spec]; simp [skewOfReal]; grind

/-- For J = 1, the map sending θ to the k₀-th column of the Cayley chart at the point
`skewColumnEquiv` k₀ (θ, 0), whose coordinate submatrix off k₀ vanishes, is injective. -/
lemma cayleyChart_col_injective :
  (fun θ ↦ (cayleyChart 1 (skewColumnEquiv k₀ (θ, 0))).1.1.col k₀).Injective := fun _ _ ↦ by
  have a θ := (and_forall_ne k₀).2 (congrFun₂
    (mul_nonsing_inv _ (det_cayleyDenom_one_ne_zero (skewColumnEquiv k₀ (θ, 0))).isUnit) · k₀)
  simp_all [sum_eq_add_sum_subtype_ne _ k₀, mul_apply, funext_iff, -Prod.forall,
    val_cayleyChart_coe, Subtype.forall', -Subtype.forall, cayleyDenom, Subtype.val_inj]
  grind +extAll [ofReal_inj, I_ne_zero, sum_eq_zero]

/-- For the family θ ↦ Cayley chart of U(n) at `skewColumnEquiv` k₀ (θ,0), the form g⁻¹dg read in
the column coordinates has absolute determinant the Cayley weight `cayleyDensity` (J = 1) at that
point. -/
lemma abs_det_logDerivU_col_eq_cayleyDensity θ : |(fst .. ∘ₗ (skewColumnEquiv _).symm.1.1 ∘ₗ
  skewCoords ∘ₗ logDerivU (cayleyChart 1) (skewColumnEquiv k₀ (θ, 0)) ∘ₗ
  (skewColumnEquiv k₀).1.1 ∘ₗ inl ..).det| = cayleyDensity 1 (skewColumnEquiv _ (θ, 0)) := by
  have h := abs_det_skew_congruence (skewColumnEquiv k₀).1.symm ?D
    (coprod ?L ((skewColumnEquiv _).1.1 ∘ₗ inr ..))
  rw [← LinearMap.det_conj _ (.prodComm ..), det_eq_mul_of_block_triangular id _ (id.ext _),
    det_eq_mul_of_block_triangular (fst .. ∘ₗ (skewColumnEquiv _).symm.1.1 ∘ₗ ?L) _ (id.ext _)] at h
  simpa [cayleyDensity, pow_mul] using eq_inv_of_mul_eq_one_right (h.symm.trans (by simp))
  repeat simp [conjTranspose_nonsing_inv, Prod.mk_zero_zero,
    logDerivU_cayleyChart, -skewColumnEquiv_spec] <;> simp [entrywise, skewCoords, cayleyDenom,
    sum_eq_add_sum_subtype_ne _ k₀] <;> simp [skewOfReal] <;> grind
