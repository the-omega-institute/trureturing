/- GID: D5/S3/Quantum/Divergence/MatrixLogResolventDerivative
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MatrixLogResolventDerivative
   mirror-E: none(waiver:analytic-operator-derivative)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ParametricIntervalIntegral]
   utility: none
   digest: Differentiate the actual matrix logarithm on the real Hermitian space. -/

import D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath

set_option quotPrecheck false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.MatrixLogResolventDerivative

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)
local notation "ι" => (selfAdjoint.submodule ℝ M).subtypeL
local notation "B" => fun (A : M) (u : ℝ) => (1 - u) • (1 : M) + u • A
local notation "pathInv" => fun (A : M) (u : ℝ) => Ring.inverse (B A u)
local notation "K" => fun (A : S) (u : ℝ) => (A.val - 1) * pathInv A.val u
local notation "L" => fun (A : S) (u : ℝ) =>
  (ContinuousLinearMap.mulLeftRight ℝ M (pathInv A.val u) (pathInv A.val u)).comp ι

private lemma inverse_norm_le {A : M} {d : ℝ} (hd : 0 < d)
    (hA : A.PosDef) (hgap : algebraMap ℝ M d ≤ A) : ‖Ring.inverse A‖ ≤ d⁻¹ := by
  let : CStarAlgebra M := {}
  rw [← cfc_ringInverse_id (R := ℝ) A hA.isUnit hA.isHermitian.isSelfAdjoint]
  apply norm_cfc_le (inv_nonneg.mpr hd.le)
  intro x hx
  have hdx := (algebraMap_le_iff_le_spectrum hA.isHermitian.isSelfAdjoint).mp hgap x hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd.trans_le hdx))]
  exact inv_anti₀ hd hdx

private lemma path_gap {A : M} {d u : ℝ} (hd : 0 < d)
    (hgap : algebraMap ℝ M d ≤ A) (hu : u ∈ Icc (0 : ℝ) 1) :
    algebraMap ℝ M (min 1 d) ≤ B A u := by
  have h1 : algebraMap ℝ M (min 1 d) ≤ (1 : M) := by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using smul_le_smul_of_nonneg_right (min_le_left 1 d) (zero_le_one : (0 : M) ≤ 1)
  have h2 : algebraMap ℝ M (min 1 d) ≤ A :=
    by
      rw [Algebra.algebraMap_eq_smul_one] at hgap ⊢
      exact (smul_le_smul_of_nonneg_right (min_le_right 1 d) (zero_le_one : (0 : M) ≤ 1)).trans hgap
  have h := add_le_add (smul_le_smul_of_nonneg_left h1 (sub_nonneg.mpr hu.2))
    (smul_le_smul_of_nonneg_left h2 hu.1)
  simpa only [← add_smul, sub_add_cancel, one_smul] using h

private lemma posdef_neighborhood (A : S) (hA : A.val.PosDef) :
    ∃ d > 0, ∃ s ∈ 𝓝 A, ∀ Y ∈ s, algebraMap ℝ M d ≤ Y.val := by
  let : CStarAlgebra M := {}
  cases subsingleton_or_nontrivial M with
  | inl hs =>
    exact ⟨1, zero_lt_one, univ, univ_mem, fun Y _ => le_of_eq (Subsingleton.elim _ _)⟩
  | inr hn =>
    obtain ⟨d, hd, hgap⟩ :=
      (CFC.exists_pos_algebraMap_le_iff hA.isHermitian.isSelfAdjoint).mpr
        (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
    refine ⟨d / 2, half_pos hd, Metric.ball A (d / 2), Metric.ball_mem_nhds A (half_pos hd), ?_⟩
    intro Y hY
    have hdist : ‖Y.val - A.val‖ < d / 2 := by
      change ‖Y - A‖ < d / 2
      simpa only [dist_eq_norm] using Metric.mem_ball.mp hY
    have hsa : IsSelfAdjoint (Y.val - A.val) := Y.property.sub A.property
    have hnorm := hsa.neg_algebraMap_norm_le_self
    have hsmall : -(algebraMap ℝ M (d / 2)) ≤ Y.val - A.val := by
      apply le_trans _ hnorm
      apply neg_le_neg
      simpa only [Algebra.algebraMap_eq_smul_one] using
        smul_le_smul_of_nonneg_right hdist.le (zero_le_one : (0 : M) ≤ 1)
    have h := add_le_add hgap hsmall
    have heq : algebraMap ℝ M d + -(algebraMap ℝ M (d / 2)) =
        algebraMap ℝ M (d / 2) := by
      rw [← map_neg, ← map_add]
      congr 1
      ring
    rw [heq] at h
    simpa only [add_sub_cancel] using h
private lemma path_hasFDerivAt (A : S) (u : ℝ) (hunit : IsUnit (B A.val u)) :
    HasFDerivAt (fun Y : S => K Y u) (L A u) A := by
  have hb : HasFDerivAt (fun Y : S => B Y.val u) (u • ι) A :=
    ((ι).hasFDerivAt.const_smul u).const_add _
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit).comp A hb
  have hi' : HasFDerivAt (fun Y : S => pathInv Y.val u)
      ((-ContinuousLinearMap.mulLeftRight ℝ M (pathInv A.val u) (pathInv A.val u)).comp (u • ι)) A := by
    simpa only [IsUnit.unit_spec, ← Ring.inverse_unit, Function.comp_def] using hi
  have hp := ((ι).hasFDerivAt.sub_const (1 : M)).mul' hi'
  apply hp.congr_fderiv
  apply ContinuousLinearMap.ext
  intro H
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, neg_apply,
    smul_apply, Submodule.subtypeL_apply,
    op_smul_eq_mul, smul_eq_mul]
  have hbr := Ring.mul_inverse_cancel (B A.val u) hunit
  have hcancel : (1 : M) - u • ((A.val - 1) * pathInv A.val u) = pathInv A.val u := by
    have hb' : B A.val u = 1 + u • (A.val - 1) := by
      simp only [smul_sub, sub_smul, one_smul]
      abel
    change B A.val u * pathInv A.val u = 1 at hbr
    nth_rw 1 [hb'] at hbr
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at hbr
    exact (eq_sub_iff_add_eq.mpr hbr).symm
  calc
    (A.val - 1) * (-(pathInv A.val u * (u • H.val) * pathInv A.val u)) + H.val * pathInv A.val u =
        (1 - u • ((A.val - 1) * pathInv A.val u)) * H.val * pathInv A.val u := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      noncomm_ring
    _ = _ := by rw [hcancel]

private lemma inverse_path_continuousOn (A : M)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (B A u)) :
    ContinuousOn (pathInv A) (Icc (0 : ℝ) 1) := by
  intro u hmem
  have hc : ContinuousAt Ring.inverse (B A u) := by
    simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt (hu u hmem).unit
  have hb : ContinuousWithinAt (fun v : ℝ => B A v) (Icc (0 : ℝ) 1) u := by
    fun_prop
  exact hc.comp_continuousWithinAt hb

private lemma derivative_path_continuousOn (A : S)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (B A.val u)) :
    ContinuousOn (L A) (Icc (0 : ℝ) 1) := by
  have hc := inverse_path_continuousOn A.val hu
  exact (((ContinuousLinearMap.mulLeftRight ℝ M).continuous.comp_continuousOn hc).clm_apply hc).clm_comp continuousOn_const

set_option diagnostics true in
set_option trace.profiler true in
set_option maxHeartbeats 3200000 in
-- Differentiating the parameter integral elaborates several operator-norm instances.
/-- The logarithm of a positive matrix has a real Fréchet derivative on the Hermitian space.
The derivative is the integral of the inverse affine-path sandwiches. -/
theorem matrix_log_hasFDerivAt_path (A : S) (hA : A.val.PosDef) :
    HasFDerivAt (fun Y : S => CFC.log Y.val) (∫ u in (0 : ℝ)..1, L A u) A := by
  let : CStarAlgebra M := {}
  obtain ⟨d, hd, s, hs, hgap⟩ := posdef_neighborhood A hA
  have hp (Y : S) (hY : Y ∈ s) : Y.val.PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp <|
      (isStrictlyPositive_algebraMap hd).of_le (hgap Y hY)
  have hpath (Y : S) (hY : Y ∈ s) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (B Y.val u).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp <|
      (isStrictlyPositive_algebraMap (lt_min zero_lt_one hd)).of_le
        (path_gap hd (hgap Y hY) hu)
  have hmem : A ∈ s := mem_of_mem_nhds hs
  have hcA := derivative_path_continuousOn A (fun u hu => (hpath A hmem u hu).isUnit)
  have hmeas : ∀ᶠ Y in 𝓝 A,
      AEStronglyMeasurable (fun u => K Y u) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    filter_upwards [hs] with Y hY
    exact (continuousOn_const.mul
      (inverse_path_continuousOn Y.val (fun u hu => (hpath Y hY u hu).isUnit))).mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ u ∂volume, u ∈ Ioc (0 : ℝ) 1 →
      ∀ Y ∈ s, ‖L Y u‖ ≤ ((min 1 d)⁻¹)^2 := by
    filter_upwards [] with u hu Y hY
    have hr := inverse_norm_le (lt_min zero_lt_one hd)
      (hpath Y hY u ⟨hu.1.le, hu.2⟩) (path_gap hd (hgap Y hY) ⟨hu.1.le, hu.2⟩)
    calc
      ‖L Y u‖ ≤ ‖ContinuousLinearMap.mulLeftRight ℝ M (pathInv Y.val u)
          (pathInv Y.val u)‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖pathInv Y.val u‖ * ‖pathInv Y.val u‖) * 1 :=
        mul_le_mul (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _)
          (Submodule.norm_subtypeL_le _) (norm_nonneg _) (by positivity)
      _ ≤ ((min 1 d)⁻¹)^2 := by nlinarith [norm_nonneg (pathInv Y.val u)]
  have hint : IntervalIntegrable (fun u => K A u) volume 0 1 := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath.matrixLogPath_intervalIntegrable A.val hA
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le hs hmeas hint
    ((hcA.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    hbound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ((min 1 d)⁻¹)^2)
      volume 0 1) (by
      filter_upwards [] with u hu Y hY
      exact path_hasFDerivAt Y u (hpath Y hY u ⟨hu.1.le, hu.2⟩).isUnit)
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [hs] with Y hY
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath.matrix_log_eq_integral_path Y.val (hp Y hY)

end D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
