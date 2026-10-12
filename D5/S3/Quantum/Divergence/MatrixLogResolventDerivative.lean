/- GID: D5/S3/Quantum/Divergence/MatrixLogResolventDerivative
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MatrixLogResolventDerivative
   mirror-E: none(waiver:analytic-operator-derivative)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ParametricIntervalIntegral]
   utility: none
   digest: Differentiate the actual matrix logarithm on the real Hermitian space. -/

import D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath
import D5.S3.Divergence.LogDerivTrace
import D5.S3.Weil.ZetaLinear.RankTrace

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

private lemma path_gap {A : M} {d u : ℝ}
    (hgap : algebraMap ℝ M d ≤ A) (hu : u ∈ Icc (0 : ℝ) 1) :
    algebraMap ℝ M (min 1 d) ≤ B A u := by
  have h1 : algebraMap ℝ M (min 1 d) ≤ (1 : M) := by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
      smul_le_smul_of_nonneg_right (min_le_left 1 d) (zero_le_one : (0 : M) ≤ 1)
  have h2 : algebraMap ℝ M (min 1 d) ≤ A :=
    by
      rw [Algebra.algebraMap_eq_smul_one] at hgap ⊢
      exact (smul_le_smul_of_nonneg_right (min_le_right 1 d)
        (zero_le_one : (0 : M) ≤ 1)).trans hgap
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
      ((-ContinuousLinearMap.mulLeftRight ℝ M
        (pathInv A.val u) (pathInv A.val u)).comp (u • ι)) A := by
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
  exact ContinuousAt.comp_continuousWithinAt (f := fun v : ℝ => B A v) hc hb

private lemma derivative_path_continuousOn (A : S)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (B A.val u)) :
    ContinuousOn (L A) (Icc (0 : ℝ) 1) := by
  have hc := inverse_path_continuousOn A.val hu
  exact (((ContinuousLinearMap.mulLeftRight ℝ M).continuous.comp_continuousOn hc).clm_apply
    hc).clm_comp continuousOn_const

set_option maxHeartbeats 800000 in
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
        (path_gap (hgap Y hY) hu)
  have hmem : A ∈ s := mem_of_mem_nhds hs
  have hcA := derivative_path_continuousOn A (fun u hu => (hpath A hmem u hu).isUnit)
  have hmeas : ∀ᶠ Y in 𝓝 A,
      AEStronglyMeasurable (fun u => K Y u) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    filter_upwards [hs] with Y hY
    exact (continuousOn_const.mul
      (inverse_path_continuousOn Y.val (fun u hu => (hpath Y hY u hu).isUnit))).mono
        Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ u ∂volume, u ∈ Ioc (0 : ℝ) 1 →
      ∀ Y ∈ s, ‖L Y u‖ ≤ ((min 1 d)⁻¹)^2 := by
    filter_upwards [] with u hu Y hY
    have hr := inverse_norm_le (lt_min zero_lt_one hd)
      (hpath Y hY u ⟨hu.1.le, hu.2⟩) (path_gap (hgap Y hY) ⟨hu.1.le, hu.2⟩)
    calc
      ‖L Y u‖ ≤ ‖ContinuousLinearMap.mulLeftRight ℝ M (pathInv Y.val u)
          (pathInv Y.val u)‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖pathInv Y.val u‖ * ‖pathInv Y.val u‖) * 1 :=
        mul_le_mul (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ M
          (pathInv Y.val u) (pathInv Y.val u))
          (Submodule.norm_subtypeL_le _) (norm_nonneg _) (by positivity)
      _ ≤ ((min 1 d)⁻¹)^2 := by nlinarith [norm_nonneg (pathInv Y.val u)]
  have hint : IntervalIntegrable (fun u => K A u) volume 0 1 := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath.matrixLogPath_intervalIntegrable
        A.val hA
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun Y : S => fun u : ℝ => K Y u) (F' := L) (x₀ := A)
    (s := s) (a := (0 : ℝ)) (b := 1) (μ := volume)
    (bound := fun _ : ℝ => ((min 1 d)⁻¹)^2) hs
    (by simpa only [uIoc_of_le zero_le_one] using hmeas) hint
    (by simpa only [uIoc_of_le zero_le_one] using
      (hcA.mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc)
    (by simpa only [uIoc_of_le zero_le_one] using hbound)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ((min 1 d)⁻¹)^2) volume 0 1)
    (by
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [] with u hu Y hY
      exact path_hasFDerivAt Y u (hpath Y hY u ⟨hu.1.le, hu.2⟩).isUnit)
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [hs] with Y hY
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath.matrix_log_eq_integral_path
      Y.val (hp Y hY)

local notation "TInv" => fun (A : M) (t : ℝ) => Ring.inverse (A + t • (1 : M))
local notation "resolventL" => fun (A : S) (t : ℝ) =>
  (ContinuousLinearMap.mulLeftRight ℝ M (TInv A.val t) (TInv A.val t)).comp ι

private lemma inverse_real_smul (C : M) (c : ℝ) (hc : c ≠ 0) (hC : IsUnit C) :
    Ring.inverse (c • C) = c⁻¹ • Ring.inverse C := by
  rcases hC with ⟨a, rfl⟩
  have h := Ring.inverse_unit ((Units.mk0 c hc) • a)
  simpa only [Units.val_smul, Units.smul_inv, Units.smul_def,
    Units.val_mk0, Units.val_inv_eq_inv_val, Ring.inverse_unit] using h

private lemma reciprocal_parameter_image :
    (fun u : ℝ => u⁻¹ - 1) '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
  change ((fun v : ℝ => v - 1) ∘ (fun u : ℝ => u⁻¹)) '' Ioo (0 : ℝ) 1 = _
  rw [image_comp, image_inv_eq_inv, inv_Ioo_0_left zero_lt_one]
  simp only [inv_one, image_sub_const_Ioi, sub_self]

/-- The substitution `t = u⁻¹ - 1` maps `(0,1)` onto `(0,∞)`. Its Jacobian
`u⁻²` cancels the two inverse-path scaling factors; interval endpoints are null. -/
private lemma path_resolvent_change (A : S) (hA : A.val.PosDef) :
    (∫ u in (0 : ℝ)..1, L A u) = (∫ t in Ioi (0 : ℝ), resolventL A t) ∧
      IntegrableOn (resolventL A) (Ioi (0 : ℝ)) := by
  let : CStarAlgebra M := {}
  have hinj : InjOn (fun u : ℝ => u⁻¹ - 1) (Ioo (0 : ℝ) 1) := by
    intro u _ v _ h
    apply inv_injective
    dsimp only at h
    linarith
  have hdiff : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun v : ℝ => v⁻¹ - 1) (-(u ^ 2)⁻¹) (Ioo (0 : ℝ) 1) u := by
    intro u hu
    exact ((hasDerivAt_inv hu.1.ne').sub_const 1).hasDerivWithinAt
  have hkernel : EqOn (L A)
      (fun u : ℝ => |-(u ^ 2)⁻¹| • resolventL A (u⁻¹ - 1)) (Ioo (0 : ℝ) 1) := by
    intro u hu
    have ht : 0 < u⁻¹ - 1 := sub_pos.mpr ((one_lt_inv₀ hu.1).mpr hu.2)
    have hC : (A.val + (u⁻¹ - 1) • (1 : M)).PosDef :=
      hA.add_posSemidef (Matrix.PosSemidef.one.smul ht.le)
    have hB : B A.val u = u • (A.val + (u⁻¹ - 1) • (1 : M)) := by
      simp only [smul_add, smul_smul]
      have hscalar : u * (u⁻¹ - 1) = 1 - u := by
        rw [mul_sub, mul_inv_cancel₀ hu.1.ne', mul_one]
      rw [hscalar]
      exact add_comm _ _
    have hi : pathInv A.val u = u⁻¹ • TInv A.val (u⁻¹ - 1) := by
      dsimp only at hB ⊢
      rw [hB, inverse_real_smul _ u hu.1.ne' hC.isUnit]
    have hweight : |-(u ^ 2)⁻¹| = u⁻¹ * u⁻¹ := by
      rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg u)), ← inv_pow, pow_two]
    apply ContinuousLinearMap.ext
    intro H
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
      smul_apply, Submodule.subtypeL_apply, hi, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hweight]
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hdiff hinj (resolventL A)
  rw [reciprocal_parameter_image] at heq
  constructor
  · rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, heq]
    exact setIntegral_congr_fun measurableSet_Ioo hkernel
  · have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo hdiff hinj (resolventL A)
    rw [reciprocal_parameter_image] at hchange
    apply hchange.mpr
    obtain ⟨d, hd, s, hs, hgap⟩ := posdef_neighborhood A hA
    have hmem : A ∈ s := mem_of_mem_nhds hs
    have hc : ContinuousOn (L A) (Icc (0 : ℝ) 1) :=
      derivative_path_continuousOn A (fun u hu =>
        ((isStrictlyPositive_algebraMap (lt_min zero_lt_one hd)).of_le
          (path_gap (hgap A hmem) hu)).isUnit)
    exact (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun hkernel measurableSet_Ioo

/-- On the real Hermitian space, the derivative of the actual matrix logarithm is the
Bochner integral of the positive-half-line resolvent sandwiches. -/
theorem matrix_log_hasFDerivAt_resolvent (A : S) (hA : A.val.PosDef) :
    HasFDerivAt (fun Y : S => CFC.log Y.val) (∫ t in Ioi (0 : ℝ), resolventL A t) A ∧
      IntegrableOn (resolventL A) (Ioi (0 : ℝ)) ∧
      ∀ H : S, (∫ t in Ioi (0 : ℝ), resolventL A t) H =
        D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val := by
  obtain ⟨heq, hint⟩ := path_resolvent_change A hA
  refine ⟨?_, hint, ?_⟩
  · rw [← heq]
    exact matrix_log_hasFDerivAt_path A hA
  · intro H
    rw [ContinuousLinearMap.integral_apply hint H]
    simp only [D5.S3.Divergence.LogDerivTrace.logDeriv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
      Submodule.subtypeL_apply, Matrix.nonsing_inv_eq_ringInverse]

local notation "Tr" =>
  Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
local notation "G" => (ContinuousLinearMap.compL ℝ S M ℝ Tr).comp
  ((ContinuousLinearMap.mul ℝ M).precompL S ι)
local notation "entropy" => fun Y : S => (Y.val * CFC.log Y.val).trace.re

private lemma trace_entropy_hasFDerivAt (A : S) (hA : A.val.PosDef) :
    HasFDerivAt entropy (G (CFC.log A.val + 1)) A := by
  obtain ⟨hlog, _, haction⟩ := matrix_log_hasFDerivAt_resolvent A hA
  have hp := (ι).hasFDerivAt.mul' hlog
  have ht := (Tr).hasFDerivAt.comp A hp
  apply ht.congr_fderiv
  ext H
  change (A.val * (∫ t in Ioi (0 : ℝ), resolventL A t) H +
    H.val * CFC.log A.val).trace.re = (H.val * (CFC.log A.val + 1)).trace.re
  rw [haction, Matrix.trace_add,
    D5.S3.Divergence.LogDerivTrace.trace_mul_logDeriv A.val H.val hA H.property,
    Matrix.mul_add, Matrix.mul_one, Matrix.trace_add]
  exact add_comm _ _

/-- The actual trace-entropy Hessian is the bilinear BKM resolvent form.
The first Hessian argument differentiates the gradient and the second evaluates it. -/
theorem trace_entropy_hessian_resolvent (A : S) (hA : A.val.PosDef) :
    HasFDerivAt (fderiv ℝ entropy) ((G).comp (∫ t in Ioi (0 : ℝ), resolventL A t)) A ∧
      (∀ H J : S, (fderiv ℝ (fderiv ℝ entropy) A) H J =
        (J.val * D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val).trace.re) ∧
      ∀ H : S, 0 ≤ (fderiv ℝ (fderiv ℝ entropy) A) H H := by
  have hlog := (matrix_log_hasFDerivAt_resolvent A hA).1
  have hgrad := (G).hasFDerivAt.comp A (hlog.add_const (1 : M))
  obtain ⟨d, hd, s, hs, hgap⟩ := posdef_neighborhood A hA
  have hevent : (fun Y : S => G (CFC.log Y.val + 1)) =ᶠ[𝓝 A] fderiv ℝ entropy := by
    filter_upwards [hs] with Y hY
    exact (trace_entropy_hasFDerivAt Y <|
      Matrix.isStrictlyPositive_iff_posDef.mp <|
        (isStrictlyPositive_algebraMap hd).of_le (hgap Y hY)).fderiv.symm
  have hh := hgrad.congr_of_eventuallyEq hevent.symm
  refine ⟨hh, ?_, ?_⟩
  · intro H J
    rw [hh.fderiv]
    change (J.val * (∫ t in Ioi (0 : ℝ), resolventL A t) H).trace.re = _
    rw [(matrix_log_hasFDerivAt_resolvent A hA).2.2 H]
  · intro H
    rw [hh.fderiv]
    change 0 ≤ (H.val * (∫ t in Ioi (0 : ℝ), resolventL A t) H).trace.re
    have hint := (ContinuousLinearMap.apply ℝ M H).integrable_comp
      (matrix_log_hasFDerivAt_resolvent A hA).2.1
    rw [ContinuousLinearMap.integral_apply
      (matrix_log_hasFDerivAt_resolvent A hA).2.1 H]
    have hcomm := ((Tr).comp ((ContinuousLinearMap.mul ℝ M) H.val)).integral_comp_comm hint
    change (∫ t in Ioi (0 : ℝ), (H.val * (resolventL A t H)).trace.re) =
      (H.val * (∫ t in Ioi (0 : ℝ), resolventL A t H)).trace.re at hcomm
    rw [← hcomm]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hR := (hA.add_posSemidef
      (Matrix.PosSemidef.one.smul (le_of_lt (show 0 < t from ht)))).posSemidef.inv
    have hHRH := hR.conjTranspose_mul_mul_same H.val
    rw [(show H.val.IsHermitian from H.property).eq] at hHRH
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
      Submodule.subtypeL_apply, Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_assoc,
      Pi.zero_apply, RCLike.re_to_complex] using
      RHLinalg.trace_mul_nonneg_of_posSemidef hHRH hR

end D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
