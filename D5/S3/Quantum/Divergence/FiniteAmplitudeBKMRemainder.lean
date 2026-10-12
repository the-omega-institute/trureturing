/- GID: D5/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   mirror-E: none(waiver:analytic-integral-identity)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts]
   utility: none
   digest: Symmetric finite differences of trace entropy along Hermitian matrix paths. -/

import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
import D5.S3.Resource.LogDet.PathSpectralClassical
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.MeasureTheory.Integral.Prod

set_option quotPrecheck false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace

namespace D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)
local notation "ι" => (selfAdjoint.submodule ℝ M).subtypeL
local notation "Tr" =>
  Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
local notation "entropy" => fun Y : S => (Y.val * CFC.log Y.val).trace.re
local notation "P" => fun (A H : S) (v : ℝ) => A + v • H
local notation "BKM" => fun (A H : S) =>
  (H.val * D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val).trace.re
local notation "R" => fun (A : S) (u : ℝ) => A.val + u • (1 : M)
local notation "K" => fun (A H : S) (u : ℝ) => CFC.conjSqrt (Ring.inverse (R A u)) H.val
local notation "q" => fun (A H : S) (v u : ℝ) =>
  (H.val * Ring.inverse (R (P A H v) u) * H.val * Ring.inverse (R (P A H v) u)).trace.re

private lemma normalized_order (A H : S) (hA : A.val.PosDef) :
    -(‖K A H 0‖ • A.val) ≤ H.val ∧ H.val ≤ ‖K A H 0‖ • A.val := by
  let : CStarAlgebra M := {}
  have hsa : IsSelfAdjoint (K A H 0) :=
    H.property.conjugate_self (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _))
  have hrec : CFC.conjSqrt A.val (K A H 0) = H.val := by
    simpa only [zero_smul, add_zero] using
      CFC.conjSqrt_conjSqrt_ringInverse A.val H.val hA.isStrictlyPositive
  have hc : CFC.conjSqrt A.val (algebraMap ℝ M ‖K A H 0‖) =
      ‖K A H 0‖ • A.val := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, CFC.conjSqrt_one _ hA.posSemidef.nonneg]
  have hl := CFC.conjSqrt_le_conjSqrt (c := A.val) hsa.neg_algebraMap_norm_le_self
  have hu := CFC.conjSqrt_le_conjSqrt (c := A.val) hsa.le_algebraMap_norm_self
  rw [map_neg, hc, hrec] at hl
  rw [hrec, hc] at hu
  exact ⟨hl, hu⟩

private lemma normalized_kernel_bounds (A H : S) (hA : A.val.PosDef)
    (u : ℝ) (hu : 0 ≤ u) :
    IsSelfAdjoint (K A H u) ∧ ‖K A H u‖ ≤ ‖K A H 0‖ := by
  let : CStarAlgebra M := {}
  let r := ‖K A H 0‖
  have hr : 0 ≤ r := norm_nonneg _
  have hR : (R A u).PosDef := hA.add_posSemidef (Matrix.PosSemidef.one.smul hu)
  have hAR : A.val ≤ R A u := le_add_of_nonneg_right
    ((Matrix.PosSemidef.one.smul hu).nonneg)
  have hbounds := normalized_order A H hA
  have hl : -(r • R A u) ≤ H.val :=
    (neg_le_neg (smul_le_smul_of_nonneg_left hAR hr)).trans hbounds.1
  have hh : H.val ≤ r • R A u :=
    hbounds.2.trans (smul_le_smul_of_nonneg_left hAR hr)
  have hsa : IsSelfAdjoint (K A H u) :=
    H.property.conjugate_self (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _))
  have hcl := CFC.conjSqrt_le_conjSqrt (c := Ring.inverse (R A u)) hl
  have hcu := CFC.conjSqrt_le_conjSqrt (c := Ring.inverse (R A u)) hh
  rw [map_neg, map_smul, CFC.conjSqrt_ringInverse_self _ hR.isStrictlyPositive] at hcl
  rw [map_smul, CFC.conjSqrt_ringInverse_self _ hR.isStrictlyPositive] at hcu
  refine ⟨hsa, ?_⟩
  rw [← cfc_id ℝ (K A H u) hsa]
  apply norm_cfc_le hr
  intro x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hl' : algebraMap ℝ M (-r) ≤ K A H u := by
      simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using hcl
    exact (algebraMap_le_iff_le_spectrum hsa).mp hl' x hx
  · have hu' : K A H u ≤ algebraMap ℝ M r := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hcu
    exact (le_algebraMap_iff_spectrum_le hsa).mp hu' x hx

private lemma finite_amplitude_path_posdef (A H : S) (hA : A.val.PosDef)
    (hr : ‖K A H 0‖ < 1) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    (P A H v).val.PosDef := by
  let : CStarAlgebra M := {}
  have hsa := (normalized_kernel_bounds A H hA 0 le_rfl).1
  have hn : ‖v • K A H 0‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr hv)).trans_lt hr
  have hg : algebraMap ℝ M (1 - ‖v • K A H 0‖) ≤ 1 + v • K A H 0 := by
    have hl := ((IsSelfAdjoint.all v).smul hsa).neg_algebraMap_norm_le_self
    have hh := add_le_add_left hl (1 : M)
    simpa only [map_sub, map_add, map_neg, map_one, sub_eq_add_neg, add_comm] using hh
  have hp := (isStrictlyPositive_algebraMap (sub_pos.mpr hn)).of_le hg
  have heq : CFC.conjSqrt A.val (1 + v • K A H 0) = (P A H v).val := by
    rw [map_add, map_smul, CFC.conjSqrt_one _ hA.posSemidef.nonneg]
    have hrec : CFC.conjSqrt A.val (K A H 0) = H.val := by
      simpa only [zero_smul, add_zero] using
        CFC.conjSqrt_conjSqrt_ringInverse A.val H.val hA.isStrictlyPositive
    rw [hrec]
    rfl
  apply Matrix.isStrictlyPositive_iff_posDef.mp
  rw [← heq]
  exact (CFC.isStrictlyPositive_conjSqrt_iff _ _ hA.isStrictlyPositive).mpr hp

private lemma resolvent_trace_eq_normalized (A H : S) (hA : A.val.PosDef)
    (hr : ‖K A H 0‖ < 1) (v u : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) (hu : 0 ≤ u) :
    q A H v u = (cfc (fun k : ℝ => k ^ 2 / (1 + v * k) ^ 2) (K A H u)).trace.re := by
  let : CStarAlgebra M := {}
  let C := R A u
  let T := CFC.sqrt C
  let W := CFC.sqrt (Ring.inverse C)
  let Z := K A H u
  let B := 1 + v • Z
  have hC : C.PosDef := hA.add_posSemidef (Matrix.PosSemidef.one.smul hu)
  have hT : IsUnit T := (CFC.isUnit_sqrt_iff _ hC.posSemidef.nonneg).mpr hC.isUnit
  have hWT : W * T = 1 := by
    rw [show W = Ring.inverse T by exact CFC.sqrt_ringInverse,
      Ring.inverse_mul_cancel _ hT]
  have hTW : T * W = 1 := by
    rw [show W = Ring.inverse T by exact CFC.sqrt_ringInverse,
      Ring.mul_inverse_cancel _ hT]
  have hH : H.val = T * Z * T := by
    simpa only [T, Z, C, CFC.conjSqrt_apply] using
      (CFC.conjSqrt_conjSqrt_ringInverse C H.val hC.isStrictlyPositive).symm
  have hR : R (P A H v) u = CFC.conjSqrt C B := by
    rw [map_add, map_smul, CFC.conjSqrt_one _ hC.posSemidef.nonneg]
    have hz : CFC.conjSqrt C Z = H.val :=
      CFC.conjSqrt_conjSqrt_ringInverse C H.val hC.isStrictlyPositive
    rw [hz]
    change (A.val + v • H.val) + u • (1 : M) = (A.val + u • 1) + v • H.val
    abel
  have hi : Ring.inverse (R (P A H v) u) = W * Ring.inverse B * W := by
    rw [hR, CFC.ringInverse_conjSqrt _ _ hC.isStrictlyPositive, CFC.conjSqrt_apply]
  have htr : q A H v u = (Z * Ring.inverse B * Z * Ring.inverse B).trace.re := by
    dsimp only
    rw [hH, hi]
    have heq : (T * Z * T) * (W * Ring.inverse B * W) * (T * Z * T) *
        (W * Ring.inverse B * W) = T * (Z * Ring.inverse B * Z * Ring.inverse B) * W := by
      calc
        _ = T * Z * (T * W) * Ring.inverse B * (W * T) * Z *
            (T * W) * Ring.inverse B * W := by noncomm_ring
        _ = _ := by rw [hTW, hWT]; noncomm_ring
    rw [heq, Matrix.trace_mul_cycle, hWT, Matrix.one_mul]
  have hsa : IsSelfAdjoint Z := (normalized_kernel_bounds A H hA u hu).1
  have hk (k : ℝ) (hk : k ∈ spectrum ℝ Z) : |k| < 1 := by
    have hb := norm_apply_le_norm_cfc (id : ℝ → ℝ) Z hk continuousOn_id hsa
    rw [cfc_id ℝ Z hsa, Real.norm_eq_abs] at hb
    exact hb.trans_lt ((normalized_kernel_bounds A H hA u hu).2.trans_lt hr)
  have hden (k : ℝ) (hk' : k ∈ spectrum ℝ Z) : 1 + v * k ≠ 0 := by
    have hm : |v * k| < 1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg k) (abs_le.mpr hv)).trans_lt (hk k hk')
    have ha := (abs_lt.mp hm).1
    linarith
  have hf : ContinuousOn (fun k : ℝ => 1 + v * k) (spectrum ℝ Z) := by fun_prop
  have hs : cfc (fun k : ℝ => 1 + v * k) Z = B := by
    rw [cfc_const_add 1 (fun k : ℝ => v * k) Z (by fun_prop) hsa,
      cfc_const_mul_id v Z hsa, map_one]
  have heq : cfc (fun k : ℝ => k ^ 2 / (1 + v * k) ^ 2) Z =
      Z * Ring.inverse B * Z * Ring.inverse B := by
    have hki : cfc (fun k : ℝ => k / (1 + v * k)) Z = Z * Ring.inverse B := by
      rw [cfc_map_div (fun k : ℝ => k) (fun k : ℝ => 1 + v * k)
        Z hden continuousOn_id hf hsa, cfc_id' ℝ Z hsa, hs]
    rw [show (fun k : ℝ => k ^ 2 / (1 + v * k) ^ 2) =
      (fun k : ℝ => (k / (1 + v * k)) ^ 2) by funext k; rw [div_pow]]
    rw [cfc_pow (fun k : ℝ => k / (1 + v * k)) 2 Z
      (continuousOn_id.div hf hden) hsa, hki, pow_two]
    noncomm_ring
  exact htr.trans (congrArg (fun C : M => C.trace.re) heq).symm

private lemma resolvent_trace_nonneg (A H : S) (hA : A.val.PosDef)
    (hr : ‖K A H 0‖ < 1) (v u : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) (hu : 0 ≤ u) :
    0 ≤ q A H v u := by
  rw [resolvent_trace_eq_normalized A H hA hr v u hv hu]
  have hn : (0 : M) ≤ cfc (fun k : ℝ => k ^ 2 / (1 + v * k) ^ 2) (K A H u) :=
    cfc_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  exact (RCLike.nonneg_iff.mp (Matrix.nonneg_iff_posSemidef.mp hn).trace_nonneg).1

private lemma bkm_eq_integral_trace (A H : S) (hA : A.val.PosDef) :
    IntegrableOn (fun u => q A H 0 u) (Ioi (0 : ℝ)) ∧
      BKM A H = ∫ u in Ioi (0 : ℝ), q A H 0 u := by
  let L : ℝ → S →L[ℝ] M := fun u =>
    (ContinuousLinearMap.mulLeftRight ℝ M (Ring.inverse (R A u))
      (Ring.inverse (R A u))).comp ι
  obtain ⟨_, hi, he⟩ := MatrixLogResolventDerivative.matrix_log_hasFDerivAt_resolvent A hA
  have hint : Integrable (fun u => L u H) (volume.restrict (Ioi (0 : ℝ))) :=
    (ContinuousLinearMap.apply ℝ M H).integrable_comp hi
  let TL : M →L[ℝ] ℝ := (Tr).comp ((ContinuousLinearMap.mul ℝ M) H.val)
  have ht := TL.integrable_comp hint
  have hc := TL.integral_comp_comm hint
  change Integrable (fun u =>
    (H.val * (Ring.inverse (R A u) * H.val * Ring.inverse (R A u))).trace.re)
    (volume.restrict (Ioi (0 : ℝ))) at ht
  change (∫ u in Ioi (0 : ℝ),
    (H.val * (Ring.inverse (R A u) * H.val * Ring.inverse (R A u))).trace.re) =
    (H.val * ∫ u in Ioi (0 : ℝ), L u H).trace.re at hc
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, zero_smul, add_zero, Matrix.mul_assoc] using ht
  · dsimp only
    rw [← he H, ContinuousLinearMap.integral_apply hi H]
    simpa only [zero_smul, add_zero, Matrix.mul_assoc] using hc.symm

private lemma entropy_differentiableAt (A : S) (hA : A.val.PosDef) :
    DifferentiableAt ℝ entropy A := by
  have hlog :=
    (MatrixLogResolventDerivative.matrix_log_hasFDerivAt_resolvent A hA).1
  exact (Tr).differentiableAt.comp A
    ((ι).differentiableAt.mul hlog.differentiableAt)

private lemma path_hasDerivAt (A H : S) (v : ℝ) :
    HasDerivAt (P A H) H v := by
  simpa only [one_smul, id_eq] using ((hasDerivAt_id v).smul_const H).const_add A

private lemma entropy_path_hasDerivAt (A H : S) (v : ℝ)
    (hpos : (P A H v).val.PosDef) :
    HasDerivAt (fun w => entropy (P A H w)) (fderiv ℝ entropy (P A H v) H) v := by
  exact (entropy_differentiableAt (P A H v) hpos).hasFDerivAt.comp_hasDerivAt v
    (path_hasDerivAt A H v)

private lemma entropy_path_gradient_hasDerivAt (A H : S) (v : ℝ)
    (hpos : (P A H v).val.PosDef) :
    HasDerivAt (fun w => fderiv ℝ entropy (P A H w) H) (BKM (P A H v) H) v := by
  obtain ⟨hh, heq, _⟩ :=
    MatrixLogResolventDerivative.trace_entropy_hessian_resolvent (P A H v) hpos
  have hc := hh.comp_hasDerivAt v (path_hasDerivAt A H v)
  have ha := hc.clm_apply (hasDerivAt_const v H)
  have hval := heq H H
  rw [hh.fderiv] at hval
  simpa only [Function.comp_def, map_zero, add_zero, hval] using ha

private lemma entropy_remainder (A H : S)
    (hpos : ∀ v ∈ Icc (0 : ℝ) 1, (P A H v).val.PosDef) :
    (entropy (A + H) - entropy A - fderiv ℝ entropy A H =
      ∫ v in (0 : ℝ)..1, (1 - v) * BKM (P A H v) H) ∧
      IntervalIntegrable (fun v => BKM (P A H v) H) volume 0 1 := by
  let f : ℝ → ℝ := fun v => entropy (P A H v)
  let g : ℝ → ℝ := fun v => fderiv ℝ entropy (P A H v) H
  have hf (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g v) v :=
    entropy_path_hasDerivAt A H v (hpos v hv)
  have hg (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g (BKM (P A H v) H) v :=
    entropy_path_gradient_hasDerivAt A H v (hpos v hv)
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    fun v hv => (hg v hv).continuousAt.continuousWithinAt
  have hq : IntervalIntegrable (fun v => BKM (P A H v) H) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (g := g) (by simpa only [uIcc_of_le zero_le_one] using hc)
    · simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using
        (fun v (hv : v ∈ Ioo (0 : ℝ) 1) => hg v ⟨hv.1.le, hv.2.le⟩)
    · simp only [min_eq_left zero_le_one, max_eq_right zero_le_one]
      intro v hv
      have hh := MatrixLogResolventDerivative.trace_entropy_hessian_resolvent
        (P A H v) (hpos v ⟨hv.1.le, hv.2.le⟩)
      rw [← hh.2.1 H H]
      exact hh.2.2 H
  refine ⟨?_, hq⟩
  have hgint : IntervalIntegrable g volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hc
  have hftc : (∫ v in (0 : ℝ)..1, g v) = f 1 - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le zero_le_one] using hf) hgint
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun v : ℝ => 1 - v) (u' := fun _ : ℝ => -1)
    (v := g) (v' := fun v => BKM (P A H v) H)
    (a := (0 : ℝ)) (b := 1)
    (by fun_prop) (by simpa only [uIcc_of_le zero_le_one] using hc)
    (fun v _ => by simpa using (hasDerivAt_id v).const_sub (1 : ℝ))
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using
      (fun v (hv : v ∈ Ioo (0 : ℝ) 1) => hg v ⟨hv.1.le, hv.2.le⟩))
    intervalIntegrable_const hq
  rw [intervalIntegral.integral_const_mul, hftc] at hb
  simp only [f, g, sub_self, sub_zero, zero_mul, one_mul, zero_smul,
    one_smul, add_zero, zero_sub, neg_one_mul] at hb
  linarith

private lemma weighted_resolvent_swap (A H : S) (hA : A.val.PosDef)
    (hr : ‖K A H 0‖ < 1) :
    ((∫ v in (0 : ℝ)..1, (1 - v) * BKM (P A H v) H) =
      ∫ u in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..1, (1 - v) * q A H v u) ∧
      IntegrableOn (fun u => ∫ v in (0 : ℝ)..1, (1 - v) * q A H v u) (Ioi (0 : ℝ)) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ × ℝ → ℝ := fun p => (1 - p.1) * q A H p.1 p.2
  have hp (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : (P A H v).val.PosDef :=
    finite_amplitude_path_posdef A H hA hr v ⟨by linarith [hv.1], hv.2⟩
  have hdata (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      Integrable (fun u => q A H v u) ν ∧ BKM (P A H v) H = ∫ u, q A H v u ∂ν := by
    simpa only [ν, IntegrableOn, zero_smul, add_zero] using
      bkm_eq_integral_trace (P A H v) H (hp v hv)
  have hc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    have hi : ContinuousOn (fun p : ℝ × ℝ => Ring.inverse (R (P A H p.1) p.2))
        (Icc (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
      intro p hp'
      have hunit := ((hp p.1 hp'.1).add_posSemidef
        (Matrix.PosSemidef.one.smul (show 0 < p.2 from hp'.2).le)).isUnit
      have hinv : ContinuousAt Ring.inverse (R (P A H p.1) p.2) := by
        simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt hunit.unit
      apply ContinuousAt.comp_continuousWithinAt
        (f := fun p : ℝ × ℝ => R (P A H p.1) p.2) hinv
      fun_prop
    exact (continuousOn_const.sub continuous_fst.continuousOn).mul
      (Complex.continuous_re.comp_continuousOn <|
        (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.continuous.comp_continuousOn <|
          ((continuousOn_const.mul hi).mul continuousOn_const).mul hi)
  have hmeas : AEStronglyMeasurable F (μ.prod ν) := by
    dsimp only [μ, ν]
    rw [Measure.prod_restrict]
    exact (hc.mono (prod_mono Ioc_subset_Icc_self Subset.rfl)).aestronglyMeasurable
      (measurableSet_Ioc.prod measurableSet_Ioi)
  have hfiber : ∀ᵐ v ∂μ, Integrable (fun u => F (v, u)) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (hdata v ⟨hv.1.le, hv.2⟩).1.const_mul (1 - v)
  have hnorm : ∀ᵐ v ∂μ, (∫ u, ‖F (v, u)‖ ∂ν) = (1 - v) * BKM (P A H v) H := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hd := (hdata v ⟨hv.1.le, hv.2⟩).2
    dsimp only at hd ⊢
    rw [hd, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    apply Real.norm_of_nonneg
    exact mul_nonneg (sub_nonneg.mpr hv.2)
      (resolvent_trace_nonneg A H hA hr v u ⟨by linarith [hv.1], hv.2⟩ hu.le)
  have hw : Integrable (fun v => (1 - v) * BKM (P A H v) H) μ := by
    have hq := (entropy_remainder A H hp).2
    exact (hq.continuousOn_mul (by fun_prop)).1
  have hprod : Integrable F (μ.prod ν) :=
    (integrable_prod_iff hmeas).mpr ⟨hfiber, hw.congr (by
      filter_upwards [hnorm] with v hv using hv.symm)⟩
  have heq : (∫ v in (0 : ℝ)..1, (1 - v) * BKM (P A H v) H) =
      ∫ v, ∫ u, F (v, u) ∂ν ∂μ := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hd := (hdata v ⟨hv.1.le, hv.2⟩).2
    dsimp only at hd ⊢
    rw [hd]
    exact (integral_const_mul (1 - v) _).symm
  have hswap := integral_integral_swap (f := fun v u => F (v, u)) hprod
  have hout := hprod.integral_prod_right
  constructor
  · calc
      _ = ∫ v, ∫ u, F (v, u) ∂ν ∂μ := heq
      _ = _ := by simpa only [F, μ, ν, intervalIntegral.integral_of_le zero_le_one] using hswap
  · simpa only [F, μ, ν, intervalIntegral.integral_of_le zero_le_one, IntegrableOn] using hout

private lemma scalar_weighted_resolvent (k : ℝ) (hk : |k| < 1) :
    (∫ v in (0 : ℝ)..1, (1 - v) * (k ^ 2 / (1 + v * k) ^ 2)) = k - Real.log (1 + k) := by
  let p : Fin 1 → ℝ := fun _ => 1 + k
  let q₀ : Fin 1 → ℝ := fun _ => 1
  let ρ : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal fun i => (p i : ℂ)
  let σ : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal fun i => (q₀ i : ℂ)
  have hp : ∀ i, 0 < p i := fun _ => by dsimp only [p]; linarith [(abs_lt.mp hk).1]
  have hq₀ : ∀ i, 0 < q₀ i := fun _ => zero_lt_one
  have hρ : ρ.PosDef := Matrix.PosDef.diagonal (fun i => by exact_mod_cast hp i)
  have hσ : σ.PosDef := Matrix.PosDef.diagonal (fun i => by exact_mod_cast hq₀ i)
  have he := (D5.S3.Resource.LogDet.PathSpectralClassical.log_det_path_spectral_classical
    ρ σ hρ hσ).1.symm
  rw [D5.S3.Resource.LogDet.PathSpectralClassical.diagonal_logDet_eq_itakuraSaito
    p q₀ hp hq₀] at he
  have hpath : D5.S3.Resource.LogDet.PathSpectralClassical.logDetPathEnergy ρ σ =
      ∫ v in (0 : ℝ)..1, (1 - v) * (k ^ 2 / (1 + v * k) ^ 2) := by
    unfold D5.S3.Resource.LogDet.PathSpectralClassical.logDetPathEnergy
    apply intervalIntegral.integral_congr
    intro v _
    have hs : D5.S3.Resource.LogDet.PathSpectralClassical.affineSegment ρ σ v =
        Matrix.diagonal (fun _ : Fin 1 => ((1 + v * k : ℝ) : ℂ)) := by
      ext i j
      fin_cases i; fin_cases j
      simp [D5.S3.Resource.LogDet.PathSpectralClassical.affineSegment, ρ, σ, p, q₀,
        Matrix.smul_apply, smul_eq_mul]
      ring
    have hΔ : ρ - σ = Matrix.diagonal (fun _ : Fin 1 => (k : ℂ)) := by
      ext i j
      fin_cases i; fin_cases j
      simp [ρ, σ, p, q₀]
    rw [hs, hΔ, Matrix.inv_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp only [Fin.sum_univ_one, Pi.inv_apply, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    congr 1
    ring
  rw [hpath] at he
  simpa [D5.S3.Resource.LogDet.PathSpectralClassical.itakuraSaito, p, q₀] using he

private lemma scalar_even_resolvent (k : ℝ) (hk : |k| < 1) :
    (∫ v in (0 : ℝ)..1, (1 - v) *
      (k ^ 2 / (1 + v * k) ^ 2 + k ^ 2 / (1 - v * k) ^ 2)) =
      -Real.log (1 - k ^ 2) ∧
      IntervalIntegrable (fun v : ℝ => (1 - v) *
        (k ^ 2 / (1 + v * k) ^ 2 + k ^ 2 / (1 - v * k) ^ 2)) volume 0 1 := by
  have hd (v : ℝ) (hv : v ∈ uIcc (0 : ℝ) 1) : 1 + v * k ≠ 0 ∧ 1 - v * k ≠ 0 := by
    rw [uIcc_of_le zero_le_one] at hv
    have hm : |v * k| < 1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg k)
        (by simpa only [abs_of_nonneg hv.1] using hv.2)).trans_lt hk
    constructor <;> linarith [(abs_lt.mp hm).1, (abs_lt.mp hm).2]
  have hp : IntervalIntegrable (fun v : ℝ => (1 - v) * (k ^ 2 / (1 + v * k) ^ 2))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : ContinuousOn (fun v : ℝ => 1 - v) (uIcc (0 : ℝ) 1)).mul
      ((continuousOn_const.div (by fun_prop) (fun v hv => pow_ne_zero 2 (hd v hv).1)))
  have hm : IntervalIntegrable (fun v : ℝ => (1 - v) * (k ^ 2 / (1 - v * k) ^ 2))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : ContinuousOn (fun v : ℝ => 1 - v) (uIcc (0 : ℝ) 1)).mul
      ((continuousOn_const.div (by fun_prop) (fun v hv => pow_ne_zero 2 (hd v hv).2)))
  constructor
  swap
  · simpa only [mul_add] using hp.add hm
  have ep := scalar_weighted_resolvent k hk
  have em := scalar_weighted_resolvent (-k) (by simpa only [abs_neg] using hk)
  simp only [neg_sq, mul_neg, ← sub_eq_add_neg] at em
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add hp hm, ep, em]
  have hkp : 1 + k ≠ 0 := (by linarith [(abs_lt.mp hk).1] : 0 < 1 + k).ne'
  have hkm : 1 - k ≠ 0 := (by linarith [(abs_lt.mp hk).2] : 0 < 1 - k).ne'
  rw [show 1 - k ^ 2 = (1 + k) * (1 - k) by ring, Real.log_mul hkp hkm]
  ring

/-- The symmetric entropy gap is the second-order integral of the two actual BKM
curvatures. No commutativity of the base and direction is assumed. -/
theorem symmetric_entropy_gap_eq_integral_bkm (A H : S)
    (hA : A.val.PosDef) (hr : ‖K A H 0‖ < 1) :
    entropy (A + H) / 2 + entropy (A - H) / 2 - entropy A =
      (∫ v in (0 : ℝ)..1, (1 - v) *
        (BKM (P A H v) H + BKM (P A (-H) v) H)) / 2 := by
  have hpos := finite_amplitude_path_posdef A H hA hr
  have hp : ∀ v ∈ Icc (0 : ℝ) 1, (P A H v).val.PosDef :=
    fun v hv => hpos v ⟨by linarith [hv.1], hv.2⟩
  have hm : ∀ v ∈ Icc (0 : ℝ) 1, (P A (-H) v).val.PosDef := by
    intro v hv
    have heq : P A (-H) v = P A H (-v) := by simp only [smul_neg, neg_smul]
    rw [heq]
    exact hpos (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
  obtain ⟨ep, ip⟩ := entropy_remainder A H hp
  obtain ⟨em, im⟩ := entropy_remainder A (-H) hm
  have hsign (v : ℝ) : BKM (P A (-H) v) (-H) = BKM (P A (-H) v) H := by
    simp only [NegMemClass.coe_neg, D5.S3.Divergence.LogDerivTrace.logDeriv,
      Matrix.mul_neg, Matrix.neg_mul, integral_neg, neg_neg]
  simp_rw [hsign] at em im
  have wcont : ContinuousOn (fun v : ℝ => 1 - v) (uIcc (0 : ℝ) 1) := by fun_prop
  have hsum := intervalIntegral.integral_add (ip.continuousOn_mul wcont)
    (im.continuousOn_mul wcont)
  have heq : (∫ v in (0 : ℝ)..1, (1 - v) *
      (BKM (P A H v) H + BKM (P A (-H) v) H)) =
      (∫ v in (0 : ℝ)..1, (1 - v) * BKM (P A H v) H) +
      (∫ v in (0 : ℝ)..1, (1 - v) * BKM (P A (-H) v) H) := by
    simpa only [mul_add] using hsum
  rw [heq]
  simp only [map_neg, ← sub_eq_add_neg] at em
  linarith

end D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
