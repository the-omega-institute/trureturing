/- GID: D5/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   mirror-E: none(waiver:analytic-integral-identity)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts]
   utility: none
   digest: Symmetric finite differences of trace entropy along Hermitian matrix paths. -/

import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
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
