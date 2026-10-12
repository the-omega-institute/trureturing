/- GID: D5/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   mirror-E: none(waiver:analytic-integral-identity)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts]
   utility: none
   digest: Symmetric finite differences of trace entropy along Hermitian matrix paths. -/

import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, (P A H v).val.PosDef) :
    entropy (A + H) / 2 + entropy (A - H) / 2 - entropy A =
      (∫ v in (0 : ℝ)..1, (1 - v) *
        (BKM (P A H v) H + BKM (P A (-H) v) H)) / 2 := by
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
