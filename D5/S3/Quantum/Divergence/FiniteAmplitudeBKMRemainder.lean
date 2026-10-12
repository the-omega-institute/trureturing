/- GID: D5/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder
   mirror-E: none(waiver:analytic-integral-identity)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts]
   utility: none
   digest: Symmetric finite differences of trace entropy along Hermitian matrix paths. -/

import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

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
  simpa only [one_smul] using ((hasDerivAt_id v).smul_const H).const_add A

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
  simpa only [ContinuousLinearMap.zero_apply, add_zero, hval] using ha

end D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
