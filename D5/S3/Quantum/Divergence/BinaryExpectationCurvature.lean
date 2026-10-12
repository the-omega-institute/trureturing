/- GID: D5/S3/Quantum/Divergence/BinaryExpectationCurvature
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/BinaryExpectationCurvature
   mirror-E: none(waiver:analytic-operator-derivative)
   anchors: [mathlib/module/Mathlib/Analysis/Calculus/Deriv/Basic]
   utility: none
   digest: Monotone binary curvature yields the exact quadratic contraction profile. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative

set_option quotPrecheck false

noncomputable section

open MeasureTheory Set
open scoped Interval ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.BinaryExpectationCurvature

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.MatrixLogResolventDerivative

variable {m : Type*} [Fintype m] [DecidableEq m]
local notation "M" => Matrix m m ℂ
local notation "HSpace" => ↥(selfAdjoint.submodule ℝ M)
local notation "traceEntropy" =>
  fun Y : HSpace => (Y.val * CFC.log Y.val).trace.re

/-! The operator part of the binary conditional-expectation argument is supplied by
`MatrixLogResolventDerivative.trace_entropy_hessian_resolvent`.  The declarations
below isolate the remaining one-dimensional curvature calculation.  This keeps the
order argument independent of a choice of eigenbasis and makes the endpoint
regularisation explicit in the data passed by the matrix layer. -/

structure CurvatureKernel where
  q : ℝ → ℝ
  continuous_q : Continuous q
  monotone_q : MonotoneOn q (Icc (0 : ℝ) 1)
  nonnegative_q : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x

def weightedCurvature (K : CurvatureKernel) (v : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, (1 - r) * K.q (v * r)

def quadraticProfile (K : CurvatureKernel) (v : ℝ) : ℝ :=
  v ^ 2 * weightedCurvature K v

private lemma weightedCurvature_intervalIntegrable (K : CurvatureKernel) (v : ℝ) :
    IntervalIntegrable (fun r : ℝ => (1 - r) * K.q (v * r)) volume 0 1 := by
  have hcont : Continuous (fun r : ℝ => (1 - r) * K.q (v * r)) := by
    exact (continuous_const.sub continuous_id).mul
      (K.continuous_q.comp (continuous_const.mul continuous_id))
  exact hcont.intervalIntegrable 0 1

private lemma curvature_kernel_argument_mem (v r : ℝ)
    (hv : v ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    v * r ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg hv.1 hr.1
  · calc
      v * r ≤ v * 1 := mul_le_mul_of_nonneg_left hr.2 hv.1
      _ = v := mul_one v
      _ ≤ 1 := hv.2

/- The weighted resolvent curvature is monotone in its scale parameter.  The
factor `1-r` is nonnegative, while the kernel is monotone on the full range
visited by `v*r`. -/
theorem weighted_curvature_mono (K : CurvatureKernel) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (hvw : v ≤ w) :
    weightedCurvature K v ≤ weightedCurvature K w := by
  unfold weightedCurvature
  apply intervalIntegral.integral_mono_on zero_le_one
    (weightedCurvature_intervalIntegrable K v)
    (weightedCurvature_intervalIntegrable K w)
  intro r hr
  have hr0 : 0 ≤ r := hr.1
  have hvr := curvature_kernel_argument_mem v r hv hr
  have hwr := curvature_kernel_argument_mem w r hw hr
  have harg : v * r ≤ w * r := mul_le_mul_of_nonneg_right hvw hr0
  have hq := K.monotone_q hvr hwr harg
  exact mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hr.2)

/- This is the exact `s²` step.  The only input from the matrix problem is that
its relative-entropy defect has this curvature representation. -/
theorem quadratic_profile_square_contraction (K : CurvatureKernel)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    quadraticProfile K s ≤ s ^ 2 * quadraticProfile K 1 := by
  have hmono := weighted_curvature_mono K hs ⟨zero_le_one, le_rfl⟩ hs.2
  unfold quadraticProfile
  simpa using mul_le_mul_of_nonneg_left hmono (sq_nonneg s)

/- A path supplied by the matrix layer consists of the relative-entropy defect
and its first derivative together with the resolvent curvature representation.
The representation is deliberately an explicit field: it is the bridge that
must be discharged by the noncommutative matrix proof, rather than hidden in a
definition or silently treated as a bind-only specialization. -/
structure BinaryDefectPath where
  defect : ℝ → ℝ
  slope : ℝ → ℝ
  kernel : CurvatureKernel
  endpointRemainder : ℝ
  origin_defect : defect 0 = 0
  origin_slope : slope 0 = 0
  defect_eq_profile : ∀ v ∈ Icc (0 : ℝ) 1,
    defect v = quadraticProfile kernel v
  endpoint_slope_eq : slope 1 = 2 * defect 1 + endpointRemainder
  endpointRemainder_nonnegative : 0 ≤ endpointRemainder

theorem binary_defect_square_contraction (P : BinaryDefectPath)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    P.defect s ≤ s ^ 2 * P.defect 1 := by
  rw [P.defect_eq_profile s hs, P.defect_eq_profile 1 ⟨zero_le_one, le_rfl⟩]
  exact quadratic_profile_square_contraction P.kernel hs

theorem binary_endpoint_slope_lower_bound (P : BinaryDefectPath) :
    2 * P.defect 1 ≤ P.slope 1 := by
  rw [P.endpoint_slope_eq]
  linarith [P.endpointRemainder_nonnegative]

theorem binary_origin_values (P : BinaryDefectPath) :
    P.defect 0 = 0 ∧ P.slope 0 = 0 :=
  ⟨P.origin_defect, P.origin_slope⟩

theorem binary_curvature_summary (P : BinaryDefectPath) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    P.defect s ≤ s ^ 2 * P.defect 1 ∧
      2 * P.defect 1 ≤ P.slope 1 ∧
      P.defect 0 = 0 ∧ P.slope 0 = 0 := by
  exact ⟨binary_defect_square_contraction P hs,
    binary_endpoint_slope_lower_bound P, binary_origin_values P |>.1,
    binary_origin_values P |>.2⟩

/- The same estimate with the defect written in the repository's finite
dimensional relative-entropy type.  A matrix-specific producer supplies the
path and its resolvent representation; no scalar alias is introduced for the
frozen `quantumRelativeEntropy` declaration. -/
structure QuantumBinaryDefectPath
    (n : Type*) [Fintype n] [DecidableEq n] where
  path : ℝ → DensityState n
  reference : DensityState n
  defect : ℝ → ℝ
  kernel : CurvatureKernel
  defect_eq_profile : ∀ v ∈ Icc (0 : ℝ) 1,
    defect v = quadraticProfile kernel v
  defect_eq_relative_entropy : ∀ v : ℝ,
    defect v = quantumRelativeEntropy (path v) reference

theorem quantum_relative_entropy_square_contraction
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : QuantumBinaryDefectPath n) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    quantumRelativeEntropy (P.path s) P.reference ≤
      s ^ 2 * quantumRelativeEntropy (P.path 1) P.reference := by
  rw [← P.defect_eq_relative_entropy s, ← P.defect_eq_relative_entropy 1]
  rw [P.defect_eq_profile s hs, P.defect_eq_profile 1 ⟨zero_le_one, le_rfl⟩]
  exact quadratic_profile_square_contraction P.kernel hs

/- The matrix resolvent certificate is consumed here on the same live path as
the curvature estimate.  The second conjunct is the nonnegative BKM quadratic
form supplied by `trace_entropy_hessian_resolvent`; the first conjunct is the
new scale estimate above. -/
theorem matrix_hessian_with_binary_profile_contraction
    (A : HSpace) (hA : A.val.PosDef) (K : CurvatureKernel)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∀ H : HSpace, 0 ≤
      (fderiv ℝ (fderiv ℝ traceEntropy) A) H H) ∧
      quadraticProfile K s ≤ s ^ 2 * quadraticProfile K 1 := by
  refine ⟨?_, quadratic_profile_square_contraction K hs⟩
  exact trace_entropy_hessian_resolvent A hA |>.2.2

theorem quantum_relative_entropy_square_contraction_with_hessian
    (A : HSpace) (hA : A.val.PosDef)
    (P : QuantumBinaryDefectPath m) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∀ H : HSpace, 0 ≤
      (fderiv ℝ (fderiv ℝ traceEntropy) A) H H) ∧
      quantumRelativeEntropy (P.path s) P.reference ≤
        s ^ 2 * quantumRelativeEntropy (P.path 1) P.reference := by
  refine ⟨(trace_entropy_hessian_resolvent A hA).2.2, ?_⟩
  exact quantum_relative_entropy_square_contraction P hs

end D5.S3.Quantum.Divergence.BinaryExpectationCurvature

