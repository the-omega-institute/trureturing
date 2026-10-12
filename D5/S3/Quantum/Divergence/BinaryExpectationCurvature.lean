/- GID: D5/S3/Quantum/Divergence/BinaryExpectationCurvature
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/BinaryExpectationCurvature
   mirror-E: none(waiver:analytic-operator-derivative)
   anchors: [mathlib/module/Mathlib/Analysis/Calculus/Deriv/Basic]
   utility: none
   digest: Actual binary conditional-expectation entropy contracts by the squared scale. -/

import D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder

set_option quotPrecheck false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace

namespace D5.S3.Quantum.Divergence.BinaryExpectationCurvature

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)
local notation "entropy" => fun Y : S => (Y.val * CFC.log Y.val).trace.re
local notation "D" => fun (B A : S) => (B.val * (CFC.log B.val - CFC.log A.val)).trace.re

private lemma log_conjugation (V : unitary M) (A : S) :
    CFC.log ((V : M) * A.val * (star V : M)) =
      (V : M) * CFC.log A.val * (star V : M) := by
  let e := Unitary.conjStarAlgAut ℂ M V
  have hsa : IsSelfAdjoint (e A.val) := A.property.map e
  simpa only [e, Unitary.conjStarAlgAut_apply, CFC.log] using
    (StarAlgHomClass.map_cfc e Real.log A.val
      (A.val.finite_real_spectrum.continuousOn _) (by fun_prop) A.property hsa).symm

private lemma trace_conjugation (V : unitary M) (B : M) :
    ((V : M) * B * (star V : M)).trace = B.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

private lemma binary_entropy_even (V : unitary M) (A H : S)
    (hA : (V : M) * A.val * (star V : M) = A.val)
    (hH : (V : M) * H.val * (star V : M) = -H.val) (s : ℝ) :
    entropy (A - s • H) = entropy (A + s • H) := by
  have he : (V : M) * (A + s • H).val * (star V : M) = (A - s • H).val := by
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hA, hH,
      smul_neg, sub_eq_add_neg]
  have hl := log_conjugation V (A + s • H)
  rw [he] at hl
  have hp : (A - s • H).val * CFC.log (A - s • H).val =
      (V : M) * ((A + s • H).val * CFC.log (A + s • H).val) * (star V : M) := by
    rw [← he, hl]
    calc
      _ = (V : M) * (A + s • H).val * ((star V : M) * V) *
          CFC.log (A + s • H).val * (star V : M) := by noncomm_ring
      _ = _ := by rw [Unitary.coe_star_mul_self]; noncomm_ring
  change (_).trace.re = (_).trace.re
  rw [hp, trace_conjugation]

private lemma binary_trace_log_zero (V : unitary M) (A H : S)
    (hA : (V : M) * A.val * (star V : M) = A.val)
    (hH : (V : M) * H.val * (star V : M) = -H.val) :
    (H.val * CFC.log A.val).trace.re = 0 := by
  have hl := log_conjugation V A
  rw [hA] at hl
  have he : (V : M) * (H.val * CFC.log A.val) * (star V : M) =
      -(H.val * CFC.log A.val) := by
    calc
      _ = ((V : M) * H.val * (star V : M)) *
          ((V : M) * CFC.log A.val * (star V : M)) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (star V : M),
          Unitary.coe_star_mul_self]
        noncomm_ring
      _ = _ := by rw [hH, ← hl, Matrix.neg_mul]
  have ht := congrArg Complex.re (trace_conjugation V (H.val * CFC.log A.val))
  rw [he, Matrix.trace_neg, Complex.neg_re] at ht
  linarith

private lemma binary_defect_eq_entropy_difference (V : unitary M) (A H : S)
    (hA : (V : M) * A.val * (star V : M) = A.val)
    (hH : (V : M) * H.val * (star V : M) = -H.val) (s : ℝ) :
    D (A + s • H) A = entropy (A + s • H) - entropy A := by
  have hz := binary_trace_log_zero V A H hA hH
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  congr 1
  simp only [Submodule.coe_add, Submodule.coe_smul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.real_smul, hz, mul_zero, add_zero]

/-- The binary entropy defect contracts by `s²` for every finite dimension,
including singular positive semidefinite endpoints. -/
theorem binary_entropy_square_contraction (V : unitary M) (A H : S)
    (hfixed : (V : M) * A.val * (star V : M) = A.val)
    (hflip : (V : M) * H.val * (star V : M) = -H.val)
    (hA : 0 ≤ A.val) (hp : 0 ≤ (A + H).val) (hm : 0 ≤ (A - H).val)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    D (A + s • H) A ≤ s ^ 2 * D (A + H) A := by
  have h := FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_square_contraction_psd
    A H hA hp hm s hs
  rw [binary_entropy_even V A H hfixed hflip s,
    show entropy (A - H) = entropy (A + H) by
      simpa only [one_smul] using binary_entropy_even V A H hfixed hflip 1] at h
  rw [binary_defect_eq_entropy_difference V A H hfixed hflip s,
    show D (A + H) A = entropy (A + H) - entropy A by
      simpa only [one_smul] using binary_defect_eq_entropy_difference V A H hfixed hflip 1]
  linarith

end D5.S3.Quantum.Divergence.BinaryExpectationCurvature
