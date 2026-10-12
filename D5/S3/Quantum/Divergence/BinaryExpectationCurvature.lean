/- GID: D5/S3/Quantum/Divergence/BinaryExpectationCurvature
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/BinaryExpectationCurvature
   mirror-E: none(waiver:analytic-operator-derivative)
   anchors: [mathlib/module/Mathlib/Analysis/Calculus/Deriv/Basic]
   utility: none
   digest: Actual binary conditional-expectation entropy contracts by the squared scale. -/

import D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  let : CStarAlgebra M := {}
  let e := Unitary.conjStarAlgAut ℂ M V
  have hsa : IsSelfAdjoint (e A.val) := A.property.map e
  change CFC.log (e A.val) = e (CFC.log A.val)
  unfold CFC.log
  symm
  apply StarAlgHomClass.map_cfc e Real.log A.val
    (A.val.finite_real_spectrum.continuousOn _)
    e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional A.property hsa

private lemma trace_conjugation (V : unitary M) (B : M) :
    ((V : M) * B * (star V : M)).trace = B.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

private lemma binary_entropy_even (V : unitary M) (A H : S)
    (hA : (V : M) * A.val * (star V : M) = A.val)
    (hH : (V : M) * H.val * (star V : M) = -H.val) (s : ℝ) :
    entropy (A - s • H) = entropy (A + s • H) := by
  have he : (V : M) * (A + s • H).val * (star V : M) = (A - s • H).val := by
    simp only [Submodule.coe_add, Submodule.coe_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hA, hH,
      smul_neg, sub_eq_add_neg, Submodule.coe_neg]
  have hl := log_conjugation V (A + s • H)
  rw [he] at hl
  have hp : (A - s • H).val * CFC.log (A - s • H).val =
      (V : M) * ((A + s • H).val * CFC.log (A + s • H).val) * (star V : M) := by
    rw [hl, ← he]
    calc
      _ = (V : M) * (A + s • H).val * ((star V : M) * V) *
          CFC.log (A + s • H).val * (star V : M) := by noncomm_ring
      _ = _ := by rw [Unitary.coe_star_mul_self]; noncomm_ring
  change ((A - s • H).val * CFC.log (A - s • H).val).trace.re =
    ((A + s • H).val * CFC.log (A + s • H).val).trace.re
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
        symm
        calc
          _ = (V : M) * H.val * ((star V : M) * V) * CFC.log A.val *
              (star V : M) := by noncomm_ring
          _ = _ := by rw [Unitary.coe_star_mul_self]; noncomm_ring
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
    Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, hz, mul_zero, add_zero]

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

private lemma endpoint_slope_of_square_contraction (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 1) (hs : ∀ s ∈ Icc (0 : ℝ) 1, f s ≤ s ^ 2 * f 1) :
    2 * f 1 ≤ d := by
  let g : ℝ → ℝ := fun s => f s - s ^ 2 * f 1
  have hg := hd.sub (((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (f 1))
  simp only [id_eq, one_pow, mul_one, Nat.cast_ofNat] at hg
  have hg1 : g 1 = 0 := by simp only [g, one_pow, one_mul, sub_self]
  have hn : 0 ≤ d - 2 * f 1 := by
    apply ge_of_tendsto (hg.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds zero_lt_one).filter_mono inf_le_left] with s hs1 hs0
    have hsg : g s ≤ 0 := sub_nonpos.mpr (hs s ⟨hs0.le, hs1.le⟩)
    rw [slope_def_field]
    change 0 ≤ (g s - g 1) / (s - 1)
    rw [hg1, sub_zero]
    exact div_nonneg_of_nonpos hsg (sub_nonpos.mpr hs1.le)
  linarith

private lemma binary_trace_zero (V : unitary M) (H : S)
    (hH : (V : M) * H.val * (star V : M) = -H.val) : H.val.trace.re = 0 := by
  have ht := congrArg Complex.re (trace_conjugation V H.val)
  rw [hH, Matrix.trace_neg, Complex.neg_re] at ht
  linarith

/-- At a positive definite endpoint, the entropy-production pairing is at least
twice the binary relative-entropy defect. -/
theorem binary_endpoint_derivative_lower_bound (V : unitary M) (A H : S)
    (hfixed : (V : M) * A.val * (star V : M) = A.val)
    (hflip : (V : M) * H.val * (star V : M) = -H.val)
    (hA : 0 ≤ A.val) (hp : (A + H).val.PosDef) (hm : 0 ≤ (A - H).val) :
    2 * D (A + H) A ≤ (H.val * CFC.log (A + H).val).trace.re := by
  let f : ℝ → ℝ := fun v => entropy (A + v • H) - entropy A
  have hd := MatrixLogResolventDerivative.trace_entropy_hasFDerivAt (A + H) hp
  have hpath : HasDerivAt (fun v : ℝ => A + v • H) H 1 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (1 : ℝ)).smul_const H).const_add A
  have hd' : HasDerivAt f (H.val * CFC.log (A + H).val).trace.re 1 := by
    have hd1 : HasFDerivAt (𝕜 := ℝ) entropy (fderiv ℝ entropy (A + H))
        (A + (1 : ℝ) • H) := by
      simpa only [one_smul] using hd.differentiableAt.hasFDerivAt
    have h := (hd1.comp_hasDerivAt (1 : ℝ) hpath).sub_const
      (entropy A)
    rw [hd.fderiv] at h
    change HasDerivAt f (H.val * (CFC.log (A + H).val + 1)).trace.re 1 at h
    simpa only [Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Complex.add_re,
      binary_trace_zero V H hflip, add_zero] using h
  have hc (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : f v ≤ v ^ 2 * f 1 := by
    have h := binary_entropy_square_contraction V A H hfixed hflip hA hp.posSemidef.nonneg hm v hv
    rw [binary_defect_eq_entropy_difference V A H hfixed hflip v,
      show D (A + H) A = entropy (A + H) - entropy A by
        simpa only [one_smul] using
          binary_defect_eq_entropy_difference V A H hfixed hflip 1] at h
    simpa only [f, one_smul] using h
  have h := endpoint_slope_of_square_contraction f _ hd' hc
  rw [show D (A + H) A = f 1 by
    simpa only [f, one_smul] using binary_defect_eq_entropy_difference V A H hfixed hflip 1]
  exact h

/-- For a self-adjoint unitary, the reference is the actual binary conditional
expectation of the input. The estimate allows every positive semidefinite input. -/
theorem binary_expectation_entropy_bounds (V : unitary M)
    (hV : IsSelfAdjoint (V : M)) (rho : S) (hrho : 0 ≤ rho.val)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    let sigma : M := (1 / 2 : ℝ) • (rho.val + (V : M) * rho.val * (star V : M))
    let output : M := s • rho.val + (1 - s) • sigma
    (output * (CFC.log output - CFC.log sigma)).trace.re ≤
      s ^ 2 * (rho.val * (CFC.log rho.val - CFC.log sigma)).trace.re ∧
    (rho.val.PosDef → 2 * (rho.val * (CFC.log rho.val - CFC.log sigma)).trace.re ≤
      ((rho.val - sigma) * CFC.log rho.val).trace.re) := by
  let e := Unitary.conjStarAlgAut ℂ M V
  let C : S := ⟨e rho.val, rho.property.map e⟩
  let A : S := (1 / 2 : ℝ) • (rho + C)
  let H : S := rho - A
  have hVV : (V : M) * (V : M) = 1 := by
    simpa only [hV.star_eq] using Unitary.coe_star_mul_self V
  have hCC : (V : M) * C.val * (star V : M) = rho.val := by
    dsimp only [C, e, Unitary.conjStarAlgAut_apply]
    rw [show (star V : M) = (V : M) from hV.star_eq]
    calc
      _ = ((V : M) * V) * rho.val * ((V : M) * V) := by noncomm_ring
      _ = _ := by rw [hVV]; simp only [Matrix.one_mul, Matrix.mul_one]
  have hfixed : (V : M) * A.val * (star V : M) = A.val := by
    dsimp only [A, Submodule.coe_smul, Submodule.coe_add]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hCC]
    change (1 / 2 : ℝ) • (C.val + rho.val) = (1 / 2 : ℝ) • (rho.val + C.val)
    rw [add_comm]
  have hflip : (V : M) * H.val * (star V : M) = -H.val := by
    change (V : M) * (rho.val - A.val) * (star V : M) = -(rho.val - A.val)
    rw [Matrix.mul_sub, Matrix.sub_mul, hfixed]
    change C.val - A.val = -(rho.val - A.val)
    dsimp only [A, Submodule.coe_smul, Submodule.coe_add]
    module
  have hC0 : 0 ≤ C.val := by
    apply Matrix.PosSemidef.nonneg
    change ((V : M) * rho.val * (star V : M)).PosSemidef
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      (Matrix.nonneg_iff_posSemidef.mp hrho).conjTranspose_mul_mul_same (star V : M)
  have hA0 : 0 ≤ A.val := by
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (add_nonneg hrho hC0)
  have hp : (A + H).val = rho.val := by
    change (A + (rho - A)).val = rho.val
    congr 1
    abel
  have hm : (A - H).val = C.val := by
    change (A - (rho - A)).val = C.val
    congr 1
    dsimp only [A]
    module
  have hc := binary_entropy_square_contraction V A H hfixed hflip hA0
    (hp.symm ▸ hrho) (hm.symm ▸ hC0) s hs
  have houtput : (A + s • H).val = s • rho.val + (1 - s) • A.val := by
    change (A + s • (rho - A)).val = (s • rho + (1 - s) • A).val
    congr 1
    module
  change ((A + s • H).val * (CFC.log (A + s • H).val - CFC.log A.val)).trace.re ≤
    s ^ 2 * ((A + H).val * (CFC.log (A + H).val - CFC.log A.val)).trace.re at hc
  rw [hp, houtput] at hc
  constructor
  · simpa only [hp, houtput, A, C, e, Submodule.coe_smul, Submodule.coe_add,
      Unitary.conjStarAlgAut_apply] using hc
  · intro hpos
    have hd := binary_endpoint_derivative_lower_bound V A H hfixed hflip hA0
      (hp.symm ▸ hpos) (hm.symm ▸ hC0)
    change 2 * ((A + H).val * (CFC.log (A + H).val - CFC.log A.val)).trace.re ≤
      (H.val * CFC.log (A + H).val).trace.re at hd
    rw [hp] at hd
    simpa only [H, A, C, e, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add,
      Unitary.conjStarAlgAut_apply] using hd


end D5.S3.Quantum.Divergence.BinaryExpectationCurvature
