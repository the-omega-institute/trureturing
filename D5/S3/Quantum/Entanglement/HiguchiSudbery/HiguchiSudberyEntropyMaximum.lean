/- GID: D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp average two-qubit entropy bound for all normalized four-qubit states. -/

/-
proof_shape: result: content
escape_witness: D5.S3.Quantum.Entanglement.HiguchiSudbery.double_contact_nonnegative: a nonnegative fourth
  derivative and two double zeros force nonnegativity on the positive half-line.
  The resulting cubic negMulLog majorant is used in the live entropy estimate.
admission_basis: escape-witness
Direct frozen dependencies of result:
  D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber.squaredAmplitudeTotal
  (owner: D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.HiguchiSudbery.PrimeHierarchyCertificate
import D5.S3.Quantum.Entanglement.HiguchiSudbery.ReflectionEvaluation
import D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation

noncomputable section
namespace D5.S3.Quantum.Entanglement.HiguchiSudbery

open Matrix Real Polynomial
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 0
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open private prime_certificate_identity
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.PrimeHierarchyCertificate
open private totalMinorE3 spectrum_e3_eq_minors cutSpectrum hs4_of_spectral_e3
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly
open private ref_lhs ref_rhs from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private ref_vars from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private ref_eval from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private ref_eval_rhs_nonneg ref_eval_lhs
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.ReflectionEvaluation
open private log_half log_sixth from D5.S3.Quantum.Entanglement.HiguchiSudbery.HermiteEntropy
open private cut_positive cut_entropy_spectral from D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly
open private squaredAmplitudeTotal
  from D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber

private lemma e3_bound_of_certificate /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.result -/ (z : Fin 16 → ℂ)
    (hcert : ref_eval (ref_vars z) ref_lhs = ref_eval (ref_vars z) ref_rhs) :
    totalMinorE3 z ≤ (5/36) * squaredAmplitudeTotal 15 z ^ 3 := by
  have h := ref_eval_rhs_nonneg z
  rw [← hcert, ref_eval_lhs] at h
  simp only [Complex.ofReal_re] at h
  linarith

def M4 (i : Fin 16) : ℂ :=
  1 / (Real.sqrt 6 : ℂ) *
    (if i=3 ∨ i=12 then 1 else if i=5 ∨ i=10 then (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3)
      else if i=6 ∨ i=9 then (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3)^2 else 0)

private lemma omega_value /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.omega_sq_conj -/ : (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3) = (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2 := by
  unfold D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega
  norm_num only [Nat.cast_ofNat]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

private lemma omega_sq_conj /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_apply -/ : (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3)^2 = star (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  apply Complex.ext <;>
    norm_num [omega_value, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def] <;> nlinarith

private lemma M4_apply /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_unit -/ (i : Fin 16) : M4 i =
    if i=3 ∨ i=12 then (Real.sqrt (1/6) : ℂ)
    else if i=5 ∨ i=10 then (Real.sqrt (1/6) : ℂ)*(D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3)
    else if i=6 ∨ i=9 then (Real.sqrt (1/6) : ℂ)*star (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3) else 0 := by
  have he : (Real.sqrt (1/6) : ℂ) = 1 / (Real.sqrt 6 : ℂ) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
    push_cast
    rfl
  simp only [M4, he, omega_sq_conj]
  split_ifs <;> simp

private def M4Marginal : Matrix (Fin 4) (Fin 4) ℂ := fun r s =>
  if r=s then if r=1 ∨ r=2 then 1/3 else 1/6
  else if (r=1 ∧ s=2) ∨ (r=2 ∧ s=1) then -1/6 else 0

private def M4Spectrum (i : Fin 4) : ℝ := if i=0 then 1/2 else 1/6

private lemma omega_normSq /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_unit -/ : Complex.normSq (D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.omega 3) = 1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  norm_num [omega_value, Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im] <;> nlinarith

private lemma M4_unit /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_entropy -/ : squaredAmplitudeTotal 15 M4 = 1 := by
  norm_num (config := { decide := true }) [squaredAmplitudeTotal, M4_apply, Fin.sum_univ_succ, Complex.normSq_mul, omega_normSq,
    Complex.normSq_ofReal]

set_option Elab.async false in
private lemma M4_cut_zero /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_cuts -/ : cutMatrix M4 0 = M4Marginal := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  ext r s
  fin_cases r <;> fin_cases s
  all_goals
    apply Complex.ext
    all_goals
      norm_num (config := { decide := true }) [Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, cutMatrix,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, Matrix.vecMulVec,
        cutFlatten, cutIndex, M4_apply, M4Marginal, omega_value, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.div_re, Complex.div_im] <;>
        ring_nf <;> norm_num [h3, h6]

set_option Elab.async false in
private lemma M4_cut_one /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_cuts -/ : cutMatrix M4 1 = M4Marginal := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  ext r s
  fin_cases r <;> fin_cases s
  all_goals
    apply Complex.ext
    all_goals
      norm_num (config := { decide := true }) [Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, cutMatrix,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, Matrix.vecMulVec,
        cutFlatten, cutIndex, M4_apply, M4Marginal, omega_value, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.div_re, Complex.div_im] <;>
        ring_nf <;> norm_num [h3, h6]

set_option Elab.async false in
private lemma M4_cut_two /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_cuts -/ : cutMatrix M4 2 = M4Marginal := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  ext r s
  fin_cases r <;> fin_cases s
  all_goals
    apply Complex.ext
    all_goals
      norm_num (config := { decide := true }) [Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, cutMatrix,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, Matrix.vecMulVec,
        cutFlatten, cutIndex, M4_apply, M4Marginal, omega_value, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.div_re, Complex.div_im] <;>
        ring_nf <;> norm_num [h3, h6]

private lemma M4_cuts /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_entropy -/ (c : Fin 3) : cutMatrix M4 c = M4Marginal := by
  fin_cases c
  · exact M4_cut_zero
  · exact M4_cut_one
  · exact M4_cut_two

private lemma M4_charpoly /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_entropy -/ : M4Marginal.charpoly = ∏ i, (X-Polynomial.C (M4Spectrum i : ℂ)) := by
  have h13 : Polynomial.C (1/3 : ℂ) = 2*Polynomial.C (1/6 : ℂ) := by
    have h : (1/3 : ℂ) = 2*(1/6) := by norm_num
    rw [h, map_mul, Polynomial.C_ofNat]
  have h12 : Polynomial.C (1/2 : ℂ) = 3*Polynomial.C (1/6 : ℂ) := by
    have h : (1/2 : ℂ) = 3*(1/6) := by norm_num
    rw [h, map_mul, Polynomial.C_ofNat]
  rw [Matrix.charpoly, Matrix.det_succ_column_zero]
  norm_num (config := { decide := true }) [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, M4Marginal,
    Matrix.submatrix, Matrix.det_fin_three, Fin.sum_univ_succ,
    M4Spectrum, Fin.prod_univ_succ]
  rw [h13, h12]
  ring

private lemma M4_entropy /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.result -/ : averageEntropy M4 M4_unit = 1+(1/2)*logb 2 3 := by
  have hc (c : Fin 3) : (∑ i, negMulLog (cutSpectrum M4 c i)) =
      ∑ i, negMulLog (M4Spectrum i) := by
    unfold cutSpectrum
    exact spectral_sum_eq_of_charpoly_prod (cut_positive M4 c).isHermitian
      M4Spectrum negMulLog (by rw [M4_cuts]; exact M4_charpoly)
  unfold averageEntropy
  simp only [cut_entropy_spectral, hc]
  norm_num (config := { decide := true }) [M4Spectrum, Fin.sum_univ_succ, negMulLog, log_sixth, log_half, logb]
  have hl : log 2 ≠ 0 := (log_pos (by norm_num)).ne'
  field_simp
  ring


/-- The average entropy of the literal AB, AC and AD cuts is bounded sharply,
and the bound is attained at the explicit Higuchi–Sudbery amplitude vector. -/
def claim : Prop :=
  (∀ (z : Fin 16 → ℂ) (hz : (∑ i, Complex.normSq (z i)) = 1),
    averageEntropy z hz ≤ 1 + (1/2)*Real.logb 2 3) ∧
  (∃ hM : (∑ i, Complex.normSq (M4 i)) = 1,
    averageEntropy M4 hM = 1 + (1/2)*Real.logb 2 3)

theorem result : claim := by
  constructor
  · intro z hz
    change squaredAmplitudeTotal 15 z = 1 at hz
    have hminor : totalMinorE3 z ≤ (5/36) * squaredAmplitudeTotal 15 z ^ 3 :=
      e3_bound_of_certificate z (prime_certificate_identity z)
    have hspectral : (∑ c, (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (cutSpectrum z c)) ≤ 5/36 := by
      rw [spectrum_e3_eq_minors z hz]
      simpa only [hz, one_pow, mul_one] using hminor
    exact hs4_of_spectral_e3 z hz hspectral
  · exact ⟨M4_unit, M4_entropy⟩

end D5.S3.Quantum.Entanglement.HiguchiSudbery

#print axioms D5.S3.Quantum.Entanglement.HiguchiSudbery.result
