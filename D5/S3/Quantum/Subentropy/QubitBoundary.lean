/- GID: D5/S3/Quantum/Subentropy/QubitBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/QubitBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quantitative determinant remainder for qubit subentropy at the pure boundary. -/

import D5.S3.Quantum.Subentropy.DensityKernel

/-! The determinant controls the first-order pure-boundary behavior of qubit subentropy. -/

noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators Topology ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Subentropy.QubitBoundary

open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.DensityKernel

private theorem qubit_kernel {A : Matrix (Fin 2) (Fin 2) ℂ} (htr : A.trace = 1)
    (hδ : 0 ≤ A.det.re) {t : ℝ} (ht : 0 < t) :
    subentropyKernel A t = A.det.re * t / ((1 + t) * (t ^ 2 + t + A.det.re)) := by
  have htrace : A 0 0 + A 1 1 = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htr
  have hd : (1 + (t⁻¹ : ℝ) • A).det =
      ((1 + t⁻¹ : ℝ) : ℂ) + ((t⁻¹ ^ 2 : ℝ) : ℂ) * A.det := by
    simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.one_apply,
      Matrix.smul_apply, Complex.real_smul]
    push_cast
    linear_combination (t⁻¹ : ℂ) * htrace
  have hdpos : 0 < t ^ 2 + t + A.det.re := by positivity
  have hre : (1 + (t⁻¹ : ℝ) • A).det.re = (t ^ 2 + t + A.det.re) / t ^ 2 := by
    rw [hd]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    field_simp
    <;> ring
  unfold subentropyKernel
  rw [hre]
  field_simp
  <;> ring

private theorem remainder_kernel_bounds {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (ht : 0 < t) :
    0 ≤ δ / (1 + t) ^ 2 - δ * t / ((1 + t) * (t ^ 2 + t + δ)) ∧
    δ / (1 + t) ^ 2 - δ * t / ((1 + t) * (t ^ 2 + t + δ)) ≤
      (δ ^ 2 / (1 - δ)) * (1 / (t + δ) - 1 / (t + 1)) := by
  have hp : 0 < t ^ 2 + t + δ := by positivity
  have he : δ / (1 + t) ^ 2 - δ * t / ((1 + t) * (t ^ 2 + t + δ)) =
      δ ^ 2 / ((1 + t) ^ 2 * (t ^ 2 + t + δ)) := by
    field_simp
    ring
  have hg : (δ ^ 2 / (1 - δ)) * (1 / (t + δ) - 1 / (t + 1)) =
      δ ^ 2 / ((t + δ) * (t + 1)) := by
    have : 1 - δ ≠ 0 := by linarith
    field_simp
    ring
  rw [he, hg]
  refine ⟨by positivity, ?_⟩
  apply div_le_div_of_nonneg_left (sq_nonneg δ) (by positivity)
  have hdiff : (1 + t) ^ 2 * (t ^ 2 + t + δ) - (t + δ) * (t + 1) =
      t * (t + 1) * (t ^ 2 + 2 * t + δ) := by ring
  have : 0 ≤ (1 + t) ^ 2 * (t ^ 2 + t + δ) - (t + δ) * (t + 1) := by
    rw [hdiff]
    positivity
  linarith

/-- For every qubit density matrix, the determinant lies in [0,1/4]. At zero
it has zero subentropy. At positive determinant the deficit from the determinant
is nonnegative and at most delta squared times log(1/delta)/(1-delta). -/
theorem qubit_subentropy_near_pure (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) (htr : A.trace = 1) :
    let δ := A.det.re
    0 ≤ δ ∧ δ ≤ 1 / 4 ∧
      (δ = 0 → matrixSubentropy A = 0) ∧
      (0 < δ → 0 ≤ δ - matrixSubentropy A ∧
        δ - matrixSubentropy A ≤ δ ^ 2 * Real.log (1 / δ) / (1 - δ)) := by
  dsimp only
  obtain ⟨hp, hs⟩ := spectral_prob hA htr
  have hs' : hA.isHermitian.eigenvalues 0 + hA.isHermitian.eigenvalues 1 = 1 := by
    simpa only [Fin.sum_univ_two] using hs
  have hd : A.det.re = hA.isHermitian.eigenvalues 0 * hA.isHermitian.eigenvalues 1 := by
    have h := congrArg Complex.re hA.isHermitian.det_eq_prod_eigenvalues
    simpa [Fin.prod_univ_two] using h
  have hδ : 0 ≤ A.det.re := by rw [hd]; exact mul_nonneg (hp 0) (hp 1)
  have hδ4 : A.det.re ≤ 1 / 4 := by
    rw [hd]
    nlinarith [sq_nonneg (hA.isHermitian.eigenvalues 0 - hA.isHermitian.eigenvalues 1)]
  refine ⟨hδ, hδ4, ?_, ?_⟩
  · intro hz
    unfold matrixSubentropy
    have he : ∀ t ∈ Ioi (0 : ℝ), subentropyKernel A t = 0 := by
      intro t ht
      rw [qubit_kernel htr hδ ht, hz]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi he]
    simp
  · intro hδpos
    have hδ1 : A.det.re < 1 := by linarith
    have hf : IntegrableOn (fun t : ℝ => A.det.re / (1 + t) ^ 2) (Ioi 0) := by
      simpa [IntegrableOn, div_eq_mul_inv, add_comm] using
        ((UniformIntegrals.inverse_power 1 (by norm_num) 0).1.const_mul A.det.re)
    have hv : (∫ t in Ioi (0 : ℝ), A.det.re / (1 + t) ^ 2) = A.det.re := by
      have h := (UniformIntegrals.inverse_power 1 (by norm_num) 0).2
      simp only [div_eq_mul_inv] at h ⊢
      rw [integral_const_mul]
      simpa [add_comm] using congrArg (fun x : ℝ => A.det.re * x) h
    have hk := integrable_subentropy_kernel hA htr
    have he := hf.sub hk
    obtain ⟨hg, hgv⟩ := UniformIntegrals.reciprocal_difference A.det.re 1 hδpos
      (by linarith)
    have hgc := hg.const_mul (A.det.re ^ 2 / (1 - A.det.re))
    have hge : (∫ t in Ioi (0 : ℝ),
        (A.det.re ^ 2 / (1 - A.det.re)) * (1 / (t + A.det.re) - 1 / (t + 1))) =
        A.det.re ^ 2 * Real.log (1 / A.det.re) / (1 - A.det.re) := by
      rw [integral_const_mul, hgv]
      simp only [Real.log_one, zero_sub, one_div, Real.log_inv]
      ring
    have hb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        0 ≤ A.det.re / (1 + t) ^ 2 - subentropyKernel A t ∧
        A.det.re / (1 + t) ^ 2 - subentropyKernel A t ≤
          (A.det.re ^ 2 / (1 - A.det.re)) * (1 / (t + A.det.re) - 1 / (t + 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [qubit_kernel htr hδ ht]
      exact remainder_kernel_bounds hδpos hδ1 ht
    have hlo := integral_nonneg_of_ae (hb.mono fun t ht => ht.1)
    have hhi := integral_mono_ae he hgc (hb.mono fun t ht => ht.2)
    simp only [Pi.sub_apply] at hhi
    rw [integral_sub hf hk, hv] at hlo hhi
    exact ⟨hlo, hhi.trans_eq hge⟩

end D5.S3.Quantum.Subentropy.QubitBoundary
