/- GID: D5/S3/Quantum/Subentropy/DensityKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/DensityKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Spectral reduction, integrability and continuity of density-matrix subentropy. -/

import Mathlib.Analysis.Matrix.Spectrum
import D5.S3.Quantum.Subentropy.KernelBounds
import D5.S3.Quantum.Subentropy.UniformIntegrals

/-! Spectral reduction supplies a uniform integrable envelope on density matrices. -/
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Subentropy.DensityKernel
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.KernelBounds

private theorem det_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (s : ℝ) :
    (1 + s • A).det = ∏ i, ((1 + s * hA.eigenvalues i : ℝ) : ℂ) := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hs : A = U * D * star U := hA.spectral_theorem
  have hm : 1 + s • A = U * (1 + s • D) * star U := by
    calc
      1 + s • A = 1 + s • (U * D * star U) := congrArg (fun B => 1 + s • B) hs
      _ = _ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
          Matrix.smul_mul, U, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  rw [hm]
  rw [Matrix.det_conj_of_mul_eq_one (Unitary.coe_mul_star_self _)
    (Unitary.coe_star_mul_self _)]
  have hd : (1 : Matrix ι ι ℂ) + (s : ℝ) • diagonal (fun i => (hA.eigenvalues i : ℂ)) =
      diagonal (fun i => ((1 + s * hA.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
    · simp [h]
  change (1 + s • diagonal (fun i => (hA.eigenvalues i : ℂ))).det = _
  rw [hd, Matrix.det_diagonal]

theorem spectral_prob {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    (∀ i, 0 ≤ hA.isHermitian.eigenvalues i) ∧
      ∑ i, hA.isHermitian.eigenvalues i = 1 := by
  refine ⟨hA.eigenvalues_nonneg, ?_⟩
  have h := hA.isHermitian.trace_eq_sum_eigenvalues
  rw [htr] at h
  have hre := congrArg Complex.re h
  rw [Complex.one_re, Complex.re_sum] at hre
  simpa using hre.symm

private theorem kernel_eq_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    subentropyKernel A t =
      subentropyKernel (diagonal (fun i => (hA.eigenvalues i : ℂ))) t := by
  unfold subentropyKernel
  rw [det_spectral hA]
  have hd : (1 : Matrix ι ι ℂ) + (t⁻¹ : ℝ) • diagonal (fun i => (hA.eigenvalues i : ℂ)) =
      diagonal (fun i => ((1 + t⁻¹ * hA.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
    · simp [h]
  rw [hd, Matrix.det_diagonal]

private theorem positive_determinant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (ht : 0 < t) :
    0 < (1 + (t⁻¹ : ℝ) • A).det.re := by
  rw [det_spectral hA.isHermitian, ← Complex.ofReal_prod, Complex.ofReal_re]
  apply Finset.prod_pos
  intro i _
  have hi := hA.eigenvalues_nonneg i
  positivity

private theorem kernel_continuousOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ContinuousOn (subentropyKernel A) (Ioi 0) := by
  intro t ht
  unfold subentropyKernel
  have htpos : 0 < t := ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : 1 + t ≠ 0 := by positivity
  have hden : (1 + (t⁻¹ : ℝ) • A).det.re ≠ 0 := (positive_determinant hA t ht).ne'
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)

/-- On every density matrix the kernel is nonnegative and is dominated by the
same integrable inverse-square function, independently of dimension. -/
theorem density_kernel_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ subentropyKernel A t ∧ subentropyKernel A t ≤ 1 / (1 + t)^2 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have hz : A.trace = 0 := by simp [Matrix.trace]
    exact False.elim (zero_ne_one (hz.symm.trans htr))
  | inr h =>
    let x : ι := Classical.choice h
    obtain ⟨hp, hsum⟩ := spectral_prob hA htr
    rw [kernel_eq_spectral hA.isHermitian]
    obtain ⟨hlo, hhi⟩ := classical_kernel_bounds _ hp hsum x t ht
    refine ⟨hlo, hhi.trans ?_⟩
    exact div_le_div_of_nonneg_right (by linarith [hp x]) (sq_nonneg (1 + t))

/-- The determinant integral is absolutely integrable on every density matrix. -/
theorem integrable_subentropy_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    IntegrableOn (subentropyKernel A) (Ioi 0) := by
  have hb := (UniformIntegrals.inverse_power 1 (by norm_num) 0).1
  have hbound : IntegrableOn (fun t : ℝ => 1 / (1 + t)^2) (Ioi 0) := by
    simpa [add_comm] using hb
  refine hbound.mono' ((kernel_continuousOn hA).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  obtain ⟨hlo, hhi⟩ := density_kernel_bounds hA htr t ht
  simpa [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi

/-- The determinant-integral subentropy is continuous on all positive trace-one
matrices, including the boundary with zero or repeated eigenvalues. -/
theorem continuousOn_matrixSubentropy {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousOn (@matrixSubentropy ι _ _) {A | A.PosSemidef ∧ A.trace = 1} := by
  letI : FirstCountableTopology (Matrix ι ι ℂ) := inferInstanceAs
    (FirstCountableTopology (ι → ι → ℂ))
  apply continuousOn_of_dominated (bound := fun t : ℝ => 1 / (1 + t)^2)
  · intro A hA
    exact (integrable_subentropy_kernel hA.1 hA.2).1
  · intro A hA
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    obtain ⟨hlo, hhi⟩ := density_kernel_bounds hA.1 hA.2 t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  · simpa only [IntegrableOn, Nat.reduceAdd, add_comm] using (UniformIntegrals.inverse_power 1 (by norm_num) 0).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro A hA
    unfold subentropyKernel
    have hd := (positive_determinant hA.1 t ht).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop

end D5.S3.Quantum.Subentropy.DensityKernel
