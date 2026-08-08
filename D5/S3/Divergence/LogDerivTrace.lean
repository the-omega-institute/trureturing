/- GID: D5/S3/Divergence/LogDerivTrace
   generality: G
   mirror-B: D5/B/S3/Divergence/LogDerivTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the logarithmic-derivative trace identity from its Bochner integral. -/

/- Library-search audit trail (2026-08-08):
   * `Matrix.IsHermitian.spectral_theorem` and `Matrix.PosDef.eigenvalues_pos` provide
     unitary diagonalization and strict positivity of every eigenvalue.
   * `MeasureTheory.integrable_pi_iff` and `Matrix.stdBasis` reduce finite-dimensional
     matrix-valued integrability to the integrability of its entries.
   * `ContinuousLinearMap.integral_comp_comm` moves fixed matrix multiplication and
     `Matrix.traceLinearMap` through the Bochner integral.
   * `integrableOn_Ioi_deriv_of_nonneg'` and
     `integral_Ioi_of_hasDerivAt_of_nonneg'` evaluate the scalar resolvent kernel.
   * No packaged theorem identifying this matrix integral or its trace with the requested
     logarithmic directional-derivative identity was found in the pinned mathlib.
-/

import Mathlib
import Mathlib.LinearAlgebra.Matrix.Bilinear

noncomputable section

open MeasureTheory
open Filter
open scoped ComplexOrder
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Divergence.LogDerivTrace

private lemma scalarKernel_integrable (lambda : ℝ) (hlambda : 0 < lambda) :
    IntegrableOn (fun t : ℝ => lambda / (lambda + t) ^ 2) (Set.Ioi 0) := by
  let F : ℝ → ℝ := fun t => -lambda / (lambda + t)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt F (lambda / (lambda + t) ^ 2) t := by
    intro t ht
    have hden : lambda + t ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hlambda ht)
    simpa [F, div_eq_mul_inv] using
      (((hasDerivAt_id t).const_add lambda).inv hden).const_mul (-lambda)
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ lambda / (lambda + t) ^ 2 := by
    intro t ht
    positivity
  have htendsto : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun t : ℝ => lambda + t) Filter.atTop Filter.atTop := by
      simpa [add_comm] using tendsto_atTop_add_const_right atTop lambda tendsto_id
    simpa [F] using tendsto_const_nhds.div_atTop hden
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htendsto

private lemma integral_scalarKernel (lambda : ℝ) (hlambda : 0 < lambda) :
    ∫ t in Set.Ioi (0 : ℝ), lambda / (lambda + t) ^ 2 = 1 := by
  let F : ℝ → ℝ := fun t => -lambda / (lambda + t)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt F (lambda / (lambda + t) ^ 2) t := by
    intro t ht
    have hden : lambda + t ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hlambda ht)
    simpa [F, div_eq_mul_inv] using
      (((hasDerivAt_id t).const_add lambda).inv hden).const_mul (-lambda)
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ lambda / (lambda + t) ^ 2 := by
    intro t ht
    positivity
  have htendsto : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun t : ℝ => lambda + t) Filter.atTop Filter.atTop := by
      simpa [add_comm] using tendsto_atTop_add_const_right atTop lambda tendsto_id
    simpa [F] using tendsto_const_nhds.div_atTop hden
  simpa [F, hlambda.ne'] using
    integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htendsto

private lemma resolvent_eq_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Matrix ι ι ℂ) (hm : m.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (m + t • 1)⁻¹ =
      hm.isHermitian.eigenvectorUnitary *
        Matrix.diagonal (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) *
        star hm.isHermitian.eigenvectorUnitary := by
  let U : Matrix ι ι ℂ := hm.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ))
  let R : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹)
  have hshift : m + t • 1 = U * D * star U := by
    rw [hm.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, U]
    change U * Matrix.diagonal (RCLike.ofReal ∘ hm.isHermitian.eigenvalues) * star U +
        t • 1 = U * D * star U
    have hscalar :
        U * (t • (1 : Matrix ι ι ℂ)) * star U = t • 1 := by
      simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      change t • ((hm.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
        star hm.isHermitian.eigenvectorUnitary) = t • 1
      rw [Unitary.coe_mul_star_self]
    have hdiagShift :
        Matrix.diagonal (RCLike.ofReal ∘ hm.isHermitian.eigenvalues) + t • 1 = D := by
      ext i j
      by_cases hij : i = j <;> simp [D, hij, add_comm]
    calc
      U * Matrix.diagonal (RCLike.ofReal ∘ hm.isHermitian.eigenvalues) * star U + t • 1 =
          U * Matrix.diagonal (RCLike.ofReal ∘ hm.isHermitian.eigenvalues) * star U +
            U * (t • 1) * star U := by rw [hscalar]
      _ = U *
            (Matrix.diagonal (RCLike.ofReal ∘ hm.isHermitian.eigenvalues) + t • 1) *
            star U := by noncomm_ring
      _ = U * D * star U := by rw [hdiagShift]
  rw [hshift]
  apply Matrix.inv_eq_right_inv
  have hdiag : D * R = 1 := by
    change Matrix.diagonal (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)) *
        Matrix.diagonal (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    apply mul_inv_cancel₀
    exact_mod_cast
      (add_pos_of_pos_of_nonneg (hm.eigenvalues_pos i) ht).ne'
  change (U * D * star U) * (U * R * star U) = 1
  calc
    (U * D * star U) * (U * R * star U) =
        U * D * (star U * U) * R * star U := by noncomm_ring
    _ = U * (D * R) * star U := by
      rw [show star U * U = 1 by exact Unitary.coe_star_mul_self _]
      simp [Matrix.mul_assoc]
    _ = U * 1 * star U := by rw [hdiag]
    _ = 1 := by
      rw [Matrix.mul_one]
      exact Unitary.coe_mul_star_self _

private lemma pairKernel_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => 1 / ((a + t) * (b + t))) (Set.Ioi 0) := by
  let c := min a b
  have hc : 0 < c := lt_min ha hb
  have hmajor : IntegrableOn (fun t : ℝ => 1 / (c + t) ^ 2) (Set.Ioi 0) := by
    have hscaled := (scalarKernel_integrable c hc).div_const c
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
    intro t _
    field_simp [hc.ne']
  apply Integrable.mono' hmajor
  · refine (continuousOn_const.div
      ((continuousOn_const.add continuousOn_id).mul
        (continuousOn_const.add continuousOn_id)) ?_).aestronglyMeasurable measurableSet_Ioi
    intro t ht
    exact mul_ne_zero (add_pos ha ht).ne' (add_pos hb ht).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hat : 0 < a + t := add_pos ha ht
    have hbt : 0 < b + t := add_pos hb ht
    have hct : 0 < c + t := add_pos hc ht
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (mul_pos hat hbt))]
    apply one_div_le_one_div_of_le (sq_pos_of_pos hct)
    have hca : c + t ≤ a + t := by
      dsimp [c]
      linarith [min_le_left a b]
    have hcb : c + t ≤ b + t := by
      dsimp [c]
      linarith [min_le_right a b]
    calc
      (c + t) ^ 2 = (c + t) * (c + t) := by ring
      _ ≤ (a + t) * (b + t) :=
        mul_le_mul hca hcb hct.le hat.le

private lemma complexPairKernel_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) :
    IntegrableOn
      (fun t : ℝ => ((a + t : ℝ) : ℂ)⁻¹ * z * ((b + t : ℝ) : ℂ)⁻¹)
      (Set.Ioi 0) := by
  have hpair := (pairKernel_integrable a b ha hb).ofReal (𝕜 := ℂ)
  have hmul := hpair.mul_const z
  apply IntegrableOn.congr_fun hmul _ measurableSet_Ioi
  intro t ht
  have hat : a + t ≠ 0 := (add_pos ha ht).ne'
  have hbt : b + t ≠ 0 := (add_pos hb ht).ne'
  push_cast
  field_simp [hat, hbt]
  rfl

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma spectralKernel_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m X : Matrix ι ι ℂ) (hm : m.PosDef) :
    IntegrableOn
      (fun t : ℝ =>
        Matrix.diagonal
            (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) *
          (star hm.isHermitian.eigenvectorUnitary * X *
            hm.isHermitian.eigenvectorUnitary) *
          Matrix.diagonal
            (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹))
      (Set.Ioi 0) := by
  rw [IntegrableOn]
  let e := (Matrix.stdBasis ℂ ι ι).equivFun.toContinuousLinearEquiv
  apply e.integrable_comp_iff.mp
  rw [integrable_pi_iff]
  rintro ⟨i, j⟩
  have hij := complexPairKernel_integrable
    (hm.isHermitian.eigenvalues i) (hm.isHermitian.eigenvalues j)
    (hm.eigenvalues_pos i) (hm.eigenvalues_pos j)
    ((star hm.isHermitian.eigenvectorUnitary * X *
      hm.isHermitian.eigenvectorUnitary) i j)
  rw [IntegrableOn] at hij
  apply hij.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
  simp [e, Matrix.stdBasis, Matrix.diagonal_mul, Matrix.mul_diagonal]

private lemma integrand_eq_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m X : Matrix ι ι ℂ) (hm : m.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (m + t • 1)⁻¹ * X * (m + t • 1)⁻¹ =
      hm.isHermitian.eigenvectorUnitary *
        (Matrix.diagonal
              (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) *
          (star hm.isHermitian.eigenvectorUnitary * X *
            hm.isHermitian.eigenvectorUnitary) *
          Matrix.diagonal
              (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹)) *
        star hm.isHermitian.eigenvectorUnitary := by
  rw [resolvent_eq_spectral m hm t ht]
  noncomm_ring

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma logDeriv_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m X : Matrix ι ι ℂ) (hm : m.PosDef) :
    IntegrableOn (fun t : ℝ => (m + t • 1)⁻¹ * X * (m + t • 1)⁻¹) (Set.Ioi 0) := by
  let U := hm.isHermitian.eigenvectorUnitary
  let K : ℝ → Matrix ι ι ℂ := fun t =>
    Matrix.diagonal
          (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) *
      (star U * X * U) *
      Matrix.diagonal
          (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹)
  let C : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    (mulRightLinearMap ι ℂ (star U)).comp (mulLeftLinearMap ι ℂ U)
  have hK : Integrable K (volume.restrict (Set.Ioi 0)) := by
    simpa only [K, U, IntegrableOn] using spectralKernel_integrable m X hm
  have hC : Integrable (fun t => C (K t)) (volume.restrict (Set.Ioi 0)) :=
    C.toContinuousLinearMap.integrable_comp hK
  rw [IntegrableOn]
  apply hC.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [C, K, U, mulLeftLinearMap_apply, mulRightLinearMap_apply,
    LinearMap.comp_apply, Unitary.coe_star] using
      (integrand_eq_spectral m X hm t ht.le).symm

private lemma trace_integrand_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m X : Matrix ι ι ℂ) (hm : m.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (m * ((m + t • 1)⁻¹ * X * (m + t • 1)⁻¹)).trace =
      ∑ i,
        ((hm.isHermitian.eigenvalues i /
          (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) *
          (star hm.isHermitian.eigenvectorUnitary * X *
            hm.isHermitian.eigenvectorUnitary) i i := by
  let U : Matrix ι ι ℂ := hm.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => (hm.isHermitian.eigenvalues i : ℂ))
  let R : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => ((hm.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹)
  let Y : Matrix ι ι ℂ := star U * X * U
  have hm_spec : m = U * D * star U := by
    rw [hm.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    change U * Matrix.diagonal (RCLike.ofReal ∘ hm.isHermitian.eigenvalues) * star U =
      U * D * star U
    congr 1
  have hkernel :
      (m + t • 1)⁻¹ * X * (m + t • 1)⁻¹ = U * (R * Y * R) * star U := by
    simpa only [U, R, Y, Unitary.coe_star] using integrand_eq_spectral m X hm t ht
  have hproduct := congrArg₂ (fun A B : Matrix ι ι ℂ => A * B) hm_spec hkernel
  calc
    (m * ((m + t • 1)⁻¹ * X * (m + t • 1)⁻¹)).trace =
        ((U * D * star U) * (U * (R * Y * R) * star U)).trace :=
      congrArg Matrix.trace hproduct
    _ = (U * (D * (R * Y * R)) * star U).trace := by
      congr 1
      calc
        (U * D * star U) * (U * (R * Y * R) * star U) =
            U * D * (star U * U) * (R * Y * R) * star U := by noncomm_ring
        _ = U * (D * (R * Y * R)) * star U := by
          rw [show star U * U = 1 by exact Unitary.coe_star_mul_self _]
          simp [Matrix.mul_assoc]
    _ = (D * (R * Y * R)).trace := by
      rw [Matrix.trace_mul_cycle]
      rw [show star U * U = 1 by exact Unitary.coe_star_mul_self _, Matrix.one_mul]
    _ = ∑ i,
          ((hm.isHermitian.eigenvalues i /
            (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) * Y i i := by
      dsimp [D, R]
      simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Matrix.mul_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      have hden : hm.isHermitian.eigenvalues i + t ≠ 0 :=
        (add_pos_of_pos_of_nonneg (hm.eigenvalues_pos i) ht).ne'
      push_cast
      field_simp [hden]
    _ = ∑ i,
          ((hm.isHermitian.eigenvalues i /
            (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) *
            (star hm.isHermitian.eigenvectorUnitary * X *
              hm.isHermitian.eigenvectorUnitary) i i := by
      simp only [Y, U, Unitary.coe_star]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- The matrix-valued Bochner integral denoted by `D ln_m[X]` in the source program. -/
def logDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (m + t • 1)⁻¹ * X * (m + t • 1)⁻¹

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- The trace of the integral logarithmic derivative in a positive definite base direction. -/
theorem trace_mul_logDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m X : Matrix ι ι ℂ) (hm : m.PosDef) (_hX : X.IsHermitian) :
    (m * logDeriv m X).trace = X.trace := by
  let f : ℝ → Matrix ι ι ℂ := fun t =>
    (m + t • 1)⁻¹ * X * (m + t • 1)⁻¹
  let U : Matrix ι ι ℂ := hm.isHermitian.eigenvectorUnitary
  let Y : Matrix ι ι ℂ := star U * X * U
  let Lm : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    (mulLeftLinearMap ι ℂ m).toContinuousLinearMap
  let Tr : Matrix ι ι ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hf : Integrable f (volume.restrict (Set.Ioi 0)) := by
    simpa only [f, IntegrableOn] using logDeriv_integrable m X hm
  have hmul :
      ∫ t in Set.Ioi (0 : ℝ), m * f t =
        m * ∫ t in Set.Ioi (0 : ℝ), f t := by
    have h := Lm.integral_comp_comm hf
    change (∫ t in Set.Ioi (0 : ℝ), m * f t) =
      m * ∫ t in Set.Ioi (0 : ℝ), f t at h
    exact h
  have hmf : Integrable (fun t => m * f t) (volume.restrict (Set.Ioi 0)) := by
    have h := Lm.integrable_comp hf
    change Integrable (fun t => m * f t) (volume.restrict (Set.Ioi 0)) at h
    exact h
  have htrace :
      ∫ t in Set.Ioi (0 : ℝ), (m * f t).trace =
        (∫ t in Set.Ioi (0 : ℝ), m * f t).trace := by
    have h := Tr.integral_comp_comm hmf
    change (∫ t in Set.Ioi (0 : ℝ), (m * f t).trace) =
      (∫ t in Set.Ioi (0 : ℝ), m * f t).trace at h
    exact h
  have hterm (i : ι) :
      Integrable
        (fun t : ℝ =>
          ((hm.isHermitian.eigenvalues i /
            (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) * Y i i)
        (volume.restrict (Set.Ioi 0)) := by
    have hi := (scalarKernel_integrable
      (hm.isHermitian.eigenvalues i) (hm.eigenvalues_pos i)).ofReal (𝕜 := ℂ)
    exact hi.mul_const (Y i i)
  have hone (i : ι) :
      ∫ t in Set.Ioi (0 : ℝ),
          ((hm.isHermitian.eigenvalues i /
            (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) * Y i i =
        Y i i := by
    rw [integral_mul_const, integral_complex_ofReal,
      integral_scalarKernel (hm.isHermitian.eigenvalues i) (hm.eigenvalues_pos i)]
    norm_num
  have hspectral :
      ∫ t in Set.Ioi (0 : ℝ), (m * f t).trace = X.trace := by
    calc
      (∫ t in Set.Ioi (0 : ℝ), (m * f t).trace) =
          ∫ t in Set.Ioi (0 : ℝ), ∑ i,
            ((hm.isHermitian.eigenvalues i /
              (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) * Y i i := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simpa only [f, Y, U, Unitary.coe_star] using
          trace_integrand_eq_sum m X hm t ht.le
      _ = ∑ i, ∫ t in Set.Ioi (0 : ℝ),
            ((hm.isHermitian.eigenvalues i /
              (hm.isHermitian.eigenvalues i + t) ^ 2 : ℝ) : ℂ) * Y i i := by
        exact integral_finsetSum Finset.univ fun i _ => hterm i
      _ = ∑ i, Y i i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hone i
      _ = Y.trace := rfl
      _ = X.trace := by
        dsimp [Y]
        rw [Matrix.trace_mul_cycle]
        rw [show U * star U = 1 by exact Unitary.coe_mul_star_self _, Matrix.one_mul]
  calc
    (m * logDeriv m X).trace =
        (∫ t in Set.Ioi (0 : ℝ), m * f t).trace := by
      change (m * ∫ t in Set.Ioi (0 : ℝ), f t).trace =
        (∫ t in Set.Ioi (0 : ℝ), m * f t).trace
      exact congrArg Matrix.trace hmul.symm
    _ = ∫ t in Set.Ioi (0 : ℝ), (m * f t).trace := htrace.symm
    _ = X.trace := hspectral

end D5.S3.Divergence.LogDerivTrace
