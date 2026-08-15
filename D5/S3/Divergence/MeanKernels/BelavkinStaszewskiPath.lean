/- GID: D5/S3/Divergence/MeanKernels/BelavkinStaszewskiPath
   generality: G
   mirror-B: D5/B/S3/Divergence/MeanKernels/BelavkinStaszewskiPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify a positive-density logarithmic divergence with its inverse path integral. -/

/- Library-search audit trail (2026-08-16):
   * `Complex.log_eq_integral` is the exact scalar logarithm path representation.
   * `cfc_setIntegral` moves a parameter integral through continuous functional calculus.
   * `CFC.log`, `cfc_mul`, `cfc_sub`, and `cfc_inv` evaluate the matrix path kernel.
   * `Matrix.PosDef.inv` and `Matrix.PosDef.conjTranspose_mul_mul_same` establish positivity.
   * `Matrix.trace_mul_cycle` and `MatrixInversion.affine_inverse_identity` supply the
     noncommutative trace and affine-inverse steps.
   * No packaged theorem for the complete density-matrix path identity was found in the
     pinned Mathlib, Loogle, LeanSearch, or the frozen D5 corpus.
-/

import Mathlib
import D5.S3.Quantum.MatrixInversion

noncomputable section

open MeasureTheory
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath

private def logPathKernel (u x : ℝ) : ℝ :=
  (x - 1) * ((1 - u) + u * x)⁻¹

private lemma integral_logPathKernel (x : ℝ) (hx : 0 < x) :
    ∫ u in (0 : ℝ)..1, logPathKernel u x = Real.log x := by
  have hz : 1 + ((x - 1 : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [show 1 + ((x - 1 : ℝ) : ℂ) = (x : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr hx
  have hlog := Complex.log_eq_integral hz
  rw [show 1 + ((x - 1 : ℝ) : ℂ) = (x : ℂ) by push_cast; ring,
    ← Complex.ofReal_log hx.le, ← intervalIntegral.integral_const_mul] at hlog
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ u in (0 : ℝ)..1, (logPathKernel u x : ℂ)) =
        ∫ u in (0 : ℝ)..1,
          ((x - 1 : ℝ) : ℂ) * (1 + u • ((x - 1 : ℝ) : ℂ))⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [logPathKernel, Algebra.smul_def, Complex.coe_algebraMap]
      push_cast
      ring
    _ = (Real.log x : ℂ) := hlog.symm

private lemma spectrum_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 < x := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

private lemma logPath_cfc_integral_data {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    (cfc (fun x => ∫ u in Set.Icc (0 : ℝ) 1, logPathKernel u x) A =
      ∫ u in Set.Icc (0 : ℝ) 1, cfc (logPathKernel u) A) ∧
    IntegrableOn (fun u => cfc (logPathKernel u) A) (Set.Icc (0 : ℝ) 1) := by
  let bound : ℝ → ℝ := fun u =>
    ∑ i, ‖logPathKernel u (hA.isHermitian.eigenvalues i)‖
  have hjoint :
      ContinuousOn (Function.uncurry logPathKernel)
        (Set.Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) := by
    refine ContinuousOn.mul (by fun_prop) <| ContinuousOn.inv₀ (by fun_prop) ?_
    rintro ⟨u, x⟩ ⟨hu, hx⟩
    have hxPos : 0 < x := spectrum_pos hA hx
    dsimp only [Function.uncurry, logPathKernel]
    by_cases huOne : u = 1
    · subst u
      simpa using hxPos.ne'
    · exact (add_pos_of_pos_of_nonneg
        (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hxPos.le)).ne'
  have hboundContinuous : ContinuousOn bound (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.norm
    refine ContinuousOn.mul (by fun_prop) <| ContinuousOn.inv₀ (by fun_prop) ?_
    intro u hu
    have hiPos := hA.eigenvalues_pos i
    by_cases huOne : u = 1
    · subst u
      simpa using hiPos.ne'
    · exact (add_pos_of_pos_of_nonneg
        (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hiPos.le)).ne'
  have hboundIntegral :
      HasFiniteIntegral bound (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hboundContinuous.integrableOn_Icc).hasFiniteIntegral
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ x ∈ spectrum ℝ A, ‖logPathKernel u x‖ ≤ bound u := by
    filter_upwards [] with u
    intro x hx
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    rcases hx with ⟨i, rfl⟩
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg (logPathKernel u (hA.isHermitian.eigenvalues j)))
      (Finset.mem_univ i)
  exact ⟨cfc_setIntegral measurableSet_Icc logPathKernel bound A hjoint hbound
      hboundIntegral hA.isHermitian.isSelfAdjoint,
    integrableOn_cfc measurableSet_Icc logPathKernel bound A hjoint hbound
      hboundIntegral hA.isHermitian.isSelfAdjoint⟩

private lemma cfc_logPathKernel_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    cfc (logPathKernel u) A =
      (A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹ := by
  have hdenom : ∀ x ∈ spectrum ℝ A, (1 - u) + u * x ≠ 0 := by
    intro x hx
    have hxPos := spectrum_pos hA hx
    by_cases huOne : u = 1
    · subst u
      simpa using hxPos.ne'
    · exact (add_pos_of_pos_of_nonneg
        (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hxPos.le)).ne'
  have hdenomContinuous :
      ContinuousOn (fun x : ℝ => (1 - u) + u * x) (spectrum ℝ A) := by
    fun_prop
  change cfc (fun x : ℝ => (x - 1) * ((1 - u) + u * x)⁻¹) A = _
  rw [cfc_mul (fun x : ℝ => x - 1) (fun x => ((1 - u) + u * x)⁻¹) A
      (by fun_prop) (ContinuousOn.inv₀ hdenomContinuous hdenom),
    cfc_sub (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ)) A,
    cfc_id' (R := ℝ) A hA.isHermitian.isSelfAdjoint,
    cfc_const (1 : ℝ) A hA.isHermitian.isSelfAdjoint,
    cfc_inv (fun x : ℝ => (1 - u) + u * x) A hdenom hdenomContinuous
      hA.isHermitian.isSelfAdjoint,
    cfc_const_add (1 - u) (fun x : ℝ => u * x) A (by fun_prop)
      hA.isHermitian.isSelfAdjoint,
    cfc_const_mul_id (R := ℝ) u A hA.isHermitian.isSelfAdjoint,
    ← Matrix.nonsing_inv_eq_ringInverse]
  simp only [map_one, Algebra.smul_def, Matrix.mul_one]

private lemma matrixLogPath_intervalIntegrable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    IntervalIntegrable
      (fun u : ℝ => (A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹)
      volume 0 1 := by
  have hcfc : IntervalIntegrable (fun u => cfc (logPathKernel u) A) volume 0 1 := by
    have h := (logPath_cfc_integral_data A hA).2
    rw [← Set.uIcc_of_le zero_le_one] at h
    exact h.intervalIntegrable
  apply hcfc.congr
  intro u hu
  rw [Set.uIoc_of_le zero_le_one] at hu
  apply cfc_logPathKernel_eq A hA u
  exact ⟨hu.1.le, hu.2⟩

private lemma matrix_log_eq_integral_path {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    CFC.log A =
      ∫ u in (0 : ℝ)..1,
        (A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹ := by
  have hcfc := (logPath_cfc_integral_data A hA).1
  calc
    CFC.log A = cfc (fun x => ∫ u in Set.Icc (0 : ℝ) 1, logPathKernel u x) A := by
      rw [CFC.log]
      apply cfc_congr
      intro x hx
      change Real.log x = ∫ u in Set.Icc (0 : ℝ) 1, logPathKernel u x
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      exact (integral_logPathKernel x (spectrum_pos hA hx)).symm
    _ = ∫ u in Set.Icc (0 : ℝ) 1, cfc (logPathKernel u) A := hcfc
    _ = ∫ u in (0 : ℝ)..1, cfc (logPathKernel u) A := by
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    _ = ∫ u in (0 : ℝ)..1,
        (A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      exact cfc_logPathKernel_eq A hA u hu

/-- The logarithmic divergence of two positive density matrices. -/
def belavkinStaszewskiDivergence {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) : ℂ :=
  (rho * CFC.log (CFC.sqrt rho * sigma⁻¹ * CFC.sqrt rho)).trace

/-- The weighted affine-inverse path energy between two density matrices. -/
def rightLogarithmicPathEnergy {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..1, (1 - u) •
    ((rho - sigma) * ((1 - u) • sigma + u • rho)⁻¹ * (rho - sigma)).trace

set_option maxHeartbeats 800000 in
-- The pointwise proof normalizes several nested noncommutative matrix products.
private lemma path_trace_integrand_eq {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef)
    (hRhoTrace : rho.trace = 1) (hSigmaTrace : sigma.trace = 1)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    let r := CFC.sqrt rho
    let A := r * sigma⁻¹ * r
    (rho * ((A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹)).trace =
      (1 - u) •
        ((rho - sigma) * ((1 - u) • sigma + u • rho)⁻¹ * (rho - sigma)).trace := by
  let r : Matrix n n ℂ := CFC.sqrt rho
  let A : Matrix n n ℂ := r * sigma⁻¹ * r
  let C : Matrix n n ℂ := sigma⁻¹ - rho⁻¹
  let B : Matrix n n ℂ := (1 - u) • rho⁻¹ + u • sigma⁻¹
  let m : Matrix n n ℂ := (1 - u) • sigma + u • rho
  let delta : Matrix n n ℂ := rho - sigma
  have hrUnit : IsUnit r :=
    show IsUnit (CFC.sqrt rho) from
      CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hRho.isStrictlyPositive
  have hrDet : IsUnit r.det := (Matrix.isUnit_iff_isUnit_det r).mp hrUnit
  have hrInvMul : r⁻¹ * r = 1 := Matrix.nonsing_inv_mul r hrDet
  have hrMulInv : r * r⁻¹ = 1 := Matrix.mul_nonsing_inv r hrDet
  have hrr : r * r = rho := by
    simpa only [r] using CFC.sqrt_mul_sqrt_self rho hRho.posSemidef.nonneg
  have hRhoInv : rho⁻¹ = r⁻¹ * r⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hrr]
    calc
      (r * r) * (r⁻¹ * r⁻¹) = r * (r * r⁻¹) * r⁻¹ := by noncomm_ring
      _ = 1 := by rw [hrMulInv, Matrix.mul_one, hrMulInv]
  have hrRhoInvR : r * rho⁻¹ * r = 1 := by
    rw [hRhoInv]
    calc
      r * (r⁻¹ * r⁻¹) * r = (r * r⁻¹) * (r⁻¹ * r) := by noncomm_ring
      _ = 1 := by rw [hrMulInv, hrInvMul, Matrix.one_mul]
  have hBPos : B.PosDef := by
    by_cases huOne : u = 1
    · subst u
      simpa [B] using hSigma.inv
    · exact (hRho.inv.smul (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne))).add_posSemidef
        (hSigma.inv.posSemidef.smul hu.1)
  have hBDet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBPos.isUnit
  have hmPos : m.PosDef := by
    by_cases huOne : u = 1
    · subst u
      simpa [m] using hRho
    · exact (hSigma.smul (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne))).add_posSemidef
        (hRho.posSemidef.smul hu.1)
  have hmDet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp hmPos.isUnit
  have hSegment :
      (1 - u) • (1 : Matrix n n ℂ) + u • A = r * B * r := by
    symm
    calc
      r * B * r =
          (1 - u) • (r * rho⁻¹ * r) + u • (r * sigma⁻¹ * r) := by
        simp only [B, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_assoc]
      _ = (1 - u) • (1 : Matrix n n ℂ) + u • A := by
        rw [hrRhoInvR]
  have hAminus : A - 1 = r * C * r := by
    calc
      A - 1 = r * sigma⁻¹ * r - r * rho⁻¹ * r := by rw [hrRhoInvR]
      _ = r * C * r := by
        simp only [C, Matrix.mul_sub, Matrix.sub_mul]
  have hSegmentInv :
      ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹ = r⁻¹ * B⁻¹ * r⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hSegment]
    calc
      (r * B * r) * (r⁻¹ * B⁻¹ * r⁻¹) =
          r * B * (r * r⁻¹) * B⁻¹ * r⁻¹ := by noncomm_ring
      _ = r * B * B⁻¹ * r⁻¹ := by rw [hrMulInv, Matrix.mul_one]
      _ = r * (B * B⁻¹) * r⁻¹ := by noncomm_ring
      _ = r * 1 * r⁻¹ := by rw [Matrix.mul_nonsing_inv B hBDet]
      _ = 1 := by simp only [Matrix.mul_one, hrMulInv]
  have hFirstTrace :
      (rho * ((A - 1) *
        ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹)).trace =
        (rho * C * B⁻¹).trace := by
    rw [hAminus, hSegmentInv]
    calc
      (rho * ((r * C * r) * (r⁻¹ * B⁻¹ * r⁻¹))).trace =
          ((r * r * r * C) * B⁻¹ * r⁻¹).trace := by
        congr 1
        rw [← hrr]
        have hcancel : r * (r⁻¹ * (B⁻¹ * r⁻¹)) = B⁻¹ * r⁻¹ := by
          rw [← Matrix.mul_assoc, hrMulInv, Matrix.one_mul]
        simp only [Matrix.mul_assoc, hcancel]
      _ = (r⁻¹ * (r * r * r * C) * B⁻¹).trace := Matrix.trace_mul_cycle _ _ _
      _ = (rho * C * B⁻¹).trace := by
        congr 1
        have hgroup : r * r * r * C = r * (r * r * C) := by
          simp only [Matrix.mul_assoc]
        have hcancelLeft (X : Matrix n n ℂ) : r⁻¹ * (r * X) = X := by
          rw [← Matrix.mul_assoc, hrInvMul, Matrix.one_mul]
        rw [hgroup, hcancelLeft, hrr]
  have hBInv : B⁻¹ = sigma * m⁻¹ * rho := by
    simpa only [B, m] using
      D5.S3.Quantum.MatrixInversion.affine_inverse_identity rho sigma hRho hSigma u hu
  have hRhoCSigma : rho * C * sigma = delta := by
    have hRhoDet : IsUnit rho.det := (Matrix.isUnit_iff_isUnit_det rho).mp hRho.isUnit
    have hSigmaDet : IsUnit sigma.det := (Matrix.isUnit_iff_isUnit_det sigma).mp hSigma.isUnit
    simp only [C, delta, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul sigma hSigmaDet, Matrix.mul_one,
      Matrix.mul_nonsing_inv rho hRhoDet, Matrix.one_mul]
  have hMiddleTrace : (rho * C * B⁻¹).trace = (delta * m⁻¹ * rho).trace := by
    rw [hBInv]
    congr 1
    calc
      rho * C * (sigma * m⁻¹ * rho) = (rho * C * sigma) * m⁻¹ * rho := by
        noncomm_ring
      _ = delta * m⁻¹ * rho := by rw [hRhoCSigma]
  have hRhoDecomp : rho = m + (1 - u) • delta := by
    simp only [m, delta]
    module
  have hDeltaTrace : delta.trace = 0 := by
    simp only [delta, Matrix.trace_sub, hRhoTrace, hSigmaTrace, sub_self]
  have hLastMatrix :
      delta * m⁻¹ * rho = delta + (1 - u) • (delta * m⁻¹ * delta) := by
    rw [hRhoDecomp, Matrix.mul_add, Matrix.mul_smul]
    rw [Matrix.mul_assoc delta m⁻¹ m, Matrix.nonsing_inv_mul m hmDet,
      Matrix.mul_one]
  change (rho * ((A - 1) *
      ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹)).trace = _
  rw [hFirstTrace, hMiddleTrace, hLastMatrix, Matrix.trace_add, Matrix.trace_smul,
    hDeltaTrace, zero_add]

/-- For positive-definite density matrices, the logarithmic divergence is exactly the
weighted affine-inverse path energy along their line segment. -/
theorem belavkin_staszewski_path {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef)
    (hRhoTrace : rho.trace = 1) (hSigmaTrace : sigma.trace = 1) :
    belavkinStaszewskiDivergence rho sigma = rightLogarithmicPathEnergy rho sigma := by
  let r : Matrix n n ℂ := CFC.sqrt rho
  let A : Matrix n n ℂ := r * sigma⁻¹ * r
  have hrUnit : IsUnit r :=
    show IsUnit (CFC.sqrt rho) from
      CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hRho.isStrictlyPositive
  have hrSelf : star r = r := by
    simpa only [r] using (CFC.sqrt_nonneg rho).isSelfAdjoint.star_eq
  have hA : A.PosDef := by
    have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff hrUnit).mpr hSigma.inv
    rw [hrSelf] at h
    exact h
  let L : Matrix n n ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.comp
      (mulLeftLinearMap n ℂ rho).toContinuousLinearMap
  have hpathIntegrable := matrixLogPath_intervalIntegrable A hA
  have hcommute := L.intervalIntegral_comp_comm hpathIntegrable
  change (rho * CFC.log A).trace =
    ∫ u in (0 : ℝ)..1, (1 - u) •
      ((rho - sigma) * ((1 - u) • sigma + u • rho)⁻¹ * (rho - sigma)).trace
  calc
    (rho * CFC.log A).trace = L (CFC.log A) := by rfl
    _ = L (∫ u in (0 : ℝ)..1,
        (A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹) := by
      rw [matrix_log_eq_integral_path A hA]
    _ = ∫ u in (0 : ℝ)..1,
        L ((A - 1) * ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹) := hcommute.symm
    _ = ∫ u in (0 : ℝ)..1, (1 - u) •
        ((rho - sigma) * ((1 - u) • sigma + u • rho)⁻¹ * (rho - sigma)).trace := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      change (rho * ((A - 1) *
        ((1 - u) • (1 : Matrix n n ℂ) + u • A)⁻¹)).trace = _
      exact path_trace_integrand_eq rho sigma hRho hSigma hRhoTrace hSigmaTrace u hu

end D5.S3.Divergence.MeanKernels.BelavkinStaszewskiPath
