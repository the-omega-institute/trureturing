/- GID: D5/S3/Resource/LogDet/PathSpectralClassical
   generality: G
   mirror-B: D5/B/S3/Resource/LogDet/PathSpectralClassical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the log-determinant path, spectrum, kernel, and classical face. -/

/- Library-search audit (2026-08-18):
   * `LogDetDivergence.logDetDivergence` is the exact frozen divergence definition.
   * `Matrix.IsHermitian.trace_eq_sum_eigenvalues`,
     `Matrix.IsHermitian.det_eq_prod_eigenvalues`, and `Real.log_prod` give the spectral sum.
   * `cfc_mul`, `cfc_inv`, and the Hermitian functional calculus reduce the affine path.
   * `intervalIntegral.integral_eq_sub_of_hasDerivAt` gives the scalar Taylor remainder.
   * `Matrix.inv_diagonal` was inspected, but the positivity-aware direct diagonal inverse is used.
   * No packaged theorem for the complete path, spectral, and classical conjunction was found in
     pinned Mathlib, Loogle, LeanSearch, or the D5 corpus. -/

import D5.S3.Resource.LogDetDivergence

noncomputable section

open scoped ComplexOrder MatrixOrder

open MeasureTheory

namespace D5.S3.Resource.LogDet.PathSpectralClassical

def relativeCongruence {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt sigma)⁻¹ * rho * (CFC.sqrt sigma)⁻¹

def affineSegment {n : Type*} (rho sigma : Matrix n n ℂ) (u : ℝ) : Matrix n n ℂ :=
  (1 - u) • sigma + u • rho

def logDetPathEnergy {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) : ℝ :=
  ∫ u in (0 : ℝ)..1, (1 - u) *
    ((affineSegment rho sigma u)⁻¹ * (rho - sigma) *
      ((affineSegment rho sigma u)⁻¹ * (rho - sigma))).trace.re

lemma relativeCongruence_pos {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef) :
    (relativeCongruence rho sigma).PosDef := by
  let s : Matrix n n ℂ := CFC.sqrt sigma
  have hsigma_nonneg : (0 : Matrix n n ℂ) ≤ sigma :=
    Matrix.nonneg_iff_posSemidef.mpr hSigma.posSemidef
  have hs_star : Matrix.conjTranspose s = s := by
    simpa [s, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg sigma).isSelfAdjoint.star_eq
  have hs_unit : IsUnit s := by
    change IsUnit (CFC.sqrt sigma)
    exact (CFC.isUnit_sqrt_iff sigma hsigma_nonneg).mpr hSigma.isUnit
  have hs_inv_unit : IsUnit s⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hs_unit
  have hs_inv_star : Matrix.conjTranspose (s⁻¹) = s⁻¹ := by
    exact (show s.IsHermitian from hs_star).inv
  rw [show relativeCongruence rho sigma =
      star (s⁻¹) * rho * s⁻¹ by simp [relativeCongruence, s,
        Matrix.star_eq_conjTranspose, hs_inv_star]]
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hs_inv_unit).mpr hRho

private def barrierPathKernel (u x : ℝ) : ℝ :=
  (1 - u) * (x - 1) ^ 2 / (1 + u * (x - 1)) ^ 2

def barrierProfile (x : ℝ) : ℝ :=
  x - Real.log x - 1

private def barrierAntideriv (x u : ℝ) : ℝ :=
  -((1 - u) * (x - 1) / (1 + u * (x - 1))) -
    Real.log (1 + u * (x - 1))

private def logPathKernel (u x : ℝ) : ℝ :=
  (x - 1) * (1 + u * (x - 1))⁻¹

private lemma integral_barrierPathKernel (x : ℝ) (hx : 0 < x) :
    ∫ u in (0 : ℝ)..1, barrierPathKernel u x = x - Real.log x - 1 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (barrierAntideriv x) (barrierPathKernel u x) u := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have hdpos : 0 < 1 + u * (x - 1) := by
      by_cases huOne : u = 1
      · subst u
        simpa using hx
      · have h := add_pos_of_pos_of_nonneg
          (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hx.le)
        nlinarith
    have hd : 1 + u * (x - 1) ≠ 0 := ne_of_gt hdpos
    have hnum : HasDerivAt (fun v : ℝ => (1 - v) * (x - 1)) (-(x - 1)) u := by
      simpa using
        ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).mul_const (x - 1)
    have hden : HasDerivAt (fun v : ℝ => 1 + v * (x - 1)) (x - 1) u := by
      simpa using ((hasDerivAt_id u).mul_const (x - 1)).const_add 1
    have hquot := hnum.div hden hd
    have hlog := hden.log hd
    have hraw := hquot.neg.sub hlog
    change HasDerivAt
      (fun v : ℝ => -((1 - v) * (x - 1) / (1 + v * (x - 1))) -
        Real.log (1 + v * (x - 1))) (barrierPathKernel u x) u
    convert hraw using 1
    all_goals first
      | exact Subsingleton.elim _ _
      | rfl
      | (unfold barrierPathKernel; field_simp [hd]; ring)
  have hint : IntervalIntegrable (fun u => barrierPathKernel u x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    apply pow_ne_zero 2
    rw [Set.uIcc_of_le zero_le_one] at hu
    by_cases huOne : u = 1
    · subst u
      simpa using hx.ne'
    · have h := add_pos_of_pos_of_nonneg
        (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hx.le)
      exact ne_of_gt (by nlinarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [barrierAntideriv]
  ring

private lemma barrierPathKernel_intervalIntegrable (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable (fun u => barrierPathKernel u x) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro u hu
  apply pow_ne_zero 2
  rw [Set.uIcc_of_le zero_le_one] at hu
  by_cases huOne : u = 1
  · subst u
    simpa using hx.ne'
  · have h := add_pos_of_pos_of_nonneg
      (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hx.le)
    exact ne_of_gt (by nlinarith)

private lemma trace_cfc_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp

private lemma spectrum_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 < x := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

private lemma cfc_logPathKernel_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    cfc (logPathKernel u) A =
      (A - 1) * (1 + u • (A - 1))⁻¹ := by
  have hdenom : ∀ x ∈ spectrum ℝ A, 1 + u * (x - 1) ≠ 0 := by
    intro x hx
    have hxPos : 0 < x := spectrum_pos hA hx
    by_cases huOne : u = 1
    · subst u
      simpa using hxPos.ne'
    · have h := add_pos_of_pos_of_nonneg
        (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hxPos.le)
      exact ne_of_gt (by nlinarith)
  have hdenomContinuous :
      ContinuousOn (fun x : ℝ => 1 + u * (x - 1)) (spectrum ℝ A) := by
    fun_prop
  change cfc (fun x : ℝ => (x - 1) * (1 + u * (x - 1))⁻¹) A = _
  rw [cfc_mul (fun x : ℝ => x - 1) (fun x => (1 + u * (x - 1))⁻¹) A
      (by fun_prop) (ContinuousOn.inv₀ hdenomContinuous hdenom),
    cfc_sub (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ)) A,
    cfc_id' (R := ℝ) A hA.isHermitian.isSelfAdjoint,
    cfc_const (1 : ℝ) A hA.isHermitian.isSelfAdjoint,
    cfc_inv (fun x : ℝ => 1 + u * (x - 1)) A hdenom hdenomContinuous
      hA.isHermitian.isSelfAdjoint,
    cfc_const_add 1 (fun x : ℝ => u * (x - 1)) A (by fun_prop)
      hA.isHermitian.isSelfAdjoint,
    cfc_const_mul u (fun x : ℝ => x - 1) A (by fun_prop),
    cfc_sub (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ)) A,
    cfc_id' (R := ℝ) A hA.isHermitian.isSelfAdjoint,
    cfc_const (1 : ℝ) A hA.isHermitian.isSelfAdjoint,
    ← Matrix.nonsing_inv_eq_ringInverse]
  simp only [map_one, Algebra.smul_def]

private lemma cfc_barrierPathKernel_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    cfc (barrierPathKernel u) A =
      (1 - u) • (((A - 1) * (1 + u • (A - 1))⁻¹) *
        ((A - 1) * (1 + u • (A - 1))⁻¹)) := by
  have hdenom : ∀ x ∈ spectrum ℝ A, 1 + u * (x - 1) ≠ 0 := by
    intro x hx
    have hxPos : 0 < x := spectrum_pos hA hx
    by_cases huOne : u = 1
    · subst u
      simpa using hxPos.ne'
    · have h := add_pos_of_pos_of_nonneg
        (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne)) (mul_nonneg hu.1 hxPos.le)
      exact ne_of_gt (by nlinarith)
  have hlogContinuous : ContinuousOn (logPathKernel u) (spectrum ℝ A) := by
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.inv₀ (by fun_prop)
    exact hdenom
  have hfun : barrierPathKernel u =
      fun x => (1 - u) * (logPathKernel u x * logPathKernel u x) := by
    funext x
    simp only [barrierPathKernel, logPathKernel, div_eq_mul_inv]
    rw [← inv_pow]
    ring
  rw [hfun, cfc_const_mul (1 - u) (fun x => logPathKernel u x * logPathKernel u x) A
      (hlogContinuous.mul hlogContinuous),
    cfc_mul (logPathKernel u) (logPathKernel u) A hlogContinuous hlogContinuous,
    cfc_logPathKernel_eq A hA u hu]

private lemma relative_trace_integrand_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u) *
        ((((1 + u • (A - 1))⁻¹ * (A - 1)) *
          ((1 + u • (A - 1))⁻¹ * (A - 1))).trace.re) =
      ∑ i, barrierPathKernel u (hA.isHermitian.eigenvalues i) := by
  let Minv : Matrix n n ℂ := (1 + u • (A - 1))⁻¹
  let delta : Matrix n n ℂ := A - 1
  have hcycle : ((delta * Minv) * (delta * Minv)).trace =
      ((Minv * delta) * (Minv * delta)).trace := by
    calc
      ((delta * Minv) * (delta * Minv)).trace =
          (delta * (Minv * delta) * Minv).trace := by
            congr 1
            noncomm_ring
      _ = (Minv * delta * (Minv * delta)).trace :=
        Matrix.trace_mul_cycle delta (Minv * delta) Minv
      _ = ((Minv * delta) * (Minv * delta)).trace := by
        congr 1
  have htrace := trace_cfc_eq_sum A hA.isHermitian (barrierPathKernel u)
  rw [cfc_barrierPathKernel_eq A hA u hu] at htrace
  have htrace' : (1 - u) * (((delta * Minv) * (delta * Minv)).trace.re) =
      ∑ i, barrierPathKernel u (hA.isHermitian.eigenvalues i) := by
    simpa only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Minv, delta] using htrace
  change (1 - u) * (((Minv * delta) * (Minv * delta)).trace.re) = _
  rw [← hcycle]
  exact htrace'

private lemma relative_path_eq_spectral_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∫ u in (0 : ℝ)..1, (1 - u) *
        ((((1 + u • (A - 1))⁻¹ * (A - 1)) *
          ((1 + u • (A - 1))⁻¹ * (A - 1))).trace.re) =
      ∑ i, (hA.isHermitian.eigenvalues i -
        Real.log (hA.isHermitian.eigenvalues i) - 1) := by
  calc
    ∫ u in (0 : ℝ)..1, (1 - u) *
        ((((1 + u • (A - 1))⁻¹ * (A - 1)) *
          ((1 + u • (A - 1))⁻¹ * (A - 1))).trace.re) =
        ∫ u in (0 : ℝ)..1,
          ∑ i, barrierPathKernel u (hA.isHermitian.eigenvalues i) := by
            apply intervalIntegral.integral_congr
            intro u hu
            rw [Set.uIcc_of_le zero_le_one] at hu
            exact relative_trace_integrand_eq_sum A hA u hu
    _ = ∑ i, ∫ u in (0 : ℝ)..1,
          barrierPathKernel u (hA.isHermitian.eigenvalues i) := by
            rw [intervalIntegral.integral_finsetSum]
            intro i _
            exact barrierPathKernel_intervalIntegrable _ (hA.eigenvalues_pos i)
    _ = ∑ i, (hA.isHermitian.eigenvalues i -
        Real.log (hA.isHermitian.eigenvalues i) - 1) := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_barrierPathKernel _ (hA.eigenvalues_pos i)

private lemma path_integrand_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    let A := relativeCongruence rho sigma
    (((affineSegment rho sigma u)⁻¹ * (rho - sigma)) *
      ((affineSegment rho sigma u)⁻¹ * (rho - sigma))).trace.re =
    (((1 + u • (A - 1))⁻¹ * (A - 1)) *
      ((1 + u • (A - 1))⁻¹ * (A - 1))).trace.re := by
  let s : Matrix n n ℂ := CFC.sqrt sigma
  let A : Matrix n n ℂ := relativeCongruence rho sigma
  let M : Matrix n n ℂ := 1 + u • (A - 1)
  let m : Matrix n n ℂ := affineSegment rho sigma u
  let delta : Matrix n n ℂ := rho - sigma
  let deltaA : Matrix n n ℂ := A - 1
  let C : Matrix n n ℂ := M⁻¹ * deltaA
  have hsigma_nonneg : (0 : Matrix n n ℂ) ≤ sigma :=
    Matrix.nonneg_iff_posSemidef.mpr hSigma.posSemidef
  have hs_sq : s * s = sigma := by
    exact CFC.sqrt_mul_sqrt_self sigma hsigma_nonneg
  have hs_unit : IsUnit s := by
    change IsUnit (CFC.sqrt sigma)
    exact (CFC.isUnit_sqrt_iff sigma hsigma_nonneg).mpr hSigma.isUnit
  have hs_det : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det s).mp hs_unit
  have hs_inv_mul : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s hs_det
  have hs_mul_inv : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hs_det
  have hA_pos : A.PosDef := relativeCongruence_pos rho sigma hRho hSigma
  have hRho : rho = s * A * s := by
    calc
      rho = (s * s⁻¹) * rho * (s⁻¹ * s) := by
        rw [hs_mul_inv, hs_inv_mul, Matrix.one_mul, Matrix.mul_one]
      _ = s * (s⁻¹ * rho * s⁻¹) * s := by noncomm_ring
      _ = s * A * s := by rfl
  have hDelta : delta = s * deltaA * s := by
    simp only [delta, deltaA, hRho, ← hs_sq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one]
  have hM_affine : M = (1 - u) • (1 : Matrix n n ℂ) + u • A := by
    simp only [M]
    module
  have hM_pos : M.PosDef := by
    rw [hM_affine]
    by_cases huOne : u = 1
    · subst u
      simpa using hA_pos
    · exact (Matrix.PosDef.one.smul (sub_pos.mpr (lt_of_le_of_ne hu.2 huOne))).add_posSemidef
        (hA_pos.posSemidef.smul hu.1)
  have hM_det : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM_pos.isUnit
  have hm_factor : m = s * M * s := by
    simp only [m, affineSegment, hRho, ← hs_sq, hM_affine, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hm_inv : m⁻¹ = s⁻¹ * M⁻¹ * s⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hm_factor]
    calc
      (s * M * s) * (s⁻¹ * M⁻¹ * s⁻¹) =
          s * M * (s * s⁻¹) * M⁻¹ * s⁻¹ := by noncomm_ring
      _ = s * (M * M⁻¹) * s⁻¹ := by
        rw [hs_mul_inv]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = s * 1 * s⁻¹ := by rw [Matrix.mul_nonsing_inv M hM_det]
      _ = 1 := by simp only [Matrix.mul_one, hs_mul_inv]
  have hproduct : m⁻¹ * delta = s⁻¹ * C * s := by
    rw [hm_inv, hDelta]
    calc
      (s⁻¹ * M⁻¹ * s⁻¹) * (s * deltaA * s) =
          s⁻¹ * M⁻¹ * (s⁻¹ * s) * deltaA * s := by noncomm_ring
      _ = s⁻¹ * C * s := by simp only [hs_inv_mul, Matrix.mul_one, C, Matrix.mul_assoc]
  change ((m⁻¹ * delta) * (m⁻¹ * delta)).trace.re =
    ((M⁻¹ * deltaA) * (M⁻¹ * deltaA)).trace.re
  rw [hproduct]
  have hsquare : (s⁻¹ * C * s) * (s⁻¹ * C * s) = s⁻¹ * (C * C) * s := by
    calc
      (s⁻¹ * C * s) * (s⁻¹ * C * s) =
          s⁻¹ * C * (s * s⁻¹) * C * s := by noncomm_ring
      _ = s⁻¹ * (C * C) * s := by
        rw [hs_mul_inv]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hsquare]
  exact congrArg Complex.re (Matrix.trace_conj' hs_unit (C * C))

private lemma logDetPathEnergy_eq_spectral_sum {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef) :
    let e := (relativeCongruence_pos rho sigma hRho hSigma).isHermitian
    logDetPathEnergy rho sigma =
      ∑ i, (e.eigenvalues i - Real.log (e.eigenvalues i) - 1) := by
  let A : Matrix n n ℂ := relativeCongruence rho sigma
  have hA : A.PosDef := relativeCongruence_pos rho sigma hRho hSigma
  let e := hA.isHermitian
  calc
    logDetPathEnergy rho sigma =
        ∫ u in (0 : ℝ)..1, (1 - u) *
          ((((1 + u • (A - 1))⁻¹ * (A - 1)) *
            ((1 + u • (A - 1))⁻¹ * (A - 1))).trace.re) := by
              unfold logDetPathEnergy
              apply intervalIntegral.integral_congr
              intro u hu
              rw [Set.uIcc_of_le zero_le_one] at hu
              exact congrArg (fun z : ℝ => (1 - u) * z)
                (path_integrand_congruence rho sigma hRho hSigma u hu)
    _ = ∑ i, (e.eigenvalues i - Real.log (e.eigenvalues i) - 1) := by
      simpa only [e] using relative_path_eq_spectral_sum A hA

private lemma logDetDivergence_eq_spectral_sum {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef) :
    let e := (relativeCongruence_pos rho sigma hRho hSigma).isHermitian
    D5.S3.Resource.LogDetDivergence.logDetDivergence rho sigma =
      ∑ i, (e.eigenvalues i - Real.log (e.eigenvalues i) - 1) := by
  let s : Matrix n n ℂ := CFC.sqrt sigma
  let A : Matrix n n ℂ := relativeCongruence rho sigma
  have hsigma_nonneg : (0 : Matrix n n ℂ) ≤ sigma :=
    Matrix.nonneg_iff_posSemidef.mpr hSigma.posSemidef
  have hs_sq : s * s = sigma := CFC.sqrt_mul_sqrt_self sigma hsigma_nonneg
  have hs_star : Matrix.conjTranspose s = s := by
    simpa [s, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg sigma).isSelfAdjoint.star_eq
  have hs_unit : IsUnit s := by
    change IsUnit (CFC.sqrt sigma)
    exact (CFC.isUnit_sqrt_iff sigma hsigma_nonneg).mpr hSigma.isUnit
  have hs_inv_mul : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s
    ((Matrix.isUnit_iff_isUnit_det s).mp hs_unit)
  have hs_mul_inv : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s
    ((Matrix.isUnit_iff_isUnit_det s).mp hs_unit)
  have hA_pos : A.PosDef := relativeCongruence_pos rho sigma hRho hSigma
  have hsigma_inv : sigma⁻¹ = s⁻¹ * s⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hs_sq]
    calc
      s * s * (s⁻¹ * s⁻¹) = s * (s * s⁻¹) * s⁻¹ := by noncomm_ring
      _ = s * s⁻¹ := by simp only [hs_mul_inv, Matrix.mul_one]
      _ = 1 := hs_mul_inv
  have hsim : sigma⁻¹ * rho = s⁻¹ * A * s := by
    simp [A, relativeCongruence, s, hsigma_inv, Matrix.mul_assoc, hs_inv_mul]
  have htrace : (sigma⁻¹ * rho).trace.re = A.trace.re := by
    rw [hsim]
    exact congrArg Complex.re <| calc
      (s⁻¹ * A * s).trace = (s * s⁻¹ * A).trace := Matrix.trace_mul_cycle _ _ _
      _ = A.trace := by simp [hs_mul_inv]
  have hdet : (sigma⁻¹ * rho).det.re = A.det.re := by
    have hsdet : s.det * (s⁻¹).det = 1 := by
      rw [← Matrix.det_mul, hs_mul_inv, Matrix.det_one]
    have hdet_complex : (s⁻¹ * A * s).det = A.det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        (s⁻¹).det * A.det * s.det = A.det * (s.det * (s⁻¹).det) := by ring
        _ = A.det := by rw [hsdet, mul_one]
    rw [hsim]
    exact congrArg Complex.re hdet_complex
  let e := hA_pos.isHermitian
  have htraceA : A.trace.re = ∑ i, e.eigenvalues i := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues e]
    simp
  have hdetA : A.det.re = ∏ i, e.eigenvalues i := by
    rw [Matrix.IsHermitian.det_eq_prod_eigenvalues e]
    calc
      (∏ i, (e.eigenvalues i : ℂ)).re =
          (↑(∏ i, e.eigenvalues i) : ℂ).re := by
            exact congrArg Complex.re
              (Complex.ofReal_prod (s := Finset.univ) e.eigenvalues).symm
      _ = ∏ i, e.eigenvalues i := Complex.ofReal_re _
  have hlogprod : Real.log (∏ i, e.eigenvalues i) =
      ∑ i, Real.log (e.eigenvalues i) := by
    apply Real.log_prod
    intro i _
    exact ne_of_gt (hA_pos.eigenvalues_pos i)
  have heq : (∑ i, (e.eigenvalues i - Real.log (e.eigenvalues i) - 1)) =
      (∑ i, e.eigenvalues i) - ∑ i, Real.log (e.eigenvalues i) -
        (Fintype.card n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [D5.S3.Resource.LogDetDivergence.logDetDivergence, htrace, hdet, htraceA,
    hdetA, hlogprod, ← heq]

def itakuraSaito {n : Type*} [Fintype n] (p q : n → ℝ) : ℝ :=
  ∑ i, (p i / q i - Real.log (p i / q i) - 1)

def geometricKernel (a b : ℝ) : ℝ :=
  2 / Real.sqrt (a * b)

lemma inverse_product_eq_geometricKernel_sq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (a * b) = (geometricKernel a b / 2) ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hsqrt : Real.sqrt (a * b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab)
  rw [geometricKernel]
  field_simp [hsqrt, ne_of_gt hab]
  nlinarith [Real.sq_sqrt hab.le]

lemma diagonal_logDet_eq_itakuraSaito {n : Type*} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    D5.S3.Resource.LogDetDivergence.logDetDivergence
        (Matrix.diagonal fun i => (p i : ℂ))
        (Matrix.diagonal fun i => (q i : ℂ)) =
      itakuraSaito p q := by
  have hratio : ∀ i, (0 : ℝ) < p i / q i := fun i => div_pos (hp i) (hq i)
  have hlogprod : Real.log (∏ i, p i / q i) = ∑ i, Real.log (p i / q i) := by
    apply Real.log_prod
    intro i _
    exact ne_of_gt (hratio i)
  have hdiagInv : (Matrix.diagonal fun i => (q i : ℂ))⁻¹ =
      Matrix.diagonal fun i => ((q i : ℂ)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [ne_of_gt (hq i)]
    · simp [hij]
  have hterm : ∀ i, ((q i : ℂ)⁻¹ * (p i : ℂ)).re = p i / q i := by
    intro i
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [div_eq_mul_inv, mul_comm]
  have hsumRe : (∑ i, (q i : ℂ)⁻¹ * (p i : ℂ)).re = ∑ i, p i / q i := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hprod : ∏ i, (q i : ℂ)⁻¹ * (p i : ℂ) =
      ((∏ i, p i / q i : ℝ) : ℂ) := by
    calc
      ∏ i, (q i : ℂ)⁻¹ * (p i : ℂ) = ∏ i, ((p i / q i : ℝ) : ℂ) := by
        apply Finset.prod_congr rfl
        intro i _
        apply Complex.ext
        · exact hterm i
        · simp
      _ = ((∏ i, p i / q i : ℝ) : ℂ) :=
        (Complex.ofReal_prod (s := Finset.univ) (fun i => p i / q i)).symm
  rw [D5.S3.Resource.LogDetDivergence.logDetDivergence, hdiagInv,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.det_diagonal]
  rw [hsumRe, hprod, Complex.ofReal_re, hlogprod]
  unfold itakuraSaito
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp [div_eq_mul_inv]

theorem log_det_path_spectral_classical {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef) :
    D5.S3.Resource.LogDetDivergence.logDetDivergence rho sigma =
        logDetPathEnergy rho sigma ∧
    (let e := (relativeCongruence_pos rho sigma hRho hSigma).isHermitian
     D5.S3.Resource.LogDetDivergence.logDetDivergence rho sigma =
        ∑ i, barrierProfile (e.eigenvalues i)) ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      1 / (a * b) = (geometricKernel a b / 2) ^ 2) ∧
    (∀ p q : n → ℝ, (∀ i, 0 < p i) → (∀ i, 0 < q i) →
      D5.S3.Resource.LogDetDivergence.logDetDivergence
          (Matrix.diagonal fun i => (p i : ℂ))
          (Matrix.diagonal fun i => (q i : ℂ)) =
        itakuraSaito p q) := by
  have hpath := logDetPathEnergy_eq_spectral_sum rho sigma hRho hSigma
  have hspectral := logDetDivergence_eq_spectral_sum rho sigma hRho hSigma
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hspectral.trans hpath.symm
  · simpa only [barrierProfile] using hspectral
  · intro a b ha hb
    exact inverse_product_eq_geometricKernel_sq a b ha hb
  · intro p q hp hq
    exact diagonal_logDet_eq_itakuraSaito p q hp hq

end D5.S3.Resource.LogDet.PathSpectralClassical

#print axioms D5.S3.Resource.LogDet.PathSpectralClassical.log_det_path_spectral_classical

