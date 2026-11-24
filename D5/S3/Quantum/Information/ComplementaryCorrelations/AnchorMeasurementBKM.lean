/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Simpson bound on logarithmic means controls the dual norm of product measurement scores. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurement
import D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean
import D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
import D5.S3.Quantum.Recovery.BKMSpectralVariance
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-! Spectral comparison and duality for the existing observable and inverse BKM maps. -/

noncomputable section

namespace AnchorMeasurement

open Matrix MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  InnerProductSpace Kronecker Topology
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree (cfc_unitary_diagonal)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Divergence.LogDerivTrace
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (pair_kernel_eval)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega continuous_mpow)
open D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
open D5.S3.Quantum.Recovery.BKMSpectralVariance
  (trace_conjStarAlgAut_symm omega_isHermitian omegaLinear)
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (trace_hermitian_product_real)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)

local notation "LM" => (fun a b : ℝ => ∫ s : ℝ in 0..1, a ^ s * b ^ (1 - s))

private def inverseMean (a b : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), 1 / ((a + t) * (b + t))

private theorem lm_self {a : ℝ} (ha : 0 < a) : LM a a = a := by
  have h (s : ℝ) : a ^ s * a ^ (1 - s) = a := by
    rw [← Real.rpow_add ha, show s + (1 - s) = 1 by ring, Real.rpow_one]
  simp [h, intervalIntegral.integral_const]

-- BKMSpectralVariance has this scalar evaluation as a private lemma.
private theorem lm_mul_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    LM a b * (Real.log a - Real.log b) = a - b := by
  let r := Real.log (a / b)
  have hr : Real.exp r = a / b := Real.exp_log (div_pos ha hb)
  rw [← Real.log_div ha.ne' hb.ne']
  change LM a b * r = a - b
  by_cases hzero : r = 0
  · rw [hzero, Real.exp_zero] at hr
    have hab := (div_eq_iff hb.ne').mp hr.symm
    simp [hzero, hab]
  have h (s : ℝ) : a ^ s * b ^ (1 - s) = b * Real.exp (s * r) := by
    calc
      _ = Real.exp (Real.log b) * Real.exp (s * r) := by
        rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [r]
        rw [Real.log_div ha.ne' hb.ne']
        ring
      _ = _ := by rw [Real.exp_log hb]
  simp only [h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_right Real.exp hzero, zero_mul, one_mul,
    smul_eq_mul, integral_exp, hr, Real.exp_zero]
  field_simp

private theorem lm_mul_pairKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    LM a b * inverseMean a b = 1 := by
  rw [inverseMean, pair_kernel_eval a b ha hb]
  by_cases h : a = b
  · subst b
    rw [ite_eq_left rfl, lm_self ha]
    field_simp
  · rw [ite_eq_right h, ← mul_div_assoc, lm_mul_log ha hb, div_self (sub_ne_zero.mpr h)]

/-- The integral coefficient is the scalar logarithmic mean used in the Simpson estimate. -/
private theorem lm_eq_logarithmicMean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    LM a b = Omega.CovarianceToAnchor.logarithmicMean a b := by
  by_cases hab : a = b
  · subst b
    simpa [Omega.CovarianceToAnchor.logarithmicMean] using lm_self ha
  · rw [Omega.CovarianceToAnchor.logarithmicMean, ite_eq_right hab]
    apply (eq_div_iff _).2 (lm_mul_log ha hb)
    exact sub_ne_zero.mpr (fun h => hab (Real.log_injOn_pos ha hb h))

theorem logMean_le_simpson {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    LM a b ≤ (a + b + 4 * (Real.sqrt a * Real.sqrt b)) / 6 := by
  rw [lm_eq_logarithmicMean ha hb, ← Real.sqrt_mul ha.le]
  exact Omega.CovarianceToAnchor.logarithmic_mean_le_simpson ha hb

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ : Mat n}

private abbrev eigenBasis (hσ : σ.PosDef) := hσ.isHermitian.eigenvectorUnitary
private abbrev eigenvalue (hσ : σ.PosDef) := hσ.isHermitian.eigenvalues

private theorem mpow_entry (hσ : σ.PosDef) (r : ℝ) :
    inBasis (eigenBasis hσ) (mpow σ r) =
      diagonal (fun i : n => ((eigenvalue hσ i ^ r : ℝ) : ℂ)) := by
  rw [mpow, hσ.isHermitian.cfc_eq, Matrix.IsHermitian.cfc]
  exact StarAlgEquiv.symm_apply_apply _ _

-- This is the entry API of BKMSpectralVariance.omega_eigenbasis_entry,
-- emitted here as a draft because its pinned declaration is private.
theorem omega_entry (hσ : σ.PosDef) (X : Mat n) (i j : n) :
    inBasis (eigenBasis hσ) (omega σ X) i j =
      (LM (eigenvalue hσ i) (eigenvalue hσ j) : ℂ) * inBasis (eigenBasis hσ) X i j := by
  let F := (Unitary.conjStarAlgAut ℂ (Mat n) (eigenBasis hσ)).symm
  let e := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap.comp
    F.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hp := continuous_mpow σ hσ
  have hc : Continuous (fun s : ℝ => 1 - s) := continuous_const.sub continuous_id
  have hi : IntervalIntegrable (fun s : ℝ => mpow σ s * X * mpow σ (1 - s))
      volume 0 1 := ((hp.mul (continuous_const (y := X))).mul (hp.comp hc)).intervalIntegrable 0 1
  change e (∫ s : ℝ in 0..1, mpow σ s * X * mpow σ (1 - s)) = _
  rw [← e.intervalIntegral_comp_comm hi]
  have he (s : ℝ) : e (mpow σ s * X * mpow σ (1 - s)) =
      ((eigenvalue hσ i ^ s * eigenvalue hσ j ^ (1 - s) : ℝ) : ℂ) *
        inBasis (eigenBasis hσ) X i j := by
    change inBasis (eigenBasis hσ) (mpow σ s * X * mpow σ (1 - s)) i j = _
    simp only [inBasis, map_mul] at ⊢
    change (inBasis (eigenBasis hσ) (mpow σ s) * inBasis (eigenBasis hσ) X *
      inBasis (eigenBasis hσ) (mpow σ (1 - s))) i j = _
    rw [mpow_entry hσ, mpow_entry hσ, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [inBasis, Complex.ofReal_mul]
    exact mul_right_comm _ _ _
  simp only [he, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
theorem logDeriv_entry (hσ : σ.PosDef) (X : Mat n) (i j : n) :
    inBasis (eigenBasis hσ) (logDeriv σ X) i j =
      (inverseMean (eigenvalue hσ i) (eigenvalue hσ j) : ℂ) *
        inBasis (eigenBasis hσ) X i j := by
  let U := eigenBasis hσ
  let F := (Unitary.conjStarAlgAut ℂ (Mat n) U).symm
  let e := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap.comp
    F.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let R (t : ℝ) := (σ + t • 1)⁻¹
  change e (∫ t in Set.Ioi (0 : ℝ), R t * X * R t) = _
  rw [← e.integral_comp_comm (logDeriv_integrable σ X hσ)]
  rw [inverseMean, ← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hR : F (R t) = diagonal (fun k => ((eigenvalue hσ k + t : ℝ) : ℂ)⁻¹) := by
    rw [show R t = _ from resolvent_eq_spectral σ hσ t ht.le]
    change F (F.symm (diagonal (fun k => ((eigenvalue hσ k + t : ℝ) : ℂ)⁻¹))) = _
    exact F.apply_symm_apply _
  change (F (R t * X * R t)) i j =
    ((1 / ((eigenvalue hσ i + t) * (eigenvalue hσ j + t)) : ℝ) : ℂ) * F X i j
  rw [map_mul, map_mul, hR, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_add, mul_inv]
  exact mul_right_comm _ _ _

/-- The actual BKM integral applied to the log resolvent returns the tangent.
This uses the pair kernel including the repeated-eigenvalue branch. -/
theorem omega_logDeriv (hσ : σ.PosDef) (X : Mat n) : omega σ (logDeriv σ X) = X := by
  apply ((Unitary.conjStarAlgAut ℂ (Mat n) (eigenBasis hσ)).symm).injective
  change inBasis (eigenBasis hσ) _ = inBasis (eigenBasis hσ) X
  ext i j
  rw [omega_entry hσ, logDeriv_entry hσ, ← mul_assoc, ← Complex.ofReal_mul,
    lm_mul_pairKernel (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j), Complex.ofReal_one, one_mul]

theorem logDeriv_omega (hσ : σ.PosDef) (X : Mat n) : logDeriv σ (omega σ X) = X := by
  apply ((Unitary.conjStarAlgAut ℂ (Mat n) (eigenBasis hσ)).symm).injective
  change inBasis (eigenBasis hσ) _ = inBasis (eigenBasis hσ) X
  ext i j
  rw [logDeriv_entry hσ, omega_entry hσ, ← mul_assoc]
  have h := lm_mul_pairKernel (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j)
  rw [mul_comm] at h
  rw [← Complex.ofReal_mul, h, Complex.ofReal_one, one_mul]

/-- BKM Cauchy–Schwarz in the repository's metric coordinates. -/
theorem bkm_pair_sq_le (hσ : σ.PosDef) (D O : Mat n) (hD : D.IsHermitian) (hO : O.IsHermitian) :
    (D * O).trace.re ^ 2 ≤
      (D * logDeriv σ D).trace.re * (O * omega σ O).trace.re := by
  let J := metricCoordinates σ hσ
  let L := logDeriv σ D
  have hJ (A B : Mat n) := metricCoordinates_inner σ hσ A B
  have hpair : (inner ℂ (J O) (J L)).re = (D * O).trace.re := by
    rw [hJ, bkmInner, omega_logDeriv hσ, hO.eq, Matrix.trace_mul_comm]
  have hleft : ‖J O‖ ^ 2 = (O * omega σ O).trace.re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hJ, bkmInner, hO.eq]
    rfl
  have hright : ‖J L‖ ^ 2 = (D * logDeriv σ D).trace.re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hJ, bkmInner, omega_logDeriv hσ]
    have hh : ((Lᴴ * D).trace) = star ((D * L).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hD.eq]
    rw [hh]
    rfl
  have hc := (Complex.abs_re_le_norm (inner ℂ (J O) (J L))).trans
    (norm_inner_le_norm (𝕜 := ℂ) (J O) (J L))
  have hh := pow_le_pow_left₀ (abs_nonneg _) hc 2
  rw [sq_abs, hpair, mul_pow, hleft, hright] at hh
  exact hh.trans_eq (mul_comm _ _)

theorem bkm_inverse_nonneg (hσ : σ.PosDef) (D : Mat n) (hD : D.IsHermitian) :
    0 ≤ (D * logDeriv σ D).trace.re := by
  let L := logDeriv σ D
  have h : ‖metricCoordinates σ hσ L‖ ^ 2 = (D * L).trace.re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), metricCoordinates_inner, bkmInner, omega_logDeriv hσ]
    have hh : (Lᴴ * D).trace = star ((D * L).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hD.eq]
    rw [hh]
    rfl
  exact h ▸ sq_nonneg _

private theorem trace_weighted_entry (U : Matrix.unitaryGroup n ℂ)
    (X Y : Mat n) (k : n → n → ℝ)
    (h : ∀ i j, inBasis U Y i j = (k i j : ℂ) * inBasis U X i j) :
    (Xᴴ * Y).trace.re = ∑ i, ∑ j, k i j * Complex.normSq (inBasis U X i j) := by
  let F := (Unitary.conjStarAlgAut ℂ (Mat n) U).symm
  rw [← trace_conjStarAlgAut_symm U (Xᴴ * Y)]
  change (F (star X * Y)).trace.re = _
  rw [map_mul, map_star]
  change (((inBasis U X)ᴴ * inBasis U Y).trace).re = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he (z : ℂ) (a : ℝ) :
      (star z * ((a : ℂ) * z)).re = a * Complex.normSq z := by
    rw [show star z * ((a : ℂ) * z) = (a : ℂ) * (z * star z) by ring]
    change ((a : ℂ) * (z * (starRingEnd ℂ) z)).re = _
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact he _ _

theorem omega_le_simpson (hσ : σ.PosDef) (O : Mat n) (hO : O.IsHermitian) :
    (O * omega σ O).trace.re ≤
      (σ * O * O).trace.re / 3 + 2 * (CFC.sqrt σ * O * CFC.sqrt σ * O).trace.re / 3 := by
  let U := eigenBasis hσ
  let l := eigenvalue hσ
  let F := (Unitary.conjStarAlgAut ℂ (Mat n) U).symm
  have hσdiag : inBasis U σ = diagonal (fun i => (l i : ℂ)) := by
    rw [hσ.isHermitian.spectral_theorem]
    exact F.apply_symm_apply _
  have hroot : inBasis U (CFC.sqrt σ) = diagonal (fun i => (Real.sqrt (l i) : ℂ)) := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hσ.posSemidef.nonneg, ← mpow]
    simpa only [Real.sqrt_eq_rpow] using mpow_entry hσ (1 / 2)
  let Y := (1 / 6 : ℝ) • (σ * O + O * σ) +
    (2 / 3 : ℝ) • (CFC.sqrt σ * O * CFC.sqrt σ)
  have hY (i j : n) : inBasis U Y i j =
      (((l i + l j + 4 * (Real.sqrt (l i) * Real.sqrt (l j))) / 6 : ℝ) : ℂ) *
        inBasis U O i j := by
    change F Y i j = _
    have hsmul (c : ℝ) (A : Mat n) : F (c • A) = c • F A :=
      F.toAlgEquiv.toLinearEquiv.map_smul_of_tower c A
    simp only [Y, map_add, hsmul, map_mul]
    change (((1 / 6 : ℝ) • (inBasis U σ * inBasis U O + inBasis U O * inBasis U σ) +
      (2 / 3 : ℝ) • (inBasis U (CFC.sqrt σ) * inBasis U O * inBasis U (CFC.sqrt σ))) i j) = _
    rw [hσdiag, hroot]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Complex.real_smul]
    push_cast
    ring
  have h := trace_weighted_entry U O (omega σ O)
    (fun i j => LM (l i) (l j)) (omega_entry hσ O)
  have hcomparison : (Oᴴ * omega σ O).trace.re ≤ (Oᴴ * Y).trace.re := by
    rw [h, trace_weighted_entry U O Y _ hY]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (logMean_le_simpson (hσ.eigenvalues_pos i)
        (hσ.eigenvalues_pos j)) (Complex.normSq_nonneg _)
  rw [hO.eq] at hcomparison
  have h₁ : (O * (σ * O)).trace = (σ * O * O).trace := by
    rw [Matrix.trace_mul_comm]
  have h₂ : (O * (O * σ)).trace = (σ * O * O).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have h₃ : (O * (CFC.sqrt σ * O * CFC.sqrt σ)).trace =
      (CFC.sqrt σ * O * CFC.sqrt σ * O).trace := Matrix.trace_mul_comm _ _
  refine hcomparison.trans_eq ?_
  simp only [Y, Matrix.mul_add, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, h₁, h₂, h₃]
  ring

end Spectral

private theorem product_mpow {A : Mat Alice} {B : Mat Bob}
    (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    mpow (A ⊗ₖ B) t = mpow A t ⊗ₖ mpow B t := by
  let U := productBasis hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let b := hB.isHermitian.eigenvalues
  have hdiag : A ⊗ₖ B = (U : Mat Joint) *
      diagonal (fun p : Joint => ((a p.1 * b p.2 : ℝ) : ℂ)) * star (U : Mat Joint) := by
    simpa [U, productBasis, a, b, Complex.ofReal_mul] using
      kronecker_eq_conj_diagonal_eigenvalues hA.isHermitian hB.isHermitian
  unfold mpow
  rw [hdiag, cfc_unitary_diagonal, hA.isHermitian.cfc_eq, hB.isHermitian.cfc_eq]
  simp only [U, productBasis, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal, Function.comp_apply]
  congr 2
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [a, b, Real.mul_rpow (hA.eigenvalues_pos p.1).le
      (hB.eigenvalues_pos p.2).le, Complex.ofReal_mul]
  · simp [hpq]

private theorem trace_mpow_sandwich {n : Type*} [Fintype n] [DecidableEq n]
    {A : Mat n} (hA : A.PosDef) (X : Mat n) (t : ℝ) :
    (mpow A t * X * mpow A (1 - t)).trace = (A * X).trace := by
  rw [Matrix.trace_mul_cycle]
  have hp (r : ℝ) : mpow A r = A ^ r := (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm
  rw [hp, hp, ← CFC.rpow_add hA.isUnit, show 1 - t + t = 1 by ring,
    CFC.rpow_one _ hA.posSemidef.nonneg]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- An observable BKM image of a product of centered tests is marginal free.
The partial-trace computation is made under the actual BKM integral. -/
theorem omega_centered_product_marginalFree
    {A : Mat Alice} {B : Mat Bob} (hA : A.PosDef) (hB : B.PosDef)
    {X : Mat Alice} {Y : Mat Bob} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hAX : (A * X).trace = 0) (hBY : (B * Y).trace = 0) :
    MarginalFree (omega (A ⊗ₖ B) (X ⊗ₖ Y)) := by
  let Pr : Mat Joint →ₗ[ℂ] Mat Alice :=
    { toFun := partialTraceRight
      map_add' := partialTraceRight_add
      map_smul' := fun c Z => by
        ext i j
        simp only [partialTraceRight, Matrix.smul_apply, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum] }
  let Pl : Mat Joint →ₗ[ℂ] Mat Bob :=
    { toFun := partialTraceLeft
      map_add' := partialTraceLeft_add
      map_smul' := fun c Z => by
        ext i j
        simp only [partialTraceLeft, Matrix.smul_apply, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum] }
  let S := A ⊗ₖ B
  let P := X ⊗ₖ Y
  have hS : S.PosDef := hA.kronecker hB
  have hP : P.IsHermitian := by
    change Pᴴ = P
    simp only [P, Matrix.conjTranspose_kronecker, hX.eq, hY.eq]
  let f : ℝ → Mat Joint := fun t => mpow S t * P * mpow S (1 - t)
  have hcont := continuous_mpow S hS
  have hsub : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
  have hi : IntervalIntegrable f volume 0 1 :=
    ((hcont.mul (continuous_const (y := P))).mul (hcont.comp hsub)).intervalIntegrable 0 1
  have hprod (t : ℝ) : f t =
      (mpow A t * X * mpow A (1 - t)) ⊗ₖ (mpow B t * Y * mpow B (1 - t)) := by
    simp only [f, S, P, product_mpow hA hB, ← Matrix.mul_kronecker_mul]
  refine ⟨omega_isHermitian hS hP, ?_, ?_⟩
  · change Pr.toContinuousLinearMap (∫ t : ℝ in 0..1, f t) = 0
    rw [← Pr.toContinuousLinearMap.intervalIntegral_comp_comm hi]
    have h (t : ℝ) : Pr.toContinuousLinearMap (f t) = 0 := by
      change partialTraceRight (f t) = 0
      rw [hprod]
      change partialTraceRight (Matrix.kronecker _ _) = 0
      rw [partialTraceRight_kronecker, trace_mpow_sandwich hB, hBY, zero_smul]
    simp only [h, intervalIntegral.integral_zero]
  · change Pl.toContinuousLinearMap (∫ t : ℝ in 0..1, f t) = 0
    rw [← Pl.toContinuousLinearMap.intervalIntegral_comp_comm hi]
    have h (t : ℝ) : Pl.toContinuousLinearMap (f t) = 0 := by
      change partialTraceLeft (f t) = 0
      rw [hprod]
      change partialTraceLeft (Matrix.kronecker _ _) = 0
      rw [partialTraceLeft_kronecker, trace_mpow_sandwich hA, hAX, zero_smul]
    simp only [h, intervalIntegral.integral_zero]

private theorem MarginalFree.add {D E : JointMatrix} (hD : MarginalFree D)
    (hE : MarginalFree E) : MarginalFree (D + E) :=
  ⟨hD.1.add hE.1, by rw [partialTraceRight_add, hD.2.1, hE.2.1, add_zero],
    by rw [partialTraceLeft_add, hD.2.2, hE.2.2, add_zero]⟩

private theorem trace_observable_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (S : Mat n) (hS : S.IsHermitian) (a : n → ℝ)
    (ha : (∑ i, readout U S i * a i) = 0) : (S * observable U a).trace = 0 :=
  Complex.ext ((trace_observable U S a).trans ha)
    (trace_hermitian_product_real S _ hS (observable_isHermitian U a))

/-- The reverse Gram-duality witness stays in the same tangent space for
two slots built from the actual centered classical scores. -/
theorem omega_centered_two_slot_marginalFree
    (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ)
    {A : Mat Alice} {B : Mat Bob} (hA : A.PosDef) (hB : B.PosDef)
    (aQ aR : Alice → ℝ) (bQ bR : Bob → ℝ)
    (haQ : (∑ i, readout UQ A i * aQ i) = 0) (haR : (∑ i, readout UR A i * aR i) = 0)
    (hbQ : (∑ j, readout VQ B j * bQ j) = 0) (hbR : (∑ j, readout VR B j * bR j) = 0) :
    MarginalFree (omega (A ⊗ₖ B)
      (observable UQ aQ ⊗ₖ observable VQ bQ + observable UR aR ⊗ₖ observable VR bR)) := by
  have hQ := omega_centered_product_marginalFree hA hB
    (observable_isHermitian UQ aQ) (observable_isHermitian VQ bQ)
    (trace_observable_eq_zero UQ A hA.isHermitian aQ haQ)
    (trace_observable_eq_zero VQ B hB.isHermitian bQ hbQ)
  have hR := omega_centered_product_marginalFree hA hB
    (observable_isHermitian UR aR) (observable_isHermitian VR bR)
    (trace_observable_eq_zero UR A hA.isHermitian aR haR)
    (trace_observable_eq_zero VR B hB.isHermitian bR hbR)
  change MarginalFree (omegaLinear (hA.kronecker hB) (_ + _))
  rw [map_add]
  exact hQ.add hR

/-- The sufficient Gram bound is consumed only on the two exact Fisher
score witnesses. No infinite supremum is needed for this direction. -/
theorem anchorQuadraticIn_nonneg_of_simpson
    (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ)
    (α : DensityState Alice) (β : DensityState Bob)
    (hα : (densityMatrix α).PosDef) (hβ : (densityMatrix β).PosDef)
    (hgram : ∀ (aQ aR : Alice → ℝ) (bQ bR : Bob → ℝ),
      (∑ i, readout UQ (densityMatrix α) i * aQ i) = 0 →
      (∑ i, readout UR (densityMatrix α) i * aR i) = 0 →
      (∑ j, readout VQ (densityMatrix β) j * bQ j) = 0 →
      (∑ j, readout VR (densityMatrix β) j * bR j) = 0 →
      let σ := densityMatrix (productState α β)
      let O := observable UQ aQ ⊗ₖ observable VQ bQ +
        observable UR aR ⊗ₖ observable VR bR
      (σ * O * O).trace.re / 3 + 2 * (CFC.sqrt σ * O * CFC.sqrt σ * O).trace.re / 3 ≤
        (densityMatrix α * observable UQ (fun i => (aQ i) ^ 2)).trace.re *
          (densityMatrix β * observable VQ (fun j => (bQ j) ^ 2)).trace.re +
        (densityMatrix α * observable UR (fun i => (aR i) ^ 2)).trace.re *
          (densityMatrix β * observable VR (fun j => (bR j) ^ 2)).trace.re)
    {D : JointMatrix} (hD : MarginalFree D) :
    0 ≤ anchorQuadraticIn UQ UR VQ VR α β D := by
  let σ := densityMatrix (productState α β)
  have hσ : σ.PosDef := productMatrix_posDef α β hα hβ
  obtain ⟨aQ, bQ, haQ, hbQ, hpairQ, hvarQ⟩ :=
    measurementFisher_centered α β hα hβ UQ VQ hD
  obtain ⟨aR, bR, haR, hbR, hpairR, hvarR⟩ :=
    measurementFisher_centered α β hα hβ UR VR hD
  let O := observable UQ aQ ⊗ₖ observable VQ bQ +
    observable UR aR ⊗ₖ observable VR bR
  let f := measurementFisher UQ VQ σ D + measurementFisher UR VR σ D
  let e := (D * logDeriv σ D).trace.re
  have hO : O.IsHermitian := by
    change Oᴴ = O
    simp only [O, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
      (observable_isHermitian UQ aQ).eq, (observable_isHermitian UR aR).eq,
      (observable_isHermitian VQ bQ).eq, (observable_isHermitian VR bR).eq]
  have he : 0 ≤ e := bkm_inverse_nonneg hσ D hD.1
  have hpair : (D * O).trace.re = f := by
    simp only [O, f, Matrix.mul_add, Matrix.trace_add, Complex.add_re, hpairQ, hpairR]
    rfl
  have hmajor := hgram aQ aR bQ bR haQ haR hbQ hbR
  change _ ≤ _ at hmajor
  rw [hvarQ, hvarR] at hmajor
  have hg : (O * omega σ O).trace.re ≤ f :=
    (omega_le_simpson hσ O hO).trans hmajor
  have hsq : f ^ 2 ≤ e * f := by
    simpa only [hpair] using (bkm_pair_sq_le hσ D O hD.1 hO).trans
      (mul_le_mul_of_nonneg_left hg he)
  have hf : f ≤ e := by
    by_cases h : 0 < f
    · by_contra! hlt
      have hpos := mul_pos h (sub_pos.mpr hlt)
      nlinarith only [hpos, hsq]
    · exact (le_of_not_gt h).trans he
  change 0 ≤ e - measurementFisher UQ VQ σ D - measurementFisher UR VR σ D
  dsimp [f] at hf
  linarith

/-- Reverse BKM duality, with the exact tangent membership isolated.
The remaining specialization is the vanishing of both partial traces of omega
on the product-centered test. -/
theorem gram_le_of_anchorQuadraticIn_nonneg
    (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ)
    (α : DensityState Alice) (β : DensityState Bob)
    (hα : (densityMatrix α).PosDef) (hβ : (densityMatrix β).PosDef)
    (hacc : ∀ D : JointMatrix, MarginalFree D → 0 ≤ anchorQuadraticIn UQ UR VQ VR α β D)
    (aQ aR : Alice → ℝ) (bQ bR : Bob → ℝ) :
    let σ := densityMatrix (productState α β)
    let O := observable UQ aQ ⊗ₖ observable VQ bQ +
      observable UR aR ⊗ₖ observable VR bR
    MarginalFree (omega σ O) →
      (O * omega σ O).trace.re ≤
        (densityMatrix α * observable UQ (fun i => (aQ i) ^ 2)).trace.re *
          (densityMatrix β * observable VQ (fun j => (bQ j) ^ 2)).trace.re +
        (densityMatrix α * observable UR (fun i => (aR i) ^ 2)).trace.re *
          (densityMatrix β * observable VR (fun j => (bR j) ^ 2)).trace.re := by
  dsimp only
  intro hD
  let σ := densityMatrix (productState α β)
  let O := observable UQ aQ ⊗ₖ observable VQ bQ +
    observable UR aR ⊗ₖ observable VR bR
  let D := omega σ O
  have h := hacc D hD
  change 0 ≤ (D * logDeriv σ D).trace.re -
    measurementFisher UQ VQ σ D - measurementFisher UR VR σ D at h
  have hInv : logDeriv σ D = O := logDeriv_omega (productMatrix_posDef α β hα hβ) O
  rw [hInv] at h
  have hQ := measurementFisher_dual_le α β hα hβ UQ VQ D aQ bQ
  have hR := measurementFisher_dual_le α β hα hβ UR VR D aR bR
  have hsplit : (D * O).trace.re =
      (D * (observable UQ aQ ⊗ₖ observable VQ bQ)).trace.re +
      (D * (observable UR aR ⊗ₖ observable VR bR)).trace.re := by
    simp only [O, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  change (O * D).trace.re ≤ _
  rw [Matrix.trace_mul_comm, hsplit]
  rw [hsplit] at h
  linarith only [h, hQ, hR]

end AnchorMeasurement
