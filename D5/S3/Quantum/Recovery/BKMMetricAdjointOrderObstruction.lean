/- GID: D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local order along an attainable measurement line obstructs positive BKM recovery. -/

import D5.S3.Quantum.Matrix.ExponentialFirstResponse
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Divergence.LogDerivTrace
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # BKM local-order obstruction for an actual projective measurement -/

noncomputable section

open Matrix MeasureTheory Set Filter NormedSpace
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Matrix.ExponentialFirstResponse (derivative derivative_apply)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (pair_kernel_eval)
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard (hadamard hadamard_unitary)
open D5.S3.Divergence.LogDerivTrace (logDeriv logDeriv_integrable resolvent_eq_spectral)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

namespace D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction

private abbrev Mat (n : Type*) := Matrix n n ℂ

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev UMat (n : Type*) [Fintype n] [DecidableEq n] := Matrix.unitaryGroup n ℂ

private abbrev basisChange (U : UMat n) := Unitary.conjStarAlgAut ℂ (Mat n) U

private def diagReal (p : n → ℝ) : Mat n := diagonal fun k => (p k : ℂ)

private def diagRealCLM : (n → ℝ) →L[ℝ] Mat n :=
  ((Matrix.diagonalLinearMap n ℝ ℂ).toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun k => Complex.ofRealCLM.comp (ContinuousLinearMap.proj k))

private def entry (i j : n) : Mat n →L[ℂ] ℂ :=
  ((Matrix.stdBasis ℂ n n).equivFun.toContinuousLinearEquiv.toContinuousLinearMap |> fun L =>
    (ContinuousLinearMap.proj (i, j)).comp L)

private theorem entry_apply (X : Mat n) (i j : n) : entry i j X = X i j := by
  simp [entry, Matrix.stdBasis]

private theorem conjugated_cfc (a : Mat n) (ha : a.PosDef) (f : ℝ → ℝ) :
    (basisChange ha.isHermitian.eigenvectorUnitary).symm (cfc f a) =
      diagReal (f ∘ ha.isHermitian.eigenvalues) := by
  rw [ha.isHermitian.cfc_eq]
  exact (basisChange ha.isHermitian.eigenvectorUnitary).symm_apply_apply _

private theorem exp_log_smul (a : Mat n) (ha : a.PosDef) (u : ℝ) :
    exp (u • CFC.log a) = mpow a u := by
  have hc : ContinuousOn Real.log (spectrum ℝ a) := by
    apply Real.continuousOn_log.mono
    rw [ha.isHermitian.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨k, rfl⟩
    exact (ha.eigenvalues_pos k).ne'
  rw [← CFC.real_exp_eq_normedSpace_exp (IsSelfAdjoint.log.smul u), CFC.log,
    ← cfc_smul u Real.log a hc,
    ← cfc_comp' Real.exp (fun x => u • Real.log x) a (by fun_prop) (by fun_prop)
      ha.isHermitian.isSelfAdjoint]
  apply (basisChange ha.isHermitian.eigenvectorUnitary).symm.injective
  rw [conjugated_cfc a ha]
  unfold mpow
  rw [conjugated_cfc a ha]
  congr 1
  funext k
  simp [Real.rpow_def_of_pos (ha.eigenvalues_pos k), mul_comm]

/-- The actual logarithmic-mean Bochner integral. -/
def omega (a X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ u : ℝ in 0..1, mpow a u * X * mpow a (1 - u)

private theorem derivative_eq_omega (a : Mat n) (ha : a.PosDef) (X : Mat n) :
    derivative (CFC.log a) X = omega a X := by
  rw [derivative_apply, omega]
  simp_rw [exp_log_smul a ha]
  simpa using (intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) (fun u => mpow a u * X * mpow a (1 - u)) 1)

private theorem continuous_mpow (a : Mat n) (ha : a.PosDef) :
    Continuous (fun u : ℝ => mpow a u) := by
  have he (u : ℝ) : mpow a u = basisChange ha.isHermitian.eigenvectorUnitary
      (diagReal fun k => Real.exp (u * Real.log (ha.isHermitian.eigenvalues k))) := by
    apply (basisChange ha.isHermitian.eigenvectorUnitary).symm.injective
    rw [StarAlgEquiv.symm_apply_apply, mpow, conjugated_cfc a ha]
    congr 1
    funext k
    simp [Real.rpow_def_of_pos (ha.eigenvalues_pos k), mul_comm]
  simp_rw [he]
  apply (basisChange ha.isHermitian.eigenvectorUnitary).toAlgEquiv.toLinearEquiv.continuous.comp
  change Continuous (fun u : ℝ => diagRealCLM (fun k => Real.exp
    (u * Real.log (ha.isHermitian.eigenvalues k))))
  fun_prop

private def logMean (x y : ℝ) : ℝ :=
  if x = y then x else (x - y) / (Real.log x - Real.log y)

private theorem logMean_integral (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ u : ℝ in 0..1, x ^ u * y ^ (1 - u)) = logMean x y := by
  by_cases h : x = y
  · subst y
    simp only [logMean, if_true, ← Real.rpow_add hx]
    norm_num
  · let c := Real.log x - Real.log y
    have hc : c ≠ 0 := sub_ne_zero.mpr (fun he => h (Real.strictMonoOn_log.injOn hx hy he))
    have hf (u : ℝ) : x ^ u * y ^ (1 - u) = y * Real.exp (c * u) := by
      rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add,
        ← Real.exp_log hy, ← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    simp_rw [hf]
    rw [intervalIntegral.integral_const_mul]
    have hd (u : ℝ) : HasDerivAt (fun t => Real.exp (c * t) / c) (Real.exp (c * u)) u := by
      convert ((Real.hasDerivAt_exp (c * u)).comp u ((hasDerivAt_id u).const_mul c)).div_const c using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      (by fun_prop : Continuous (fun u : ℝ => Real.exp (c * u))).intervalIntegrable]
    rw [logMean, if_neg h]
    simp only [mul_one, mul_zero, Real.exp_zero]
    have he : Real.exp c = x / y := by
      dsimp [c]
      rw [Real.exp_sub, Real.exp_log hx, Real.exp_log hy]
    rw [he]
    change y * (x / y / c - 1 / c) = (x - y) / c
    field_simp
    <;> ring

private theorem omega_entry (a X : Mat n) (ha : a.PosDef) (i j : n) :
    (basisChange ha.isHermitian.eigenvectorUnitary).symm (omega a X) i j =
      (logMean (ha.isHermitian.eigenvalues i) (ha.isHermitian.eigenvalues j) : ℂ) *
        (basisChange ha.isHermitian.eigenvectorUnitary).symm X i j := by
  let U := basisChange ha.isHermitian.eigenvectorUnitary
  let L := (entry i j).comp U.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hi : IntervalIntegrable (fun u : ℝ => mpow a u * X * mpow a (1 - u)) volume 0 1 :=
    (((continuous_mpow a ha).mul continuous_const).mul
      ((continuous_mpow a ha).comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hf (u : ℝ) : L (mpow a u * X * mpow a (1 - u)) =
      ((ha.isHermitian.eigenvalues i ^ u * ha.isHermitian.eigenvalues j ^ (1 - u) : ℝ) : ℂ) *
        U.symm X i j := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearEquiv.coe_toContinuousLinearEquiv, entry_apply, AlgEquiv.toLinearEquiv_apply]
    change U.symm (mpow a u * X * mpow a (1 - u)) i j = _
    rw [map_mul, map_mul]
    simp only [U, mpow, conjugated_cfc a ha, diagReal, Function.comp_apply,
      diagonal_mul, mul_diagonal, Complex.ofReal_mul]
    ring
  rw [show U.symm (omega a X) i j = L (omega a X) by simp [L, entry_apply],
    omega, ← L.intervalIntegral_comp_comm hi]
  simp_rw [hf]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    logMean_integral _ _ (ha.eigenvalues_pos i) (ha.eigenvalues_pos j)]

private theorem resolvent_pair (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (∫ t in Ioi (0 : ℝ), ((x + t : ℝ) : ℂ)⁻¹ * z * ((y + t : ℝ) : ℂ)⁻¹) =
      ((logMean x y : ℂ))⁻¹ * z := by
  have hf (t : ℝ) : ((x + t : ℝ) : ℂ)⁻¹ * z * ((y + t : ℝ) : ℂ)⁻¹ =
      ((1 / ((x + t) * (y + t)) : ℝ) : ℂ) * z := by
    push_cast
    simp only [one_div, mul_inv_rev]
    ring
  simp_rw [hf]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_ofReal, pair_kernel_eval x y hx hy]
  congr 1
  by_cases h : x = y <;> simp [logMean, h, div_eq_mul_inv, mul_comm]

private theorem logDeriv_entry (a X : Mat n) (ha : a.PosDef) (i j : n) :
    (basisChange ha.isHermitian.eigenvectorUnitary).symm (logDeriv a X) i j =
      (logMean (ha.isHermitian.eigenvalues i) (ha.isHermitian.eigenvalues j) : ℂ)⁻¹ *
        (basisChange ha.isHermitian.eigenvectorUnitary).symm X i j := by
  let U := basisChange ha.isHermitian.eigenvectorUnitary
  let L := (entry i j).comp U.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  rw [show U.symm (logDeriv a X) i j = L (logDeriv a X) by simp [L, entry_apply]]
  unfold logDeriv
  rw [← L.integral_comp_comm (logDeriv_integrable a X ha)]
  refine Eq.trans (integral_congr_ae ?_) (resolvent_pair _ _ (ha.eigenvalues_pos i) (ha.eigenvalues_pos j) _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hR : U.symm ((a + t • 1)⁻¹) =
      diagonal (fun k => ((ha.isHermitian.eigenvalues k + t : ℝ) : ℂ)⁻¹) := by
    rw [resolvent_eq_spectral a ha t ht.le]
    exact U.symm_apply_apply _
  change entry i j (U.symm ((a + t • 1)⁻¹ * X * (a + t • 1)⁻¹)) = _
  simp only [entry_apply, map_mul, hR, diagonal_mul, mul_diagonal]

private theorem logMean_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < logMean x y := by
  unfold logMean
  split_ifs with h
  · exact hx
  · rcases lt_or_gt_of_ne h with hxy | hyx
    · exact div_pos_of_neg_of_neg (sub_neg.mpr hxy) (sub_neg.mpr (Real.log_lt_log hx hxy))
    · exact div_pos (sub_pos.mpr hyx) (sub_pos.mpr (Real.log_lt_log hy hyx))

private theorem logDeriv_omega (a X : Mat n) (ha : a.PosDef) : logDeriv a (omega a X) = X := by
  apply (basisChange ha.isHermitian.eigenvectorUnitary).symm.injective
  ext i j
  rw [logDeriv_entry a _ ha, omega_entry a X ha, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (logMean_pos _ _ (ha.eigenvalues_pos i) (ha.eigenvalues_pos j)).ne'

private theorem logDeriv_diag (p : n → ℝ) (hp : ∀ k, 0 < p k) (X : Mat n) (i j : n) :
    logDeriv (diagReal p) X i j = (logMean (p i) (p j) : ℂ)⁻¹ * X i j := by
  have hpD : (diagReal p).PosDef := Matrix.posDef_diagonal_iff.mpr (fun k => by exact_mod_cast hp k)
  rw [show logDeriv (diagReal p) X i j = entry i j (logDeriv (diagReal p) X) by rw [entry_apply]]
  unfold logDeriv
  rw [← (entry i j).integral_comp_comm (logDeriv_integrable _ _ hpD)]
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun t => ?_))
    (resolvent_pair _ _ (hp i) (hp j) _)
  have hD : diagReal p + t • (1 : Mat n) = diagReal (fun k => p k + t) := by
    ext k l
    by_cases h : k = l
    · subst l
      simp [diagReal, Matrix.one_apply, Complex.ofReal_add]
    · simp [diagReal, Matrix.one_apply, h]
  simp only [entry_apply, hD, diagReal, diagonal_inv, diagonal_mul, mul_diagonal]
