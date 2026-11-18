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

local notation "logDeriv" => D5.S3.Divergence.LogDerivTrace.logDeriv
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Matrix.ExponentialFirstResponse (derivative derivative_apply)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (pair_kernel_eval)
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard (hadamard hadamard_unitary)
open D5.S3.Divergence.LogDerivTrace (logDeriv_integrable resolvent_eq_spectral)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

namespace D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction

private abbrev Mat (n : Type*) := Matrix n n ℂ

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev UMat (n : Type*) [Fintype n] [DecidableEq n] := Matrix.unitaryGroup n ℂ

private abbrev basisChange (U : UMat n) := (Unitary.conjStarAlgAut ℂ (Mat n) U).toAlgEquiv

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
  have hlog : ContinuousOn (fun x : ℝ => u • Real.log x) (spectrum ℝ a) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => u) _).smul hc
  rw [← CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all u).smul IsSelfAdjoint.log), CFC.log,
    ← cfc_smul u Real.log a hc,
    ← cfc_comp' Real.exp (fun x => u • Real.log x) a (by fun_prop) hlog
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
    rw [AlgEquiv.symm_apply_apply, mpow, conjugated_cfc a ha]
    congr 1
    funext k
    simp [Real.rpow_def_of_pos (ha.eigenvalues_pos k), mul_comm]
  simp_rw [he]
  apply (basisChange ha.isHermitian.eigenvectorUnitary).toLinearEquiv.toContinuousLinearEquiv.continuous.comp
  change Continuous (fun u : ℝ => diagRealCLM (fun k => Real.exp
    (u * Real.log (ha.isHermitian.eigenvalues k))))
  fun_prop

private def logMean (x y : ℝ) : ℝ :=
  if x = y then x else (x - y) / (Real.log x - Real.log y)

private theorem logMean_integral (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ u : ℝ in 0..1, x ^ u * y ^ (1 - u)) = logMean x y := by
  by_cases h : x = y
  · subst y
    simp only [logMean, ite_true, ← Real.rpow_add hx]
    norm_num
  · let c := Real.log x - Real.log y
    have hc : c ≠ 0 := sub_ne_zero.mpr (fun he => h (Real.strictMonoOn_log.injOn hx hy he))
    have hf (u : ℝ) : x ^ u * y ^ (1 - u) = y * Real.exp (c * u) := by
      rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add,
        show y * Real.exp (c * u) = Real.exp (Real.log y) * Real.exp (c * u) by rw [Real.exp_log hy],
        ← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    simp_rw [hf]
    rw [intervalIntegral.integral_const_mul]
    have hd (u : ℝ) : HasDerivAt (fun t => Real.exp (c * t) / c) (Real.exp (c * u)) u := by
      have hv : HasDerivAt (fun t : ℝ => c * t) c u := by
        simpa using (hasDerivAt_id u).const_mul c
      simpa [Function.comp_def, hc] using ((Real.hasDerivAt_exp (c * u)).comp u hv).div_const c
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      ((by fun_prop : Continuous (fun u : ℝ => Real.exp (c * u))).intervalIntegrable 0 1)]
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
  let L := (entry i j).comp U.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
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
    simp only [one_div, _root_.mul_inv_rev]
    ring
  simp_rw [hf]
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, pair_kernel_eval x y hx hy]
  congr 1
  by_cases h : x = y <;> simp [logMean, h, div_eq_mul_inv, mul_comm]

private theorem logDeriv_entry (a X : Mat n) (ha : a.PosDef) (i j : n) :
    (basisChange ha.isHermitian.eigenvectorUnitary).symm (logDeriv a X) i j =
      (logMean (ha.isHermitian.eigenvalues i) (ha.isHermitian.eigenvalues j) : ℂ)⁻¹ *
        (basisChange ha.isHermitian.eigenvectorUnitary).symm X i j := by
  let U := basisChange ha.isHermitian.eigenvectorUnitary
  let L := (entry i j).comp U.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  rw [show U.symm (logDeriv a X) i j = L (logDeriv a X) by simp [L, entry_apply]]
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  rw [← L.integral_comp_comm (logDeriv_integrable a X ha)]
  refine Eq.trans (integral_congr_ae ?_) (resolvent_pair _ _ (ha.eigenvalues_pos i) (ha.eigenvalues_pos j) _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hR : U.symm ((a + t • 1)⁻¹) =
      diagonal (fun k => ((ha.isHermitian.eigenvalues k + t : ℝ) : ℂ)⁻¹) := by
    rw [resolvent_eq_spectral a ha t ht.le]
    exact U.symm_apply_apply _
  change entry i j (U.symm ((a + t • 1)⁻¹ * X * (a + t • 1)⁻¹)) = _
  simp only [entry_apply, map_mul, hR, diagonal_mul, mul_diagonal]
  rfl

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
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  rw [← (entry i j).integral_comp_comm (logDeriv_integrable _ _ hpD)]
  refine Eq.trans (integral_congr_ae ?_) (resolvent_pair _ _ (hp i) (hp j) _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hD : diagReal p + t • (1 : Mat n) = diagReal (fun k => p k + t) := by
    ext k l
    by_cases h : k = l
    · subst l
      simp [diagReal, Matrix.one_apply, Complex.ofReal_add]
    · simp [diagReal, Matrix.one_apply, h]
  simp only [entry_apply]
  rw [hD]
  have hinv : (diagReal (fun k => p k + t))⁻¹ =
      diagonal (fun k => ((p k + t : ℝ) : ℂ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagReal, Matrix.diagonal_mul_diagonal]
    have hf (k : n) : ((p k + t : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (add_pos (hp k) ht).ne'
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    exact inv_mul_cancel₀ (hf k)
  rw [hinv, mul_diagonal, diagonal_mul]

private def projector (k : n) : Mat n := Matrix.single k k 1

private theorem projector_sandwich (k : n) (X : Mat n) :
    projector k * X * projector k = Matrix.single k k (X k k) := by
  simpa [projector] using Matrix.single_mul_mul_single k k k k (1 : ℂ) X 1

private def measurementKraus (V : UMat n) (k : n) : Mat n :=
  projector k * (star (V : Mat n))

private theorem kraus_complete (V : UMat n) :
    ∑ k, (measurementKraus V k)ᴴ * measurementKraus V k = 1 := by
  have h (k : n) : (measurementKraus V k)ᴴ * measurementKraus V k =
      (basisChange V) (projector k) := by
    change star (measurementKraus V k) * measurementKraus V k = _
    have hp : star (projector k) = projector k := by simp [projector, Matrix.star_eq_conjTranspose]
    have hpp : projector k * projector k = projector k := by
      simp [projector, Matrix.single_mul_single_same]
    simp only [measurementKraus, star_mul, star_star, hp, Unitary.conjStarAlgAut_apply]
    rw [← mul_assoc, mul_assoc (V : Mat n), hpp]
    rfl
  simp_rw [h]
  rw [← map_sum]
  change basisChange V (∑ k, Matrix.single k k 1) = 1
  rw [Matrix.sum_single_one, map_one]

private theorem measurement_apply (V : UMat n) (X : Mat n) :
    MatrixMap.of_kraus (measurementKraus V) (measurementKraus V) X =
      diagonal (diag ((basisChange V).symm X)) := by
  have h (k : n) : measurementKraus V k * X * (measurementKraus V k)ᴴ =
      Matrix.single k k (((basisChange V).symm X) k k) := by
    change measurementKraus V k * X * star (measurementKraus V k) = _
    rw [← projector_sandwich]
    change measurementKraus V k * X * star (measurementKraus V k) =
      projector k * ((star (V : Mat n)) * X * (V : Mat n)) * projector k
    have hp : star (projector k) = projector k := by simp [projector, Matrix.star_eq_conjTranspose]
    simp only [measurementKraus, star_mul, star_star, hp, Unitary.conjStarAlgAut_symm_apply]
    noncomm_ring
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, h]
  exact Matrix.sum_single_eq_diagonal _

private def diagonalPart : Mat n →ₗ[ℂ] Mat n :=
  (Matrix.diagonalLinearMap n ℂ ℂ).comp (Matrix.diagLinearMap n ℂ ℂ)

/-- The Hilbert–Schmidt adjoint of the measurement with standard diagonal encoding. -/
def measurementAdjoint (V : Matrix.unitaryGroup n ℂ) : MatrixMap n n ℂ :=
  (basisChange V).toLinearMap.comp diagonalPart

private theorem adjoint_kraus (V : UMat n) (Y : Mat n) :
    measurementAdjoint V Y = ∑ k, (measurementKraus V k)ᴴ * Y * measurementKraus V k := by
  change basisChange V (diagonal (diag Y)) = _
  rw [← Matrix.sum_single_eq_diagonal, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change basisChange V (Matrix.single k k (Y k k)) = _
  rw [← projector_sandwich]
  have hp : star (projector k) = projector k := by simp [projector, Matrix.star_eq_conjTranspose]
  change (V : Mat n) * (projector k * Y * projector k) * star (V : Mat n) =
    star (measurementKraus V k) * Y * measurementKraus V k
  simp only [measurementKraus, star_mul, star_star, hp, Unitary.conjStarAlgAut_apply]
  noncomm_ring

set_option maxHeartbeats 500000 in
private theorem trace_adjoint (V : UMat n) (H Y : Mat n) :
    (Hᴴ * measurementAdjoint V Y).trace =
      ((MatrixMap.of_kraus (measurementKraus V) (measurementKraus V) H)ᴴ * Y).trace := by
  rw [adjoint_kraus]
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  set Q := measurementKraus V k
  calc
    _ = ((Hᴴ * Qᴴ) * (Y * Q)).trace := by simp only [mul_assoc]
    _ = ((Y * Q) * (Hᴴ * Qᴴ)).trace := Matrix.trace_mul_comm _ _
    _ = ((Y * (Q * Hᴴ * Qᴴ))).trace := by simp only [mul_assoc]
    _ = ((Q * Hᴴ * Qᴴ) * Y).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

private theorem diagReal_posDef (p : n → ℝ) (hp : ∀ k, 0 < p k) : (diagReal p).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun k => by exact_mod_cast hp k)

private theorem log_curve (p d : n → ℝ) (hp : ∀ k, 0 < p k) :
    HasDerivAt (fun t : ℝ => CFC.log (diagReal p + t • diagReal d))
      (logDeriv (diagReal p) (diagReal d)) 0 := by
  have hs (k : n) : HasDerivAt (fun t : ℝ => Real.log (p k + t * d k)) (d k / p k) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => p k + t * d k) (d k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d k)).const_add (p k)
    have hlog := Real.hasDerivAt_log (hp k).ne'
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      hlog.comp_of_eq 0 hlin (by simp)
  have hpi := hasDerivAt_pi.mpr hs
  have hdiag := (diagRealCLM (n := n)).hasFDerivAt.comp_hasDerivAt 0 hpi
  have hl : diagReal (fun k => d k / p k) = logDeriv (diagReal p) (diagReal d) := by
    ext i j
    rw [logDeriv_diag p hp]
    by_cases h : i = j
    · subst j
      simp [diagReal, logMean, div_eq_mul_inv, mul_comm]
    · simp [diagReal, h]
  change HasDerivAt (fun t : ℝ => diagReal (fun k => Real.log (p k + t * d k)))
    (diagReal (fun k => d k / p k)) 0 at hdiag
  rw [hl] at hdiag
  apply hdiag.congr_of_eventuallyEq
  filter_upwards [] with t
  change CFC.log (diagReal p + t • diagReal d) =
    diagReal (fun k => Real.log (p k + t * d k))
  have he : diagReal p + t • diagReal d = diagReal (fun k => p k + t * d k) := by
    change diagRealCLM p + t • diagRealCLM d = diagRealCLM (p + t • d)
    simp
  rw [he]
  exact cfc_log_diagonal _

private theorem affine_posDef [Nonempty n] (a B : Mat n) (ha : a.PosDef) (hB : IsSelfAdjoint B) :
    ∀ᶠ t : ℝ in 𝓝 0, (a + t • B).PosDef := by
  obtain ⟨ε, hε, hle⟩ := (CFC.exists_pos_algebraMap_le_iff a ha.isHermitian.isSelfAdjoint).mpr
    (fun x hx => by
      rw [ha.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ha.eigenvalues_pos k)
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ‖t • B‖ < ε / 2 := by
    have hc : Continuous (fun t : ℝ => ‖t • B‖) := by fun_prop
    exact hc.continuousAt (Iio_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hn] with t ht
  have hsmall : algebraMap ℝ (Mat n) (ε / 2) ≤ a + t • B := by
    have hb := ((IsSelfAdjoint.all t).smul hB).neg_algebraMap_norm_le_self
    have h := add_le_add hle hb
    rw [← map_neg, ← map_add] at h
    exact (algebraMap_mono (Mat n) (show ε / 2 ≤ ε + -‖t • B‖ by linarith)).trans h
  exact (IsStrictlyPositive.of_le (by
    apply Matrix.PosDef.isStrictlyPositive
    change (diagReal (fun _ : n => ε / 2)).PosDef
    exact diagReal_posDef _ (fun _ => half_pos hε)) hsmall).posDef

/-- The exponential Gibbs curve built from the measurement adjoint and actual CFC logarithms. -/
def gibbs (a τ : Matrix n n ℂ) (V : Matrix.unitaryGroup n ℂ) (Y : Matrix n n ℂ) :
    Matrix n n ℂ :=
  exp (CFC.log a + measurementAdjoint V (CFC.log Y - CFC.log τ))

private theorem gibbs_derivative (a : Mat n) (ha : a.PosDef) (V : UMat n)
    (p d : n → ℝ) (hp : ∀ k, 0 < p k) :
    HasDerivAt (fun t : ℝ => gibbs a (diagReal p) V (diagReal p + t • diagReal d))
      (omega a (measurementAdjoint V (logDeriv (diagReal p) (diagReal d)))) 0 := by
  let L := (measurementAdjoint V).toContinuousLinearMap.restrictScalars ℝ
  have hlog := (log_curve p d hp).sub_const (CFC.log (diagReal p))
  have hA := (L.hasFDerivAt.comp_hasDerivAt 0 hlog).const_add (CFC.log a)
  have h0 : CFC.log a + L
      (CFC.log (diagReal p + (0 : ℝ) • diagReal d) - CFC.log (diagReal p)) = CFC.log a := by simp
  have hexp := (D5.S3.Quantum.Matrix.ExponentialFirstResponse.hasFDerivAt_exp
    (CFC.log a)).restrictScalars ℝ
  have h := hexp.comp_hasDerivAt_of_eq 0 hA h0.symm
  change HasDerivAt (fun t : ℝ => gibbs a (diagReal p) V (diagReal p + t • diagReal d))
    (derivative (CFC.log a) (measurementAdjoint V (logDeriv (diagReal p) (diagReal d)))) 0 at h
  rwa [derivative_eq_omega a ha] at h

private theorem trace_basisChange (U : UMat n) (X : Mat n) :
    (basisChange U X).trace = X.trace := by
  change ((U : Mat n) * X * star (U : Mat n)).trace = _
  rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

set_option maxHeartbeats 500000 in
private theorem trace_omega (a X : Mat n) (ha : a.PosDef) :
    (omega a X).trace = (a * X).trace := by
  let U := basisChange ha.isHermitian.eigenvectorUnitary
  have ht (Y : Mat n) : (U.symm Y).trace = Y.trace := by
    change ((star (ha.isHermitian.eigenvectorUnitary : Mat n)) * Y *
      (ha.isHermitian.eigenvectorUnitary : Mat n)).trace = Y.trace
    rw [trace_mul_cycle]
    change ((ha.isHermitian.eigenvectorUnitary : Mat n) *
      (↑(star ha.isHermitian.eigenvectorUnitary) : Mat n) * Y).trace = _
    rw [Unitary.coe_mul_star_self, one_mul]
  rw [← ht (omega a X), ← ht (a * X)]
  have hspec : U.symm a = diagReal ha.isHermitian.eigenvalues := by
    conv_lhs => rw [ha.isHermitian.spectral_theorem]
    exact U.symm_apply_apply _
  rw [map_mul, hspec]
  apply Finset.sum_congr rfl
  intro k _
  change U.symm (omega a X) k k = (diagReal ha.isHermitian.eigenvalues * U.symm X) k k
  rw [omega_entry a X ha]
  simp only [logMean, ite_true, eq_self, diagReal, Matrix.diagonal_mul]
  rfl

private theorem omega_one (a : Mat n) (ha : a.PosDef) : omega a 1 = a := by
  let U := basisChange ha.isHermitian.eigenvectorUnitary
  apply U.symm.injective
  have hspec : U.symm a = diagReal ha.isHermitian.eigenvalues := by
    conv_lhs => rw [ha.isHermitian.spectral_theorem]
    exact U.symm_apply_apply _
  ext i j
  rw [hspec]
  change (basisChange ha.isHermitian.eigenvectorUnitary).symm (omega a 1) i j = _
  rw [omega_entry a 1 ha, map_one]
  by_cases h : i = j
  · subst j
    simp [logMean, diagReal]
  · simp [diagReal, Matrix.one_apply, h]

private def scaledDiagonal (p : n → ℝ) : Mat n →ₗ[ℂ] Mat n :=
  (mulLeftLinearMap n ℂ (diagReal fun k => (p k)⁻¹)).comp diagonalPart

private theorem adjoint_logDeriv (V : UMat n) (p : n → ℝ) (hp : ∀ k, 0 < p k) (Y : Mat n) :
    measurementAdjoint V (logDeriv (diagReal p) Y) = basisChange V (scaledDiagonal p Y) := by
  apply congrArg (basisChange V)
  change diagonal (diag (logDeriv (diagReal p) Y)) = _
  ext i j
  by_cases h : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diag_apply]
    change logDeriv (diagReal p) Y i i = (diagReal (fun k => (p k)⁻¹) * diagonal (diag Y)) i i
    rw [logDeriv_diag p hp]
    simp [logMean, diagReal]
  · simp [scaledDiagonal, diagonalPart, diagReal, h]

private def metricAdjoint (a : Mat n) (V : UMat n) (p : n → ℝ) : Mat n →ₗ[ℂ] Mat n :=
  (derivative (CFC.log a)).toLinearMap.comp
    ((basisChange V).toLinearMap.comp (scaledDiagonal p))

private theorem metricAdjoint_apply (a : Mat n) (ha : a.PosDef) (V : UMat n)
    (p : n → ℝ) (hp : ∀ k, 0 < p k) (Y : Mat n) :
    metricAdjoint a V p Y = omega a (measurementAdjoint V (logDeriv (diagReal p) Y)) := by
  rw [adjoint_logDeriv V p hp]
  exact derivative_eq_omega a ha _

private theorem logMean_symm (x y : ℝ) : logMean x y = logMean y x := by
  by_cases h : x = y
  · subst y
    rfl
  · simp only [logMean, if_neg h, if_neg (Ne.symm h)]
    rw [← neg_div_neg_eq, neg_sub, neg_sub]

private theorem metricAdjoint_star (a : Mat n) (ha : a.PosDef) (V : UMat n)
    (p : n → ℝ) (hp : ∀ k, 0 < p k) (Y : Mat n) :
    metricAdjoint a V p (star Y) = star (metricAdjoint a V p Y) := by
  have hDiag : scaledDiagonal p (star Y) = star (scaledDiagonal p Y) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [scaledDiagonal, diagonalPart, diagReal, Matrix.star_eq_conjTranspose, mul_comm]
    · simp [scaledDiagonal, diagonalPart, diagReal, Matrix.star_eq_conjTranspose, h, Ne.symm h]
  have hv (X : Mat n) : basisChange V (star X) = star (basisChange V X) :=
    map_star (Unitary.conjStarAlgAut ℂ (Mat n) V) X
  have hStar : ∀ X : Mat n, omega a (star X) = star (omega a X) := by
    intro X
    let U := Unitary.conjStarAlgAut ℂ (Mat n) ha.isHermitian.eigenvectorUnitary
    apply U.symm.toAlgEquiv.injective
    rw [show U.symm.toAlgEquiv (star (omega a X)) =
      star (U.symm.toAlgEquiv (omega a X)) from map_star U.symm _]
    ext i j
    change (basisChange ha.isHermitian.eigenvectorUnitary).symm (omega a (star X)) i j = _
    rw [omega_entry a _ ha, show (basisChange ha.isHermitian.eigenvectorUnitary).symm (star X) =
      star (U.symm.toAlgEquiv X) from map_star U.symm X]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    change _ = star ((basisChange ha.isHermitian.eigenvectorUnitary).symm (omega a X) j i)
    rw [omega_entry a X ha, star_mul]
    simp only [show ∀ r : ℝ, star (r : ℂ) = r by intro r; simp,
      logMean_symm (ha.isHermitian.eigenvalues j) (ha.isHermitian.eigenvalues i)]
    exact mul_comm _ _
  change derivative (CFC.log a) (basisChange V (scaledDiagonal p (star Y))) =
    star (derivative (CFC.log a) (basisChange V (scaledDiagonal p Y)))
  simp only [derivative_eq_omega a ha, hDiag, hv, hStar]

private theorem scaledDiagonal_ref (p : n → ℝ) (hp : ∀ k, 0 < p k) :
    scaledDiagonal p (diagReal p) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    have hne : (p i : ℂ) ≠ 0 := by exact_mod_cast (hp i).ne'
    simp [scaledDiagonal, diagonalPart, diagReal, hne]
  · simp [scaledDiagonal, diagonalPart, diagReal, Matrix.one_apply, h]

private theorem metricAdjoint_ref (a : Mat n) (ha : a.PosDef) (V : UMat n)
    (p : n → ℝ) (hp : ∀ k, 0 < p k) :
    metricAdjoint a V p (diagReal p) = a := by
  change derivative (CFC.log a) (basisChange V (scaledDiagonal p (diagReal p))) = a
  rw [scaledDiagonal_ref p hp, map_one, derivative_eq_omega a ha, omega_one a ha]

private theorem trace_ref_logDeriv (p : n → ℝ) (hp : ∀ k, 0 < p k) (Y : Mat n) :
    (diagReal p * logDeriv (diagReal p) Y).trace = Y.trace := by
  apply Finset.sum_congr rfl
  intro k _
  change (diagReal p * logDeriv (diagReal p) Y) k k = Y k k
  rw [show (diagReal p * logDeriv (diagReal p) Y) k k =
    (p k : ℂ) * logDeriv (diagReal p) Y k k by simp [diagReal], logDeriv_diag p hp]
  have hne : (p k : ℂ) ≠ 0 := by exact_mod_cast (hp k).ne'
  simp [logMean, ← mul_assoc, hne]

private def quadratic (z : n → ℂ) (X : Mat n) : ℝ := (star z ⬝ᵥ (X *ᵥ z)).re

private def quadraticCLM (z : n → ℂ) : Mat n →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (({ toFun := fun X => star z ⬝ᵥ (X *ᵥ z)
        map_add' := fun X Y => by rw [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun r X => by
          rw [RingHom.id_apply, Matrix.smul_mulVec, dotProduct_smul] } :
      Mat n →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ)

private theorem quadratic_conj (U : UMat n) (z : n → ℂ) (X : Mat n) :
    quadratic ((U : Mat n) *ᵥ z) X = quadratic z ((basisChange U).symm X) := by
  change (star ((U : Mat n) *ᵥ z) ⬝ᵥ (X *ᵥ ((U : Mat n) *ᵥ z))).re =
    (star z ⬝ᵥ (((U : Mat n)ᴴ * X * (U : Mat n)) *ᵥ z)).re
  have hs : star ((U : Mat n) *ᵥ z) = star z ᵥ* (U : Mat n)ᴴ := Matrix.star_mulVec _ _
  rw [hs, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

private theorem local_order_impossible (a τ P : Mat n) (V : UMat n) (z : n → ℂ)
    (hP : P.PosSemidef) (h0 : gibbs a τ V τ = a)
    (hpos : ∀ᶠ t : ℝ in 𝓝 0, (τ + t • (P - τ)).PosDef)
    (E : Mat n →ₗ[ℂ] Mat n)
    (hneg : quadratic z (E P) < 0)
    (hd : HasDerivAt (fun t : ℝ => gibbs a τ V (τ + t • (P - τ))) (E P - a) 0) :
    ¬ ∃ R : Mat n →ₗ[ℂ] Mat n, (∀ X, X.PosSemidef → (R X).PosSemidef) ∧ R τ = a ∧
      ∃ ε > (0 : ℝ), ∀ t : ℝ, |t| < ε → (τ + t • (P - τ)).PosDef →
        (R (τ + t • (P - τ)) - gibbs a τ V (τ + t • (P - τ))).PosSemidef := by
  rintro ⟨R, hR, hRτ, ε, hε, hdom⟩
  let f := fun t : ℝ => quadratic z (R (τ + t • (P - τ)) - gibbs a τ V (τ + t • (P - τ)))
  have hf0 : f 0 = 0 := by simp [f, quadratic, hRτ, h0]
  have hmin : IsLocalMin f 0 := by
    have hrad : ∀ᶠ t : ℝ in 𝓝 0, |t| < ε :=
      continuous_abs.continuousAt (Iio_mem_nhds (by simpa using hε))
    filter_upwards [hrad, hpos] with t ht hpt
    rw [hf0]
    exact (Complex.nonneg_iff.mp ((hdom t ht hpt).dotProduct_mulVec_nonneg z)).1
  have hw : HasDerivAt (fun t : ℝ => τ + t • (P - τ)) (P - τ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (P - τ)).const_add τ
  have hRw := ((R.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hw)
  have hdf := (quadraticCLM z).hasFDerivAt.comp_hasDerivAt 0 (hRw.sub hd)
  have heq : quadratic z (R P - E P) = 0 := by
    have hdz := hmin.hasDerivAt_eq_zero hdf
    change quadratic z (R (P - τ) - (E P - a)) = 0 at hdz
    rw [map_sub, hRτ] at hdz
    convert hdz using 1
    abel
  have hproper : 0 ≤ quadratic z (R P) :=
    (Complex.nonneg_iff.mp ((hR P hP).dotProduct_mulVec_nonneg z)).1
  change quadraticCLM z (R P - E P) = 0 at heq
  rw [map_sub] at heq
  change quadratic z (R P) - quadratic z (E P) = 0 at heq
  exact (not_lt_of_ge hproper) ((sub_eq_zero.mp heq).symm ▸ hneg)

private theorem strict_mean (x y : ℝ) (hy : 0 < y) (hyx : y < x) :
    Real.sqrt (x * y) < logMean x y := by
  have hx := hy.trans hyx
  let u := (Real.log x - Real.log y) / 2
  let v := (Real.log x + Real.log y) / 2
  have hu : 0 < u := half_pos (sub_pos.mpr (Real.log_lt_log hy hyx))
  have hv : Real.exp v = Real.sqrt (x * y) := by
    dsimp [v]
    rw [← Real.log_mul hx.ne' hy.ne']
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos hx hy)]
    congr 1
    ring
  have hx' : Real.exp v * Real.exp u = x := by
    rw [← Real.exp_add, show v + u = Real.log x by dsimp [v, u]; ring, Real.exp_log hx]
  have hy' : Real.exp v * Real.exp (-u) = y := by
    rw [← Real.exp_add, show v + -u = Real.log y by dsimp [v, u]; ring, Real.exp_log hy]
  have hs := Real.self_lt_sinh_iff.mpr hu
  rw [Real.sinh_eq] at hs
  have hmul := mul_lt_mul_of_pos_left hs (Real.exp_pos v)
  have hlog : 0 < Real.log x - Real.log y := sub_pos.mpr (Real.log_lt_log hy hyx)
  rw [logMean, if_neg hyx.ne', lt_div_iff₀ hlog, ← hv]
  dsimp [u] at hu hs hmul ⊢
  dsimp [u] at hx' hy'
  linarith only [hmul, hx', hy']

private def hadamardAmplitude : ℂ := (Real.sqrt 2 / 2 : ℝ)

private theorem hadamardAmplitude_sq :
    2 * hadamardAmplitude ^ 2 = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have ht : 2 * (Real.sqrt 2 / 2) ^ 2 = 1 := by nlinarith
  change (2 : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 2 = 1
  exact_mod_cast ht

private def rotation (i j : n) (hij : i ≠ j) : UMat n :=
  ⟨D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard i j hadamardAmplitude,
    hadamard_unitary i j hij _ (by simp [hadamardAmplitude]) hadamardAmplitude_sq⟩

private theorem rotation_column (i j : n) (hij : i ≠ j) (r : n) :
    (rotation i j hij : Mat n) r i =
      if r = i ∨ r = j then hadamardAmplitude else 0 := by
  by_cases hi : r = i
  · subst r
    simp [rotation, D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard, Matrix.single_apply, Matrix.one_apply, hij, hij.symm]
  by_cases hj : r = j
  · subst r
    simp [rotation, D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard, Matrix.single_apply, Matrix.one_apply, hij, hij.symm]
  simp [rotation, D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard, Matrix.single_apply, Matrix.one_apply, hi, hj, Ne.symm hi, Ne.symm hj]

private theorem rotation_diagonal_first (i j : n) (hij : i ≠ j) (p : n → ℝ) :
    ((basisChange (rotation i j hij)).symm (diagReal p)) i i = ((p i + p j) / 2 : ℝ) := by
  change (((rotation i j hij : Mat n)ᴴ * diagReal p) * (rotation i j hij : Mat n)) i i = _
  rw [Matrix.mul_apply]
  simp only [diagReal, Matrix.mul_diagonal, Matrix.conjTranspose_apply, rotation_column]
  have ht : hadamardAmplitude * hadamardAmplitude = (1 : ℂ) / 2 := by
    linear_combination hadamardAmplitude_sq / 2
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hz : ∑ k ∈ (Finset.univ.erase i).erase j,
      star (if k = i ∨ k = j then hadamardAmplitude else 0) * (p k : ℂ) *
        (if k = i ∨ k = j then hadamardAmplitude else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hi := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hj := (Finset.mem_erase.mp hk).1
    simp [hi, hj]
  rw [hz]
  simp only [eq_self, true_or, or_true, ite_true, zero_add,
    show star hadamardAmplitude = hadamardAmplitude by simp [hadamardAmplitude]]
  push_cast
  rw [show hadamardAmplitude * (p j : ℂ) * hadamardAmplitude = (p j : ℂ) * (1 / 2) by
    rw [mul_comm hadamardAmplitude, mul_assoc, ht],
    show hadamardAmplitude * (p i : ℂ) * hadamardAmplitude = (p i : ℂ) * (1 / 2) by
    rw [mul_comm hadamardAmplitude, mul_assoc, ht]]
  ring

private theorem projector_diagonal (i : n) :
    projector i = diagonal (fun k => if k = i then (1 : ℂ) else 0) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hj : j = i <;> simp [projector, Matrix.single_apply, hj, eq_comm]
  · simp [projector, Matrix.single_apply, Matrix.diagonal_apply, hjk]
    intro hij hik
    exact hjk (hij.symm.trans hik)


private theorem projector_posSemidef (i : n) : (projector i).PosSemidef := by
  rw [projector_diagonal, posSemidef_diagonal_iff]
  intro j
  by_cases hj : j = i <;> simp [hj]

private theorem witness_quadratic (i j : n) (hij : i ≠ j) (X : Mat n)
    (x y m s : ℝ)
    (hii : X i i = (x / s : ℝ)) (hij' : X i j = (m / s : ℝ))
    (hji : X j i = (m / s : ℝ)) (hjj : X j j = (y / s : ℝ))
    (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) :
    quadratic (Pi.single (M := fun _ : n => ℂ) i (Real.sqrt y : ℂ) - Pi.single (M := fun _ : n => ℂ) j (Real.sqrt x : ℂ)) X =
      (2 * x * y - 2 * m * Real.sqrt (x * y)) / s := by
  have hstar : star (Pi.single (M := fun _ : n => ℂ) i (Real.sqrt y : ℂ) - Pi.single (M := fun _ : n => ℂ) j (Real.sqrt x : ℂ)) =
      Pi.single (M := fun _ : n => ℂ) i (Real.sqrt y : ℂ) - Pi.single (M := fun _ : n => ℂ) j (Real.sqrt x : ℂ) := by
    funext k
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp [Pi.single_apply, hi, hj, hij, Ne.symm hij]
  unfold quadratic
  rw [hstar, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [single_dotProduct, Matrix.mulVec, dotProduct_single, hii, hij', hji, hjj,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  rw [Real.sqrt_mul hx.le y]
  field_simp
  nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]

private theorem measured_density (a : Mat n) (ha : a.PosDef) (V : UMat n) :
    ∃ p : n → ℝ, (∀ k, 0 < p k) ∧
      MatrixMap.of_kraus (measurementKraus V) (measurementKraus V) a = diagReal p := by
  have hV : IsUnit (V : Mat n) := Unitary.isUnit_coe (U := V)
  have h := hV.posDef_star_left_conjugate_iff.mpr ha
  change ((basisChange V).symm a).PosDef at h
  refine ⟨fun k => (((basisChange V).symm a) k k).re, fun k => ?_, ?_⟩
  · exact (Complex.pos_iff.mp (h.diag_pos (i := k))).1
  · rw [measurement_apply]
    congr 1
    funext k
    have hdiag := h.diag_pos (i := k)
    apply Complex.ext
    · simp [Matrix.diag]
    · simpa [Matrix.diag] using (Complex.pos_iff.mp hdiag).2.symm

private theorem rotated_projector_entry (T : UMat n) (r s i : n) :
    basisChange T (projector i) r s = (T : Mat n) r i * star ((T : Mat n) s i) := by
  change ((T : Mat n) * projector i * (T : Mat n)ᴴ) r s = _
  rw [projector, mul_assoc]
  rw [show Matrix.single i i (1 : ℂ) * (T : Mat n)ᴴ =
      Matrix.of (fun k l => if k = i then star ((T : Mat n) l i) else 0) by
    ext k l
    by_cases hk : k = i
    · subst k
      simp [Matrix.single_mul_apply_same]
    · simp [Matrix.single_mul_apply_of_ne, hk]]
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · exact fun hi => (hi (Finset.mem_univ _)).elim

private theorem metricAdjoint_projector (a : Mat n) (ha : a.PosDef)
    (T : UMat n) (p : n → ℝ) (i r s : n) :
    (basisChange ha.isHermitian.eigenvectorUnitary).symm
      (metricAdjoint a (ha.isHermitian.eigenvectorUnitary * T) p (projector i)) r s =
    (logMean (ha.isHermitian.eigenvalues r) (ha.isHermitian.eigenvalues s) : ℂ) *
      ((p i : ℂ)⁻¹ * ((T : Mat n) r i * star ((T : Mat n) s i))) := by
  let U := ha.isHermitian.eigenvectorUnitary
  have hP : scaledDiagonal p (projector i) = (p i : ℂ)⁻¹ • projector i := by
    change diagReal (fun k => (p k)⁻¹) * diagonal (diag (projector i)) =
      (p i : ℂ)⁻¹ • projector i
    rw [projector_diagonal, Matrix.diag_diagonal, diagReal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_smul]
    congr 1
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  change (basisChange U).symm
    (derivative (CFC.log a) (basisChange (U * T) (scaledDiagonal p (projector i)))) r s = _
  rw [derivative_eq_omega a ha, omega_entry a _ ha]
  have hc : basisChange (U * T) (scaledDiagonal p (projector i)) =
      basisChange U (basisChange T (scaledDiagonal p (projector i))) :=
    Unitary.conjStarAlgAut_mul_apply (S := ℂ) _ _ _
  change _ = _
  rw [hc, AlgEquiv.symm_apply_apply, hP, map_smul, Matrix.smul_apply, rotated_projector_entry]
  rfl

set_option maxHeartbeats 2200000 in
/-- Every faithful nonflat density has a projective measurement whose attainable Gibbs
line cannot be locally dominated in operator order by a positive reference-exact map. -/
theorem measurement_order_obstruction (a : Matrix n n ℂ) (ha : a.PosDef)
    (htr : a.trace = 1) (hflat : ¬ ∃ c : ℝ, a = c • (1 : Matrix n n ℂ)) :
    ∃ (i j : n) (hij : i ≠ j), ∃ (V : Matrix.unitaryGroup n ℂ)
      (Q : n → Matrix n n ℂ) (E : MatrixMap n n ℂ) (z : n → ℂ),
      let eigen := ha.isHermitian.eigenvalues
      let U := ha.isHermitian.eigenvectorUnitary
      let N := MatrixMap.of_kraus Q Q
      let τ := N a
      let P := Matrix.single i i (1 : ℂ)
      let w := fun t : ℝ => τ + t • (P - τ)
      let ρ := fun t : ℝ => a + t • ((V : Mat n) * (P - τ) * (V : Mat n)ᴴ)
      eigen j < eigen i ∧ V = U * rotation i j hij ∧ (∀ k, Q k = measurementKraus V k) ∧
      (∑ k, (Q k)ᴴ * Q k) = 1 ∧ N.IsCompletelyPositive ∧ N.IsTracePreserving ∧
      τ.PosDef ∧ τ.trace = 1 ∧ P.PosSemidef ∧ P.trace = 1 ∧
      (∀ X, (V : Mat n) * N X * (V : Mat n)ᴴ =
        ∑ k, (V : Mat n) * projector k * (V : Mat n)ᴴ * X *
          ((V : Mat n) * projector k * (V : Mat n)ᴴ)) ∧
      (∀ Y, measurementAdjoint V Y = ∑ k, (Q k)ᴴ * Y * Q k) ∧
      (∀ Y, E Y = omega a (measurementAdjoint V (logDeriv τ Y))) ∧
      (∀ Y, E (star Y) = star (E Y)) ∧ E.IsTracePreserving ∧ E τ = a ∧
      (∀ H Y, (Hᴴ * logDeriv a (E Y)).trace = ((N H)ᴴ * logDeriv τ Y).trace) ∧
      z = (U : Mat n) *ᵥ (Pi.single (M := fun _ : n => ℂ) i (Real.sqrt (eigen j) : ℂ) -
        Pi.single (M := fun _ : n => ℂ) j (Real.sqrt (eigen i) : ℂ)) ∧
      (∀ r s, (r = i ∨ r = j) → (s = i ∨ s = j) →
        (basisChange U).symm (E P) r s = (logMean (eigen r) (eigen s) / (eigen i + eigen j) : ℝ)) ∧
      quadratic z (E P) = (2 * eigen i * eigen j - 2 * logMean (eigen i) (eigen j) *
        Real.sqrt (eigen i * eigen j)) / (eigen i + eigen j) ∧ quadratic z (E P) < 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, (w t).PosDef ∧ (w t).trace = 1 ∧
        (ρ t).PosDef ∧ (ρ t).trace = 1 ∧ N (ρ t) = w t) ∧
      gibbs a τ V τ = a ∧ HasDerivAt (fun t : ℝ => gibbs a τ V (w t)) (E P - a) 0 ∧
      ¬ ∃ R : MatrixMap n n ℂ, (∀ X, X.PosSemidef → (R X).PosSemidef) ∧ R τ = a ∧
        ∃ ε > (0 : ℝ), ∀ t : ℝ, |t| < ε → (w t).PosDef →
          (R (w t) - gibbs a τ V (w t)).PosSemidef := by
  classical
  let eigen := ha.isHermitian.eigenvalues
  let U := ha.isHermitian.eigenvectorUnitary
  have hspec : (basisChange U).symm a = diagReal eigen := by
    conv_lhs => rw [ha.isHermitian.spectral_theorem]
    exact (basisChange U).symm_apply_apply _
  have hpair : ∃ i j, eigen j < eigen i := by
    by_contra! h
    have hconst : ∀ i j, eigen i = eigen j := fun i j => le_antisymm (h i j) (h j i)
    obtain he | hn := isEmpty_or_nonempty n
    · apply hflat
      exact ⟨0, Subsingleton.elim _ _⟩
    · obtain ⟨k⟩ := hn
      apply hflat
      refine ⟨eigen k, (basisChange U).symm.injective ?_⟩
      rw [hspec]
      have hm : (basisChange U).symm (eigen k • (1 : Mat n)) = eigen k • (1 : Mat n) := by
        change ((basisChange U).symm.toLinearMap.restrictScalars ℝ) (eigen k • (1 : Mat n)) = _
        rw [map_smul]
        congr 1
        exact map_one (basisChange U).symm
      rw [hm]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [diagReal, hconst i k]
      · simp [diagReal, Matrix.one_apply, hij]
  obtain ⟨i, j, hlt⟩ := hpair
  letI : Nonempty n := ⟨i⟩
  have hij : i ≠ j := fun h => (ne_of_gt hlt) (congr_arg eigen h)
  let T := rotation i j hij
  let V := U * T
  let Q := measurementKraus V
  let N := MatrixMap.of_kraus Q Q
  let τ := N a
  obtain ⟨p, hp, hpτ⟩ := measured_density a ha V
  change τ = _ at hpτ
  let P := projector i
  let E : MatrixMap n n ℂ := metricAdjoint a V p
  let z₀ : n → ℂ := Pi.single (M := fun _ : n => ℂ) i (Real.sqrt (eigen j) : ℂ) -
    Pi.single (M := fun _ : n => ℂ) j (Real.sqrt (eigen i) : ℂ)
  let z := (U : Mat n) *ᵥ z₀
  have hTP : N.IsTracePreserving :=
    MatrixMap.IsTracePreserving.of_kraus_isTracePreserving Q Q (kraus_complete V)
  have hτtr : τ.trace = 1 := (hTP a).trans htr
  have hτ : τ.PosDef := hpτ.symm ▸ diagReal_posDef p hp
  have hP : P.PosSemidef := projector_posSemidef i
  have hPtr : P.trace = 1 := by simp [P, projector]
  have hAdj : ∀ Y, E Y = omega a (measurementAdjoint V (logDeriv τ Y)) := by
    rw [hpτ]
    exact metricAdjoint_apply a ha V p hp
  have heτ : E τ = a := by rw [hpτ]; exact metricAdjoint_ref a ha V p hp
  have hMetric (H Y : Mat n) :
      (Hᴴ * logDeriv a (E Y)).trace = ((N H)ᴴ * logDeriv τ Y).trace := by
    rw [hAdj, logDeriv_omega a _ ha, trace_adjoint]
  have heTP : E.IsTracePreserving := by
    intro Y
    rw [hAdj, trace_omega a _ ha, ← ha.isHermitian.eq, trace_adjoint]
    change (τᴴ * logDeriv τ Y).trace = Y.trace
    rw [hτ.isHermitian.eq, hpτ]
    exact trace_ref_logDeriv p hp Y
  have hLueders (X : Mat n) : (V : Mat n) * N X * (V : Mat n)ᴴ =
      ∑ k, (V : Mat n) * projector k * (V : Mat n)ᴴ * X *
        ((V : Mat n) * projector k * (V : Mat n)ᴴ) := by
    change (V : Mat n) * MatrixMap.of_kraus Q Q X * (V : Mat n)ᴴ = _
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    have hpk : (projector k)ᴴ = projector k := by simp [projector]
    simp only [Q, measurementKraus, Matrix.star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hpk]
    noncomm_ring
  have hpi : p i = (eigen i + eigen j) / 2 := by
    have h := congr_arg (fun X : Mat n => (X i i).re) hpτ
    change ((MatrixMap.of_kraus Q Q a i i).re) = _ at h
    rw [measurement_apply] at h
    simp only [Matrix.diagonal_apply_eq, Matrix.diag_apply, diagReal,
      Complex.ofReal_re] at h
    have hc : (basisChange V).symm a = (basisChange T).symm ((basisChange U).symm a) := by
      change star (V : Mat n) * a * (V : Mat n) =
        star (T : Mat n) * (star (U : Mat n) * a * (U : Mat n)) * (T : Mat n)
      change star ((U : Mat n) * (T : Mat n)) * a * ((U : Mat n) * (T : Mat n)) = _
      simp only [star_mul, mul_assoc]
    rw [hc, hspec, rotation_diagonal_first] at h
    exact h.symm
  have hsum : 0 < eigen i + eigen j := add_pos (ha.eigenvalues_pos i) (ha.eigenvalues_pos j)
  have hentry (r s : n) (hr : r = i ∨ r = j) (hs : s = i ∨ s = j) :
      (basisChange U).symm (E P) r s =
        (logMean (eigen r) (eigen s) / (eigen i + eigen j) : ℝ) := by
    rw [metricAdjoint_projector a ha T p i r s, rotation_column i j hij r,
      rotation_column i j hij s, if_pos hr, if_pos hs, hpi]
    have ht : hadamardAmplitude * star hadamardAmplitude = (1 : ℂ) / 2 := by
      rw [show star hadamardAmplitude = hadamardAmplitude by simp [hadamardAmplitude]]
      linear_combination hadamardAmplitude_sq / 2
    push_cast
    rw [ht]
    field_simp
    <;> ring
  have hzVal : quadratic z (E P) =
      (2 * eigen i * eigen j - 2 * logMean (eigen i) (eigen j) * Real.sqrt (eigen i * eigen j)) / (eigen i + eigen j) := by
    change quadratic ((U : Mat n) *ᵥ z₀) (E P) = _
    rw [quadratic_conj]
    exact witness_quadratic i j hij _ (eigen i) (eigen j) (logMean (eigen i) (eigen j)) (eigen i + eigen j)
      (by simpa [logMean] using hentry i i (.inl rfl) (.inl rfl))
      (hentry i j (.inl rfl) (.inr rfl))
      (by simpa [logMean_symm (eigen j) (eigen i)] using hentry j i (.inr rfl) (.inl rfl))
      (by simpa [logMean] using hentry j j (.inr rfl) (.inr rfl))
      (ha.eigenvalues_pos i) (ha.eigenvalues_pos j) hsum
  have hz : quadratic z (E P) < 0 := by
    rw [hzVal]
    apply div_neg_of_neg_of_pos _ hsum
    have hroot := Real.sqrt_pos_of_pos (mul_pos (ha.eigenvalues_pos i) (ha.eigenvalues_pos j))
    have hm := mul_lt_mul_of_pos_right (strict_mean _ _ (ha.eigenvalues_pos j) hlt) hroot
    nlinarith [Real.sq_sqrt (mul_pos (ha.eigenvalues_pos i) (ha.eigenvalues_pos j)).le]
  let B := basisChange V (P - τ)
  have hbase (X : Mat n) : N (basisChange V X) = diagonal (diag X) := by
    rw [measurement_apply, AlgEquiv.symm_apply_apply]
  have hNB : N B = P - τ := by
    rw [hbase, hpτ]
    change diagonal (diag (projector i - diagReal p)) = projector i - diagReal p
    rw [projector_diagonal, diagReal, Matrix.diagonal_sub, Matrix.diag_diagonal]
  have hBstar : IsSelfAdjoint B := by
    have h := (hP.isHermitian.isSelfAdjoint.sub hτ.isHermitian.isSelfAdjoint)
    exact h.map (Unitary.conjStarAlgAut ℂ (Mat n) V)
  have hAff : ∀ᶠ t : ℝ in 𝓝 0,
      (τ + t • (P - τ)).PosDef ∧ (τ + t • (P - τ)).trace = 1 ∧
      (a + t • B).PosDef ∧ (a + t • B).trace = 1 ∧ N (a + t • B) = τ + t • (P - τ) := by
    have hw := affine_posDef τ _ hτ (hP.isHermitian.isSelfAdjoint.sub hτ.isHermitian.isSelfAdjoint)
    have hρ := affine_posDef a B ha hBstar
    have htrB : B.trace = 0 := by rw [← hTP, hNB, Matrix.trace_sub, hPtr, hτtr, sub_self]
    filter_upwards [hw, hρ] with t hwt hρt
    exact ⟨hwt, by simp [Matrix.trace_add, Matrix.trace_sub, hPtr, hτtr],
      hρt, by simp [Matrix.trace_add, htr, htrB], by simp [hNB, τ]⟩
  have hkτ : gibbs a τ V τ = a := by
    simpa [gibbs] using CFC.exp_log a ha.isStrictlyPositive
  have hder : HasDerivAt (fun t : ℝ => gibbs a τ V (τ + t • (P - τ))) (E P - a) 0 := by
    let d : n → ℝ := fun k => (if k = i then 1 else 0) - p k
    have hd : diagReal d = P - τ := by
      rw [hpτ]
      change diagReal d = projector i - diagReal p
      rw [projector_diagonal, diagReal, diagReal, Matrix.diagonal_sub]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [d, hk]
    have h := gibbs_derivative a ha V p d hp
    rw [hd, ← hpτ, ← hAdj, map_sub, heτ] at h
    exact h
  exact ⟨i, j, hij, V, Q, E, z, hlt, rfl, fun _ => rfl, kraus_complete V,
    MatrixMap.of_kraus_isCompletelyPositive Q, hTP, hτ, hτtr, hP, hPtr, hLueders,
    adjoint_kraus V, hAdj, metricAdjoint_star a ha V p hp, heTP, heτ, hMetric, rfl,
    hentry, hzVal, hz, hAff, hkτ, hder,
    local_order_impossible a τ P V z hP hkτ (hAff.mono fun _ h => h.1) E hz hder⟩

#print axioms measurement_order_obstruction

end D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
