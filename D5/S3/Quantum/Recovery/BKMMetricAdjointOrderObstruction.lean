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
  rw [← CFC.real_exp_eq_normedSpace_exp (IsSelfAdjoint.smul (r := u) IsSelfAdjoint.log), CFC.log,
    ← cfc_smul u Real.log a hc,
    ← cfc_comp' Real.exp (fun x => u • Real.log x) a (by fun_prop) (continuousOn_const.smul hc)
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
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun t => ?_))
    (resolvent_pair _ _ (hp i) (hp j) _)
  have hD : diagReal p + t • (1 : Mat n) = diagReal (fun k => p k + t) := by
    ext k l
    by_cases h : k = l
    · subst l
      simp [diagReal, Matrix.one_apply, Complex.ofReal_add]
    · simp [diagReal, Matrix.one_apply, h]
  rw [entry_apply, hD]
  simp only [diagReal, inv_diagonal, diagonal_mul, mul_diagonal, Pi.inv_apply]

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
    _ = ((Hᴴ * Qᴴ) * (Y * Q)).trace := by noncomm_ring
    _ = ((Y * Q) * (Hᴴ * Qᴴ)).trace := Matrix.trace_mul_comm _ _
    _ = ((Y * (Q * Hᴴ * Qᴴ))).trace := by noncomm_ring
    _ = ((Q * Hᴴ * Qᴴ) * Y).trace := Matrix.trace_mul_comm _ _

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
  change diagReal (fun k => Real.log (p k + t * d k)) =
    CFC.log (diagReal p + t • diagReal d)
  have he : diagReal p + t • diagReal d = diagReal (fun k => p k + t * d k) := by
    change diagRealCLM p + t • diagRealCLM d = diagRealCLM (p + t • d)
    simp
  rw [he]
  exact (cfc_log_diagonal _).symm

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
    have hb := (hB.smul t).neg_algebraMap_norm_le_self
    have h := add_le_add hle hb
    rw [← map_neg, ← map_add] at h
    exact (algebraMap_mono (R := ℝ) (A := Mat n) (by linarith)).trans h
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

private theorem trace_omega (a X : Mat n) (ha : a.PosDef) :
    (omega a X).trace = (a * X).trace := by
  let U := basisChange ha.isHermitian.eigenvectorUnitary
  rw [← trace_basisChange (star ha.isHermitian.eigenvectorUnitary) (omega a X),
    ← trace_basisChange (star ha.isHermitian.eigenvectorUnitary) (a * X)]
  change (U.symm (omega a X)).trace = (U.symm (a * X)).trace
  have hspec : U.symm a = diagReal ha.isHermitian.eigenvalues := by
    conv_lhs => rw [ha.isHermitian.spectral_theorem]
    exact U.symm_apply_apply _
  rw [map_mul, hspec]
  apply Finset.sum_congr rfl
  intro k _
  change U.symm (omega a X) k k = (diagReal ha.isHermitian.eigenvalues * U.symm X) k k
  rw [omega_entry a X ha]
  simp [logMean, diagReal]

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
  (Matrix.mulLeftLinearMap n ℂ (diagReal fun k => (p k)⁻¹)).comp diagonalPart

private theorem adjoint_logDeriv (V : UMat n) (p : n → ℝ) (hp : ∀ k, 0 < p k) (Y : Mat n) :
    measurementAdjoint V (logDeriv (diagReal p) Y) = basisChange V (scaledDiagonal p Y) := by
  apply (basisChange V).congr_arg
  change diagonal (diag (logDeriv (diagReal p) Y)) = _
  ext i j
  by_cases h : i = j
  · subst j
    simp [scaledDiagonal, diagonalPart, diagReal, logDeriv_diag p hp, logMean]
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
  · simp only [logMean, if_neg h, if_neg h.symm]
    rw [← neg_div_neg_eq, neg_sub, neg_sub]

private theorem metricAdjoint_star (a : Mat n) (ha : a.PosDef) (V : UMat n)
    (p : n → ℝ) (hp : ∀ k, 0 < p k) (Y : Mat n) :
    metricAdjoint a V p (star Y) = star (metricAdjoint a V p Y) := by
  have hDiag : scaledDiagonal p (star Y) = star (scaledDiagonal p Y) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [scaledDiagonal, diagonalPart, diagReal, Matrix.star_eq_conjTranspose, mul_comm]
    · simp [scaledDiagonal, diagonalPart, diagReal, Matrix.star_eq_conjTranspose, h, h.symm]
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
    rw [omega_entry a X ha, star_mul, starRingEnd_apply, Complex.conj_ofReal, logMean_symm]
    ring
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
  rw [← Matrix.vecMul_conjTranspose, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

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
    rw [map_sub, hRτ, sub_sub_sub_cancel_right] at hdz
    exact hdz
  have hproper : 0 ≤ quadratic z (R P) :=
    (Complex.nonneg_iff.mp ((hR P hP).dotProduct_mulVec_nonneg z)).1
  change quadraticCLM z (R P - E P) = 0 at heq
  rw [map_sub] at heq
  change quadratic z (R P) - quadratic z (E P) = 0 at heq
  linarith
