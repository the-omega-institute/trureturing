/- GID: D5/S3/Quantum/Divergence/UmegakiSupportedNoise
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiSupportedNoise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A supported Umegaki limit for density mixtures with an eventual upper bound. -/

import D5.S3.Quantum.Divergence.AlphaZAffine.Result
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Order
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-! The trace against the upper comparison logarithm controls the singular boundary.
The cross-log limit uses the support regularization theorem of AlphaZAffine.

proof_shape: content
admission_basis: escape-witness
escape_witness: a supported cross-log comparison supplies the lower limit for
variable density noises, and the eventual data-processing upper bound gives
convergence of the finite divergence at the singular pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.UmegakiSupportedNoise

open _root_.Matrix Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.AlphaZAffine (cross_log_regularization_tendsto)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem density_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    (1 - A).PosSemidef := by
  let H : HermitianMat n ℂ := ⟨A, hA.isHermitian⟩
  have h := HermitianMat.le_trace_smul_one (HermitianMat.zero_le_iff.mpr hA : 0 ≤ H)
  change A ≤ A.trace.re • (1 : Matrix n n ℂ) at h
  rw [htr, Complex.one_re, one_smul] at h
  exact Matrix.le_iff.mp h

omit [DecidableEq n] in
private lemma continuous_reTrace : Continuous (fun A : Matrix n n ℂ => A.trace.re) := by
  unfold Matrix.trace
  fun_prop

private lemma zero_weight_log_shift_tendsto {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    Tendsto (fun t : ℝ => (t • (1 : Matrix n n ℂ)) * CFC.log (H + t • 1))
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [zero_add, Matrix.zero_mul] using
    (cross_log_regularization_tendsto (ρ := 0) hH (fun _ _ => Matrix.zero_mulVec _))

private lemma supported_log_shift_tendsto {W H : Matrix n n ℂ} (hH : H.PosSemidef)
    (hs : ∀ v : n → ℂ, H *ᵥ v = 0 → W *ᵥ v = 0) :
    Tendsto (fun t : ℝ => W * CFC.log (H + t • 1))
      (𝓝[>] 0) (𝓝 (W * CFC.log H)) := by
  simpa only [Matrix.add_mul, add_sub_cancel_right, sub_zero] using
    (cross_log_regularization_tendsto hH hs).sub (zero_weight_log_shift_tendsto hH)

private lemma supported_trace_log_le {W H J : Matrix n n ℂ}
    (hW : W.PosSemidef) (hH : H.PosSemidef) (hJ : J.PosDef)
    (hs : ∀ v : n → ℂ, H *ᵥ v = 0 → W *ᵥ v = 0) (hHJ : H ≤ J) :
    (W * CFC.log H).trace.re ≤ (W * CFC.log J).trace.re := by
  have hsJ : ∀ v : n → ℂ, J *ᵥ v = 0 → W *ᵥ v = 0 := by
    intro v hv
    have hv0 : v = 0 := hJ.mulVec_injective (hv.trans (Matrix.mulVec_zero _).symm)
    rw [hv0, Matrix.mulVec_zero]
  apply le_of_tendsto_of_tendsto
    (continuous_reTrace.continuousAt.tendsto.comp (supported_log_shift_tendsto hH hs))
    (continuous_reTrace.continuousAt.tendsto.comp
      (supported_log_shift_tendsto hJ.posSemidef hsJ))
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with s hs0
  have hshift : (H + s • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hH (Matrix.PosDef.one.smul hs0)
  have hlog := CFC.log_le_log (add_le_add_left hHJ (s • (1 : Matrix n n ℂ)))
    hshift.isStrictlyPositive
  have htrace := RHLinalg.trace_mul_nonneg_of_posSemidef hW (Matrix.le_iff.mp hlog)
  change 0 ≤ (W * (CFC.log (J + s • 1) - CFC.log (H + s • 1))).trace.re at htrace
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg,
    Function.comp_apply] using htrace

private lemma tendsto_self_log_mixture {X K : Matrix n n ℂ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) :
    Tendsto (fun t : ℝ =>
      ((1 - t) • X + t • K) * CFC.log ((1 - t) • X + t • K))
      (𝓝[>] 0) (𝓝 (X * CFC.log X)) := by
  let A (t : ℝ) := (1 - t) • X + t • K
  have hA (t : ℝ) : (A t).IsHermitian :=
    (hX.smul (show IsSelfAdjoint (1 - t) from rfl)).add
      (hK.smul (show IsSelfAdjoint t from rfl))
  have hprod {B : Matrix n n ℂ} (hB : B.IsHermitian) :
      cfc (fun x : ℝ => x * Real.log x) B = B * CFC.log B := by
    change cfc (fun x : ℝ => id x * Real.log x) B = _
    rw [cfc_mul id Real.log B continuousOn_id (B.finite_real_spectrum.continuousOn _)]
    change cfc (fun x : ℝ => x) B * cfc Real.log B = _
    rw [cfc_id' ℝ B hB.isSelfAdjoint, CFC.log]
  have hcont : Continuous (fun t : ℝ => cfc (fun x : ℝ => x * Real.log x) (A t)) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := Set.univ)
      (by simp (config := { congrConsts := false }))
      (by unfold A; fun_prop) (fun t => (hA t).isSelfAdjoint)
      Real.continuous_mul_log.continuousOn
  have ht := hcont.continuousAt (x := (0 : ℝ)) |>.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  simpa only [ContinuousWithinAt, hprod (hA _), hprod hX, A, sub_zero, one_smul, zero_smul,
    add_zero] using ht

private lemma tendsto_cross_log_mixture_shift {X Y K : Matrix n n ℂ}
    (hY : Y.PosSemidef) (hs : ∀ v : n → ℂ, Y *ᵥ v = 0 → X *ᵥ v = 0) :
    Tendsto (fun t : ℝ => ((1 - t) • X + t • K) * CFC.log (Y + t • 1))
      (𝓝[>] 0) (𝓝 (X * CFC.log Y)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmain := (tendsto_const_nhds.sub ht : Tendsto (fun t : ℝ => 1 - t)
    (𝓝[>] 0) (𝓝 (1 - 0))).smul (supported_log_shift_tendsto hY hs)
  have hnoise := (tendsto_const_nhds (x := K)).mul (zero_weight_log_shift_tendsto hY)
  simpa only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, sub_zero, one_smul, add_zero] using hmain.add hnoise

open scoped CStarAlgebra in
private lemma finiteTraceLog_eq_raw (X Y : DensityState n) :
    finiteTraceLogRelativeEntropy X Y =
      ((CStarMatrix.ofMatrix.symm X.1) * CFC.log (CStarMatrix.ofMatrix.symm X.1)).trace.re -
      ((CStarMatrix.ofMatrix.symm X.1) * CFC.log (CStarMatrix.ofMatrix.symm Y.1)).trace.re := by
  have mapLog (A : Matrix n n ℂ) (hA : A.IsHermitian) :
      CStarMatrix.ofMatrix (CFC.log A) = CFC.log (CStarMatrix.ofMatrix A) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log A
      (A.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
      hA.isSelfAdjoint hA.isSelfAdjoint
  let A := CStarMatrix.ofMatrix.symm X.1
  let B := CStarMatrix.ofMatrix.symm Y.1
  change (CStarMatrix.ofMatrix A * (CFC.log (CStarMatrix.ofMatrix A) -
    CFC.log (CStarMatrix.ofMatrix B)) : CStarMatrix n n ℂ).trace.re = _
  rw [← mapLog A (density_posSemidef X).isHermitian,
    ← mapLog B (density_posSemidef Y).isHermitian]
  change (A * (CFC.log A - CFC.log B)).trace.re = _
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- The finite branch of support-aware Umegaki entropy converges at a supported pair
along density mixtures with an eventual upper bound from data processing. -/
theorem tendsto_finiteTraceLogRelativeEntropy_of_noise
    (X Y K L : DensityState n) (Xt Yt : ℝ → DensityState n)
    (hXY : SupportContained X Y)
    (hX : ∀ᶠ t : ℝ in 𝓝[>] 0, CStarMatrix.ofMatrix.symm (Xt t).1 =
      (1 - t) • CStarMatrix.ofMatrix.symm X.1 + t • CStarMatrix.ofMatrix.symm K.1)
    (hY : ∀ᶠ t : ℝ in 𝓝[>] 0, CStarMatrix.ofMatrix.symm (Yt t).1 =
      (1 - t) • CStarMatrix.ofMatrix.symm Y.1 + t • CStarMatrix.ofMatrix.symm L.1)
    (hSupport : ∀ᶠ t : ℝ in 𝓝[>] 0, SupportContained (Xt t) (Yt t))
    (hUpper : ∀ᶠ t : ℝ in 𝓝[>] 0, finiteTraceLogRelativeEntropy (Xt t) (Yt t) ≤
      finiteTraceLogRelativeEntropy X Y) :
    Tendsto (fun t : ℝ => finiteTraceLogRelativeEntropy (Xt t) (Yt t))
      (𝓝[>] 0) (𝓝 (finiteTraceLogRelativeEntropy X Y)) := by
  let A := CStarMatrix.ofMatrix.symm X.1
  let B := CStarMatrix.ofMatrix.symm Y.1
  let N := CStarMatrix.ofMatrix.symm K.1
  let M := CStarMatrix.ofMatrix.symm L.1
  let Aₜ (t : ℝ) := CStarMatrix.ofMatrix.symm (Xt t).1
  let Bₜ (t : ℝ) := CStarMatrix.ofMatrix.symm (Yt t).1
  have hA : A.PosSemidef := density_posSemidef X
  have hB : B.PosSemidef := density_posSemidef Y
  have hM : (1 - M).PosSemidef := density_le_one (density_posSemidef L) L.2.2
  have hs : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0 := fun v hv => hXY hv
  have hself := tendsto_self_log_mixture hA.isHermitian (density_posSemidef K).isHermitian
  have hcross := tendsto_cross_log_mixture_shift (K := N) hB hs
  have hlow := (continuous_reTrace.continuousAt.tendsto.comp hself).sub
    (continuous_reTrace.continuousAt.tendsto.comp hcross)
  rw [← finiteTraceLog_eq_raw X Y] at hlow
  refine hlow.squeeze' tendsto_const_nhds ?_ hUpper
  filter_upwards [hX, hY, hSupport, self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with
    t hAt hBt hst ht
  have hAt' : Aₜ t = (1 - t) • A + t • N := hAt
  have hBt' : Bₜ t = (1 - t) • B + t • M := hBt
  have hshift : (B + t • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul ht)
  have hle : Bₜ t ≤ B + t • 1 := by
    apply Matrix.le_iff.mpr
    rw [hBt', show B + t • (1 : Matrix n n ℂ) - ((1 - t) • B + t • M) =
      t • (B + (1 - M)) by rw [smul_add, smul_sub, sub_smul, one_smul]; abel]
    exact (hB.add hM).smul ht.le
  have hlog := supported_trace_log_le (density_posSemidef (Xt t)) (density_posSemidef (Yt t))
    hshift (fun v hv => hst hv) hle
  rw [finiteTraceLog_eq_raw]
  change (((1 - t) • A + t • N) * CFC.log ((1 - t) • A + t • N)).trace.re -
      (((1 - t) • A + t • N) * CFC.log (B + t • 1)).trace.re ≤
      (Aₜ t * CFC.log (Aₜ t)).trace.re - (Aₜ t * CFC.log (Bₜ t)).trace.re
  rw [← hAt']
  exact sub_le_sub_left hlog _

#print axioms tendsto_finiteTraceLogRelativeEntropy_of_noise

end D5.S3.Quantum.Divergence.UmegakiSupportedNoise
