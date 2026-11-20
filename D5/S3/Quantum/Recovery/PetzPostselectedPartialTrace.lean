import D5.S3.Quantum.Recovery.PetzPostselectedReference
import D5.S3.Quantum.Recovery.PetzPostselectionSpectralJensen
import D5.S3.Quantum.Recovery.PetzPhysicalAmplitude
import D5.S3.Quantum.Lieb.SupportPerspectiveTransport
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

/-! Ordinary Petz recovery after a commuting postselection and right partial trace. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef marginalRight partialTraceRight partialTraceRight_posSemidef)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (partialTraceRight_smul)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (spectral_sqrt_normalization support_of_nonneg_le_smul)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open PetzPhysicalAmplitude (lift lift_mul lift_conjTranspose ordinaryPetz trace_lift_mul)
open PetzPostselectedReference
  (finiteTraceLogRelativeEntropy_of_postselection sqrt_mul_sqrt_of_postselection
    traceNorm_gram_sub_sq_le)
open PetzPostselectionSpectralJensen (stateMatrix exp_half_entropy_le_trace_threeHalves_inverseSqrt)

namespace PetzPostselectedPartialTrace

universe u

private theorem cfc_real_adjoint {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (X : Matrix n n ℂ) : (cfc f X)ᴴ = cfc f X := by
  change star (cfc f X) = cfc f X
  exact (cfc_predicate f X : IsSelfAdjoint (cfc f X)).star_eq

private theorem cfc_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  rw [← cfc_mul Real.sqrt Real.sqrt X
    Real.continuous_sqrt.continuousOn Real.continuous_sqrt.continuousOn]
  calc
    _ = cfc (fun x : ℝ => x) X := by
      apply cfc_congr
      intro x hx
      exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)
    _ = X := cfc_id' ℝ X hX.isHermitian.isSelfAdjoint

private theorem frobenius_eq_one_of_gram_trace {n : Type*} [Fintype n]
    (X : Matrix n n ℂ) (hX : (X * Xᴴ).trace = 1) : ‖X‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg X) zero_le_one).mp
  have h := congrArg Complex.re (frobenius_norm_sq_eq_trace X)
  simpa only [Complex.ofReal_re, Matrix.trace_mul_comm Xᴴ X, hX,
    Complex.one_re, one_pow] using h

private theorem supportContained_of_le_smul {n : Type*} [Fintype n] [DecidableEq n]
    (p q : DensityState n) (r : ℝ) (hle : stateMatrix p ≤ r • stateMatrix q) :
    SupportContained p q := by
  intro v hv
  change stateMatrix q *ᵥ v = 0 at hv
  change stateMatrix p *ᵥ v = 0
  have hp := density_posSemidef p
  have hnonneg := hp.dotProduct_mulVec_nonneg v
  have hdiff := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, dotProduct_sub,
    dotProduct_zero, zero_sub] at hdiff
  exact hp.dotProduct_mulVec_zero_iff.mp (le_antisymm (neg_nonneg.mp hdiff) hnonneg)

variable {a e : Type u} [Fintype a] [DecidableEq a] [Fintype e] [DecidableEq e]

private theorem stateMatrix_marginalRight (ρ : DensityState (a × e)) :
    stateMatrix (marginalRight ρ) = partialTraceRight (stateMatrix ρ) := rfl

omit [Fintype a] [DecidableEq a] [DecidableEq e] in
private theorem partialTraceRight_sub (X Y : Matrix (a × e) (a × e) ℂ) :
    partialTraceRight (X - Y) = partialTraceRight X - partialTraceRight Y := by
  ext i j
  simp only [partialTraceRight, Matrix.sub_apply, Finset.sum_sub_distrib]

/-- The discarded projection contributes a positive matrix, so the reference
marginal dominates the postselected marginal after rescaling. -/
theorem marginalRight_le_inv_smul_of_postselection (ρ σ : DensityState (a × e))
    {P : Matrix (a × e) (a × e) ℂ} {t : ℝ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    stateMatrix (marginalRight ρ) ≤ t⁻¹ • stateMatrix (marginalRight σ) := by
  let S := stateMatrix σ
  have hscaled : t • stateMatrix ρ = S * P := by
    rw [hρ, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hPS : P * S = S * P := hSP.symm.eq
  have hcomm : (1 - P) * S = S * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPS]
  have hproj : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hcomp : (1 - P) * S * (1 - P)ᴴ = S - t • stateMatrix ρ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP, hcomm, Matrix.mul_assoc,
      hproj, Matrix.mul_sub, Matrix.mul_one, hscaled]
  have hdiff : (S - t • stateMatrix ρ).PosSemidef := by
    rw [← hcomp]
    exact (density_posSemidef σ).mul_mul_conjTranspose_same (1 - P)
  have hmarginal :
      (stateMatrix (marginalRight σ) - t • stateMatrix (marginalRight ρ)).PosSemidef := by
    simpa only [stateMatrix_marginalRight, partialTraceRight_sub, partialTraceRight_smul, S] using
      partialTraceRight_posSemidef hdiff
  apply Matrix.le_iff.mpr
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using
    hmarginal.smul (inv_nonneg.mpr ht.le)

/-- The full amplitude for ordinary Petz recovery, with the inverse square
root evaluated on the support of the actual reference marginal. -/
def petzAmplitude (σ : Matrix (a × e) (a × e) ℂ) (p : Matrix a a ℂ) :
    Matrix (a × e) (a × e) ℂ :=
  cfc Real.sqrt σ * lift (spectralInverseSqrt (partialTraceRight σ) * cfc Real.sqrt p)

theorem petzAmplitude_gram (σ : Matrix (a × e) (a × e) ℂ) {p : Matrix a a ℂ}
    (hp : p.PosSemidef) :
    petzAmplitude σ p * (petzAmplitude σ p)ᴴ = ordinaryPetz σ p := by
  let U := cfc Real.sqrt σ
  let V := cfc Real.sqrt p
  let W := spectralInverseSqrt (partialTraceRight σ)
  have hW : Wᴴ = W := cfc_real_adjoint (fun x : ℝ => (Real.sqrt x)⁻¹) (partialTraceRight σ)
  have hV : Vᴴ = V := cfc_real_adjoint Real.sqrt p
  have hU : Uᴴ = U := cfc_real_adjoint Real.sqrt σ
  have hVV : V * V = p := cfc_sqrt_mul_self hp
  change (U * lift (W * V)) * (U * lift (W * V))ᴴ = U * lift (W * p * W) * U
  rw [Matrix.conjTranspose_mul, lift_conjTranspose, Matrix.conjTranspose_mul, hV, hW, hU]
  calc
    _ = U * (lift (W * V) * lift (V * W)) * U := by simp only [Matrix.mul_assoc]
    _ = U * lift (W * p * W) * U := by
      rw [← lift_mul, show (W * V) * (V * W) = W * p * W by
        calc
          _ = W * (V * V) * W := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hVV]]

/-- The Petz Gram has trace one when the retained input is dominated by a
scalar multiple of the retained reference. -/
theorem ordinaryPetz_trace_of_le_smul (σ : Matrix (a × e) (a × e) ℂ)
    (hσ : σ.PosSemidef) {p : Matrix a a ℂ} (hp : p.PosSemidef) (htr : p.trace = 1)
    (r : ℝ) (hle : p ≤ r • partialTraceRight σ) : (ordinaryPetz σ p).trace = 1 := by
  let q := partialTraceRight σ
  let W := spectralInverseSqrt q
  let U := cfc Real.sqrt σ
  have hq : q.PosSemidef := partialTraceRight_posSemidef hσ
  obtain ⟨_, _, hQ, _, _, _, hQq, hWqW⟩ := spectral_sqrt_normalization q hq
  obtain ⟨hQp, _⟩ := support_of_nonneg_le_smul q p (spectralSupport q) hQ hQq hp r hle
  have hUU : U * U = σ := cfc_sqrt_mul_self hσ
  change (U * lift (W * p * W) * U).trace = 1
  calc
    _ = (U * U * lift (W * p * W)).trace := Matrix.trace_mul_cycle _ _ _
    _ = (lift (W * p * W) * σ).trace := by
      rw [hUU, Matrix.trace_mul_comm σ (lift (W * p * W))]
    _ = (W * p * W * q).trace := trace_lift_mul _ _
    _ = ((W * q * W) * p).trace := by
      rw [Matrix.mul_assoc (W * p) W q, Matrix.trace_mul_comm (W * p) (W * q),
        ← Matrix.mul_assoc (W * q) W p]
    _ = 1 := by rw [hWqW, hQp, htr]

private theorem threeHalves_eq_mul_sqrt {p : Matrix a a ℂ} (hp : p.PosSemidef) :
    cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p = p * cfc Real.sqrt p := by
  calc
    _ = cfc (fun x : ℝ => x * Real.sqrt x) p := by
      apply cfc_congr
      intro x hx
      change x ^ (3 / 2 : ℝ) = x * Real.sqrt x
      have hx₀ := spectrum_nonneg_of_nonneg hp.nonneg hx
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add_of_nonneg hx₀ zero_le_one (by norm_num), Real.rpow_one]
    _ = cfc (fun x : ℝ => x) p * cfc Real.sqrt p :=
      cfc_mul (fun x : ℝ => x) Real.sqrt p continuous_id.continuousOn
        Real.continuous_sqrt.continuousOn
    _ = _ := by rw [cfc_id' ℝ p hp.isHermitian.isSelfAdjoint]

/-- The complex trace of the postselected amplitude overlap is the retained
spectral moment scaled by the square root of the postselection weight. -/
theorem trace_sqrt_mul_petzAmplitude (ρ σ : DensityState (a × e))
    {P : Matrix (a × e) (a × e) ℂ} {t : ℝ}
    (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    let p := stateMatrix (marginalRight ρ)
    let q := stateMatrix (marginalRight σ)
    (cfc Real.sqrt (stateMatrix ρ) * petzAmplitude (stateMatrix σ) p).trace =
      (Real.sqrt t : ℂ) *
        (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p * spectralInverseSqrt q).trace := by
  let p := stateMatrix (marginalRight ρ)
  let W := spectralInverseSqrt (stateMatrix (marginalRight σ))
  let V := cfc Real.sqrt p
  have hroot := sqrt_mul_sqrt_of_postselection
    (density_posSemidef ρ) (density_posSemidef σ) hSP hPP ht hρ
  have hVp : Commute V p := (Commute.refl p).cfc_real Real.sqrt
  change (cfc Real.sqrt (stateMatrix ρ) *
      (cfc Real.sqrt (stateMatrix σ) * lift (W * V))).trace = _
  calc
    _ = ((Real.sqrt t • stateMatrix ρ) * lift (W * V)).trace := by
      rw [← Matrix.mul_assoc, hroot]
    _ = (Real.sqrt t : ℂ) * (lift (W * V) * stateMatrix ρ).trace := by
      rw [Matrix.smul_mul, Matrix.trace_smul,
        Matrix.trace_mul_comm (stateMatrix ρ) (lift (W * V)), Complex.real_smul]
    _ = (Real.sqrt t : ℂ) * ((W * V) * p).trace := by
      rw [trace_lift_mul, ← stateMatrix_marginalRight ρ]
    _ = (Real.sqrt t : ℂ) * ((p * V) * W).trace := by
      rw [Matrix.mul_assoc W V p, Matrix.trace_mul_comm W (V * p), hVp.eq]
    _ = _ := by rw [threeHalves_eq_mul_sqrt (density_posSemidef (marginalRight ρ))]

/-- The full squared trace-norm recovery error is at most `4 * (1 - exp (-Δ))`
for the finite trace-log loss of the actual right partial trace. -/
theorem traceNorm_sub_ordinaryPetz_sq_le (ρ σ : DensityState (a × e))
    {P : Matrix (a × e) (a × e) ℂ} {t : ℝ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    let p := marginalRight ρ
    let q := marginalRight σ
    let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
    traceNorm (stateMatrix ρ - ordinaryPetz (stateMatrix σ) (stateMatrix p)) ^ 2 ≤
      4 * (1 - Real.exp (-Δ)) := by
  let p := marginalRight ρ
  let q := marginalRight σ
  let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
  let A := cfc Real.sqrt (stateMatrix ρ)
  let B := petzAmplitude (stateMatrix σ) (stateMatrix p)
  have hp := density_posSemidef p
  have hle := marginalRight_le_inv_smul_of_postselection ρ σ hP hPP hSP ht hρ
  have hsupport : SupportContained p q := supportContained_of_le_smul p q t⁻¹ hle
  have hAadj : Aᴴ = A := cfc_real_adjoint Real.sqrt (stateMatrix ρ)
  have hAgram : A * Aᴴ = stateMatrix ρ := by
    rw [hAadj]
    exact cfc_sqrt_mul_self (density_posSemidef ρ)
  have hBgram : B * Bᴴ = ordinaryPetz (stateMatrix σ) (stateMatrix p) :=
    petzAmplitude_gram _ hp
  have hBtrace : (B * Bᴴ).trace = 1 := by
    rw [hBgram]
    exact ordinaryPetz_trace_of_le_smul _ (density_posSemidef σ) hp p.2.2 t⁻¹ hle
  have hA : ‖A‖ = 1 := frobenius_eq_one_of_gram_trace A (by
    rw [hAgram]
    exact ρ.2.2)
  have hB : ‖B‖ = 1 := frobenius_eq_one_of_gram_trace B hBtrace
  have htrace : (Aᴴ * B).trace.re = Real.sqrt t *
      (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (stateMatrix p) *
        spectralInverseSqrt (stateMatrix q)).trace.re := by
    rw [hAadj]
    have h := trace_sqrt_mul_petzAmplitude ρ σ hPP hSP ht hρ
    exact (congrArg Complex.re h).trans (Complex.re_ofReal_mul _ _)
  have hlog : -Δ / 2 = Real.log t / 2 + finiteTraceLogRelativeEntropy p q / 2 := by
    dsimp only [Δ]
    rw [finiteTraceLogRelativeEntropy_of_postselection ρ σ hSP hPP ht hρ]
    ring
  have hoverlap : Real.exp (-Δ / 2) ≤ (Aᴴ * B).trace.re := by
    rw [htrace, hlog, Real.exp_add, Real.exp_half (Real.log t), Real.exp_log ht]
    exact mul_le_mul_of_nonneg_left
      (exp_half_entropy_le_trace_threeHalves_inverseSqrt p q hsupport) (Real.sqrt_nonneg t)
  have hexp_sq : Real.exp (-Δ / 2) ^ 2 = Real.exp (-Δ) := by
    rw [pow_two, ← Real.exp_add, add_halves]
  have hsq : Real.exp (-Δ) ≤ (Aᴴ * B).trace.re ^ 2 := by
    rw [← hexp_sq]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hoverlap 2
  change traceNorm (stateMatrix ρ - ordinaryPetz (stateMatrix σ) (stateMatrix p)) ^ 2 ≤
    4 * (1 - Real.exp (-Δ))
  calc
    _ = traceNorm (A * Aᴴ - B * Bᴴ) ^ 2 := by rw [hAgram, hBgram]
    _ ≤ 4 * (1 - (Aᴴ * B).trace.re ^ 2) := traceNorm_gram_sub_sq_le A B hA hB
    _ ≤ _ := by linarith only [hsq]

/-- The same squared trace-norm error is at most four times the entropy loss. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_four_mul (ρ σ : DensityState (a × e))
    {P : Matrix (a × e) (a × e) ℂ} {t : ℝ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    let p := marginalRight ρ
    let q := marginalRight σ
    let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
    traceNorm (stateMatrix ρ - ordinaryPetz (stateMatrix σ) (stateMatrix p)) ^ 2 ≤ 4 * Δ := by
  let Δ := finiteTraceLogRelativeEntropy ρ σ -
    finiteTraceLogRelativeEntropy (marginalRight ρ) (marginalRight σ)
  change traceNorm (stateMatrix ρ -
    ordinaryPetz (stateMatrix σ) (stateMatrix (marginalRight ρ))) ^ 2 ≤ 4 * Δ
  exact le_trans (traceNorm_sub_ordinaryPetz_sq_le ρ σ hP hPP hSP ht hρ)
    (by linarith only [Real.add_one_le_exp (-Δ)])

end PetzPostselectedPartialTrace
