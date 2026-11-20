import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Recovery.PetzPositiveTracePostselection

/-!
Ordinary Petz recovery for a commuting projector likelihood. The positive-map
estimate below uses the actual finite POVM attaining the fidelity overlap.
The entropy comparison uses the supported spectral weights and the repository's
finite branch of Umegaki relative entropy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.CommutingMidpoint (rootFidelity)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)
open PetzPositiveTraceFidelity
  (fidelityEigenvalues fidelityObservable_posSemidef fidelitySpectralPovm
    fidelitySpectralPovm_attains povmOverlap)
open PetzPositiveTracePostselection (mapDensityState ordinaryPetz)
open PetzPostselectedReference
  (finiteTraceLogRelativeEntropy_of_postselection sqrt_mul_sqrt_of_postselection)
open PetzPostselectionSpectralJensen (stateMatrix exp_half_entropy_le_trace_threeHalves_inverseSqrt)

open private frobenius_sqrt_mul_sqrt traceNorm_mul_le_frobenius traceNorm_sum_le from
  D5.S3.Quantum.Recovery.PetzPositiveTraceFidelity

open private postselection_le_inv_smul ordinaryPetz_state supportContained_of_le_smul
  sqrt_eq_cfc_real threeHalves_eq_mul_sqrt traceNorm_sub_sq_le_four_one_sub_fidelity_sq from
  D5.S3.Quantum.Recovery.PetzPositiveTracePostselection

namespace PetzProjectorSharpFour

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The attaining input POVM bounds the full trace norm of the output product.
Both matrix arguments of the fidelity may have arbitrary trace. -/
theorem traceNorm_sqrt_test_mul_image_le_rootFidelity
    (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (B : Matrix a a ℂ) (T : Matrix b b ℂ) (hB : B.PosSemidef) (hT : T.PosSemidef) :
    traceNorm (CFC.sqrt T * Φ B) ≤
      rootFidelity B (CFC.sqrt B * Φ.dual T * CFC.sqrt B) := by
  let U := CFC.sqrt B
  let A := U * Φ.dual T * U
  have hU : Uᴴ = U := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hUU : U * U = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hA : A.PosSemidef := by
    simpa only [A, hU] using (hΦ.dual hT).mul_mul_conjTranspose_same U
  let hK := (fidelityObservable_posSemidef B A hB hA).isHermitian
  let N := fidelitySpectralPovm B A hK
  obtain ⟨hN, hNsum, hOverlap⟩ := fidelitySpectralPovm_attains B A hB hA hK
  change (∀ i, IsStarProjection (N i)) at hN
  change (∑ i, N i) = 1 at hNsum
  change povmOverlap B A N = rootFidelity B A at hOverlap
  let X := fun i => Φ (U * N i * U)
  have hX (i : Option ↥(fidelityEigenvalues hK)) : (X i).PosSemidef := by
    change (Φ (U * N i * U)).PosSemidef
    apply hΦ
    simpa only [hU] using (hN i).nonneg.posSemidef.mul_mul_conjTranspose_same U
  have hXsum : (∑ i, X i) = Φ B := by
    change (∑ i, Φ (U * N i * U)) = Φ B
    rw [← map_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hNsum, Matrix.mul_one, hUU]
  have hMass (i : Option ↥(fidelityEigenvalues hK)) : (X i).trace = (B * N i).trace := by
    change (Φ (U * N i * U)).trace = _
    rw [hTP, Matrix.trace_mul_cycle U (N i) U, hUU]
  have hTest (i : Option ↥(fidelityEigenvalues hK)) : (T * X i).trace = (A * N i).trace := by
    calc
      _ = (X i * T).trace := Matrix.trace_mul_comm _ _
      _ = ((U * N i * U) * Φ.dual T).trace :=
        MatrixMap.Dual.trace_eq Φ (U * N i * U) T
      _ = (U * (N i * U * Φ.dual T)).trace := by simp only [Matrix.mul_assoc]
      _ = ((N i * U * Φ.dual T) * U).trace := Matrix.trace_mul_comm _ _
      _ = (N i * A).trace := by simp only [A, Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  change traceNorm (CFC.sqrt T * Φ B) ≤ rootFidelity B A
  calc
    _ = traceNorm (∑ i, CFC.sqrt T * X i) := by rw [← Matrix.mul_sum, hXsum]
    _ ≤ ∑ i, traceNorm (CFC.sqrt T * X i) := traceNorm_sum_le Finset.univ _
    _ ≤ povmOverlap B A N := by
      unfold povmOverlap
      refine Finset.sum_le_sum fun i _ => ?_
      let V := CFC.sqrt (X i)
      have hV : Vᴴ = V := (CFC.sqrt_nonneg (X i)).posSemidef.isHermitian.eq
      have hVV : V * V = X i := CFC.sqrt_mul_sqrt_self _ (hX i).nonneg
      have hNorm : ‖V‖ = Real.sqrt (X i).trace.re := by
        have hSq := congrArg Complex.re (frobenius_norm_sq_eq_trace V)
        rw [Complex.ofReal_re, hV, hVV] at hSq
        rw [← hSq, Real.sqrt_sq (norm_nonneg V)]
      have hTestNonneg : 0 ≤ (T * X i).trace.re :=
        (Complex.nonneg_iff.mp (hT.trace_mul_nonneg (hX i))).1
      calc
        traceNorm (CFC.sqrt T * X i) = traceNorm ((CFC.sqrt T * V) * V) := by
          rw [Matrix.mul_assoc, hVV]
        _ ≤ ‖CFC.sqrt T * V‖ * ‖V‖ := traceNorm_mul_le_frobenius _ _
        _ = Real.sqrt ((B * N i).trace.re * (A * N i).trace.re) := by
          rw [frobenius_sqrt_mul_sqrt T (X i) hT (hX i), hNorm,
            ← Real.sqrt_mul hTestNonneg, hTest i, hMass i, mul_comm]
    _ = _ := hOverlap

private theorem scaled_spectral_moment_le_traceNorm {p H : Matrix b b ℂ}
    (hp : p.PosSemidef) (hH : Hᴴ = H) {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt s * (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p * H).trace.re ≤
      traceNorm (CFC.sqrt (s • (H * p * H)) * p) := by
  let T := s • (H * p * H)
  let V := CFC.sqrt p
  let G : Matrix b b ℂ := Real.sqrt s • (V * H * p)
  have hT : T.PosSemidef := by
    simpa only [T, hH] using (hp.mul_mul_conjTranspose_same H).smul hs
  have hTsqrt : (CFC.sqrt T)ᴴ = CFC.sqrt T := (CFC.sqrt_nonneg T).posSemidef.isHermitian.eq
  have hV : Vᴴ = V := (CFC.sqrt_nonneg p).posSemidef.isHermitian.eq
  have hVV : V * V = p := CFC.sqrt_mul_sqrt_self p hp.nonneg
  have hGramLeft : (CFC.sqrt T * p)ᴴ * (CFC.sqrt T * p) = p * T * p := by
    rw [Matrix.conjTranspose_mul, hp.isHermitian.eq, hTsqrt]
    calc
      _ = p * (CFC.sqrt T * CFC.sqrt T) * p := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self T hT.nonneg]
  have hGramRight : Gᴴ * G = p * T * p := by
    change (Real.sqrt s • (V * H * p))ᴴ * (Real.sqrt s • (V * H * p)) = _
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Real.mul_self_sqrt hs, Matrix.conjTranspose_mul, hp.isHermitian.eq, hH, hV, T]
    congr 1
    calc
      _ = p * H * (V * V) * H * p := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hVV]; simp only [Matrix.mul_assoc]
  have hTrace : G.trace.re =
      Real.sqrt s * (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p * H).trace.re := by
    change ((Real.sqrt s • (V * H * p)).trace).re = _
    rw [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul,
      Matrix.trace_mul_cycle V H p, threeHalves_eq_mul_sqrt hp]
  have hNorm : traceNorm (CFC.sqrt T * p) = traceNorm G := by
    change (CFC.sqrt ((CFC.sqrt T * p)ᴴ * (CFC.sqrt T * p))).trace.re =
      (CFC.sqrt (Gᴴ * G)).trace.re
    rw [hGramLeft, hGramRight]
  rw [← hTrace]
  change G.trace.re ≤ traceNorm (CFC.sqrt T * p)
  rw [hNorm]
  exact (traceNorm_eq_max_re_tr_U G).2 ⟨1, by simp⟩

set_option maxHeartbeats 1000000 in
/-- The full squared trace norm of the actual ordinary Petz residual is at
most `4 * (1 - exp (-Δ))`, which is at most `4 * Δ`. Both trace-log terms
of `Δ` are on their finite Umegaki branches, including for singular states. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_four_one_sub_exp_neg_umegakiLoss
    (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (ρ σ : DensityState a) {P : Matrix a a ℂ} {s : ℝ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (hs : 0 < s) (hρ : stateMatrix ρ = s⁻¹ • (P * stateMatrix σ * P)) :
    let p := mapDensityState Φ hΦ hTP ρ
    let q := mapDensityState Φ hΦ hTP σ
    let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
    let R := ordinaryPetz Φ (stateMatrix σ) (stateMatrix p)
    traceNorm (stateMatrix ρ - R) ^ 2 ≤ 4 * (1 - Real.exp (-Δ)) ∧
      4 * (1 - Real.exp (-Δ)) ≤ 4 * Δ := by
  let B := stateMatrix ρ
  let S := stateMatrix σ
  let p := mapDensityState Φ hΦ hTP ρ
  let q := mapDensityState Φ hΦ hTP σ
  let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
  let R := ordinaryPetz Φ S (stateMatrix p)
  let U := CFC.sqrt B
  let V := CFC.sqrt S
  let H := spectralInverseSqrt (stateMatrix q)
  let T := s • (H * stateMatrix p * H)
  let A := U * Φ.dual T * U
  have hB := density_posSemidef ρ
  have hS := density_posSemidef σ
  have hp := density_posSemidef p
  have hq := density_posSemidef q
  have hρ' : B = s⁻¹ • (S * P) := by
    change stateMatrix ρ = _
    rw [hρ, hSP.symm.eq, Matrix.mul_assoc, hPP]
  have hInLe := postselection_le_inv_smul ρ σ hP hPP hSP hs hρ'
  have _hInSupport : SupportContained ρ σ := supportContained_of_le_smul ρ σ s⁻¹ hInLe
  have hOutLe : stateMatrix p ≤ s⁻¹ • stateMatrix q := by
    change Φ B ≤ s⁻¹ • Φ S
    apply Matrix.le_iff.mpr
    rw [← Φ.map_smul_of_tower, ← map_sub]
    exact hΦ (Matrix.le_iff.mp hInLe)
  have hOutSupport : SupportContained p q := supportContained_of_le_smul p q s⁻¹ hOutLe
  obtain ⟨hR, hRtr⟩ := ordinaryPetz_state Φ hΦ hS hp p.2.2 s⁻¹ hOutLe
  change R.PosSemidef at hR
  change R.trace = 1 at hRtr
  obtain ⟨_, hH, _, _, _, _, _, _⟩ := spectral_sqrt_normalization (stateMatrix q) hq
  change Hᴴ = H at hH
  have hT : T.PosSemidef := by
    simpa only [T, hH] using (hp.mul_mul_conjTranspose_same H).smul hs.le
  have hUS : U * V = Real.sqrt s • B := by
    change CFC.sqrt B * CFC.sqrt S = _
    rw [sqrt_eq_cfc_real hB, sqrt_eq_cfc_real hS]
    exact sqrt_mul_sqrt_of_postselection hB hS hSP hPP hs hρ'
  have hU : Uᴴ = U := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hV : Vᴴ = V := (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hBB : Bᴴ = B := hB.isHermitian.eq
  have hVU : V * U = Real.sqrt s • B := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial,
      hU, hV, hBB] using congrArg Matrix.conjTranspose hUS
  have hUU : U * U = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hSandwichA : U * A * U = B * Φ.dual T * B := by
    calc
      _ = (U * U) * Φ.dual T * (U * U) := by simp only [A, Matrix.mul_assoc]
      _ = _ := by rw [hUU]
  have hSandwichR : U * R * U = B * Φ.dual T * B := by
    change U * (V * Φ.dual (H * stateMatrix p * H) * V) * U = _
    calc
      _ = (U * V) * Φ.dual (H * stateMatrix p * H) * (V * U) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hUS, hVU]
        simp only [T, Φ.dual.map_smul_of_tower, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul, Real.mul_self_sqrt hs.le]
  have hFidelity : rootFidelity B A = rootFidelity B R := by
    change (CFC.sqrt (U * A * U)).trace.re = (CFC.sqrt (U * R * U)).trace.re
    rw [hSandwichA, hSandwichR]
  have hLoss : -Δ / 2 = Real.log s / 2 + finiteTraceLogRelativeEntropy p q / 2 := by
    dsimp only [Δ]
    rw [finiteTraceLogRelativeEntropy_of_postselection ρ σ hSP hPP hs hρ']
    ring
  have hExp : Real.exp (-Δ / 2) ≤
      Real.sqrt s * (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (stateMatrix p) * H).trace.re := by
    rw [hLoss, Real.exp_add, Real.exp_half (Real.log s), Real.exp_log hs]
    exact mul_le_mul_of_nonneg_left
      (exp_half_entropy_le_trace_threeHalves_inverseSqrt p q hOutSupport) (Real.sqrt_nonneg s)
  have hLower : Real.exp (-Δ / 2) ≤ rootFidelity B R := by
    calc
      _ ≤ Real.sqrt s *
          (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (stateMatrix p) * H).trace.re := hExp
      _ ≤ traceNorm (CFC.sqrt T * stateMatrix p) := scaled_spectral_moment_le_traceNorm hp hH hs.le
      _ ≤ rootFidelity B A := traceNorm_sqrt_test_mul_image_le_rootFidelity Φ hΦ hTP B T hB hT
      _ = _ := hFidelity
  have hExpSq : Real.exp (-Δ / 2) ^ 2 = Real.exp (-Δ) := by
    rw [pow_two, ← Real.exp_add, add_halves]
  have hSq := pow_le_pow_left₀ (Real.exp_pos (-Δ / 2)).le hLower 2
  rw [hExpSq] at hSq
  change traceNorm (B - R) ^ 2 ≤ 4 * (1 - Real.exp (-Δ)) ∧
    4 * (1 - Real.exp (-Δ)) ≤ 4 * Δ
  refine ⟨?_, by linarith only [Real.add_one_le_exp (-Δ)]⟩
  exact (traceNorm_sub_sq_le_four_one_sub_fidelity_sq hB hR ρ.2.2 hRtr).trans
    (by linarith only [hSq])

end PetzProjectorSharpFour
