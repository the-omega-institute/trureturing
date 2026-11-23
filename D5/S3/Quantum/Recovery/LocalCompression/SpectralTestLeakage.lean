/- GID: D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound both directions of spectral leakage by the full reconstruction error. -/

import D5.S3.Quantum.Measurement.Auric.DiamondBounds
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Weil.ZetaLinear.HermitianPosPart

/-!
# Spectral leakage of finite Kraus maps

Kohdai Kuroiwa's thesis, Chapter 4, Lemma 4.6, equations (4.23)–(4.24),
gives the two sign-leakage trace terms. Separate spectral floors bound the
two Kraus blocks, and the trace-zero effect estimate bounds their weighted sum.
-/

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage

open _root_.Matrix RHLinalg
open scoped Matrix ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_add_le traceNorm_neg)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
  (traceNorm_smul_nonneg)
open D5.S3.Quantum.Measurement.Auric.DiamondBounds (twice_effect_trace_le_traceNorm)

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- The projection onto the strictly positive spectral subspace. -/
def positiveSpectralProjection {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    Matrix n n ℂ :=
  specMap hH (fun x => if 0 < x then 1 else 0)

private lemma specMap_one {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    specMap hH 1 = 1 := by
  simp [specMap]

private lemma specMap_smul {H : Matrix n n ℂ} (hH : H.IsHermitian) (c : ℝ)
    (f : ℝ → ℝ) :
    specMap hH (fun x => c * f x) = (c : ℂ) • specMap hH f := by
  unfold specMap
  rw [← map_smul]
  congr 1
  rw [← diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul, RCLike.ofReal_eq_complex_ofReal]

private lemma spectralProjection_mul_self {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    positiveSpectralProjection hH * positiveSpectralProjection hH =
      positiveSpectralProjection hH := by
  unfold positiveSpectralProjection
  rw [← specMap_mul]
  congr 1
  funext x
  by_cases hx : 0 < x <;> simp [Pi.mul_apply, hx]

omit [DecidableEq n] in
private lemma rtrace_sub' (X Y : Matrix n n ℂ) :
    (X - Y).trace.re = X.trace.re - Y.trace.re := by
  rw [trace_sub, Complex.sub_re]

omit [DecidableEq n] in
private lemma frobSq_block {P Q : Matrix n n ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (K : Matrix n n ℂ) :
    frobSq (Q * K * P) = (Q * (K * P * Kᴴ)).trace.re := by
  change (((Q * K * P)ᴴ * (Q * K * P)).trace).re = _
  rw [conjTranspose_mul, conjTranspose_mul, hP.eq, hQ.eq]
  congr 1
  rw [show P * (Kᴴ * Q) * (Q * K * P) = P * (Kᴴ * (Q * Q) * K) * P by
    simp only [mul_assoc]]
  rw [hQQ, trace_mul_cycle, hPP]
  calc
    (P * (Kᴴ * Q * K)).trace = ((P * Kᴴ) * (Q * K)).trace := by
      simp only [mul_assoc]
    _ = ((Q * K) * (P * Kᴴ)).trace := trace_mul_comm _ _
    _ = (Q * (K * P * Kᴴ)).trace := by simp only [mul_assoc]

private lemma frobSq_commutator {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (K : Matrix n n ℂ) :
    frobSq ⁅P, K⁆ = frobSq ((1 - P) * K * P) + frobSq (P * K * (1 - P)) := by
  let Q := 1 - P
  have hQ : Q.IsHermitian := isHermitian_one.sub hP
  have hPQ : P * Q = 0 := by simp [Q, mul_sub, hPP]
  have hQP : Q * P = 0 := by simp [Q, sub_mul, hPP]
  let A := P * K * Q
  let B := Q * K * P
  have hcomm : ⁅P, K⁆ = A - B := by
    change P * K - K * P = _
    dsimp [A, B, Q]
    noncomm_ring
  have hAB : Aᴴ * B = 0 := by
    simp only [A, B, conjTranspose_mul, hP.eq, hQ.eq, mul_assoc]
    rw [← mul_assoc P Q, hPQ]
    simp
  have hBA : Bᴴ * A = 0 := by
    simp only [A, B, conjTranspose_mul, hP.eq, hQ.eq, mul_assoc]
    rw [← mul_assoc Q P, hQP]
    simp
  change frobSq ⁅P, K⁆ = frobSq B + frobSq A
  rw [hcomm]
  simp only [frobSq, conjTranspose_sub, sub_mul, mul_sub, hAB, hBA,
    zero_sub, sub_zero, sub_neg_eq_add, trace_add, map_add]
  change (Aᴴ * A).trace.re + (Bᴴ * B).trace.re =
    (Bᴴ * B).trace.re + (Aᴴ * A).trace.re
  exact add_comm _ _

private lemma block_trace_bound (K : κ → Matrix n n ℂ) {P Q X : Matrix n n ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hQpos : Q.PosSemidef) {g : ℝ} (hgap : (X - (g : ℂ) • P).PosSemidef) :
    g * (∑ a, frobSq (Q * K a * P)) ≤ (Q * MatrixMap.of_kraus K K X).trace.re := by
  simp only [MatrixMap.of_kraus_apply, Finset.mul_sum, trace_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := trace_mul_nonneg_of_posSemidef hQpos (hgap.mul_mul_conjTranspose_same (K a))
  change 0 ≤ (Q * (K a * (X - (g : ℂ) • P) * (K a)ᴴ)).trace.re at h
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, rtrace_sub', trace_smul] at h
  simpa only [frobSq_block hP hQ hPP hQQ, smul_eq_mul, Complex.re_ofReal_mul,
    sub_nonneg] using h

set_option maxHeartbeats 800000 in
-- The two spectral-floor comparisons elaborate through the finite matrix order instance.
/-- Separate spectral floors control the two directions of the off-diagonal Kraus action. -/
theorem spectral_test_leakage_asymmetric (K : κ → Matrix n n ℂ)
    (hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (gPos gNeg : ℝ)
    (hgap : ∀ i, gPos ≤ hH.eigenvalues i ∨ hH.eigenvalues i ≤ -gNeg)
    (hgPos : 0 < gPos) (hgNeg : 0 < gNeg) :
    let P := positiveSpectralProjection hH
    2 * (gPos * (∑ a, frobSq ((1 - P) * K a * P)) +
      gNeg * (∑ a, frobSq (P * K a * (1 - P)))) ≤
      traceNorm (H - MatrixMap.of_kraus K K H) := by
  dsimp only
  let P := positiveSpectralProjection hH
  let Q := 1 - P
  let T := MatrixMap.of_kraus K K
  let A := hermPosPart hH
  let B := hermNegPart hH
  change 2 * (gPos * (∑ a, frobSq (Q * K a * P)) +
    gNeg * (∑ a, frobSq (P * K a * Q))) ≤ traceNorm (H - T H)
  have hP : P.IsHermitian := specMap_isHermitian _ _
  have hQ : Q.IsHermitian := isHermitian_one.sub hP
  have hPP : P * P = P := spectralProjection_mul_self hH
  have hQQ : Q * Q = Q := by
    simp only [Q, mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hPpos : P.PosSemidef := by
    simpa only [hP.eq, hPP] using posSemidef_conjTranspose_mul_self P
  have hQpos : Q.PosSemidef := by
    simpa only [hQ.eq, hQQ] using posSemidef_conjTranspose_mul_self Q
  have hQspec : Q = specMap hH (1 - (fun x => if 0 < x then 1 else 0)) := by
    simp only [specMap_sub, specMap_one, Q, P, positiveSpectralProjection]
  have hA : (A - (gPos : ℂ) • P).PosSemidef := by
    change (specMap hH (·⁺) - (gPos : ℂ) •
      specMap hH (fun x => if 0 < x then 1 else 0)).PosSemidef
    rw [← specMap_smul, ← specMap_sub]
    refine specMap_posSemidef hH fun i => ?_
    rcases hgap i with hi | hi
    · simpa [Pi.sub_apply, hgPos.trans_le hi, posPart_eq_self.mpr (hgPos.le.trans hi)]
        using sub_nonneg.mpr hi
    · have hn : hH.eigenvalues i ≤ 0 := hi.trans (by linarith)
      simp [Pi.sub_apply, not_lt.mpr hn, posPart_eq_zero.mpr hn]
  have hB : (B - (gNeg : ℂ) • Q).PosSemidef := by
    rw [hQspec]
    change (specMap hH (·⁻) - (gNeg : ℂ) • _).PosSemidef
    rw [← specMap_smul, ← specMap_sub]
    refine specMap_posSemidef hH fun i => ?_
    rcases hgap i with hi | hi
    · simp [Pi.sub_apply, hgPos.trans_le hi, negPart_eq_zero.mpr (hgPos.le.trans hi)]
    · have hn : hH.eigenvalues i ≤ 0 := hi.trans (by linarith)
      simpa [Pi.sub_apply, not_lt.mpr hn, negPart_eq_neg.mpr hn] using
        (show 0 ≤ -hH.eigenvalues i - gNeg by linarith)
  have hPA : P * A = A := by
    change specMap hH _ * specMap hH _ = specMap hH _
    rw [← specMap_mul]
    congr 1
    funext x
    by_cases hx : 0 < x
    · simp [Pi.mul_apply, hx]
    · simp [Pi.mul_apply, hx, posPart_eq_zero.mpr (le_of_not_gt hx)]
  have hPB : P * B = 0 := by
    change specMap hH _ * specMap hH _ = 0
    rw [← specMap_mul, ← specMap_zero hH]
    congr 1
    funext x
    by_cases hx : 0 < x
    · simp [Pi.mul_apply, hx, hx.le]
    · simp [Pi.mul_apply, hx]
  have hsplit : A - B = H := hermPosPart_sub_hermNegPart hH
  have htrace : (H - T H).trace = 0 := by rw [trace_sub, hT H, sub_self]
  have hHerm : (H - T H).IsHermitian := hH.sub (by
    rw [MatrixMap.of_kraus_apply]
    unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, mul_assoc])
  have hleak : (P * (H - T H)).trace.re =
      (Q * T A).trace.re + (P * T B).trace.re := by
    rw [← hsplit]
    simp only [map_sub, Matrix.mul_sub, hPA, hPB, sub_zero, rtrace_sub']
    rw [show Q * T A = T A - P * T A from by simp [Q, Matrix.sub_mul],
      rtrace_sub', hT A]
    ring
  have hleft := block_trace_bound K hP hQ hPP hQQ hQpos hA
  have hright := block_trace_bound K hQ hP hQQ hPP hPpos hB
  have heffect := twice_effect_trace_le_traceNorm _ P hHerm htrace hPpos hQpos
  rw [hleak] at heffect
  linarith

/-- A common two-sided gap controls the full squared Frobenius commutator. -/
theorem spectral_test_leakage (K : κ → Matrix n n ℂ)
    (hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (g : ℝ)
    (hgap : ∀ i, g ≤ hH.eigenvalues i ∨ hH.eigenvalues i ≤ -g) (hg : 0 < g) :
    2 * g * (∑ a, frobSq ⁅positiveSpectralProjection hH, K a⁆) ≤
      traceNorm (H - MatrixMap.of_kraus K K H) := by
  have h := spectral_test_leakage_asymmetric K hT hH g g hgap hg hg
  dsimp only at h
  have hP : (positiveSpectralProjection hH).IsHermitian := specMap_isHermitian _ _
  simp_rw [frobSq_commutator hP (spectralProjection_mul_self hH)]
  rw [Finset.sum_add_distrib]
  linarith only [h]

/-- A uniform reconstruction error bounds the weighted commutators of a finite collection
of signed tests. The common reference and every selected input satisfy the error bound. -/
theorem finite_test_commutator_bound {ι : Type*} [Fintype ι]
    (K : κ → Matrix n n ℂ) (hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    (ρ : ι → Matrix n n ℂ) (σ : Matrix n n ℂ) (t g w : ι → ℝ) (δ : ℝ)
    (hH : ∀ j, (ρ j - (t j : ℂ) • σ).IsHermitian)
    (hg : ∀ j, 0 < g j) (ht : ∀ j, 0 ≤ t j) (hw : ∀ j, 0 ≤ w j)
    (hgap : ∀ j i, g j ≤ (hH j).eigenvalues i ∨ (hH j).eigenvalues i ≤ -g j)
    (hρ : ∀ j, traceNorm (ρ j - MatrixMap.of_kraus K K (ρ j)) ≤ δ)
    (hσ : traceNorm (σ - MatrixMap.of_kraus K K σ) ≤ δ) :
    (∑ j, w j * ∑ a, frobSq ⁅positiveSpectralProjection (hH j), K a⁆) ≤
      (∑ j, w j * (1 + t j) / (2 * g j)) * δ := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  let T := MatrixMap.of_kraus K K
  have hsplit : (ρ j - (t j : ℂ) • σ) - T (ρ j - (t j : ℂ) • σ) =
      (ρ j - T (ρ j)) - (t j : ℂ) • (σ - T σ) := by
    rw [map_sub, map_smul, smul_sub]
    abel
  have hleak := spectral_test_leakage K hT (hH j) (g j) (hgap j) (hg j)
  rw [hsplit] at hleak
  have htriangle := traceNorm_add_le (ρ j - T (ρ j)) (-((t j : ℂ) • (σ - T σ)))
  rw [← sub_eq_add_neg, traceNorm_neg, traceNorm_smul_nonneg _ _ (ht j)] at htriangle
  have herror : 2 * g j * (∑ a, frobSq ⁅positiveSpectralProjection (hH j), K a⁆) ≤
      (1 + t j) * δ := by
    calc
      _ ≤ _ := hleak
      _ ≤ _ := htriangle
      _ ≤ δ + t j * δ := add_le_add (hρ j) (mul_le_mul_of_nonneg_left hσ (ht j))
      _ = _ := by ring
  have hdivide :
      (∑ a, frobSq ⁅positiveSpectralProjection (hH j), K a⁆) ≤
        (1 + t j) * δ / (2 * g j) :=
    (le_div_iff₀ (mul_pos two_pos (hg j))).mpr (by
      rwa [mul_comm _ (2 * g j)])
  calc
    _ ≤ w j * ((1 + t j) * δ / (2 * g j)) :=
      mul_le_mul_of_nonneg_left hdivide (hw j)
    _ = _ := by ring

end D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
