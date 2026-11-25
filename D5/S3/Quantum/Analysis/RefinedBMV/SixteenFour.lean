/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/SixteenFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV product and exponential lower bounds at bidegree (16,4). -/

import D5.S3.Quantum.Analysis.RefinedBMV67
import D5.S3.Quantum.Analysis.RefinedBMV84
import D5.S3.Quantum.Analysis.RefinedBMV.CenteredFourthTrace
import D5.S3.Quantum.Analysis.RefinedBMV.SixteenFourReplay
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

/-! # Four-copy refined BMV at degree sixteen

Two rational Gram blocks compare the ordered word mean with the fourth
trace of the Hermitian part of the shifted product.
-/

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder CStarAlgebra

namespace RefinedBMV
namespace Algebra164

open Algebra44 (realTrace)
open private Word Terms shift aGap aRun gramTerms scaleTerms
  coefficientsVanish coefficients_sound Algebra84.representative weightedSum weightedSum_eq_map
  weightedSum_append weightedSum_scale traceWord traceWord_representative
  eval_gramTerms eval_aRun weightedGram weightedGram_nonneg
  realTrace_smul from D5.S3.Quantum.Analysis.RefinedBMV84
open private Algebra44.realTrace_mul_comm Algebra44.realTrace_add_four
  from D5.S3.Quantum.Analysis.RefinedBMV44
open private evalWord_append43 from D5.S3.Quantum.Analysis.RefinedBMV43

open private words0 words1 G0 G1 ldl0 ldl1
  from D5.S3.Quantum.Analysis.RefinedBMV.SixteenFourCertificate
open private shiftedWord shiftedTerms gapList gapWord gapList_nodup gapList_toFinset
  orderedTerms certificateTerms gapTerms allTerms checkedTraceSum
  from D5.S3.Quantum.Analysis.RefinedBMV.SixteenFourReplay
open private gapTrace word_count from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private def phase (A B : Mat) (i : Bool) : Mat :=
  A ^ (2 + shift i) * B * A ^ (2 - shift i)

private theorem phase_eval (A B : Mat) (i j k l : Bool) :
    realTrace (phase A B i * (phase A B j * (phase A B k * phase A B l))) =
      traceWord A B (shiftedWord i j k l) := by
  simp only [phase, mul_assoc]
  rw [Algebra44.realTrace_mul_comm (A ^ (2 + shift i))]
  unfold traceWord
  apply congrArg realTrace
  simp only [shiftedWord, aGap, evalWord_append43, eval_aRun, evalWord, mul_one, mul_assoc]
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [shift, pow_succ, mul_assoc]

private theorem phase_sum (A B : Mat) :
    weightedSum ℝ (traceWord A B) shiftedTerms =
      16 * realTrace (((1 / 2 : ℝ) • (A ^ 3 * B * A + A ^ 2 * B * A ^ 2)) ^ 4) := by
  have h0 : phase A B false = A ^ 2 * B * A ^ 2 := by simp [phase, shift]
  have h1 : phase A B true = A ^ 3 * B * A := by simp [phase, shift]
  rw [← h1, ← h0, smul_pow, realTrace_smul, Algebra44.realTrace_add_four]
  simp only [shiftedTerms, weightedSum, smul_eq_mul, ← phase_eval]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  norm_num
  ring

/-- The word mean dominates the trace of the fourth power of the shifted Hermitian average. -/
theorem shifted_bound164 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    4845 * realTrace (((1 / 2 : ℝ) • (A ^ 3 * B * A + A ^ 2 * B * A ^ 2)) ^ 4) ≤
      ((balancedWords 16 4).map fun w => realTrace (evalWord A B w)).sum := by
  have h := checkedTraceSum A B hA.isHermitian hB
  simp only [allTerms, gapTerms, certificateTerms, weightedSum_append, weightedSum_scale, phase_sum,
    eval_gramTerms A B hA.isHermitian hB] at h
  have gapEval (g : FourCopyGap.Gap) :
      trace (evalWord A B (gapWord g)) = gapTrace A B g := by
    simp only [gapWord, gapTrace, aGap, evalWord_append43, eval_aRun, evalWord, mul_one, mul_assoc]
  have hsum :
      5 * (∑ g ∈ FourCopyGap.gaps 16, gapTrace A B g) =
        ((balancedWords 16 4).map fun w => trace (evalWord A B w)).sum := by
    have hg := FourCopyGap.wordMean_eq_gaps 16 A B
    rw [FourCopyGap.wordMean, word_count, FourCopyGap.gaps_card] at hg
    rw [show (20 : ℕ).choose 4 = 4845 by decide, show (19 : ℕ).choose 3 = 969 by decide] at hg
    norm_num at hg
    linear_combination -4845 * hg
  have hwords : 5 * weightedSum ℝ (traceWord A B) orderedTerms =
      ((balancedWords 16 4).map fun w => realTrace (evalWord A B w)).sum := by
    have hh := congrArg Complex.re hsum
    rw [← gapList_toFinset, List.sum_toFinset _ gapList_nodup] at hh
    have reSum (l : List ℂ) : l.sum.re = (l.map Complex.re).sum := by
      induction l with
      | nil => simp
      | cons z zs ih => simp only [List.sum_cons, List.map_cons, Complex.add_re, ih]
    rw [Complex.mul_re] at hh
    norm_num at hh
    simp only [reSum, List.map_map, Function.comp_def] at hh
    simpa only [orderedTerms, weightedSum_eq_map, List.map_map, Function.comp_def, Rat.cast_one,
      one_smul, traceWord, realTrace, gapEval] using hh
  simp only [evalWord, mul_one] at h
  have h0 := weightedGram_nonneg G0 (fun i => evalWord A B (words0 i)) 1 Matrix.PosSemidef.one ldl0
  have h1 := weightedGram_nonneg G1 (fun i => evalWord A B (words1 i)) A hA ldl1
  simp only [smul_add] at h ⊢
  norm_num at h
  linarith only [h, h0, h1, hwords]

end
end Algebra164

open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower
open private fourthWordTraceSum exponentialLowerOfRoot
  from D5.S3.Quantum.Analysis.RefinedBMV67

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The refined BMV product lower bound at bidegree (16,4). -/
theorem product_bound164 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    4845 * (trace ((A ^ 4 * B) ^ 4)).re ≤
      ((balancedWords 16 4).map fun w => (trace (evalWord A B w)).re).sum := by
  let J := (1 / 2 : ℝ) • (A * B + B * A)
  have hphase : (1 / 2 : ℝ) • (A ^ 3 * B * A + A ^ 2 * B * A ^ 2) = A ^ 2 * J * A := by
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul,
      pow_succ, pow_zero, one_mul, mul_assoc]
  have htrace : trace (((1 / 2 : ℝ) • (A ^ 3 * B * A + A ^ 2 * B * A ^ 2)) ^ 4) =
      trace ((A ^ 3 * J) ^ 4) := by
    rw [hphase, trace_cycle_power (A ^ 2 * J) A 4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hcenter : (trace ((A ^ 4 * B) ^ 4)).re ≤ (trace ((A ^ 3 * J) ^ 4)).re := by
    simpa only [J, Nat.reduceAdd, pow_one] using
      fourth_trace_le_centered_power A B hA hB 3 1
  have hcmp : (trace ((A ^ 4 * B) ^ 4)).re ≤
      (trace (((1 / 2 : ℝ) • (A ^ 3 * B * A + A ^ 2 * B * A ^ 2)) ^ 4)).re := by
    rw [htrace]
    exact hcenter
  exact (mul_le_mul_of_nonneg_left hcmp (show 0 ≤ (4845 : ℝ) by norm_num)).trans
    (Algebra164.shifted_bound164 A B hA hB)

/-- The refined exponential lower bound at bidegree (16,4). -/
theorem exponential_bound164 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    4845 * (trace (exp ((16 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 16 4).map fun w => (trace (evalWord (exp H) (exp K) w)).re).sum := by
  simpa only [Nat.cast_ofNat, fourthWordTraceSum] using
    exponentialLowerOfRoot 16 4845 H K hH hK (fun X B hX hB => by
      simpa only [Nat.cast_ofNat, fourthWordTraceSum, ← pow_mul X 4 4] using
        product_bound164 (X ^ 4) B (hX.pow 4) hB.isHermitian)

end
end RefinedBMV
