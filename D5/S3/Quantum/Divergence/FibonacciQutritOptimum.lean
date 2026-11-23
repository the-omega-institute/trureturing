/- GID: D5/S3/Quantum/Divergence/FibonacciQutritOptimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/FibonacciQutritOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact attained Umegaki maximum under CPTP qutrit encoding. -/

import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Divergence.FannesRootFidelityHolevo
import D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
import D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport
import D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Recovery.DiagonalRecordCapacity
import D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation
import D5.S3.Weil.ZetaLinear.RankTrace

/-! Exact Fibonacci Umegaki optimum for qutrit encoding of a diagonal pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

namespace D5.S3.Quantum.Divergence.FibonacciQutritOptimum

open ConditionalHockeyStickOrthogonalReduction (trace_reindex)
open FannesRootFidelityHolevo (supported_of_le)
open D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity (zero_trace_mul_eq_zero)
open D5.S3.Quantum.Recovery.DiagonalRecordCapacity.Basis (basisState basisState_matrix)

/-- The exact optimum in nats. -/
abbrev C3 : ℝ := (113 / 141) * Real.log (113 / 81) + (28 / 141) * Real.log (7 / 3)

private abbrev inputWeights : Fin 3 → ℝ := ![88 / 141, 25 / 141, 28 / 141]
private abbrev referenceWeights : Fin 3 → ℝ := ![66 / 141, 15 / 141, 12 / 141]

private abbrev Mat (n : Type*) := Matrix n n ℂ

open FibonacciQutritSingularSupport.Preparation (matrix)

/-- The likelihood ratios multiply the three positive reference weights to give
`(88, 25, 28) / 141`. -/
private def inputOutput {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 3 → DensityState n) : Mat n :=
  ((4 / 3 : ℝ) * (66 / 141)) • matrix (X 0) +
    ((5 / 3 : ℝ) * (15 / 141)) • matrix (X 1) +
    ((7 / 3 : ℝ) * (12 / 141)) • matrix (X 2)

/-- Reference mixture on the three positive-likelihood classes. -/
def positiveReference {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 3 → DensityState n) : Mat n :=
  (66 / 141 : ℝ) • matrix (X 0) + (15 / 141 : ℝ) • matrix (X 1) +
    (12 / 141 : ℝ) • matrix (X 2)

/-- The reference includes the preparation of the class with zero input weight. -/
private def referenceOutput {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 3 → DensityState n) (X₀ : DensityState n) : Mat n :=
  positiveReference X + (48 / 141 : ℝ) • matrix X₀

private abbrev traceLog {n : Type*} [Fintype n] [DecidableEq n] (A B : Mat n) : ℝ :=
  (A * (CFC.log A - CFC.log B)).trace.re

/-- Umegaki divergence between the two mixtures of the preparations. -/
private def divergence {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 3 → DensityState n) (X₀ : DensityState n) : ℝ :=
  traceLog (inputOutput X) (referenceOutput X X₀)

private theorem first_weight : (4 / 3 : ℝ) * (66 / 141) = 88 / 141 := by norm_num
private theorem second_weight : (5 / 3 : ℝ) * (15 / 141) = 25 / 141 := by norm_num
private theorem third_weight : (7 / 3 : ℝ) * (12 / 141) = 28 / 141 := by norm_num

private theorem sum_inputWeights {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 3 → DensityState n) :
    (∑ i, inputWeights i • matrix (X i)) = inputOutput X := by
  simp only [inputWeights, inputOutput, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, ← add_assoc,
    first_weight, second_weight, third_weight]
  rfl

private theorem sum_referenceWeights {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 3 → DensityState n) :
    (∑ i, referenceWeights i • matrix (X i)) = positiveReference X := by
  simp only [referenceWeights, positiveReference, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, ← add_assoc]
  rfl

private abbrev classicalFormula : ℝ :=
  (4 / 3 * (66 / 141) + 5 / 3 * (15 / 141)) *
      Real.log ((4 / 3 * (66 / 141) + 5 / 3 * (15 / 141)) / (66 / 141 + 15 / 141)) +
    (7 / 3 * (12 / 141)) * Real.log (7 / 3)

private theorem classicalFormula_eq : classicalFormula = C3 := by
  norm_num [classicalFormula, C3]

private theorem overlap_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : DensityState n) : 0 ≤ (matrix X * matrix Y).trace.re :=
  RHLinalg.trace_mul_nonneg_of_posSemidef (density_posSemidef X) (density_posSemidef Y)

private theorem overlap_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : DensityState n) : (matrix X * matrix Y).trace.re ≤ 1 := by
  let A : HermitianMat n ℂ := ⟨matrix X, (density_posSemidef X).isHermitian⟩
  let B : HermitianMat n ℂ := ⟨matrix Y, (density_posSemidef Y).isHermitian⟩
  have h := HermitianMat.inner_le_mul_trace (A := A) (B := B)
    (HermitianMat.zero_le_iff.mpr (density_posSemidef X))
    (HermitianMat.zero_le_iff.mpr (density_posSemidef Y))
  rw [HermitianMat.inner_eq_re_trace] at h
  change (matrix X * matrix Y).trace.re ≤ (matrix X).trace.re * (matrix Y).trace.re at h
  simpa only [show (matrix X).trace = 1 from X.2.2,
    show (matrix Y).trace = 1 from Y.2.2, Complex.one_re, mul_one] using h

private abbrev overlapDeficit (X : Fin 3 → DensityState (Fin 3)) : ℝ :=
  (3 * (1 - (matrix (X 0) * matrix (X 1)).trace.re) +
    11 * (matrix (X 0) * matrix (X 2)).trace.re) / 63360

private abbrev nullLoss (X : Fin 3 → DensityState (Fin 3)) (X₀ : DensityState (Fin 3)) : ℝ :=
  (inputOutput X * (CFC.log (referenceOutput X X₀) - CFC.log (positiveReference X))).trace.re

private theorem overlapDeficit_nonneg (X : Fin 3 → DensityState (Fin 3)) :
    0 ≤ overlapDeficit X :=
  div_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (overlap_le_one (X 0) (X 1))))
      (mul_nonneg (by norm_num) (overlap_nonneg (X 0) (X 2)))) (by norm_num)

private theorem singular_bound (X : Fin 3 → DensityState (Fin 3))
    (X₀ : DensityState (Fin 3))
    (h : ¬ (positiveReference X).PosDef ∨ (positiveReference X).rank ≤ 2) :
    divergence X X₀ ≤ C3 - overlapDeficit X - nullLoss X X₀ ∧
      0 ≤ nullLoss X X₀ ∧ (nullLoss X X₀ = 0 ↔ positiveReference X * matrix X₀ = 0) := by
  have hq (i : Fin 3) : 0 < referenceWeights i := by
    fin_cases i <;> norm_num [referenceWeights]
  have hp (i : Fin 3) :
      (4 / 3 : ℝ) * referenceWeights i ≤ inputWeights i ∧
        inputWeights i ≤ (7 / 3 : ℝ) * referenceWeights i := by
    fin_cases i <;> norm_num [inputWeights, referenceWeights]
  obtain ⟨Y, hdiv, hLoss, hZero, hOverlap⟩ :=
    FibonacciQutritSingularSupport.singular_support_reduction
      X X₀ inputWeights referenceWeights (48 / 141) hq hp (by norm_num)
      (by simpa only [sum_referenceWeights] using h)
  simp only [sum_inputWeights, sum_referenceWeights] at hdiv hLoss hZero
  have hqubit :
      traceLog (∑ i, inputWeights i • matrix (Y i)) (∑ i, referenceWeights i • matrix (Y i)) ≤
        C3 - (3 * (1 - (matrix (Y 0) * matrix (Y 1)).trace.re) +
          11 * (matrix (Y 0) * matrix (Y 2)).trace.re) / 63360 :=
    Qubit.FibonacciMixedQubit.traceLog_le_benchmark_sub_margin
      (fun i => matrix (Y i)) (fun i => density_posSemidef (Y i)) (fun i => (Y i).2.2)
  rw [sum_inputWeights, sum_referenceWeights, hOverlap 0 1, hOverlap 0 2] at hqubit
  refine ⟨?_, hLoss, hZero⟩
  calc
    divergence X X₀ = traceLog (inputOutput Y) (positiveReference Y) - nullLoss X X₀ := hdiv
    _ ≤ _ := sub_le_sub_right hqubit _

private theorem singular_le (X : Fin 3 → DensityState (Fin 3))
    (X₀ : DensityState (Fin 3))
    (h : ¬ (positiveReference X).PosDef ∨ (positiveReference X).rank ≤ 2) :
    divergence X X₀ ≤ C3 := by
  obtain ⟨hBound, hLoss, _⟩ := singular_bound X X₀ h
  exact hBound.trans (sub_le_self _ hLoss) |>.trans (sub_le_self _ (overlapDeficit_nonneg X))

private def reindexDensity {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) (X : DensityState n) : DensityState m :=
  ⟨CStarMatrix.ofMatrix ((matrix X).reindex e e),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef X).submatrix e.symm).nonneg,
    (trace_reindex e (matrix X)).trans X.2.2⟩

private theorem reindex_traceLog {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (e : n ≃ m) (A B : Mat n) :
    traceLog (A.reindex e e) (B.reindex e e) = traceLog A B := by
  let E := Matrix.reindexAlgEquiv ℝ ℂ e
  have hlog (M : Mat n) : CFC.log (E M) = E (CFC.log M) :=
    Matrix.cfc_reindex Real.log e
  change (E A * (CFC.log (E A) - CFC.log (E B))).trace.re = _
  rw [hlog, hlog, ← map_sub, ← map_mul]
  exact congrArg Complex.re (trace_reindex e _)

private theorem reindexed_singular_le {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ Fin 3) (Y : Fin 3 → DensityState n) (Y₀ : DensityState n)
    (hRank : (positiveReference Y).rank ≤ 2) : divergence Y Y₀ ≤ C3 := by
  let Z (i : Fin 3) := reindexDensity e (Y i)
  let Z₀ := reindexDensity e Y₀
  let E := Matrix.reindexAlgEquiv ℝ ℂ e
  have hMatrix (U : DensityState n) : matrix (reindexDensity e U) = E (matrix U) := rfl
  have hA : inputOutput Z = E (inputOutput Y) := by
    simp only [inputOutput, Z, hMatrix, map_add, map_smul]
  have hC : positiveReference Z = E (positiveReference Y) := by
    simp only [positiveReference, Z, hMatrix, map_add, map_smul]
  have hB : referenceOutput Z Z₀ = E (referenceOutput Y Y₀) := by
    simp only [referenceOutput, Z₀, hMatrix, hC, map_add, map_smul]
  have hRankZ : (positiveReference Z).rank ≤ 2 := by
    rw [hC]
    change ((positiveReference Y).reindex e e).rank ≤ 2
    rwa [Matrix.rank_reindex]
  have hdiv : divergence Z Z₀ = divergence Y Y₀ := by
    unfold divergence
    rw [hA, hB]
    exact reindex_traceLog e _ _
  exact hdiv ▸ singular_le Z Z₀ (Or.inr hRankZ)

/-- A full-rank positive-class reference has strictly suboptimal divergence. -/
private theorem divergence_lt_of_posDef (X : Fin 3 → DensityState (Fin 3))
    (X₀ : DensityState (Fin 3)) (hFull : (positiveReference X).PosDef) :
    divergence X X₀ < C3 := by
  by_contra h
  have hStart : classicalFormula ≤ divergence X X₀ := by
    rw [classicalFormula_eq]
    exact le_of_not_gt h
  have hComparison := FibonacciQutritBenchmark.full_rank_benchmark_comparison
    (66 / 141) (15 / 141) (12 / 141) (48 / 141) (X 0) (X 1) (X 2) X₀
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hFull
  obtain ⟨_, _, Y₁, Y₂, Y₃, Y₀, _, _, _, hRank, _, hBetter⟩ := hComparison.2 hStart
  let Y : Fin 3 → DensityState (Fin 2 ⊕ Unit) := ![Y₁, Y₂, Y₃]
  let e : Fin 2 ⊕ Unit ≃ Fin 3 := Fintype.equivFinOfCardEq (by decide)
  have hSmall : divergence Y Y₀ ≤ C3 :=
    reindexed_singular_le e Y Y₀ hRank
  have hBetter' : divergence X X₀ < divergence Y Y₀ := hBetter
  exact h (hBetter'.trans_le hSmall)

/-- Every qutrit preparation has Umegaki divergence at most the Fibonacci benchmark. -/
private theorem divergence_le (X : Fin 3 → DensityState (Fin 3)) (X₀ : DensityState (Fin 3)) :
    divergence X X₀ ≤ C3 := by
  by_cases h : (positiveReference X).PosDef
  · exact (divergence_lt_of_posDef X X₀ h).le
  · exact singular_le X X₀ (Or.inl h)

private theorem reverse_mul_zero {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : DensityState n} (h : matrix X * matrix Y = 0) : matrix Y * matrix X = 0 := by
  simpa only [Matrix.conjTranspose_mul, (density_posSemidef X).isHermitian.eq,
    (density_posSemidef Y).isHermitian.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

/-- The optimal commuting outputs put the first two preparations on a common ray
and place the third and zero-likelihood preparations on separate orthogonal rays. -/
private theorem commuting_attainment :
    ∃ P Q R : DensityState (Fin 3),
      matrix P * matrix Q = 0 ∧ matrix P * matrix R = 0 ∧ matrix Q * matrix R = 0 ∧
      let X : Fin 3 → DensityState (Fin 3) := ![P, P, Q]
      inputOutput X = (113 / 141 : ℝ) • matrix P + (28 / 141 : ℝ) • matrix Q ∧
      referenceOutput X R =
        (81 / 141 : ℝ) • matrix P + (12 / 141 : ℝ) • matrix Q + (48 / 141 : ℝ) • matrix R ∧
      Commute (inputOutput X) (referenceOutput X R) ∧
        (referenceOutput X R).PosDef ∧ divergence X R = C3 := by
  obtain ⟨P, Q, R, hPQ, hPR, hQR, hPos, hValue⟩ :=
    FibonacciQutritBenchmark.classical_benchmark_attained
      (66 / 141) (15 / 141) (12 / 141) (48 / 141)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change matrix P * matrix Q = 0 at hPQ
  change matrix P * matrix R = 0 at hPR
  change matrix Q * matrix R = 0 at hQR
  let X : Fin 3 → DensityState (Fin 3) := ![P, P, Q]
  let A := ((4 / 3 : ℝ) * (66 / 141) + (5 / 3) * (15 / 141)) • matrix P +
    ((7 / 3 : ℝ) * (12 / 141)) • matrix Q
  let B := (66 / 141 + 15 / 141 : ℝ) • matrix P + (12 / 141 : ℝ) • matrix Q +
    (48 / 141 : ℝ) • matrix R
  have hA : inputOutput X = A := by
    simp only [inputOutput, X, A, add_smul]
    rfl
  have hB : referenceOutput X R = B := by
    simp only [referenceOutput, positiveReference, X, B, add_smul]
    rfl
  have hQP := reverse_mul_zero (X := P) (Y := Q) hPQ
  have hRP := reverse_mul_zero (X := P) (Y := R) hPR
  have hRQ := reverse_mul_zero (X := Q) (Y := R) hQR
  refine ⟨P, Q, R, hPQ, hPR, hQR, ?_, ?_, ?_, ?_, ?_⟩
  · change inputOutput X = _
    rw [hA]
    have hMerged : (4 / 3 : ℝ) * (66 / 141) + (5 / 3) * (15 / 141) = 113 / 141 := by
      norm_num
    simp only [A, hMerged, third_weight]
  · change referenceOutput X R = _
    rw [hB]
    have hMerged : (66 / 141 : ℝ) + 15 / 141 = 81 / 141 := by norm_num
    simp only [B, hMerged]
  · change Commute (inputOutput X) (referenceOutput X R)
    rw [hA, hB, commute_iff_eq]
    simp only [A, B, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      hPQ, hPR, hQR, hQP, hRP, hRQ, smul_zero, add_zero, zero_add, smul_smul]
    rw [mul_comm (66 / 141 + 15 / 141 : ℝ), mul_comm (12 / 141 : ℝ)]
  · change (referenceOutput X R).PosDef
    rw [hB]
    exact hPos
  · change divergence X R = C3
    rw [divergence, hA, hB, ← classicalFormula_eq]
    exact hValue

private theorem trace_eq_of_re_trace_eq {A B : Mat (Fin 3)}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {r : ℝ} (h : (A * B).trace.re = r) :
    (A * B).trace = (r : ℂ) := by
  let U : HermitianMat (Fin 3) ℂ := ⟨A, hA⟩
  let V : HermitianMat (Fin 3) ℂ := ⟨B, hB⟩
  exact (HermitianMat.inner_eq_trace_rc U V).symm.trans (congrArg Complex.ofReal h)

private theorem one_sub_posSemidef (X : DensityState (Fin 3)) :
    (1 - matrix X).PosSemidef := by
  let U : HermitianMat (Fin 3) ℂ := ⟨matrix X, (density_posSemidef X).isHermitian⟩
  have hTrace : U.trace = 1 := by
    change (matrix X).trace.re = 1
    rw [show (matrix X).trace = 1 from X.2.2, Complex.one_re]
  have h := HermitianMat.le_trace_smul_one (A := U)
    (HermitianMat.zero_le_iff.mpr (density_posSemidef X))
  rw [hTrace, one_smul] at h
  exact HermitianMat.le_iff.mp h

private theorem matrix_eq_of_overlap_one (X Y : DensityState (Fin 3))
    (h : (matrix X * matrix Y).trace.re = 1) : matrix X = matrix Y := by
  have hxy := trace_eq_of_re_trace_eq (density_posSemidef X).isHermitian
    (density_posSemidef Y).isHermitian h
  have hyx : (matrix Y * matrix X).trace = 1 := by
    rw [Matrix.trace_mul_comm, hxy, Complex.ofReal_one]
  have hleft := zero_trace_mul_eq_zero _ _ (one_sub_posSemidef X) (density_posSemidef Y)
    (by rw [sub_mul, one_mul, Matrix.trace_sub, show (matrix Y).trace = 1 from Y.2.2,
      hxy, Complex.ofReal_one, sub_self])
  have hright := zero_trace_mul_eq_zero _ _ (one_sub_posSemidef Y) (density_posSemidef X)
    (by rw [sub_mul, one_mul, Matrix.trace_sub, show (matrix X).trace = 1 from X.2.2,
      hyx, sub_self])
  have hYX : matrix Y = matrix X * matrix Y :=
    sub_eq_zero.mp (by simpa only [sub_mul, one_mul] using hleft)
  have hXY : matrix X = matrix Y * matrix X :=
    sub_eq_zero.mp (by simpa only [sub_mul, one_mul] using hright)
  have hAdj : matrix Y = matrix Y * matrix X := by
    simpa only [Matrix.conjTranspose_mul, (density_posSemidef X).isHermitian.eq,
      (density_posSemidef Y).isHermitian.eq] using congrArg Matrix.conjTranspose hYX
  exact hXY.trans hAdj.symm

/-- At a maximizer the positive reference is singular, the two overlap bounds
are saturated, and the zero-likelihood preparation is orthogonal to that reference. -/
private theorem equality_conditions {X : Fin 3 → DensityState (Fin 3)} {X₀ : DensityState (Fin 3)}
    (hEq : divergence X X₀ = C3) :
    ¬ (positiveReference X).PosDef ∧
      (matrix (X 0) * matrix (X 1)).trace.re = 1 ∧
      (matrix (X 0) * matrix (X 2)).trace.re = 0 ∧
      positiveReference X * matrix X₀ = 0 := by
  have hSing : ¬ (positiveReference X).PosDef := fun h =>
    (ne_of_lt (divergence_lt_of_posDef X X₀ h)) hEq
  obtain ⟨hBound, hLoss, hZero⟩ := singular_bound X X₀ (Or.inl hSing)
  rw [hEq] at hBound
  have hDeficit : overlapDeficit X = 0 := by
    linarith only [hBound, hLoss, overlapDeficit_nonneg X]
  have hNull : nullLoss X X₀ = 0 := by
    linarith only [hBound, hLoss, overlapDeficit_nonneg X]
  have hGap : (3 * (1 - (matrix (X 0) * matrix (X 1)).trace.re) +
      11 * (matrix (X 0) * matrix (X 2)).trace.re) / 63360 = 0 := hDeficit
  have h01 := overlap_le_one (X 0) (X 1)
  have h02 := overlap_nonneg (X 0) (X 2)
  exact ⟨hSing, by linarith only [hGap, h01, h02],
    by linarith only [hGap, h01, h02], hZero.mp hNull⟩

/-- Weights of the diagonal input and reference states in likelihood-class order. -/
abbrev p : Fin 4 → ℝ := ![88 / 141, 25 / 141, 28 / 141, 0]
abbrev q : Fin 4 → ℝ := ![66 / 141, 15 / 141, 12 / 141, 48 / 141]

private theorem p_nonneg (i : Fin 4) : 0 ≤ p i := by
  fin_cases i <;> norm_num [p]

private theorem q_pos (i : Fin 4) : 0 < q i := by
  fin_cases i <;> norm_num [q]

private theorem p_sum : ∑ i, p i = 1 := by
  norm_num [p, Fin.sum_univ_succ, Fin.sum_univ_zero]

private theorem q_sum : ∑ i, q i = 1 := by
  norm_num [q, Fin.sum_univ_succ, Fin.sum_univ_zero]

def diagonalInput : DensityState (Fin 4) :=
  diagonalState p p_nonneg p_sum

def diagonalReference : DensityState (Fin 4) :=
  diagonalState q (fun i => (q_pos i).le) q_sum

private theorem diagonal_decomposition (r : Fin 4 → ℝ) :
    CStarMatrix.ofMatrix (Matrix.diagonal fun i => (r i : ℂ)) =
      ∑ i, (r i : ℂ) • (basisState i).1 := by
  apply CStarMatrix.ofMatrixL.symm.injective
  change Matrix.diagonal (fun i => (r i : ℂ)) =
    CStarMatrix.ofMatrixL.symm (∑ i, (r i : ℂ) • (basisState i).1)
  rw [map_sum, ← Matrix.sum_single_eq_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change Matrix.single i i (r i : ℂ) = (r i : ℂ) • matrix (basisState i)
  rw [show matrix (basisState i) = Matrix.single i i 1 from basisState_matrix i,
    Matrix.smul_single, smul_eq_mul, mul_one]

private theorem map_diagonal (Φ : QuantumChannel (Fin 4) (Fin 3)) (r : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hr₁ : ∑ i, r i = 1) :
    matrix (Φ.mapState (diagonalState r hr hr₁)) =
      ∑ i, r i • matrix (Φ.mapState (basisState i)) := by
  let L := CStarMatrix.ofMatrixL.symm.toLinearMap.comp Φ.toCompletelyPositiveMap.toLinearMap
  change L (CStarMatrix.ofMatrix (Matrix.diagonal fun i => (r i : ℂ))) =
    ∑ i, r i • L (basisState i).1
  rw [diagonal_decomposition, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (L.restrictScalars ℝ).map_smul (r i) (basisState i).1

private theorem preparation_diagonal (X : Fin 4 → DensityState (Fin 3)) :
    ∃ Φ : QuantumChannel (Fin 4) (Fin 3),
      matrix (Φ.mapState diagonalInput) = ∑ i, p i • matrix (X i) ∧
      matrix (Φ.mapState diagonalReference) = ∑ i, q i • matrix (X i) := by
  obtain ⟨Φ, hΦ⟩ := finite_preparation_quantum_channel X
  refine ⟨Φ, ?_, ?_⟩
  · change CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix
      (Matrix.diagonal fun i => (p i : ℂ)))) = _
    simpa only [Matrix.diagonal_apply_eq, Complex.coe_smul] using
      hΦ (Matrix.diagonal fun i => (p i : ℂ))
  · change CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix
      (Matrix.diagonal fun i => (q i : ℂ)))) = _
    simpa only [Matrix.diagonal_apply_eq, Complex.coe_smul] using
      hΦ (Matrix.diagonal fun i => (q i : ℂ))

abbrev positiveClasses (W : Fin 4 → DensityState (Fin 3)) :
    Fin 3 → DensityState (Fin 3) := ![W 0, W 1, W 2]

private theorem sum_p (W : Fin 4 → DensityState (Fin 3)) :
    (∑ i, p i • matrix (W i)) = inputOutput (positiveClasses W) := by
  simp only [p, inputOutput, positiveClasses, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, zero_smul, add_zero, ← add_assoc,
    first_weight, second_weight, third_weight]
  rfl

private theorem sum_q (W : Fin 4 → DensityState (Fin 3)) :
    (∑ i, q i • matrix (W i)) = referenceOutput (positiveClasses W) (W 3) := by
  simp only [q, referenceOutput, positiveReference, positiveClasses, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, ← add_assoc]
  rfl

/-- Every preparation tuple is realized by a CPTP channel on the diagonal pair. -/
private theorem preparations_realized (X : Fin 3 → DensityState (Fin 3))
    (X₀ : DensityState (Fin 3)) :
    ∃ Φ : QuantumChannel (Fin 4) (Fin 3),
      matrix (Φ.mapState diagonalInput) = inputOutput X ∧
      matrix (Φ.mapState diagonalReference) = referenceOutput X X₀ := by
  let W : Fin 4 → DensityState (Fin 3) := ![X 0, X 1, X 2, X₀]
  have hX : positiveClasses W = X := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨Φ, hp, hq⟩ := preparation_diagonal W
  have hW : W 3 = X₀ := rfl
  exact ⟨Φ, by simpa only [sum_p, hX] using hp, by simpa only [sum_q, hX, hW] using hq⟩

private theorem channel_score (Φ : QuantumChannel (Fin 4) (Fin 3)) :
    extendedQuantumRelativeEntropy (Φ.mapState diagonalInput) (Φ.mapState diagonalReference) =
      (finiteTraceLogRelativeEntropy (Φ.mapState diagonalInput)
        (Φ.mapState diagonalReference) : WithTop ℝ) := by
  let W (i : Fin 4) := Φ.mapState (basisState i)
  have hp := map_diagonal Φ p p_nonneg p_sum
  have hq := map_diagonal Φ q (fun i => (q_pos i).le) q_sum
  have hdom (i : Fin 4) : p i ≤ (7 / 3 : ℝ) * q i := by
    fin_cases i <;> norm_num [p, q]
  have hle : matrix (Φ.mapState diagonalInput) ≤ (7 / 3 : ℝ) •
      matrix (Φ.mapState diagonalReference) := by
    rw [show matrix (Φ.mapState diagonalInput) = ∑ i, p i • matrix (W i) from hp,
      show matrix (Φ.mapState diagonalReference) = ∑ i, q i • matrix (W i) from hq,
      Finset.smul_sum]
    simp only [smul_smul]
    exact Finset.sum_le_sum fun i _ =>
      smul_le_smul_of_nonneg_right (hdom i) (density_posSemidef (W i)).nonneg
  apply extendedQuantumRelativeEntropy_eq_coe_of_support
  intro v hv
  change matrix (Φ.mapState diagonalReference) *ᵥ v = 0 at hv
  exact supported_of_le (density_posSemidef _) hle v (by rw [Matrix.smul_mulVec, hv, smul_zero])

/-- Measuring the diagonal input in its basis and preparing the optimal rays
gives a CPTP encoder whose commuting outputs attain the benchmark. -/
private theorem commuting_channel_attainment :
    ∃ Φ : QuantumChannel (Fin 4) (Fin 3),
      Commute (matrix (Φ.mapState diagonalInput)) (matrix (Φ.mapState diagonalReference)) ∧
        extendedQuantumRelativeEntropy (Φ.mapState diagonalInput) (Φ.mapState diagonalReference) =
          (C3 : WithTop ℝ) := by
  obtain ⟨P, Q, R, _, _, _, _, _, hComm, _, hValue⟩ := commuting_attainment
  obtain ⟨Φ, hp, hq⟩ := preparations_realized ![P, P, Q] R
  refine ⟨Φ, ?_, ?_⟩
  · rw [hp, hq]
    exact hComm
  · rw [channel_score]
    apply congrArg (fun r : ℝ => (r : WithTop ℝ))
    change traceLog (matrix (Φ.mapState diagonalInput)) (matrix (Φ.mapState diagonalReference)) = C3
    rw [hp, hq]
    exact hValue

/-- The same benchmark is the exact maximum over all CPTP qutrit encoders of
the four-class diagonal input pair. -/
theorem isGreatest_channel :
    IsGreatest (Set.range (fun Φ : QuantumChannel (Fin 4) (Fin 3) =>
      extendedQuantumRelativeEntropy (Φ.mapState diagonalInput) (Φ.mapState diagonalReference)))
      (C3 : WithTop ℝ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, _, hValue⟩ := commuting_channel_attainment
    exact ⟨Φ, hValue⟩
  · rintro _ ⟨Φ, rfl⟩
    let W (i : Fin 4) := Φ.mapState (basisState i)
    have hp : matrix (Φ.mapState diagonalInput) = inputOutput (positiveClasses W) := by
      simpa only [sum_p, diagonalInput, W] using map_diagonal Φ p p_nonneg p_sum
    have hq : matrix (Φ.mapState diagonalReference) =
        referenceOutput (positiveClasses W) (W 3) := by
      simpa only [sum_q, diagonalReference, W] using map_diagonal Φ q (fun i => (q_pos i).le) q_sum
    change extendedQuantumRelativeEntropy (Φ.mapState diagonalInput)
      (Φ.mapState diagonalReference) ≤ (C3 : WithTop ℝ)
    rw [channel_score, WithTop.coe_le_coe]
    change traceLog (matrix (Φ.mapState diagonalInput)) (matrix (Φ.mapState diagonalReference)) ≤ C3
    rw [hp, hq]
    exact divergence_le (positiveClasses W) (W 3)

/-- Every optimal channel merges the first two positive-likelihood preparations.
The merged preparation, the third positive class and the null class have
pairwise orthogonal supports. The positive-class reference is singular. -/
theorem channel_equality_conditions (Φ : QuantumChannel (Fin 4) (Fin 3))
    (hEq : extendedQuantumRelativeEntropy (Φ.mapState diagonalInput)
      (Φ.mapState diagonalReference) = (C3 : WithTop ℝ)) :
    let W (i : Fin 4) := Φ.mapState (basisState i)
    ¬ (positiveReference (positiveClasses W)).PosDef ∧
      matrix (W 0) = matrix (W 1) ∧
      matrix (W 0) * matrix (W 2) = 0 ∧
      matrix (W 0) * matrix (W 3) = 0 ∧
      matrix (W 2) * matrix (W 3) = 0 := by
  let W (i : Fin 4) := Φ.mapState (basisState i)
  let X := positiveClasses W
  have hp : matrix (Φ.mapState diagonalInput) = inputOutput X := by
    simpa only [sum_p, diagonalInput, W, X] using map_diagonal Φ p p_nonneg p_sum
  have hq : matrix (Φ.mapState diagonalReference) = referenceOutput X (W 3) := by
    simpa only [sum_q, diagonalReference, W, X] using map_diagonal Φ q (fun i => (q_pos i).le) q_sum
  rw [channel_score, WithTop.coe_eq_coe] at hEq
  change traceLog (matrix (Φ.mapState diagonalInput)) (matrix (Φ.mapState diagonalReference)) =
    C3 at hEq
  rw [hp, hq] at hEq
  obtain ⟨hSing, h01, h02, hNull⟩ := equality_conditions (X := X) (X₀ := W 3) hEq
  have hAnnihilates (i : Fin 3) : matrix (X i) * matrix (W 3) = 0 := by
    have hqi : 0 < referenceWeights i := by fin_cases i <;> norm_num [referenceWeights]
    have hWeighted : referenceWeights i • matrix (X i) ≤ positiveReference X := by
      rw [← sum_referenceWeights]
      exact Finset.single_le_sum
        (fun j _ => ((density_posSemidef (X j)).smul (by
          fin_cases j <;> norm_num [referenceWeights])).nonneg) (Finset.mem_univ i)
    ext a b
    have hz := congrArg (fun M : Mat (Fin 3) => M *ᵥ Pi.single b (1 : ℂ)) hNull
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec] at hz
    have hz' := supported_of_le ((density_posSemidef (X i)).smul hqi.le)
      hWeighted (matrix (W 3) *ᵥ Pi.single b (1 : ℂ)) hz
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec] at hz'
    have hCol := (smul_eq_zero.mp hz').resolve_left hqi.ne'
    rw [Matrix.mulVec_single_one] at hCol
    exact congrFun hCol a
  have ht := trace_eq_of_re_trace_eq (density_posSemidef (W 0)).isHermitian
    (density_posSemidef (W 2)).isHermitian h02
  have hOrth := zero_trace_mul_eq_zero _ _ (density_posSemidef (W 0)) (density_posSemidef (W 2))
    (by simpa only [Complex.ofReal_zero] using ht)
  exact ⟨hSing, matrix_eq_of_overlap_one (W 0) (W 1) h01, hOrth,
    hAnnihilates 0, hAnnihilates 2⟩

#print axioms isGreatest_channel
#print axioms channel_equality_conditions

end D5.S3.Quantum.Divergence.FibonacciQutritOptimum
