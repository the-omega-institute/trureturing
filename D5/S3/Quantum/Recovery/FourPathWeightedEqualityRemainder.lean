/- GID: D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder
   mirror-E: none(waiver:weighted-equality-remainder)
   anchors: []
   utility: none
   digest: A unitary four-path matrix is quadratically close to a phased nonnegative diagonal, with the trace defect as remainder.
-/

import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.GNSMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder

abbrev Index := Fin 4

def transport (U : Matrix Index Index ℂ) (v : Index → ℂ) : Matrix Index Index ℂ :=
  U * Matrix.diagonal v

def radius (v : Index → ℂ) : ℝ := ∑ i, ‖v i‖

def traceRadius (U : Matrix Index Index ℂ) (v : Index → ℂ) : ℝ :=
  ‖Matrix.trace (transport U v)‖

def remainder (U : Matrix Index Index ℂ) (v : Index → ℂ) : ℝ :=
  radius v ^ 2 - traceRadius U v ^ 2

private lemma transport_trace (U : Matrix Index Index ℂ) (v : Index → ℂ) :
    Matrix.trace (transport U v) = ∑ i, U i i * v i := by
  simp [transport, Matrix.trace, Matrix.mul_diagonal]

private lemma unitary_entry_bound (U : Matrix Index Index ℂ)
    (hU : U ∈ Matrix.unitaryGroup Index ℂ) (i j : Index) :
    ‖U i j‖ ≤ 1 := by
  exact Matrix.entry_norm_bound_of_unitary hU i j

private lemma transport_gram (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (hU : U ∈ Matrix.unitaryGroup Index ℂ) :
    (transport U v)ᴴ * transport U v =
      Matrix.diagonal (fun i => conj (v i) * v i) := by
  have hU' : Uᴴ * U = (1 : Matrix Index Index ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp hU
  simp [transport, Matrix.conjTranspose_mul, hU', Matrix.mul_assoc,
    Matrix.diagonal_mul_diagonal]

private lemma transport_norm_sq (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (hU : U ∈ Matrix.unitaryGroup Index ℂ) :
    ‖transport U v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have h := D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace (transport U v)
  rw [transport_gram U v hU, Matrix.trace_diagonal] at h
  simpa only [Complex.normSq_eq_norm_sq, map_sum, Complex.ofReal_sum] using
    congrArg Complex.re h

private lemma diagonal_norm_sq (v : Index → ℂ) :
    ‖Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [← D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq]
  simp [D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq,
    Matrix.diagonal_apply]

private lemma matrix_inner_formula (A B : Matrix Index Index ℂ) :
    ⟪A, B⟫_ℂ = ∑ i, ∑ j, conj (A i j) * B i j := by
  rfl

private lemma transport_diagonal_inner (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (λ : ℂ) :
    (⟪transport U v,
      λ • Matrix.diagonal (fun i => (‖v i‖ : ℂ))⟫_ℂ).re =
      ∑ i, ‖v i‖ * (conj λ * (U i i * v i)).re := by
  rw [matrix_inner_formula]
  simp only [transport, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.diagonal_apply, map_sum, Complex.sum_re]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.mul_re,
    Complex.conj_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The trace defect controls the Hilbert--Schmidt distance to a phased positive diagonal. -/
theorem weighted_equality_remainder (v : Index → ℂ)
    (U : Matrix Index Index ℂ) (hU : U ∈ Matrix.unitaryGroup Index ℂ) :
    ∃ λ : ℂ, ‖λ‖ = 1 ∧
      ‖transport U v - λ • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 ≤
        2 * remainder U v := by
  let z : ℂ := Matrix.trace (transport U v)
  obtain ⟨λ, hλ, hphase⟩ := Complex.exists_norm_mul_eq_self z
  have hconjphase : conj λ * z = (‖z‖ : ℂ) := by
    rw [← hphase]
    simp only [map_mul, Complex.conj_mul, Complex.normSq_eq_norm_sq, hλ,
      one_mul]
  let a : Index → ℝ := fun i => ‖v i‖
  let r : Index → ℝ := fun i => a i - (conj λ * (U i i * v i)).re
  have hra : ∀ i, 0 ≤ r i := by
    intro i
    dsimp [r, a]
    have hentry := unitary_entry_bound U hU i i
    have hmul : ‖U i i‖ * ‖v i‖ ≤ ‖v i‖ :=
      mul_le_mul_of_nonneg_right hentry (norm_nonneg _)
    have hnorm : ‖conj λ * (U i i * v i)‖ ≤ ‖v i‖ := by
      rw [norm_mul, norm_mul, norm_conj, hλ]
      simpa only [one_mul] using hmul
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hnorm)
  have hsumr : ∑ i, r i = radius v - traceRadius U v := by
    have hzre := congrArg Complex.re hconjphase
    rw [transport_trace] at hzre
    dsimp [r, a, radius, traceRadius, z] at hzre ⊢
    simp only [Complex.re_sum] at hzre
    rw [← hzre]
    simp only [Finset.sum_sub_distrib]
    ring
  have htrace_le : traceRadius U v ≤ radius v := by
    rw [traceRadius, transport_trace]
    calc
      ‖∑ i, U i i * v i‖ ≤ ∑ i, ‖U i i * v i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖v i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (unitary_entry_bound U hU i i)
          (norm_nonneg _)
  have hradius_nonneg : 0 ≤ radius v := by
    dsimp [radius]
    exact Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hnorm_expand :
      ‖transport U v - λ • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 =
        2 * ∑ i, a i * r i := by
    rw [norm_sub_sq (𝕜 := ℂ), transport_norm_sq U v hU,
      norm_smul, hλ, one_mul, diagonal_norm_sq]
    rw [transport_diagonal_inner U v λ]
    dsimp [a, r]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring_nf
    rw [Finset.mul_sum]
    apply congrArg id
    simp_rw [mul_sub]
    ring
  have hweighted : ∑ i, a i * r i ≤ radius v * (radius v - traceRadius U v) := by
    calc
      ∑ i, a i * r i ≤ radius v * ∑ i, r i := by
        apply Finset.sum_le_sum
        intro i hi
        have hai : a i ≤ radius v := by
          dsimp [a, radius]
          exact Finset.single_le_sum (fun j hj => norm_nonneg _) (Finset.mem_univ i)
        exact mul_le_mul_of_nonneg_right hai (hra i)
      _ = radius v * (radius v - traceRadius U v) := by rw [hsumr]
  have hfinal :
      2 * (radius v * (radius v - traceRadius U v)) ≤
        2 * remainder U v := by
    dsimp [remainder]
    have hnonneg : 0 ≤ radius v + traceRadius U v := by
      positivity
    have hfactor : radius v * (radius v - traceRadius U v) ≤
        (radius v + traceRadius U v) * (radius v - traceRadius U v) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · linarith
    nlinarith [hfactor]
  refine ⟨λ, hλ, ?_⟩
  rw [hnorm_expand]
  calc
    2 * ∑ i, a i * r i ≤ 2 * (radius v * (radius v - traceRadius U v)) := by
      exact mul_le_mul_of_nonneg_left hweighted (by norm_num)
    _ ≤ 2 * remainder U v := hfinal

end D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
