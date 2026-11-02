/- GID: D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder
   mirror-E: none(waiver:weighted-equality-remainder)
   anchors: []
   utility: none
   digest: A unitary four-path matrix is quadratically close to a phased nonnegative diagonal, with the trace defect as remainder. -/

import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.GNSMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix.Norms.Frobenius

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
  exact entry_norm_bound_of_unitary hU i j

private lemma transport_gram (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (hU : U ∈ Matrix.unitaryGroup Index ℂ) :
    (transport U v)ᴴ * transport U v =
      Matrix.diagonal (fun i => star (v i) * v i) := by
  have hU' : Uᴴ * U = (1 : Matrix Index Index ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp hU
  simp only [transport, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
  rw [← Matrix.mul_assoc (Matrix.diagonal (star v) * Uᴴ) U (Matrix.diagonal v),
    Matrix.mul_assoc (Matrix.diagonal (star v)) Uᴴ U, hU', Matrix.mul_one,
    Matrix.diagonal_mul_diagonal]
  rfl

private lemma transport_norm_sq (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (hU : U ∈ Matrix.unitaryGroup Index ℂ) :
    ‖transport U v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have h := D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace (transport U v)
  rw [transport_gram U v hU, Matrix.trace_diagonal] at h
  have h' := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.re_sum] at h'
  have hterm (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    simp [Complex.star_def, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  simp_rw [hterm] at h'
  exact h'

private lemma diagonal_norm_sq (v : Index → ℂ) :
    ‖Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [Matrix.frobenius_norm_diagonal]
  change ‖WithLp.toLp 2 (fun i => (‖v i‖ : ℂ))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2]

private lemma transport_phase_cross (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (phase : ℂ) :
    (∑ i, ∑ j, (transport U v i j *
      star ((phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))) i j)).re) =
      ∑ i, ‖v i‖ * (star phase * (U i i * v i)).re := by
  simp [transport, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply,
    Fin.sum_univ_succ, Complex.star_def]
  ring

private lemma distance_sq (U : Matrix Index Index ℂ) (v : Index → ℂ)
    (hU : U ∈ Matrix.unitaryGroup Index ℂ) (phase : ℂ) (hphase : ‖phase‖ = 1) :
    ‖transport U v - phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 =
      2 * ∑ i, ‖v i‖ * (‖v i‖ - (star phase * (U i i * v i)).re) := by
  rw [← D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq]
  unfold D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq
  simp only [Matrix.sub_apply]
  change (∑ i, ∑ j, ‖(transport U v) i j -
    (phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))) i j‖ ^ 2) = _
  have hnorm_sub (x y : ℂ) :
      ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * star y).re := by
    simpa only [Complex.sq_norm, Complex.star_def] using Complex.normSq_sub x y
  simp only [hnorm_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : (∑ i, ∑ j, ‖transport U v i j‖ ^ 2) = ‖transport U v‖ ^ 2 := by
    exact D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq _
  have hB :
      (∑ i, ∑ j, ‖(phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))) i j‖ ^ 2) =
        ∑ i, ‖v i‖ ^ 2 := by
    change D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq
      (phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))) = _
    rw [D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq]
    rw [norm_smul, hphase, one_mul, diagonal_norm_sq]
  have hcross2 :
      (∑ i, ∑ j, 2 * (transport U v i j *
        star ((phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))) i j)).re) =
        2 * (∑ i, ∑ j, (transport U v i j *
          star ((phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))) i j)).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hA, hB, hcross2, transport_phase_cross U v phase]
  rw [transport_norm_sq U v hU]
  rw [Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  have hsqsum :
      (∑ i : Index, 2 * (‖v i‖ * ‖v i‖)) =
        (∑ i : Index, ‖v i‖ ^ 2) + ∑ i : Index, ‖v i‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsqsum]

/-- The trace defect controls the Hilbert--Schmidt distance to a phased positive diagonal. -/
theorem weighted_equality_remainder (v : Index → ℂ)
    (U : Matrix Index Index ℂ) (hU : U ∈ Matrix.unitaryGroup Index ℂ) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧
      ‖transport U v - phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 ≤
        2 * remainder U v := by
  let z : ℂ := Matrix.trace (transport U v)
  obtain ⟨phase, hphase_norm, hphase⟩ := Complex.exists_norm_mul_eq_self z
  have hconjphase : star phase * z = (‖z‖ : ℂ) := by
    rw [← hphase]
    have hp : star phase * phase = (1 : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, hphase_norm]
      norm_num
    rw [← mul_assoc, hp, one_mul]
    simp [norm_mul, hphase_norm, Complex.norm_real, abs_of_nonneg (norm_nonneg z)]
  let a : Index → ℝ := fun i => ‖v i‖
  let r : Index → ℝ := fun i => a i - (star phase * (U i i * v i)).re
  have hra : ∀ i, 0 ≤ r i := by
    intro i
    dsimp [r, a]
    have hentry := unitary_entry_bound U hU i i
    have hmul : ‖U i i‖ * ‖v i‖ ≤ ‖v i‖ := by
      simpa using (mul_le_mul_of_nonneg_right hentry (norm_nonneg (v i)))
    have hnorm : ‖star phase * (U i i * v i)‖ ≤ ‖v i‖ := by
      rw [norm_mul, norm_mul, norm_star, hphase_norm]
      simpa only [one_mul] using hmul
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hnorm)
  have hsumr : ∑ i, r i = radius v - traceRadius U v := by
    have hzre := congrArg Complex.re hconjphase
    dsimp [z] at hzre
    rw [transport_trace] at hzre
    dsimp [r, a, radius, traceRadius] at hzre ⊢
    rw [transport_trace]
    rw [Finset.mul_sum, Complex.re_sum] at hzre
    rw [← hzre]
    simp only [Finset.sum_sub_distrib]
  have htrace_le : traceRadius U v ≤ radius v := by
    rw [traceRadius, transport_trace]
    calc
      ‖∑ i, U i i * v i‖ ≤ ∑ i, ‖U i i * v i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖v i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        simpa using (mul_le_mul_of_nonneg_right (unitary_entry_bound U hU i i)
          (norm_nonneg (v i)))
  have hradius_nonneg : 0 ≤ radius v := by
    dsimp [radius]
    exact Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hnorm_expand :
      ‖transport U v - phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 =
        2 * ∑ i, a i * r i := by
    simpa [a, r] using distance_sq U v hU phase hphase_norm
  have hweighted : ∑ i, a i * r i ≤ radius v * (radius v - traceRadius U v) := by
    calc
      ∑ i, a i * r i ≤ radius v * ∑ i, r i := by
        have hpoint : ∀ i, a i * r i ≤ radius v * r i := by
          intro i
          have hai : a i ≤ radius v := by
            dsimp [a, radius]
            exact Finset.single_le_sum (fun j hj => norm_nonneg _) (Finset.mem_univ i)
          exact mul_le_mul_of_nonneg_right hai (hra i)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (s := (Finset.univ : Finset Index))
          (fun i hi => hpoint i)
      _ = radius v * (radius v - traceRadius U v) := by rw [hsumr]
  have hfinal :
      2 * (radius v * (radius v - traceRadius U v)) ≤
        2 * remainder U v := by
    dsimp [remainder]
    have htrace_nonneg : 0 ≤ traceRadius U v := norm_nonneg _
    have hdelta_nonneg : 0 ≤ radius v - traceRadius U v :=
      sub_nonneg.mpr htrace_le
    have hfactor : radius v * (radius v - traceRadius U v) ≤
        (radius v + traceRadius U v) * (radius v - traceRadius U v) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact hdelta_nonneg
    calc
      2 * (radius v * (radius v - traceRadius U v)) ≤
          2 * ((radius v + traceRadius U v) * (radius v - traceRadius U v)) :=
        mul_le_mul_of_nonneg_left hfactor (by norm_num)
      _ = 2 * (radius v ^ 2 - traceRadius U v ^ 2) := by ring
  refine ⟨phase, hphase_norm, ?_⟩
  rw [hnorm_expand]
  calc
    2 * ∑ i, a i * r i ≤ 2 * (radius v * (radius v - traceRadius U v)) := by
      exact mul_le_mul_of_nonneg_left hweighted (by norm_num)
    _ ≤ 2 * remainder U v := hfinal

end D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
