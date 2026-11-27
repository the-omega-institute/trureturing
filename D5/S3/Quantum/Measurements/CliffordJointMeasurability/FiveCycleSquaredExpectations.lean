/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/FiveCycleSquaredExpectations
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/FiveCycleSquaredExpectations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the sum of squared expectations of five cycle observables by two. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
import Mathlib.Analysis.Matrix.Order

compile_only_with_mathlib

/-!
For five Hermitian involutions with the commutation signs of a cycle, the
products of the nonadjacent pairs form a pairwise anticommuting family.
This gives a bound on real expectations for the coherence operators in
Wu, arXiv:2610.33686v1, (3.54).
-/

namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.FiveCycleSquaredExpectations

open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
  (Realization signed_product majorana_quadratic_symmetrization)
open scoped BigOperators ComplexOrder Matrix

noncomputable section

set_option autoImplicit false

private abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

variable {d : ℕ} {A : Fin 5 → Mat d}

private def chord (A : Fin 5 → Mat d) (i : Fin 5) : Mat d := A i * A (i + 2)

private theorem chord_commute (hA : Realization (SimpleGraph.cycleGraph 5) A) (i : Fin 5) :
    A i * A (i + 2) = A (i + 2) * A i := by
  have h : ∀ j : Fin 5, j ≠ j + 2 ∧ ¬ (SimpleGraph.cycleGraph 5).Adj j (j + 2) := by
    decide
  exact hA.nonadjacent i (i + 2) (h i).1 (h i).2

private theorem chord_hermitian (hA : Realization (SimpleGraph.cycleGraph 5) A) (i : Fin 5) :
    (chord A i).IsHermitian := by
  change (A i * A (i + 2))ᴴ = A i * A (i + 2)
  rw [Matrix.conjTranspose_mul, (hA.hermitian (i + 2)).eq, (hA.hermitian i).eq]
  exact (chord_commute hA i).symm

private theorem chord_square (hA : Realization (SimpleGraph.cycleGraph 5) A) (i : Fin 5) :
    chord A i * chord A i = 1 := by
  unfold chord
  calc
    _ = A i * (A (i + 2) * A i) * A (i + 2) := by noncomm_ring
    _ = (A i * A i) * (A (i + 2) * A (i + 2)) := by
      rw [← chord_commute hA i]
      noncomm_ring
    _ = 1 := by simp only [hA.square, one_mul]

private def cycleSign (i j : Fin 5) : ℤ :=
  if (SimpleGraph.cycleGraph 5).Adj i j then -1 else 1

private theorem chord_anticommute (hA : Realization (SimpleGraph.cycleGraph 5) A)
    (i j : Fin 5) (hij : i ≠ j) :
    chord A i * chord A j = -(chord A j * chord A i) := by
  have hswap (k l : Fin 5) : A k * A l = (cycleSign k l : ℂ) • (A l * A k) := by
    by_cases hadj : (SimpleGraph.cycleGraph 5).Adj k l
    · simpa [cycleSign, hadj] using hA.adjacent k l hadj.ne hadj
    · rcases eq_or_ne k l with rfl | hne
      · simp [cycleSign, hadj]
      · simpa [cycleSign, hadj] using hA.nonadjacent k l hne hadj
  let sign (k l : Fin 5) := cycleSign k l * cycleSign (k + 2) l
  have hmove (k l : Fin 5) :
      chord A k * A l = (sign k l : ℂ) • (A l * chord A k) := by
    simpa only [chord, sign, Int.cast_mul] using
      signed_product (A k) (A (k + 2)) (A l) (cycleSign k l) (cycleSign (k + 2) l)
        (hswap k l) (hswap (k + 2) l)
  -- The four swaps between the two chords have odd sign parity.
  have hparity : ∀ k l : Fin 5, k ≠ l →
      (cycleSign k l * cycleSign (k + 2) l) *
        (cycleSign k (l + 2) * cycleSign (k + 2) (l + 2)) = -1 := by decide
  have hsign : sign i j * sign i (j + 2) = -1 := hparity i j hij
  calc
    chord A i * chord A j = (chord A i * A j) * A (j + 2) := by
      exact (mul_assoc _ _ _).symm
    _ = (sign i j : ℂ) • (A j * (chord A i * A (j + 2))) := by
      rw [hmove i j, smul_mul_assoc, mul_assoc]
    _ = ((sign i j * sign i (j + 2) : ℤ) : ℂ) • (chord A j * chord A i) := by
      rw [hmove i (j + 2), mul_smul_comm, smul_smul, Int.cast_mul, ← mul_assoc] <;> rfl
    _ = -(chord A j * chord A i) := by rw [hsign, Int.cast_neg, Int.cast_one, neg_one_smul]

private def weightedSum (A : Fin 5 → Mat d) (t : Fin 5 → ℝ) : Mat d :=
  ∑ i, (t i : ℂ) • A i

private theorem weightedSum_hermitian (A : Fin 5 → Mat d)
    (hA : ∀ i, (A i).IsHermitian) (t : Fin 5 → ℝ) : (weightedSum A t).IsHermitian := by
  have hstar (i : Fin 5) : star (A i) = A i := (hA i).eq
  change star (weightedSum A t) = weightedSum A t
  simp only [weightedSum, star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, hstar]

-- The ten unordered pairs split into the five edges and the five chords.
private theorem expand_square (T : Fin 5 → Mat d) :
    (∑ i, T i) * (∑ i, T i) =
      (∑ i, T i * T i) +
      (∑ i, (T i * T (i + 1) + T (i + 1) * T i)) +
      (∑ i, (T i * T (i + 2) + T (i + 2) * T i)) := by
  simp only [Fin.sum_univ_five, Fin.reduceAdd]
  noncomm_ring

private theorem cycle_sum_square (hA : Realization (SimpleGraph.cycleGraph 5) A)
    (t : Fin 5 → ℝ) :
    weightedSum A t * weightedSum A t =
      ((∑ i, t i ^ 2 : ℝ) : ℂ) • (1 : Mat d) +
        (2 : ℂ) • weightedSum (chord A) (fun i => t i * t (i + 2)) := by
  let T (i : Fin 5) : Mat d := (t i : ℂ) • A i
  have hdiag (i : Fin 5) : T i * T i = ((t i ^ 2 : ℝ) : ℂ) • (1 : Mat d) := by
    simp only [T, smul_mul_smul, hA.square, pow_two, Complex.ofReal_mul]
  have hadj : ∀ i : Fin 5, (SimpleGraph.cycleGraph 5).Adj i (i + 1) := by decide
  have hedge (i : Fin 5) : T i * T (i + 1) + T (i + 1) * T i = 0 := by
    simp only [T, smul_mul_smul]
    rw [mul_comm (t (i + 1) : ℂ) (t i : ℂ), ← smul_add,
      hA.adjacent i (i + 1) (hadj i).ne (hadj i), neg_add_cancel, smul_zero]
  have hchord (i : Fin 5) : T i * T (i + 2) + T (i + 2) * T i =
      (2 : ℂ) • (((t i * t (i + 2) : ℝ) : ℂ) • chord A i) := by
    simp only [T, smul_mul_smul, chord, Complex.ofReal_mul]
    rw [← chord_commute hA i, mul_comm (t (i + 2) : ℂ) (t i : ℂ), two_smul]
  change (∑ i, T i) * (∑ i, T i) = _
  rw [expand_square T]
  simp only [hdiag, hedge, hchord, Finset.sum_const_zero, add_zero, ← Finset.sum_smul,
    ← Complex.ofReal_sum, ← Finset.smul_sum, weightedSum]

private theorem chord_sum_square (hA : Realization (SimpleGraph.cycleGraph 5) A)
    (w : Fin 5 → ℝ) :
    weightedSum (chord A) w * weightedSum (chord A) w =
      ((∑ i, w i ^ 2 : ℝ) : ℂ) • (1 : Mat d) := by
  have hdiff (i j : Fin 5) : ((w i * w j : ℝ) : ℂ) - ((w j * w i : ℝ) : ℂ) = 0 := by
    rw [mul_comm (w j) (w i), sub_self]
  have h := majorana_quadratic_symmetrization (chord A) (chord_square hA)
    (chord_anticommute hA) (fun i j => ((w i * w j : ℝ) : ℂ))
  simp only [hdiff, zero_smul, Finset.sum_const_zero, add_zero, ← pow_two,
    ← Complex.ofReal_sum] at h
  simpa only [weightedSum, Finset.sum_mul_sum, smul_mul_smul, Complex.ofReal_mul] using h

private theorem chord_weight_bound (x : Fin 5 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, x i * x (i + 2)) ≤ ((∑ i, x i) / 2) ^ 2 := by
  simp only [Fin.sum_univ_five, Fin.reduceAdd]
  -- Transfer the combined weight of vertices 0 and 1 to the vertex with the
  -- greater sum of chord-neighbor weights. The remaining chords are bipartite.
  rcases le_total (x 4) (x 2) with h | h
  · have hgap := add_nonneg (mul_nonneg (hx 1) (sub_nonneg.mpr h))
      (mul_nonneg (hx 4) (hx 3))
    nlinarith only [hgap, sq_nonneg (x 0 + x 1 + x 4 - (x 2 + x 3))]
  · have hgap := add_nonneg (mul_nonneg (hx 0) (sub_nonneg.mpr h))
      (mul_nonneg (hx 2) (hx 3))
    nlinarith only [hgap, sq_nonneg (x 0 + x 1 + x 2 - (x 3 + x 4))]

private theorem trace_expectation_sq_le (ρ H : Mat d) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (hH : H.IsHermitian) :
    (ρ * H).trace.re ^ 2 ≤ (ρ * (H * H)).trace.re := by
  letI := ρ.toMatrixSeminormedAddCommGroup hρ
  letI := ρ.toMatrixInnerProductSpace hρ
  have hinner (U V : Mat d) : inner ℂ U V = (V * ρ * Uᴴ).trace := rfl
  have hone : inner ℂ (1 : Mat d) 1 = 1 := by
    simpa only [hinner, Matrix.conjTranspose_one, one_mul, mul_one] using htrace
  have hmean : inner ℂ (1 : Mat d) H = (ρ * H).trace := by
    rw [hinner, Matrix.conjTranspose_one, mul_one, Matrix.trace_mul_comm H ρ]
  have hsecond : inner ℂ H H = (ρ * (H * H)).trace := by
    rw [hinner, hH.eq, Matrix.trace_mul_cycle H ρ H, Matrix.trace_mul_comm (H * H) ρ]
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (1 : Mat d) H) 2
  rw [hmean, mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ) (1 : Mat d), norm_sq_eq_re_inner (𝕜 := ℂ) H,
    hone, Complex.one_re, one_mul, hsecond] at hc
  have hre := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (ρ * H).trace) 2
  rw [sq_abs] at hre
  exact hre.trans hc

/-- For a five-cycle realization, the squared real expectations in any positive
trace-one state sum to at most two. -/
theorem sum_squared_expectations_le_two
    (A : Fin 5 → Matrix (Fin d) (Fin d) ℂ)
    (hA : Realization (SimpleGraph.cycleGraph 5) A)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (∑ i, (ρ * A i).trace.re ^ 2) ≤ 2 := by
  let t (i : Fin 5) : ℝ := (ρ * A i).trace.re
  let S : ℝ := ∑ i, t i ^ 2
  let X := weightedSum A t
  let w (i : Fin 5) := t i * t (i + 2)
  let Y := weightedSum (chord A) w
  have hX : X * X = (S : ℂ) • (1 : Mat d) + (2 : ℂ) • Y :=
    cycle_sum_square hA t
  have hY : Y * Y = ((∑ i, w i ^ 2 : ℝ) : ℂ) • (1 : Mat d) :=
    chord_sum_square hA w
  have hQ : (∑ i, w i ^ 2) ≤ (S / 2) ^ 2 := by
    simpa only [w, S, mul_pow] using
      chord_weight_bound (fun i => t i ^ 2) (fun i => sq_nonneg (t i))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg (t i)
  have hYexp := trace_expectation_sq_le ρ Y hρ htrace
    (weightedSum_hermitian (chord A) (chord_hermitian hA) w)
  have hYbound : (ρ * Y).trace.re ≤ S / 2 := by
    rw [hY] at hYexp
    simp only [Matrix.mul_smul, mul_one, Matrix.trace_smul, htrace, smul_eq_mul,
      Complex.ofReal_re] at hYexp
    exact le_of_sq_le_sq (hYexp.trans hQ) (div_nonneg hS (by norm_num))
  have hXexp := trace_expectation_sq_le ρ X hρ htrace (weightedSum_hermitian A hA.hermitian t)
  have hXvalue : (ρ * X).trace.re = S := by
    simp only [X, weightedSum, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul, S, pow_two, t]
  have hXsecond : (ρ * (X * X)).trace.re = S + 2 * (ρ * Y).trace.re := by
    rw [hX, two_smul]
    simp [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      htrace, smul_eq_mul, two_mul]
  rw [hXvalue, hXsecond] at hXexp
  change S ≤ 2
  by_contra! hgt
  have hpos : 0 < S := (by norm_num : (0 : ℝ) < 2).trans hgt
  nlinarith only [hXexp, hYbound, mul_pos hpos (sub_pos.mpr hgt)]

#print axioms sum_squared_expectations_le_two

end

end D5.S3.Quantum.Measurements.CliffordJointMeasurability.FiveCycleSquaredExpectations
