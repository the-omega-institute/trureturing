/- GID: D5/S3/Quantum/Matrix/TaylorMajorization/Pauli
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/TaylorMajorization/Pauli
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Pauli trace defects and strictly negative scalar shifts at every odd order above three. -/

import D5.S3.Quantum.Matrix.TaylorMajorization.Shift
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

noncomputable section
open Matrix BigOperators Finset
open D5.S3.Quantum.Matrix.TaylorMajorization.Defs
open D5.S3.Quantum.Matrix.TaylorMajorization.Shift
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Quantum.Matrix.TaylorMajorization.Pauli

open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

private theorem trace_moment (p q : ℕ) :
    (qubitZ ^ p * qubitX ^ q).trace =
      (1 + (-1 : ℂ) ^ p) * (1 + (-1 : ℂ) ^ q) / 2 := by
  rw [pow_eq_pow_mod p qubit_weyl_star.2.2.2.2,
    pow_eq_pow_mod q qubit_weyl_star.2.2.2.1,
    pow_eq_pow_mod p (show (-1 : ℂ) ^ 2 = 1 by norm_num),
    pow_eq_pow_mod q (show (-1 : ℂ) ^ 2 = 1 by norm_num)]
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;>
    rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · convert pauli_trace_pair .I .I using 1 <;> norm_num [hp, hq, pauliMatrix]
  · convert pauli_trace_pair .I .X using 1 <;> norm_num [hp, hq, pauliMatrix]
  · convert pauli_trace_pair .Z .I using 1 <;> norm_num [hp, hq, pauliMatrix]
  · convert pauli_trace_pair .Z .X using 1 <;> norm_num [hp, hq, pauliMatrix]

private theorem traceQ_closed (k : ℕ) :
    (taylorQ qubitZ qubitX k).trace =
      ((2 : ℂ) ^ k + (-2 : ℂ) ^ k) / 2 + (0 : ℂ) ^ k := by
  have hs (a b : ℂ) :
      (∑ p ∈ range (k + 1), (k.choose p : ℂ) * a ^ p * b ^ (k-p)) =
        (a + b) ^ k := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using (add_pow a b k).symm
  calc
    _ = (1 / 2 : ℂ) *
      ((∑ p ∈ range (k + 1), (k.choose p : ℂ) * 1 ^ p * 1 ^ (k-p)) +
       (∑ p ∈ range (k + 1), (k.choose p : ℂ) * (-1) ^ p * 1 ^ (k-p)) +
       (∑ p ∈ range (k + 1), (k.choose p : ℂ) * 1 ^ p * (-1) ^ (k-p)) +
       (∑ p ∈ range (k + 1), (k.choose p : ℂ) * (-1) ^ p * (-1) ^ (k-p))) := by
        delta taylorQ
        simp only [trace_sum, trace_smul, trace_moment, smul_eq_mul,
          mul_add, mul_sum]
        rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
        apply sum_congr rfl
        intro p hp
        ring
    _ = _ := by rw [hs, hs, hs, hs]; norm_num; ring

private theorem sum_square : (qubitZ + qubitX) ^ 2 = (2 : ℂ) • 1 := by
  have hz := qubit_weyl_star.2.2.2.2
  have hx := qubit_weyl_star.2.2.2.1
  have ha := qubit_weyl_star.1
  simp only [pow_two] at hz hx ⊢
  rw [add_mul, mul_add, mul_add, hz, hx, ha]
  module

private theorem traceH_even (m : ℕ) :
    (((qubitZ + qubitX) ^ (2 * m)).trace).re = (2 : ℝ) ^ (m + 1) := by
  rw [pow_mul, sum_square, smul_pow, one_pow, trace_smul]
  simp [Matrix.trace, Complex.mul_re, pow_succ]
  norm_cast

/-- At positive even orders the Pauli defect is the difference of two geometric powers. -/
theorem defect_even (m : ℕ) (hm : 1 ≤ m) :
    defect qubitZ qubitX (2 * m) = (4 : ℝ) ^ m - 2 ^ (m + 1) := by
  rw [defect, trace_taylorR, traceQ_closed, traceH_even,
    (even_two_mul m).neg_pow]
  have hz : 2 * m ≠ 0 := by omega
  rw [zero_pow hz, add_zero, add_self_div_two]
  norm_cast
  rw [pow_mul]
  norm_num

/-- At every odd order the unshifted Pauli defect vanishes. -/
theorem defect_odd (m : ℕ) : defect qubitZ qubitX (2 * m + 1) = 0 := by
  rw [defect, trace_taylorR, traceQ_closed,
    (show Odd (2 * m + 1) from ⟨m, rfl⟩).neg_pow]
  simp only [add_neg_cancel, zero_div, zero_pow (by omega : 2*m+1 ≠ 0), add_zero,
    Complex.zero_re, zero_sub, neg_eq_zero]
  rw [pow_succ, pow_mul, sum_square, smul_pow, one_pow, smul_mul_assoc, one_mul,
    trace_smul, trace_add]
  have hz := trace_moment 1 0
  have hx := trace_moment 0 1
  norm_num at hz hx
  simp [hz, hx]

private theorem defect_zero : defect qubitZ qubitX 0 = 0 := by
  rw [defect, trace_taylorR]
  delta taylorQ
  simp

/-- Every positive scalar shift to the left makes every odd Pauli defect above three negative. -/
theorem defect_shift_negative (k : ℕ) (hk : Odd k) (hk5 : 5 ≤ k)
    (t : ℝ) (ht : 0 < t) :
    defect (qubitZ - (t : ℂ) • 1) qubitX k < 0 := by
  rw [sub_eq_add_neg, ← neg_smul, ← Complex.ofReal_neg, defect_shift]
  have hn (j : ℕ) (hj : j ∈ range (k+1)) :
      (k.choose j : ℝ) * (-t) ^ (k-j) * defect qubitZ qubitX j ≤ 0 := by
    rcases Nat.even_or_odd j with he | ho
    · obtain ⟨m, hm⟩ := he
      have hjm : j = 2 * m := by omega
      by_cases hm0 : m = 0
      · subst m
        simp [hjm, defect_zero]
      · rw [hjm, defect_even m (by omega)]
        have hd : 0 ≤ (4 : ℝ)^m - 2^(m+1) := by
          have hmp : m = 1 + (m-1) := by omega
          rw [hmp, pow_add, pow_add, pow_add]
          have hh : (2 : ℝ) ^ (m-1) ≤ 4 ^ (m-1) := by gcongr; norm_num
          norm_num at *
          nlinarith
        have ho : Odd (k - 2*m) := Nat.Odd.sub_even
          (by have := mem_range.mp hj; omega) hk (even_two_mul m)
        rw [ho.neg_pow]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonpos.mpr (pow_nonneg ht.le _))) hd
    · obtain ⟨m, hm⟩ := ho
      have hjm : j = 2 * m + 1 := by omega
      rw [hjm, defect_odd]
      simp
  have hs : (∑ j ∈ range (k+1),
      (k.choose j : ℝ) * (-t) ^ (k-j) * defect qubitZ qubitX j) <
      ∑ _j ∈ range (k+1), (0 : ℝ) := by
    apply sum_lt_sum hn
    refine ⟨4, by simp; omega, ?_⟩
    rw [show 4 = 2*2 from rfl, defect_even 2 (by omega)]
    have ho : Odd (k-4) := Nat.Odd.sub_even (by omega) hk (by decide)
    rw [show 2*2 = 4 from rfl, ho.neg_pow]
    have hc : (0 : ℝ) < k.choose 4 := by exact_mod_cast Nat.choose_pos (by omega : 4 ≤ k)
    have hp : 0 < t ^ (k-4) := pow_pos ht _
    norm_num
    nlinarith [mul_pos hc hp]
  simpa using hs

end D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
