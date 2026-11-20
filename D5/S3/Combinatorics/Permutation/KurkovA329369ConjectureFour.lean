/- GID: D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal A358612 array gives the signed factorial-power formula for A329369. -/

import D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
import D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm

/-! The Pochhammer expansion and signed factorial-power evaluation for A329369. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour

open Polynomial
open scoped BigOperators
open D5.S1.Digit.DyadicRowPolynomialRecurrence (R wt)
open D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock (T)
open D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm (b)
open D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient

noncomputable section

private theorem row_expansion (k : ℕ) :
    rowPolynomial k = ∑ i ∈ Finset.Icc 1 (wt k + 2),
      ((-1 : ℚ) ^ (wt k + 2 - i) * T k i) • ascPochhammer ℚ i := by
  classical
  apply pochhammerBasis.ext_elem
  intro j
  change pochhammerBasis.coord j (rowPolynomial k) = pochhammerBasis.coord j _
  have hc : pochhammerBasis.coord j (rowPolynomial k) =
      (-1 : ℚ) ^ (wt k + 2 - j) * T k j := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact source_coordinate 0 j
    · exact ((positiveEvenCoefficient k 2 hk le_rfl).2 j).2
  simp only [map_sum, map_smul, coord_basis, smul_eq_mul]
  by_cases hj : j ∈ Finset.Icc 1 (wt k + 2)
  · rw [Finset.sum_eq_single_of_mem j hj]
    · simpa using hc
    · intro i _ hij
      simp [hij]
  · have hz : T k j = 0 := by
      by_cases h0 : j = 0
      · subst j
        rw [T, ite_eq_left rfl]
      · apply D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge.support
        simp only [Finset.mem_Icc, not_and_or] at hj
        omega
    rw [hc, hz, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]

private theorem dyadic_expansion (m k : ℕ) :
    rationalRow (2 ^ m * (2 * k + 1)) =
      ∑ i ∈ Finset.Icc 1 (wt k + 2),
        (((-1 : ℚ) ^ (wt k + 2 - i) * T k i) * (i : ℚ) ^ m) •
          ascPochhammer ℚ i := by
  induction m with
  | zero =>
    simpa [rationalRow_odd, rowPolynomial] using row_expansion k
  | succ m ih =>
    rw [show 2 ^ (m + 1) * (2 * k + 1) = 2 * (2 ^ m * (2 * k + 1)) by ring,
      rationalRow_even _ (by positivity), ih, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, difference_pochhammer, smul_smul, pow_succ, mul_assoc]

private theorem ascPochhammer_eval_one (i : ℕ) :
    (ascPochhammer ℚ i).eval 1 = (i.factorial : ℚ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [ascPochhammer_succ_right, eval_mul, ih, Nat.factorial_succ, Nat.cast_mul]
    simp
    ring

private theorem source_sign (w i : ℕ) (hi : i ≤ w + 2) :
    (-1 : ℚ) ^ (w + 2 - i) = (-1 : ℚ) ^ ((w : ℤ) - (i : ℤ)) := by
  have he : ((w + 2 - i : ℕ) : ℤ) = (w : ℤ) - (i : ℤ) + 2 := by omega
  rw [← zpow_natCast, he, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
  norm_num

private theorem b_factorial_sum (m k : ℕ) :
    (b (2 ^ m * (2 * k + 1)) : ℚ) =
      ∑ i ∈ Finset.Icc 1 (wt k + 2),
        (i.factorial : ℚ) * (i : ℚ) ^ m * T k i *
          (-1 : ℚ) ^ ((wt k : ℤ) - (i : ℤ)) := by
  have heval (n : ℕ) : (rationalRow n).eval 1 = (b n : ℚ) := by
    simp [rationalRow, b]
  rw [← heval, dyadic_expansion, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_smul, ascPochhammer_eval_one, source_sign _ _ (Finset.mem_Icc.mp hi).2]
  simp only [smul_eq_mul]
  ring

end
end D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
