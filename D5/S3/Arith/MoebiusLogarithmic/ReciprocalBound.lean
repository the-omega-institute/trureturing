/- GID: D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound
   generality: G
   mirror-B: D5/B/S3/Arith/MoebiusLogarithmic/ReciprocalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: Every real prefix of the reciprocal Moebius sum has absolute value at most one. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction.zeta
open Finset

noncomputable section
namespace D5.S3.Arith.MoebiusLogarithmic

/-- The reciprocal sum with the exact real cutoff. -/
def reciprocalSum (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n

theorem floor_cancellation {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊,
      (ArithmeticFunction.moebius n : ℝ) * (⌊x / n⌋₊ : ℝ)) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) ⌊x⌋₊
  simp only [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  have hsum : (∑ n ∈ Ioc 0 ⌊x⌋₊, (1 : ArithmeticFunction ℝ) n) = 1 := by
    rw [sum_eq_single 1]
    · simp
    · intro n hn hn1
      simp [hn1]
    · intro hnot
      exact (hnot (mem_Ioc.mpr ⟨by omega, Nat.le_floor (by simpa using hx)⟩)).elim
  rw [hsum] at h
  simpa only [ArithmeticFunction.intCoe_apply, ← Nat.floor_div_natCast] using h.symm

/-- Separating the first fractional part gives a bound uniform in the real cutoff. -/
theorem abs_reciprocalSum_le_one (x : ℝ) : |reciprocalSum x| ≤ 1 := by
  by_cases hx : x < 1
  · simp [reciprocalSum, Nat.floor_eq_zero.mpr hx]
  have hx1 : 1 ≤ x := le_of_not_gt hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  let s := Ioc 0 ⌊x⌋₊
  let r : ℕ → ℝ := fun n => x / n - ⌊x / n⌋₊
  have h1 : 1 ∈ s := mem_Ioc.mpr ⟨by omega, Nat.le_floor (by simpa using hx1)⟩
  have hr (n : ℕ) : 0 ≤ r n := by
    exact sub_nonneg.mpr (Nat.floor_le (div_nonneg hx0.le (Nat.cast_nonneg n)))
  have hr1 (n : ℕ) : r n ≤ 1 := by
    dsimp [r]
    linarith [Nat.lt_floor_add_one (x / n)]
  have hmu (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hid : x * reciprocalSum x = 1 + ∑ n ∈ s,
      (ArithmeticFunction.moebius n : ℝ) * r n := by
    have hc := floor_cancellation hx1
    change (∑ n ∈ s, (ArithmeticFunction.moebius n : ℝ) * (⌊x / n⌋₊ : ℝ)) = 1 at hc
    rw [← hc, ← sum_add_distrib]
    simp only [reciprocalSum, mul_sum]
    apply sum_congr rfl
    intro n hn
    dsimp [r]
    ring
  have habs : |x * reciprocalSum x| ≤ x := by
    rw [hid]
    calc
      _ ≤ 1 + ∑ n ∈ s, |(ArithmeticFunction.moebius n : ℝ)| * r n := by
        calc
          _ ≤ |(1 : ℝ)| + |∑ n ∈ s, (ArithmeticFunction.moebius n : ℝ) * r n| := abs_add_le _ _
          _ ≤ _ := by
            simp only [abs_one]
            gcongr
            convert abs_sum_le_sum_abs (fun n => (ArithmeticFunction.moebius n : ℝ) * r n) s using 1
            apply sum_congr rfl
            intro n hn
            rw [abs_mul, abs_of_nonneg (hr n)]
      _ ≤ x := by
        rw [← sum_erase_add _ _ h1]
        have ht : (∑ n ∈ s.erase 1, |(ArithmeticFunction.moebius n : ℝ)| * r n) ≤
            (s.erase 1).card := by
          calc
            _ ≤ ∑ n ∈ s.erase 1, (1 : ℝ) := sum_le_sum fun n hn =>
              (mul_le_mul_of_nonneg_right (hmu n) (hr n)).trans (by simpa using hr1 n)
            _ = _ := by simp
        have hc : ((s.erase 1).card : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
          have hcard := card_erase_of_mem h1
          have hs : s.card = ⌊x⌋₊ := by simp [s]
          rw [hs] at hcard
          have hc := congrArg (fun k : ℕ => (k : ℝ)) hcard
          have hk : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx1)
          simpa only [Nat.cast_sub hk, Nat.cast_one] using hc
        simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, abs_one, one_mul]
        simpa only [r, Nat.cast_one, div_one] using
          (show 1 + ((∑ n ∈ s.erase 1, |(ArithmeticFunction.moebius n : ℝ)| * r n) +
            (x - (⌊x⌋₊ : ℝ))) ≤ x by linarith)
  rw [abs_mul, abs_of_pos hx0] at habs
  exact (mul_le_mul_iff_right₀ hx0).mp (by simpa [mul_comm] using habs)

#print axioms abs_reciprocalSum_le_one
end D5.S3.Arith.MoebiusLogarithmic
