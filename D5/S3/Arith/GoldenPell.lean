/- GID: D5/S3/Arith/GoldenPell
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: x^2-5y^2=pm4 solutions are exactly signed Fibonacci-Lucas pairs. -/

import D5.S1.Scale.UnitGroup
import D5.S1.Scale.Lucas
import Mathlib.Data.Int.Fib.Basic

namespace D5.S3.Arith.GoldenPell

open D5.S0.Carrier
open D5.S1.Scale

/-- The golden integer represented by the integral power `phi ^ n`. -/
def goldenPhiZPow (n : ℤ) : GoldenInt :=
  ((phiUnit ^ n : GoldenIntˣ) : GoldenInt)

/-- The Lucas sequence on integer indices, realized as the trace of `phi ^ n`. -/
def goldenLucasZ (n : ℤ) : ℤ := trace (goldenPhiZPow n)

/-- Apply the sign encoded by a boolean. -/
def signedInt (negative : Bool) (z : ℤ) : ℤ :=
  if negative then -z else z

@[simp] theorem goldenPhiZPow_natCast (n : ℕ) :
    goldenPhiZPow (n : ℤ) = phi ^ n := by
  simp [goldenPhiZPow]

@[simp] theorem goldenLucasZ_natCast (n : ℕ) :
    goldenLucasZ (n : ℤ) = goldenLucas n := by
  simp [goldenLucasZ, golden_lucas_eq_trace_phi_pow]

private theorem goldenPhiZPow_neg_natCast (n : ℕ) :
    goldenPhiZPow (-(n : ℤ)) = (-1 : GoldenInt) ^ n * conj (phi ^ n) := by
  have hphi : phi - 1 = -conj phi := by
    rw [conj_phi]
    abel
  unfold goldenPhiZPow
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  change (phi - 1) ^ n = (-1 : GoldenInt) ^ n * conj (phi ^ n)
  rw [hphi, neg_pow]
  congr 1
  exact (conjEquiv.map_pow phi n).symm

/-- The second coordinate of an integral golden power is the integer-indexed
Fibonacci number. -/
theorem goldenPhiZPow_b_eq_intFib (n : ℤ) :
    (goldenPhiZPow n).b = Int.fib n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · cases k with
    | zero =>
        rw [goldenPhiZPow_natCast, Int.fib_natCast]
        exact golden_phi_pow_b_eq_fib_index 0
    | succ k =>
        rw [goldenPhiZPow_natCast, Int.fib_natCast]
        simpa [Nat.succ_eq_add_one] using
          congrArg GoldenInt.b (golden_phi_pow_eq_fib_pair k)
  · rw [goldenPhiZPow_neg_natCast, Int.fib_neg_natCast]
    have hnegpow : (-1 : GoldenInt) ^ k = ((-1 : ℤ) ^ k : ℤ) := by
      norm_cast
    rw [hnegpow]
    simp only [b_mul, a_intCast, b_intCast, conj_b,
      golden_phi_pow_b_eq_fib_index, zero_mul, add_zero]
    ring

theorem trace_signedPhiPower (s : Bool) (n : ℤ) :
    trace (signedPhiPower s n) = signedInt s (goldenLucasZ n) := by
  cases s <;> simp [signedPhiPower, signedInt, goldenLucasZ, goldenPhiZPow, trace]
  all_goals ring

theorem b_signedPhiPower (s : Bool) (n : ℤ) :
    (signedPhiPower s n).b = signedInt s (Int.fib n) := by
  cases s
  · simpa [signedPhiPower, signedInt, goldenPhiZPow] using
      goldenPhiZPow_b_eq_intFib n
  · simpa [signedPhiPower, signedInt, goldenPhiZPow] using
      congrArg Neg.neg (goldenPhiZPow_b_eq_intFib n)

/-- The Pell discriminant in trace coordinates is four times the golden norm. -/
theorem pell_form_eq_four_mul_norm (g : GoldenInt) :
    (2 * g.a + g.b) ^ 2 - 5 * g.b ^ 2 = 4 * norm g := by
  rw [norm_def]
  ring

private theorem even_sub_of_pell_pm_four {x y : ℤ}
    (h : x ^ 2 - 5 * y ^ 2 = 4 ∨ x ^ 2 - 5 * y ^ 2 = -4) :
    Even (x - y) := by
  obtain ⟨a, rfl | rfl⟩ := x.even_or_odd'
  · obtain ⟨b, rfl | rfl⟩ := y.even_or_odd'
    · exact ⟨a - b, by ring⟩
    · rcases h with h | h <;> ring_nf at h <;> omega
  · obtain ⟨b, rfl | rfl⟩ := y.even_or_odd'
    · rcases h with h | h <;> ring_nf at h <;> omega
    · exact ⟨a - b, by ring⟩

/-- Every integral solution of `x^2 - 5*y^2 = ±4` is, and only is, a
simultaneously signed integer-indexed Lucas-Fibonacci pair. -/
theorem pell_pm_four_iff_signed_lucas_fib (x y : ℤ) :
    (x ^ 2 - 5 * y ^ 2 = 4 ∨ x ^ 2 - 5 * y ^ 2 = -4) ↔
      ∃ (s : Bool) (n : ℤ),
        x = signedInt s (goldenLucasZ n) ∧ y = signedInt s (Int.fib n) := by
  constructor
  · intro hpell
    rcases even_sub_of_pell_pm_four hpell with ⟨a, ha⟩
    let g : GoldenInt := ⟨a, y⟩
    have htrace : trace g = x := by
      simp [g, trace]
      omega
    have hnorm : norm g = 1 ∨ norm g = -1 := by
      have hbridge := pell_form_eq_four_mul_norm g
      change trace g ^ 2 - 5 * g.b ^ 2 = 4 * norm g at hbridge
      rw [htrace] at hbridge
      change x ^ 2 - 5 * y ^ 2 = 4 * norm g at hbridge
      rcases hpell with hpell | hpell
      · left
        omega
      · right
        omega
    have hunit : IsUnit g :=
      (isUnit_iff_norm_eq_one_or_neg_one g).2 hnorm
    rcases (golden_units_eq_signed_phi_pow g).1 hunit with ⟨s, n, hg⟩
    refine ⟨s, n, ?_, ?_⟩
    · rw [← trace_signedPhiPower s n, ← hg]
      exact htrace.symm
    · rw [← b_signedPhiPower s n, ← hg]
  · rintro ⟨s, n, rfl, rfl⟩
    have hunit := signedPhiPower_isUnit s n
    have hnorm := (isUnit_iff_norm_eq_one_or_neg_one (signedPhiPower s n)).1 hunit
    have hbridge := pell_form_eq_four_mul_norm (signedPhiPower s n)
    change trace (signedPhiPower s n) ^ 2 - 5 * (signedPhiPower s n).b ^ 2 =
      4 * norm (signedPhiPower s n) at hbridge
    rw [trace_signedPhiPower, b_signedPhiPower] at hbridge
    rcases hnorm with hnorm | hnorm
    · left
      rw [hnorm] at hbridge
      norm_num at hbridge ⊢
      exact hbridge
    · right
      rw [hnorm] at hbridge
      norm_num at hbridge ⊢
      exact hbridge

end D5.S3.Arith.GoldenPell
