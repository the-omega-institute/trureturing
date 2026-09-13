/- GID: D5/S1/Recurrence/FibonacciPrimePowerPeriod
   generality: G
   mirror-B: none(waiver:actual-all-prime-power-period)
   mirror-E: none(waiver:unbounded-depth-and-exponent)
   anchors: []
   digest: Every odd-prime period tower is determined by the valuation of the actual first return content; explicit dyadic and ramified towers complete the boundary cases. -/

import D5.S1.Recurrence.GoldenPrimePowerDepth
import D5.S1.Recurrence.FibonacciFrobeniusQuotientBridge

set_option autoImplicit false

namespace D5.S1.Recurrence.FibonacciPrimePowerPeriod

open D5.S0.Carrier D5.S1.Scale
open FibonacciReturnSpectrum GoldenModReturnBridge GoldenPrimePowerDepth
open FibonacciFrobeniusQuotientBridge

/-- Actual first-return depth, not a freely supplied plateau length. -/
noncomputable def initialDepth (p : ℕ) : ℕ :=
  padicValNat p (returnContent (period p))

lemma returnContent_period_ne_zero (p : ℕ) (hp : 0 < p) :
    returnContent (period p) ≠ 0 := by
  have hF : Nat.fib (period p) ≠ 0 := ne_of_gt (Nat.fib_pos.mpr (period_pos p hp))
  have hd : returnContent (period p) ∣ Nat.fib (period p) := Nat.gcd_dvd_left _ _
  intro h
  rw [h, zero_dvd_iff] at hd
  exact hF hd

theorem initialDepth_pos (p : ℕ) (hp : p.Prime) : 0 < initialDepth p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact one_le_padicValNat_of_dvd (returnContent_period_ne_zero p hp.pos)
    ((period_dvd_iff_dvd_returnContent p (period p)).mp (dvd_refl _))

/-- Scalar divisibility of the original golden power is exactly the computable return content. -/
lemma scalar_return_iff (q r : ℕ) :
    (q : GoldenInt) ∣ D5.S0.Carrier.phi ^ r - 1 ↔ q ∣ returnContent r := by
  rw [← reduce_eq_one_iff, ← period_dvd_iff_reduced_phi,
    period_dvd_iff_dvd_returnContent]

/-- Construct the primitive first defect from the actual p-adic valuation. -/
theorem actual_initial_seed (p : ℕ) (hp : p.Prime) :
    ∃ B : GoldenInt, ¬ (p : GoldenInt) ∣ B ∧
      D5.S0.Carrier.phi ^ period p = 1 + (p : GoldenInt) ^ initialDepth p * B := by
  have hC := returnContent_period_ne_zero p hp.pos
  have hd : p ^ initialDepth p ∣ returnContent (period p) :=
    (pow_dvd_iff_le_padicValNat hp.ne_one hC).mpr (le_refl _)
  have hn : ¬ p ^ (initialDepth p + 1) ∣ returnContent (period p) := by
    rw [pow_dvd_iff_le_padicValNat hp.ne_one hC]
    change ¬ initialDepth p + 1 ≤ initialDepth p
    omega
  obtain ⟨B, hB⟩ := (scalar_return_iff (p ^ initialDepth p) (period p)).mpr hd
  refine ⟨B, ?_, ?_⟩
  · intro h
    obtain ⟨D, hD⟩ := h
    apply hn
    apply (scalar_return_iff _ _).mp
    refine ⟨D, ?_⟩
    rw [hB, hD, Nat.cast_pow, Nat.cast_pow, pow_succ]
    ring
  · push_cast at hB
    linear_combination hB

/-- Entire odd-prime tower, including a hypothetical exceptional initial plateau.
Natural subtraction in e-initialDepth is max(e-initialDepth,0). -/
theorem odd_prime_power_period (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ℕ) (he : 0 < e) :
    period (p ^ e) = period p * p ^ (e - initialDepth p) := by
  obtain ⟨B, hB, hseed⟩ := actual_initial_seed p hp
  have hs := initialDepth_pos p hp
  have hp3 : 3 ≤ p := by have ht := hp.two_le; omega
  have hstable : initialDepth p + 2 ≤ p * initialDepth p := by
    have hm := Nat.mul_le_mul_right (initialDepth p) hp3
    nlinarith
  have hx : D5.S0.Carrier.phi ^ period (p ^ 1) =
      1 + (p : GoldenInt) ^ initialDepth p * B := by simpa only [pow_one] using hseed
  simpa only [pow_one] using seeded_period_all p hp 1 (initialDepth p)
    (by omega) hs hstable B hB hx e (by omega)

/-- The standard quotient is zero exactly when the actual plateau reaches at least p squared. -/
theorem standard_quotient_zero_iff_depth (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    quotientMod p (frobeniusIndex p) = 0 ↔ 2 ≤ initialDepth p := by
  rw [← wall_iff_standard_quotient hp hp2 hp5, square_period_eq_iff,
    pow_dvd_iff_le_padicValNat hp.ne_one (returnContent_period_ne_zero p hp.pos)]
  rfl

/-- A nonzero standard Fibonacci quotient controls every higher prime power at once. -/
theorem full_tower_of_standard_quotient_nonzero (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hq : quotientMod p (frobeniusIndex p) ≠ 0) (e : ℕ) (he : 0 < e) :
    period (p ^ e) = period p * p ^ (e - 1) := by
  have hs := initialDepth_pos p hp
  have hlt : ¬ 2 ≤ initialDepth p := by
    intro h
    exact hq ((standard_quotient_zero_iff_depth p hp hp2 hp5).mpr h)
  have hs1 : initialDepth p = 1 := by omega
  simpa only [hs1] using odd_prime_power_period p hp hp2 e he

/-- These small seeds are consumed by the unbounded exceptional-characteristic formulas below. -/
private theorem period_two : period 2 = 3 := by
  have hd : period 2 ∣ 3 := (period_dvd_iff_pair 2 3).mpr (by norm_num [Nat.fib])
  have hn : period 2 ≠ 1 := by
    intro h
    have hz := ((period_dvd_iff_pair 2 1).mp (by rw [h])).1
    norm_num [Nat.fib] at hz
  exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hn

private theorem period_four : period 4 = 6 := by
  have h3 : 3 ∣ period 4 := by
    rw [← period_two]
    exact period_dvd_of_dvd (by decide : 2 ∣ 4)
  have h6 : period 4 ∣ 6 := (period_dvd_iff_pair 4 6).mpr (by norm_num [Nat.fib])
  have hpos := period_pos 4 (by decide)
  have hle := Nat.le_of_dvd (by decide : 0 < 6) h6
  have hcases : period 4 = 3 ∨ period 4 = 6 := by
    obtain ⟨k, hk⟩ := h3
    omega
  rcases hcases with h | h
  · have hz := ((period_dvd_iff_pair 4 3).mp (by rw [h])).1
    norm_num [Nat.fib] at hz
  · exact h

private theorem period_five : period 5 = 20 := by
  change orderOf (fibUnit (ZMod 5)) = 20
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 20)
    ((fibUnit_pow_eq_one_iff 5 20).mpr (by norm_num [Nat.fib]))
  intro q hq hq20
  have hcases : q = 2 ∨ q = 5 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 20) hq20
    interval_cases q <;> norm_num at hq hq20 ⊢
  rcases hcases with rfl | rfl
  · intro h
    have hz := ((fibUnit_pow_eq_one_iff 5 10).mp h).1
    norm_num [Nat.fib] at hz
  · intro h
    have hz := ((fibUnit_pow_eq_one_iff 5 4).mp h).1
    norm_num [Nat.fib] at hz

/-- p=2 must be seeded at modulus four; the odd-prime depth-one rule is not reused. -/
theorem dyadic_period (e : ℕ) (he : 0 < e) :
    period (2 ^ e) = 3 * 2 ^ (e - 1) := by
  by_cases he1 : e = 1
  · simpa [he1] using period_two
  · have hseed : D5.S0.Carrier.phi ^ period (2 ^ 2) =
        1 + (2 : GoldenInt) ^ 2 * (⟨1, 2⟩ : GoldenInt) := by
      norm_num only [show 2 ^ 2 = 4 by decide, period_four]
      rw [show (6 : ℕ) = 5 + 1 by rfl, golden_phi_pow_eq_fib_pair]
      ext <;> norm_num [Nat.fib]
    have hB : ¬ (2 : GoldenInt) ∣ (⟨1, 2⟩ : GoldenInt) := by
      rw [scalar_dvd_iff_coordinates]
      norm_num
    have ht := seeded_period_all 2 Nat.prime_two 2 2 (by decide) (by decide)
      (by decide) (⟨1, 2⟩ : GoldenInt) hB hseed e (by omega)
    norm_num only [show 2 ^ 2 = 4 by decide, period_four] at ht
    rw [ht, show e - 1 = (e - 2) + 1 by omega, pow_succ]
    ring

/-- The ramified prime has a genuine nonzero first defect and an explicit complete tower. -/
theorem ramified_five_period (e : ℕ) (he : 0 < e) :
    period (5 ^ e) = 20 * 5 ^ (e - 1) := by
  have hseed : D5.S0.Carrier.phi ^ period (5 ^ 1) =
      1 + (5 : GoldenInt) ^ 1 * (⟨836, 1353⟩ : GoldenInt) := by
    rw [pow_one, period_five, show (20 : ℕ) = 19 + 1 by rfl, golden_phi_pow_eq_fib_pair]
    ext <;> norm_num [Nat.fib]
  have hB : ¬ (5 : GoldenInt) ∣ (⟨836, 1353⟩ : GoldenInt) := by
    rw [scalar_dvd_iff_coordinates]
    norm_num
  simpa only [pow_one, period_five] using seeded_period_all 5 Nat.prime_five 1 1
    (by decide) (by decide) (by decide) (⟨836, 1353⟩ : GoldenInt) hB hseed e (by omega)

end D5.S1.Recurrence.FibonacciPrimePowerPeriod
