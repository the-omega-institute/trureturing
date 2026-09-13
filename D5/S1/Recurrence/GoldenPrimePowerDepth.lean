/- GID: D5/S1/Recurrence/GoldenPrimePowerDepth
   generality: G
   mirror-B: none(waiver:new-existing-carrier-lift)
   mirror-E: none(waiver:universal-prime-power-depth)
   anchors: []
   digest: A primitive golden-integer defect at depth s has order p^j modulo p^(s+j), using the existing all-prime-power binomial expansion. -/

import D5.S1.Recurrence.GoldenModReturnBridge
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false

namespace D5.S1.Recurrence.GoldenPrimePowerDepth

open D5.S0.Carrier D5.S3.Arith.GoldenApparition
open FibonacciReturnSpectrum GoldenModReturnBridge

/-- Divisibility by an ordinary scalar in the actual quadratic ring is coordinatewise. -/
theorem scalar_dvd_iff_coordinates (q : ℕ) (z : GoldenInt) :
    (q : GoldenInt) ∣ z ↔ (q : ℤ) ∣ z.a ∧ (q : ℤ) ∣ z.b := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · exact ⟨w.a, by simp⟩
    · exact ⟨w.b, by simp⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨a, b⟩, ?_⟩
    apply GoldenInt.ext
    · simpa using ha
    · simpa using hb

theorem reduce_eq_zero_iff (q : ℕ) (z : GoldenInt) :
    GoldenMod.reduce q z = 0 ↔ (q : GoldenInt) ∣ z := by
  rw [scalar_dvd_iff_coordinates]
  constructor
  · intro h
    constructor
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z.a q).mp (congrArg GoldenMod.a h)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z.b q).mp (congrArg GoldenMod.b h)
  · rintro ⟨ha, hb⟩
    apply GoldenMod.ext
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z.a q).mpr ha
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z.b q).mpr hb

theorem reduce_eq_one_iff (q : ℕ) (z : GoldenInt) :
    GoldenMod.reduce q z = 1 ↔ (q : GoldenInt) ∣ z - 1 := by
  rw [← reduce_eq_zero_iff, map_sub, map_one, sub_eq_zero]

lemma scalar_mul_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (fun z : GoldenInt => (q : GoldenInt) * z) := by
  intro x y h
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  apply GoldenInt.ext
  · apply mul_left_cancel₀ hqz
    simpa using congrArg GoldenInt.a h
  · apply mul_left_cancel₀ hqz
    simpa using congrArg GoldenInt.b h

lemma scalar_pow_cancel_dvd (p : ℕ) (hp : 0 < p) (s : ℕ) (B : GoldenInt) :
    (p : GoldenInt) ^ (s + 1) ∣ (p : GoldenInt) ^ s * B ↔ (p : GoldenInt) ∣ B := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    apply scalar_mul_injective (p ^ s) (pow_pos hp s)
    simpa only [Nat.cast_pow, pow_succ, mul_assoc] using hC
  · rintro ⟨C, rfl⟩
    exact ⟨C, by rw [pow_succ, mul_assoc]⟩

lemma primitive_add_scalar (p : ℕ) (B C : GoldenInt) (hB : ¬ (p : GoldenInt) ∣ B) :
    ¬ (p : GoldenInt) ∣ B + (p : GoldenInt) * C := by
  intro h
  apply hB
  simpa using dvd_sub h (show (p : GoldenInt) ∣ (p : GoldenInt) * C from ⟨C, rfl⟩)

/-- The stable domain is s>=1 for odd p, and s>=2 for p=2.
The inequality in the statement is exactly the pinned binomial lemma's endpoint condition. -/
theorem prime_power_expansion (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (hstable : s + 2 ≤ p * s) (B : GoldenInt) (j : ℕ) :
    ∃ C : GoldenInt,
      (1 + (p : GoldenInt) ^ s * B) ^ (p ^ j) =
        1 + (p : GoldenInt) ^ (s + j) * (B + (p : GoldenInt) * C) := by
  have hv : (p : GoldenInt) ∣ (p : GoldenInt) ^ s := dvd_pow_self _ (by omega)
  have ht : (p : GoldenInt) * (p : GoldenInt) ^ s * p ∣ ((p : GoldenInt) ^ s) ^ p := by
    rw [← pow_succ', ← pow_succ, ← pow_mul]
    exact pow_dvd_pow _ (by simpa only [Nat.mul_comm] using hstable)
  obtain ⟨C, hC⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq
    (R := GoldenInt) (u := (p : GoldenInt) ^ s) (v := (p : GoldenInt)) hp hv ht B j
  refine ⟨C, ?_⟩
  simpa only [← pow_add, Nat.add_comm j s] using hC

/-- The defect has exactly the indicated depth, not only a divisibility lower bound. -/
theorem exact_depth_after_prime_power (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (hstable : s + 2 ≤ p * s) (B : GoldenInt)
    (hB : ¬ (p : GoldenInt) ∣ B) (j : ℕ) :
    (p : GoldenInt) ^ (s + j) ∣ (1 + (p : GoldenInt) ^ s * B) ^ (p ^ j) - 1 ∧
      ¬ (p : GoldenInt) ^ (s + j + 1) ∣
        (1 + (p : GoldenInt) ^ s * B) ^ (p ^ j) - 1 := by
  obtain ⟨C, hC⟩ := prime_power_expansion p hp s hs hstable B j
  rw [hC, add_sub_cancel_left]
  refine ⟨⟨B + p * C, rfl⟩, ?_⟩
  rw [scalar_pow_cancel_dvd p hp.pos]
  exact primitive_add_scalar p B C hB

/-- The exact depth determines the complete order in every finer residue ring. -/
theorem reduced_order_at_depth (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (hstable : s + 2 ≤ p * s) (B : GoldenInt)
    (hB : ¬ (p : GoldenInt) ∣ B) (j : ℕ) :
    orderOf (GoldenMod.reduce (p ^ (s + j)) (1 + (p : GoldenInt) ^ s * B)) = p ^ j := by
  letI : Fact p.Prime := ⟨hp⟩
  cases j with
  | zero =>
      have hz : GoldenMod.reduce (p ^ s) (1 + (p : GoldenInt) ^ s * B) = 1 := by
        apply (reduce_eq_one_iff _ _).mpr
        exact ⟨B, by simp [Nat.cast_pow]⟩
      simp only [Nat.add_zero, pow_zero, hz, orderOf_one]
  | succ j =>
      apply orderOf_eq_prime_pow
      · intro h
        have hd := (exact_depth_after_prime_power p hp s hs hstable B hB j).2
        apply hd
        have he : GoldenMod.reduce (p ^ (s + j + 1))
            ((1 + (p : GoldenInt) ^ s * B) ^ (p ^ j)) = 1 := by
          simpa only [map_pow, Nat.add_assoc] using h
        simpa only [Nat.cast_pow] using (reduce_eq_one_iff _ _).mp he
      · have hd := (exact_depth_after_prime_power p hp s hs hstable B hB (j + 1)).1
        have he := (reduce_eq_one_iff (p ^ (s + (j + 1)))
          ((1 + (p : GoldenInt) ^ s * B) ^ (p ^ (j + 1)))).mpr
          (by simpa only [Nat.cast_pow] using hd)
        simpa only [map_pow] using he

/-- A genuine seed period and exact initial defect determine all periods above that depth.
No lifting law is assumed; it is supplied by reduced_order_at_depth. -/
theorem seeded_period_above_depth (p : ℕ) (hp : p.Prime) (h s : ℕ)
    (hhs : h ≤ s) (hs : 0 < s) (hstable : s + 2 ≤ p * s)
    (B : GoldenInt) (hB : ¬ (p : GoldenInt) ∣ B)
    (hseed : D5.S0.Carrier.phi ^ period (p ^ h) = 1 + (p : GoldenInt) ^ s * B)
    (j : ℕ) :
    period (p ^ (s + j)) = period (p ^ h) * p ^ j := by
  have hr : 0 < period (p ^ h) := period_pos _ (pow_pos hp.pos h)
  have hdiv : period (p ^ h) ∣ period (p ^ (s + j)) :=
    period_dvd_of_dvd (pow_dvd_pow p (by omega))
  have ho := reduced_order_at_depth p hp s hs hstable B hB j
  rw [← hseed, map_pow] at ho
  change orderOf ((GoldenMod.phi : GoldenMod (p ^ (s + j))) ^ period (p ^ h)) = p ^ j at ho
  rw [orderOf_pow' _ (ne_of_gt hr), ← period_eq_golden_order,
    Nat.gcd_eq_right hdiv] at ho
  have hm := Nat.mul_div_cancel' hdiv
  rw [ho] at hm
  exact hm.symm

/-- The plateau and growth regimes are both included, at every e >= the seed modulus depth. -/
theorem seeded_period_all (p : ℕ) (hp : p.Prime) (h s : ℕ)
    (hhs : h ≤ s) (hs : 0 < s) (hstable : s + 2 ≤ p * s)
    (B : GoldenInt) (hB : ¬ (p : GoldenInt) ∣ B)
    (hseed : D5.S0.Carrier.phi ^ period (p ^ h) = 1 + (p : GoldenInt) ^ s * B)
    (e : ℕ) (he : h ≤ e) :
    period (p ^ e) = period (p ^ h) * p ^ (e - s) := by
  by_cases hes : e ≤ s
  · rw [Nat.sub_eq_zero_of_le hes, pow_zero, mul_one]
    apply Nat.dvd_antisymm
    · apply (period_dvd_iff_reduced_phi _ _).mpr
      rw [hseed]
      apply (reduce_eq_one_iff _ _).mpr
      have hd : (p : GoldenInt) ^ e ∣ (p : GoldenInt) ^ s := pow_dvd_pow _ hes
      simpa only [Nat.cast_pow, add_sub_cancel_left] using
        hd.trans (show (p : GoldenInt) ^ s ∣ (p : GoldenInt) ^ s * B from ⟨B, rfl⟩)
    · exact period_dvd_of_dvd (pow_dvd_pow p he)
  · have hi : s + (e - s) = e := by omega
    simpa only [hi] using seeded_period_above_depth p hp h s hhs hs hstable B hB hseed (e - s)

end D5.S1.Recurrence.GoldenPrimePowerDepth
