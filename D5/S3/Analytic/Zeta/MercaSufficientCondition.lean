/- GID: D5/S3/Analytic/Zeta/MercaSufficientCondition
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/MercaSufficientCondition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The historical prime-divisor sufficient condition for equal quartic coordinates. -/

import D5.S3.Analytic.Zeta.MercaRelativeClassNumber
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.IntervalCases

/-!
The sufficient condition is attributed to the Ma--Zhang historical manuscript.
The descent uses the classical obstruction to minus one being a square modulo
a prime congruent to three modulo four. It includes relative class number one.
-/
set_option autoImplicit false

namespace D5.S3.Analytic.Zeta.MercaSufficientCondition

private lemma prime_divides_coordinates (p a b n : ℕ) (hp : p.Prime)
    (hp1 : p % 4 ≠ 1) (hpn : p ∣ n) (h : a ^ 2 + b ^ 2 = 2 * n ^ 2) :
    p ∣ a ∧ p ∣ b := by
  by_cases hp2 : p = 2
  · subst p
    have hn : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
    have ha : (a : ℤ) ^ 2 % 4 = (a : ℤ) % 2 := Int.sq_emod_four a
    have hb : (b : ℤ) ^ 2 % 4 = (b : ℤ) % 2 := Int.sq_emod_four b
    have heq : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 2 * (n : ℤ) ^ 2 := by exact_mod_cast h
    have hm := congrArg (fun z : ℤ => z % 4) heq
    have hnz : (n : ℤ) % 2 = 0 := by exact_mod_cast hn
    have hnm : (2 * (n : ℤ) ^ 2) % 4 = 0 := by
      obtain ⟨d, hd⟩ := hpn
      have hd' : (n : ℤ) = 2 * d := by exact_mod_cast hd
      rw [hd']
      ring_nf
      omega
    rw [Int.add_emod, ha, hb, hnm] at hm
    constructor <;> apply Nat.dvd_iff_mod_eq_zero.mpr <;> omega
  · haveI : Fact p.Prime := ⟨hp⟩
    have hp3 : p % 4 = 3 := by
      have ho := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      omega
    have hz : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    have heq : (a : ZMod p) ^ 2 = -(b : ZMod p) ^ 2 := by
      have hc : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 2 * (n : ZMod p) ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
          congrArg (fun z : ℕ => (z : ZMod p)) h
      rw [hz, zero_pow two_ne_zero, mul_zero] at hc
      exact eq_neg_of_add_eq_zero_left hc
    have hb : (b : ZMod p) = 0 := by
      by_contra hb
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hb heq hp3
    have ha : (a : ZMod p) = 0 := by
      rw [hb, zero_pow two_ne_zero, neg_zero, sq_eq_zero_iff] at heq
      exact heq
    exact ⟨(ZMod.natCast_eq_zero_iff a p).mp ha, (ZMod.natCast_eq_zero_iff b p).mp hb⟩

private theorem equal_coordinates (n : ℕ) :
    ∀ a b : ℕ, a ^ 2 + b ^ 2 = 2 * n ^ 2 →
      (∀ p : ℕ, p.Prime → p ∣ n → p % 4 ≠ 1) → a = b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b heq hprime
    by_cases hn0 : n = 0
    · subst n
      simp only [zero_pow two_ne_zero, mul_zero] at heq
      nlinarith
    by_cases hn1 : n = 1
    · subst n
      have ha : a ≤ 1 := by nlinarith
      have hb : b ≤ 1 := by nlinarith
      interval_cases a <;> interval_cases b <;> norm_num at *
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨hpa, hpb⟩ := prime_divides_coordinates p a b n hp (hprime p hp hpn) hpn heq
    obtain ⟨a', rfl⟩ := hpa
    obtain ⟨b', rfl⟩ := hpb
    obtain ⟨n', hn'⟩ := hpn
    have hn'pos : 0 < n' := by
      by_contra hz
      have hz' : n' = 0 := by omega
      rw [hz', mul_zero] at hn'
      exact hn0 hn'
    have hn'lt : n' < n := by nlinarith [Nat.mul_le_mul_right n' hp.two_le]
    have heq' : a' ^ 2 + b' ^ 2 = 2 * n' ^ 2 := by
      rw [hn'] at heq
      have hcancel : p ^ 2 * (a' ^ 2 + b' ^ 2) = p ^ 2 * (2 * n' ^ 2) := by
        nlinarith [heq]
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hcancel
    have hab := ih n' hn'lt a' b' heq' (fun ℓ hℓ hℓn =>
      hprime ℓ hℓ (hℓn.trans (by rw [hn']; exact Nat.dvd_mul_left n' p)))
    rw [hab]

/-- A square genuine relative class number with no prime divisor congruent to one
modulo four forces equal absolute Bernoulli coordinates. The quotient is exact. -/
theorem sufficient_condition (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) (hr5 : 5 < r)
    (h : ℕ) (hh : (h : ℚ) = MercaRelativeClassNumber.relativeClassNumber r hr)
    (hsquare : IsSquare h) (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p % 4 ≠ 1) :
    |D5.S3.ArithUnits.MercaQuarticMoments.realCoordinate r hr| =
      |D5.S3.ArithUnits.MercaQuarticMoments.imagCoordinate r hr| := by
  obtain ⟨n, hn⟩ := hsquare
  let k := D5.S3.ArithUnits.MercaQuarticMoments.realCoordinate r hr
  let t := D5.S3.ArithUnits.MercaQuarticMoments.imagCoordinate r hr
  have hnorm : k ^ 2 + t ^ 2 = 2 * (n : ℤ) ^ 2 := by
    have hq := MercaRelativeClassNumber.relative_norm r hr hr5
    rw [← hh, hn] at hq
    have hq' : (k : ℚ) ^ 2 + (t : ℚ) ^ 2 = 2 * (n : ℚ) ^ 2 := by
      simpa only [k, t, pow_two, Nat.cast_mul] using hq
    exact_mod_cast hq'
  have heq : k.natAbs ^ 2 + t.natAbs ^ 2 = 2 * n ^ 2 := by
    zify
    simpa only [Int.natCast_natAbs, sq_abs] using hnorm
  have hab := equal_coordinates n k.natAbs t.natAbs heq (fun p hp hpn =>
    hprime p hp (by rw [hn]; exact dvd_mul_of_dvd_left hpn n))
  have habZ := congrArg (fun z : ℕ => (z : ℤ)) hab
  simpa only [Int.natCast_natAbs, k, t] using habZ

end D5.S3.Analytic.Zeta.MercaSufficientCondition
