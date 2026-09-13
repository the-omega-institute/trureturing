/- GID: D5/S1/Recurrence/FibonacciFrobeniusQuotientBridge
   generality: G
   mirror-B: none(waiver:exact-signed-index-transport)
   mirror-E: none(waiver:universal-prime-quotient-bridge)
   anchors: []
   digest: For every prime p other than 2 and 5, the return quotient is minus the actual period times the signed Frobenius quotient, and that factor is a unit. -/

import D5.S1.Recurrence.GoldenFirstOrderTransport
import D5.S1.Recurrence.GoldenModReturnBridge
import D5.S1.Recurrence.FibonacciLiftTrace

set_option autoImplicit false

namespace D5.S1.Recurrence.FibonacciFrobeniusQuotientBridge

open D5.S0.Carrier D5.S1.Scale D5.S3.Arith.GoldenApparition
open FibonacciReturnSpectrum FibonacciLiftTrace GoldenModReturnBridge GoldenFirstOrderTransport

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- mathlib writes (p/5) as legendreSym 5 p. -/
abbrev epsilon (p : ℕ) : ℤ := legendreSym 5 p

/-- Quadratic reciprocity proves agreement with the standard symbol (5/p).
The convention is an equality of the actual library symbols, not a prose identification. -/
theorem epsilon_eq_standard (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    epsilon p = legendreSym p (5 : ℤ) := by
  exact (legendreSym.quadratic_reciprocity_one_mod_four
    (p := 5) (q := p) (by decide) hp2).symm

/-- Keep the SIGN. In the inert case this is p+1, not p-1. -/
def frobeniusIndex (p : ℕ) : ℕ := ((p : ℤ) - epsilon p).toNat

/-- Divide in the natural numbers FIRST, then reduce. No division by zero in ZMod p. -/
def quotientMod (p n : ℕ) : ZMod p := ((Nat.fib n / p : ℕ) : ZMod p)

lemma epsilon_cases {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    epsilon p = 1 ∨ epsilon p = -1 := by
  have hmod : (p : ZMod 5) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm
  exact legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hmod

lemma frobeniusIndex_cast {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    (frobeniusIndex p : ℤ) = (p : ℤ) - epsilon p := by
  unfold frobeniusIndex
  apply Int.toNat_of_nonneg
  have hpge := hp.two_le
  rcases epsilon_cases hp hp5 with he | he <;> rw [he] <;> omega

theorem frobenius_index_pos {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    0 < frobeniusIndex p := by
  have hi := frobeniusIndex_cast hp hp5
  have hpge := hp.two_le
  rcases epsilon_cases hp hp5 with he | he <;> rw [he] at hi <;> omega

lemma frobeniusIndex_residue {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    (frobeniusIndex p : ZMod p) = -(epsilon p : ZMod p) := by
  have h := congrArg (fun z : ℤ => (z : ZMod p)) (frobeniusIndex_cast hp hp5)
  simpa using h

/-- The source's genuine signed-index Frobenius theorem supplies divisibility. -/
theorem frobenius_index_fib_dvd {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    p ∣ Nat.fib (frobeniusIndex p) := by
  have hnot : ¬ p ∣ 5 := by
    intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
  have h := (fibonacci_apparition_entry_point hp hnot).1
  rw [← frobeniusIndex_cast hp hp5, Int.fib_natCast, Int.cast_natCast] at h
  exact (ZMod.natCast_eq_zero_iff _ p).mp h

lemma canonical_a_residue {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    ((D5.S0.Carrier.phi ^ frobeniusIndex p).a : ZMod p) = (epsilon p : ZMod p) := by
  have hnot : ¬ p ∣ 5 := by
    intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
  have hFp : (Nat.fib p : ZMod p) = (epsilon p : ZMod p) := by
    simpa only [Int.fib_natCast, Int.cast_natCast] using
      (fibonacci_apparition_entry_point hp hnot).2
  have hz : (Nat.fib (frobeniusIndex p) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr (frobenius_index_fib_dvd hp hp5)
  have ha := congrArg (fun z : ℤ => (z : ZMod p)) (phi_power_a_add_b (frobeniusIndex p))
  rw [phi_power_b] at ha
  push_cast at ha
  rw [hz, add_zero] at ha
  rw [ha]
  rcases epsilon_cases hp hp5 with he | he
  · have hn : frobeniusIndex p + 1 = p := by
      have hi := frobeniusIndex_cast hp hp5
      rw [he] at hi
      omega
    simpa only [hn] using hFp
  · have hn : frobeniusIndex p = p + 1 := by
      have hi := frobeniusIndex_cast hp hp5
      rw [he] at hi
      omega
    rw [hn] at hz ⊢
    simpa only [Nat.add_assoc, Nat.fib_add_two, Nat.cast_add, hz, add_zero] using hFp

lemma canonical_golden_power {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    GoldenMod.reduce p (D5.S0.Carrier.phi ^ frobeniusIndex p) =
      (epsilon p : GoldenMod p) := by
  apply GoldenMod.ext
  · simpa only [GoldenMod.reduce, GoldenMod.a_intCast] using canonical_a_residue hp hp5
  · change ((D5.S0.Carrier.phi ^ frobeniusIndex p).b : ZMod p) = 0
    rw [phi_power_b]
    exact (ZMod.natCast_eq_zero_iff _ p).mpr (frobenius_index_fib_dvd hp hp5)

/-- The old period divides a prime-to-p exponent, including both split and inert branches. -/
theorem period_dvd_twice_frobenius {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    period p ∣ 2 * frobeniusIndex p := by
  apply (period_dvd_iff_reduced_phi p _).mpr
  rw [two_mul, pow_add, map_mul, canonical_golden_power hp hp5]
  rcases epsilon_cases hp hp5 with he | he <;> simp [he]

theorem period_residue_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (period p : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hn : (frobeniusIndex p : ZMod p) ≠ 0 := by
    rw [frobeniusIndex_residue hp hp5]
    rcases epsilon_cases hp hp5 with he | he <;> simp [he]
  obtain ⟨k, hk⟩ := period_dvd_twice_frobenius hp hp5
  intro hr
  have hh := congrArg (fun n : ℕ => (n : ZMod p)) hk
  push_cast at hh
  rw [hr, zero_mul] at hh
  exact (mul_ne_zero htwo hn) hh

/-- Exact coefficient: eta_p = -pi(p) q_p. No equality of the two indices is required. -/
theorem quotient_period_eq_frobenius {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    quotientMod p (period p) =
      -(period p : ZMod p) * quotientMod p (frobeniusIndex p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hr := period_pos p hp.pos
  have hdR : p ∣ Nat.fib (period p) :=
    (ZMod.natCast_eq_zero_iff _ p).mp ((period_dvd_iff_pair p (period p)).mp (dvd_refl _)).1
  have hdN := frobenius_index_fib_dvd hp hp5
  have hx : (D5.S0.Carrier.phi ^ period p).b =
      (p : ℤ) * (Nat.fib (period p) / p : ℕ) := by
    rw [phi_power_b]
    exact_mod_cast (Nat.mul_div_cancel' hdR).symm
  have hy : (D5.S0.Carrier.phi ^ frobeniusIndex p).b =
      (p : ℤ) * (Nat.fib (frobeniusIndex p) / p : ℕ) := by
    rw [phi_power_b]
    exact_mod_cast (Nat.mul_div_cancel' hdN).symm
  have hpow : (D5.S0.Carrier.phi ^ period p) ^ frobeniusIndex p =
      (D5.S0.Carrier.phi ^ frobeniusIndex p) ^ period p := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hc := coefficient_transport p hp.pos
    (D5.S0.Carrier.phi ^ period p) (D5.S0.Carrier.phi ^ frobeniusIndex p)
    (frobeniusIndex p) (period p)
    (Nat.fib (period p) / p : ℕ) (Nat.fib (frobeniusIndex p) / p : ℕ) hx hy hpow
  have hreturn := (period_dvd_iff_pair p (period p)).mp (dvd_refl _)
  have hAr : ((D5.S0.Carrier.phi ^ period p).a : ZMod p) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) (phi_power_a_add_b (period p))
    rw [phi_power_b] at h
    push_cast at h
    simpa [hreturn.1, hreturn.2] using h
  have hepow : (epsilon p : ZMod p) ^ (period p - 1) = (epsilon p : ZMod p) := by
    rcases epsilon_cases hp hp5 with he | he
    · simp [he]
    · simp only [he, Int.cast_neg, Int.cast_one]
      have hh := (period_even p hp hp2).neg_one_pow (α := ZMod p)
      have hi : period p = (period p - 1) + 1 := by omega
      rw [hi, pow_succ] at hh
      linear_combination -hh
  rw [hAr, canonical_a_residue hp hp5, hepow, one_pow, mul_one,
    frobeniusIndex_residue hp hp5] at hc
  have hez : (epsilon p : ZMod p) ≠ 0 := by
    rcases epsilon_cases hp hp5 with he | he <;> simp [he]
  apply mul_left_cancel₀ hez
  unfold quotientMod
  push_cast at hc
  linear_combination -hc

theorem quotient_period_eq_frobenius_factor_isUnit {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    IsUnit (-(period p : ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (period_residue_ne_zero hp hp2 hp5))

/-- The standard Frobenius-index test and the actual period plateau are now equivalent. -/
theorem wall_iff_standard_quotient {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    period (p ^ 2) = period p ↔ quotientMod p (frobeniusIndex p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [square_period_eq_iff_firstQuotient p hp hp2,
      ← ZMod.natCast_eq_zero_iff]
  change quotientMod p (period p) = 0 ↔ _
  rw [quotient_period_eq_frobenius hp hp2 hp5]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (neg_ne_zero.mpr (period_residue_ne_zero hp hp2 hp5))
  · intro h
    rw [h, mul_zero]

end D5.S1.Recurrence.FibonacciFrobeniusQuotientBridge
