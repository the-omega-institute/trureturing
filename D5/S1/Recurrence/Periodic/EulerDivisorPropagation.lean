/- GID: D5/S1/Recurrence/Periodic/EulerDivisorPropagation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerDivisorPropagation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordinary A000111 divisor propagation with Euler totient shifts. -/

import D5.S1.Recurrence.Periodic.EulerOddPrimePower
import D5.S1.Recurrence.Periodic.EulerTwoPrimary
import D5.S1.Recurrence.Periodic.EulerSecantBridge
import Mathlib.Data.Nat.Factorization.Basic

/-! All-parameter prime-power assembly for the literal ordinary source assertion. -/

open D5.S1.Recurrence.Periodic.EulerUpDownSource
open D5.S1.Recurrence.Periodic.EulerSecantBridge

namespace D5.S1.Recurrence.Periodic.EulerDivisorPropagation

private theorem zero_even (q s : ℕ) :
    (E (2 * s) : ZMod q) = 0 ↔
      (EulerSignedFrequency.A 1 (2 * s) : ZMod q) = 0 := by
  have he := congrArg (Int.castRingHom (ZMod q)) (signed_even s)
  simp only [Int.coe_castRingHom, Int.cast_natCast, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one] at he
  rw [he]
  exact ((isUnit_one : IsUnit (1 : ZMod q)).neg.pow s).mul_right_eq_zero

private theorem zero_odd (q s : ℕ) :
    (E (2 * s + 1) : ZMod q) = 0 ↔
      (EulerSignedFrequency.A 0 (2 * s + 1) : ZMod q) = 0 := by
  have he := congrArg (Int.castRingHom (ZMod q)) (signed_odd s)
  simp only [Int.coe_castRingHom, Int.cast_natCast, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one] at he
  rw [he]
  exact ((isUnit_one : IsUnit (1 : ZMod q)).neg.pow (s + 1)).mul_right_eq_zero

/-- Ordinary Euler zeros propagate at every positive index for odd prime powers. -/
theorem odd_prime_power (p r k m : ℕ) (hp : p.Prime) (ho : Odd p)
    (hk : 0 < k) (hdiv : p ^ (r + 1) ∣ E k) :
    p ^ (r + 1) ∣ E (k + m * Nat.totient (p ^ (r + 1))) := by
  let q := p ^ (r + 1)
  have hq : 2 < q := by
    have hp2 : 2 < p := by
      have hh := hp.two_le
      have := Nat.odd_iff.mp ho
      omega
    have hle : p ≤ p ^ (r + 1) := Nat.le_self_pow (by omega) p
    omega
  have hperiod := Nat.totient_even hq
  have hzero : (E k : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  by_cases he : Even k
  · obtain ⟨s, hs⟩ := he
    have hkform : k = 2 * s := by omega
    have hn : Even (k + m * Nat.totient q) :=
      (show Even k from ⟨s, hs⟩).add (hperiod.mul_left m)
    obtain ⟨t, ht⟩ := hn
    have hnform : k + m * Nat.totient q = 2 * t := by omega
    rw [hkform] at hzero
    have ha := EulerOddPrimePower.signed_zero_transfer p r 1 k m hp ho (by decide)
      hk (by rw [hkform]; exact (zero_even q s).mp hzero)
    rw [hnform] at ha ⊢
    exact (zero_even q t).mpr ha
  · have ho' := Nat.not_even_iff_odd.mp he
    obtain ⟨s, hs⟩ := ho'
    have hkform : k = 2 * s + 1 := by omega
    have hn : Odd (k + m * Nat.totient q) :=
      (show Odd k from ⟨s, hs⟩).add_even (hperiod.mul_left m)
    obtain ⟨t, ht⟩ := hn
    have hnform : k + m * Nat.totient q = 2 * t + 1 := by omega
    rw [hkform] at hzero
    have ha := EulerOddPrimePower.signed_zero_transfer p r 0 k m hp ho (by decide)
      hk (by rw [hkform]; exact (zero_odd q s).mp hzero)
    rw [hnform] at ha ⊢
    exact (zero_odd q t).mpr ha

private theorem exponential_lower (a : ℕ) : 2 * a ≤ 2 ^ a + 1 := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    by_cases ha : a = 0
    · subst a; norm_num
    have hp : 2 ≤ 2 ^ a := Nat.le_self_pow (by omega) 2
    rw [pow_succ]
    nlinarith

private theorem two_primary (a k m d : ℕ) (hd : 2 < d) (hm : 0 < m)
    (had : 2 ^ (a + 1) ∣ d) (hdiv : d ∣ E k) :
    2 ^ (a + 1) ∣ E (k + m * Nat.totient d) := by
  have htwo : 2 ∣ E k :=
    (dvd_pow_self 2 (by omega : a + 1 ≠ 0)).trans (had.trans hdiv)
  have hkodd : Odd k := by
    apply Nat.not_even_iff_odd.mp
    intro he
    obtain ⟨s, hs⟩ := he
    have heq : k = 2 * s := by omega
    have ho := EulerTwoPrimary.secant_odd s
    rw [heq] at htwo
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr htwo)
  have hk3 : 3 ≤ k := by
    have hb := boundary_values
    by_contra h
    interval_cases k <;> simp_all
  have hphieven := Nat.totient_even hd
  have hnodd : Odd (k + m * Nat.totient d) := hkodd.add_even (hphieven.mul_left m)
  obtain ⟨s, hs⟩ := hnodd
  have hnform : k + m * Nat.totient d = 2 * s + 1 := by omega
  have hphi : 2 ^ a ≤ Nat.totient d := by
    have hh := Nat.totient_dvd_of_dvd had
    rw [Nat.totient_prime_pow_succ Nat.prime_two] at hh
    simp only [Nat.reduceSub, mul_one] at hh
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) hh
  have hmphi : Nat.totient d ≤ m * Nat.totient d := Nat.le_mul_of_pos_left _ hm
  have ha : a + 1 ≤ s := by
    have hb := exponential_lower a
    omega
  rw [hnform]
  exact (pow_dvd_pow 2 ha).trans (EulerTwoPrimary.tangent_power s)

/-- The complete main A386381 Conjecture 2 assertion for ordinary A000111. -/
theorem divisor_propagation (k m d : ℕ) (hd : 2 < d) (hdiv : d ∣ E k) :
    d ∣ E (k + m * Nat.totient d) := by
  by_cases hm : m = 0
  · simpa [hm] using hdiv
  have hk : 0 < k := by
    by_contra hh
    have he : k = 0 := by omega
    rw [he, boundary_values.1] at hdiv
    have := Nat.le_of_dvd (by decide : 0 < 1) hdiv
    omega
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p a hp hpa
  cases a with
  | zero => simp
  | succ a =>
    by_cases hp2 : p = 2
    · subst p
      exact two_primary a k m d hd (by omega) hpa hdiv
    · have ho := hp.odd_of_ne_two hp2
      obtain ⟨t, ht⟩ := Nat.totient_dvd_of_dvd hpa
      have hh := odd_prime_power p a k (m * t) hp ho hk (hpa.trans hdiv)
      simpa only [ht, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

/-- The particular family excludes exactly the source's index three. -/
theorem particular (k m : ℕ) (hk : k ≠ 3) :
    E k ∣ E (k + m * Nat.totient (E k)) := by
  by_cases hsmall : k < 4
  · interval_cases k <;> simp_all [boundary_values.1, boundary_values.2.1,
      boundary_values.2.2.1]
  · exact divisor_propagation k m (E k) (boundary_values.2.2.2.2 k (by omega)) dvd_rfl

end D5.S1.Recurrence.Periodic.EulerDivisorPropagation
