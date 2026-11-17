/- GID: D5/S1/Recurrence/Periodic/EulerDivisorPropagation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerDivisorPropagation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordinary A000111 divisor propagation with Euler totient shifts. -/

/-
proof_shape: corrected_sum and signed_zero_transfer are bind-only auxiliary declarations,
consumed by signed_zero_transfer and odd_prime_power respectively. odd_prime_power,
divisor_propagation and particular are content after same-delivery inlining of the signed
correspondence and two-primary inductions. particular's direct step specializes
divisor_propagation with the explicit source boundaries and the sole k=3 exception.
escape_witness: odd_prime_power, consumed by divisor_propagation; corrected_sum and
signed_zero_transfer are its live frequency-transfer chain, while two_primary is the live
two-adic witness.
admission_basis: open-problem-resolution (#31280; Proved) for divisor_propagation and
particular, counting the two source assertions once; supporting declarations use
escape-witness. The two assertions are one resolution unit; its typed claim requires the
host to be a member of frozen state.
Direct frozen dependencies: none beyond pinned Mathlib; EulerTwoPrimary and EulerSecantBridge
are same-delivery dependencies.
Private theorem consumers: frequency_eq -> deleted_sum; deleted_index -> deleted_sum;
deleted_sum -> corrected_sum; correction_unit -> signed_zero_transfer;
zero_even/zero_odd -> odd_prime_power; exponential_lower -> two_primary;
two_primary -> divisor_propagation.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31291.
-/

import D5.S1.Recurrence.Periodic.EulerTwoPrimary
import D5.S1.Recurrence.Periodic.EulerSecantBridge
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-! All-parameter prime-power assembly for the literal ordinary source assertion. -/

open D5.S1.Recurrence.Periodic.EulerUpDownSource
open D5.S1.Recurrence.Periodic.EulerSecantBridge
open Finset
open D5.S1.Recurrence.Periodic.EulerSignedFrequency

/-! The correction factor is a unit at every positive index, including early indices. -/

namespace D5.S1.Recurrence.Periodic.EulerOddPrimePower

private theorem frequency_eq (p b v : ℕ) (hp : Odd p) :
    2 * (p * v + b * (p / 2)) + b = p * (2 * v + b) := by
  have h : 2 * (p / 2) + 1 = p := by have := Nat.odd_iff.mp hp; omega
  nlinarith

private theorem deleted_index (p R b h : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hb : b ≤ 1) (hh : h < p * R) (hdiv : p ∣ 2 * h + b) :
    ∃ v < R, h = p * v + b * (p / 2) := by
  have hp0 := hp.pos
  have hhalf : 2 * (p / 2) + 1 = p := by have := Nat.odd_iff.mp hodd; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp only [add_zero] at hdiv
    have hd : p ∣ h := (hp.dvd_mul.mp hdiv).resolve_left (by
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
      subst p
      norm_num at hodd)
    obtain ⟨v, rfl⟩ := hd
    refine ⟨v, ?_, by simp⟩
    exact (Nat.mul_lt_mul_left hp0).mp hh
  · obtain ⟨t, ht⟩ := hdiv
    have htodd : Odd t := by
      have hpt : Odd (p * t) := by
        rw [← ht]
        exact ⟨h, by omega⟩
      exact (Nat.odd_mul.mp hpt).2
    obtain ⟨v, hv⟩ := htodd
    have he : h = p * v + p / 2 := by nlinarith
    refine ⟨v, ?_, by simpa using he⟩
    nlinarith

private theorem deleted_sum (p R b q j : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hb : b ≤ 1) :
    (∑ h ∈ (range (p * R)).filter (fun h => p ∣ 2 * h + b),
      (-1 : ZMod q) ^ h * (2 * h + b : ℕ) ^ j) =
      (-1 : ZMod q) ^ (b * (p / 2)) *
        ∑ v ∈ range R, (-1 : ZMod q) ^ v * (p * (2 * v + b) : ℕ) ^ j := by
  rw [mul_sum]
  symm
  apply sum_bij (fun v _ => p * v + b * (p / 2))
  · intro v hv
    simp only [mem_filter, mem_range]
    have hv' := mem_range.mp hv
    have hhalf : p / 2 < p := Nat.div_lt_self hp.pos (by decide)
    refine ⟨?_, ?_⟩
    · have hb' : b * (p / 2) ≤ p / 2 := by
        simpa using Nat.mul_le_mul_right (p / 2) hb
      have hstep := Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr hv')
      nlinarith
    · rw [frequency_eq p b v hodd]
      exact dvd_mul_right _ _
  · intro v hv w hw he
    have := hp.pos
    nlinarith
  · intro h hh
    obtain ⟨hh, hd⟩ := mem_filter.mp hh
    obtain ⟨v, hv, he⟩ := deleted_index p R b h hp hodd hb (mem_range.mp hh) hd
    exact ⟨v, mem_range.mpr hv, he.symm⟩
  · intro v hv
    rw [frequency_eq p b v hodd, pow_add,
      pow_mul (-1 : ZMod q) p v, hodd.neg_one_pow]
    ring

/-- The prime-deleted finite frequency sum is the corrected integral coefficient. -/
theorem corrected_sum (p r b j : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hb : b ≤ 1) :
    (1 - (-1 : ZMod (p ^ (r + 1))) ^ (b * (p / 2)) *
        (p : ZMod (p ^ (r + 1))) ^ j) * (A b j : ZMod (p ^ (r + 1))) =
      ∑ h ∈ (range (p ^ (r + 1))).filter (fun h => ¬p ∣ 2 * h + b),
        (-1 : ZMod (p ^ (r + 1))) ^ h * (2 * h + b : ℕ) ^ j := by
  let q := p ^ (r + 1)
  have hfull := scaled_moment b q 1 q j hodd.pow hodd.pow (by simp)
  simp only [Nat.cast_one, one_pow, one_mul] at hfull
  have hscaled := scaled_moment b (p ^ r) p q j hodd.pow hodd.pow (by
    dsimp [q]
    rw [pow_succ'] )
  have hdel := deleted_sum p (p ^ r) b q j hp hodd hb
  rw [← pow_succ'] at hdel
  rw [← hscaled] at hdel
  have hsplit := sum_filter_add_sum_filter_not (range q)
    (fun h => p ∣ 2 * h + b)
    (fun h => (-1 : ZMod q) ^ h * (2 * h + b : ℕ) ^ j)
  change _ = _ at hfull hdel
  linear_combination hfull + hdel - hsplit

private theorem correction_unit (p r b j : ℕ) (hj : 0 < j) :
    IsUnit (1 - (-1 : ZMod (p ^ (r + 1))) ^ (b * (p / 2)) *
      (p : ZMod (p ^ (r + 1))) ^ j) := by
  apply IsNilpotent.isUnit_one_sub
  refine ⟨r + 1, ?_⟩
  have hz : (p : ZMod (p ^ (r + 1))) ^ (r + 1) = 0 := by
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr dvd_rfl
  have hnil : ((p : ZMod (p ^ (r + 1))) ^ j) ^ (r + 1) = 0 := by
    rw [← pow_mul, Nat.mul_comm j, pow_mul, hz, zero_pow (by omega : j ≠ 0)]
  rw [mul_pow, hnil, mul_zero]

/-- Young's zero-transfer consequence, with no lower bound by the prime-power exponent. -/
theorem signed_zero_transfer (p r b k m : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hb : b ≤ 1) (hk : 0 < k) (hzero : (A b k : ZMod (p ^ (r + 1))) = 0) :
    (A b (k + m * Nat.totient (p ^ (r + 1))) : ZMod (p ^ (r + 1))) = 0 := by
  let q := p ^ (r + 1)
  have heq :
      (∑ h ∈ (range q).filter (fun h => ¬p ∣ 2 * h + b),
        (-1 : ZMod q) ^ h * (2 * h + b : ℕ) ^
          (k + m * Nat.totient q)) =
      ∑ h ∈ (range q).filter (fun h => ¬p ∣ 2 * h + b),
        (-1 : ZMod q) ^ h * (2 * h + b : ℕ) ^ k := by
    apply sum_congr rfl
    intro h hh
    have hcop : (2 * h + b).Coprime q := hp.coprime_pow_of_not_dvd (mem_filter.mp hh).2
    have hpow : (2 * h + b : ZMod q) ^ Nat.totient q = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hcop)
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one] using h
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_add,
      Nat.mul_comm m, pow_mul, hpow, one_pow, mul_one]
  have hbefore := corrected_sum p r b k hp hodd hb
  have hafter := corrected_sum p r b (k + m * Nat.totient q) hp hodd hb
  rw [heq, ← hbefore, hzero, mul_zero] at hafter
  exact (correction_unit p r b (k + m * Nat.totient q) (by omega)).mul_left_cancel
    (by simpa using hafter)

end D5.S1.Recurrence.Periodic.EulerOddPrimePower

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
  have h := Nat.mul_le_pow (a := 2) (by decide) a
  omega

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
