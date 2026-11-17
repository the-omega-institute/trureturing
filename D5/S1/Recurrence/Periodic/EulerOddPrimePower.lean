/- GID: D5/S1/Recurrence/Periodic/EulerOddPrimePower
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerOddPrimePower
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Deleting nonunit frequencies propagates every positive-index Euler zero at odd prime powers. -/

import D5.S1.Recurrence.Periodic.EulerSignedFrequency
import Mathlib.RingTheory.Nilpotent.Basic

/-! The correction factor is a unit at every positive index, including early indices. -/

open Finset
open D5.S1.Recurrence.Periodic.EulerSignedFrequency

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
