/- GID: D5/S3/Arith/Primes/PrimeProgressionDifference
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/PrimeProgressionDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: An arithmetic progression of primes longer than a prime p has p dividing its common difference, unless p is one of its terms. -/

import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.PrimeProgressionDifference

/-- A prime no larger than the length of a prime arithmetic progression divides its
common difference unless it occurs as a term. -/
theorem prime_dvd_difference_or_eq_term
    {a d L p : ℕ}
    (hprime : ∀ i < L, Nat.Prime (a + i * d))
    (hp : Nat.Prime p)
    (hpL : p ≤ L) :
    p ∣ d ∨ ∃ i < L, a + i * d = p := by
  by_cases hpd : p ∣ d
  · exact Or.inl hpd
  · right
    let _ : NeZero p := ⟨hp.ne_zero⟩
    have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    let x : ZMod p := -(a : ZMod p) * (d : ZMod p)⁻¹
    let i : ℕ := x.val
    have hi_p : i < p := ZMod.val_lt x
    have hi_L : i < L := hi_p.trans_le hpL
    have hzero : (a + i * d : ZMod p) = 0 := by
      rw [show (i : ZMod p) = x from ZMod.natCast_zmod_val x]
      change (a : ZMod p) + (-(a : ZMod p) * (d : ZMod p)⁻¹) * (d : ZMod p) = 0
      rw [mul_assoc, mul_comm (d : ZMod p)⁻¹ (d : ZMod p),
        ZMod.coe_mul_inv_eq_one d hcop]
      simp
    have hpdiv : p ∣ a + i * d := (ZMod.natCast_eq_zero_iff (a + i * d) p).mp (by
      simpa only [Nat.cast_add, Nat.cast_mul] using hzero)
    exact ⟨i, hi_L, (Nat.prime_dvd_prime_iff_eq hp (hprime i hi_L)).mp hpdiv |>.symm⟩

/-- If a prime arithmetic progression starts above its length, every prime no larger
than that length divides the common difference. -/
theorem prime_dvd_difference_of_length_lt_start
    {a d L : ℕ}
    (hprime : ∀ i < L, Nat.Prime (a + i * d))
    (hLa : L < a) :
    ∀ p, Nat.Prime p → p ≤ L → p ∣ d := by
  intro p hp hpL
  rcases prime_dvd_difference_or_eq_term hprime hp hpL with hpd | ⟨i, _hi, heq⟩
  · exact hpd
  · have ha_p : a ≤ p := (Nat.le_add_right a (i * d)).trans_eq heq
    exact (not_lt_of_ge hpL (hLa.trans_le ha_p)).elim

end D5.S3.Arith.Primes.PrimeProgressionDifference
