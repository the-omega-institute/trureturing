/- GID: D5/S3/Arith/Congruence/MultipleOfThreeCoincidence
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/MultipleOfThreeCoincidence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A multiple-of-three residue coincidence characterizes composites with four exceptions. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.MultipleOfThreeCoincidence

/-- Equality of the fractions at 3 and a larger multiple of 3, with positive denominators. -/
def Coincides (k : ℕ) : Prop :=
  ∃ m : ℕ, 6 ≤ m ∧ m ≤ k ∧ 3 ∣ m ∧ 3 * ((2 * k) % m) = m * ((2 * k) % 3)

private theorem residue_factor_iff (x t : ℕ) (ht : 0 < t) :
    x % (3 * t) = t * (x % 3) ↔ t ∣ x ∧ (x / t) % 3 = x % 3 := by
  constructor
  · intro h
    have hd : t ∣ x := by
      refine ⟨x % 3 + 3 * (x / (3 * t)), ?_⟩
      have hm := Nat.mod_add_div x (3 * t)
      rw [h] at hm
      nlinarith
    refine ⟨hd, ?_⟩
    have hm : x % (3 * t) = t * ((x / t) % 3) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hd]
      rw [Nat.mul_comm 3 t, Nat.mul_mod_mul_left]
    nlinarith
  · rintro ⟨hd, hq⟩
    calc
      x % (3 * t) = (t * (x / t)) % (t * 3) := by
        rw [Nat.mul_div_cancel' hd, Nat.mul_comm t 3]
      _ = t * ((x / t) % 3) := Nat.mul_mod_mul_left _ _ _
      _ = t * (x % 3) := by rw [hq]

private theorem coincides_iff_divisor (k : ℕ) :
    Coincides k ↔ ∃ t : ℕ, 2 ≤ t ∧ 3 * t ≤ k ∧ t ∣ 2 * k ∧
      ((2 * k) / t) % 3 = (2 * k) % 3 := by
  constructor
  · rintro ⟨m, hm, hmk, ⟨t, rfl⟩, he⟩
    have ht : 2 ≤ t := by omega
    refine ⟨t, ht, hmk, (residue_factor_iff _ _ (by omega)).mp ?_⟩
    nlinarith
  · rintro ⟨t, ht, htk, hd, hq⟩
    refine ⟨3 * t, by omega, htk, dvd_mul_right _ _, ?_⟩
    have he := (residue_factor_iff _ _ (by omega : 0 < t)).mpr ⟨hd, hq⟩
    nlinarith

private theorem coincides_of_divisor_mod_one (k t : ℕ) (ht : 2 ≤ t)
    (htk : 3 * t ≤ k) (hd : t ∣ 2 * k) (hr : t % 3 = 1) : Coincides k := by
  apply (coincides_iff_divisor k).mpr
  refine ⟨t, ht, htk, hd, ?_⟩
  have hm := Nat.mul_mod t ((2 * k) / t) 3
  rw [Nat.mul_div_cancel' hd, hr, one_mul, Nat.mod_mod] at hm
  exact hm.symm

private theorem not_coincides_prime (k : ℕ) (hk : k.Prime) : ¬Coincides k := by
  rintro h
  obtain ⟨t, ht, htk, hd, hq⟩ := (coincides_iff_divisor k).mp h
  have hkt : ¬k ∣ t := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < t) h
    omega
  have hc : t.Coprime k := (hk.coprime_iff_not_dvd.mpr hkt).symm
  have ht2 : t ∣ 2 := hc.dvd_mul_right.mp hd
  have he : t = 2 := (Nat.dvd_prime_two_le Nat.prime_two ht).mp ht2
  subst t
  have h3 : 3 ∣ k := by omega
  have := hk.eq_one_or_self_of_dvd 3 h3
  omega

private theorem not_coincides_exception (k : ℕ) (hk : k ∈ ({4, 8, 10, 25} : Finset ℕ)) :
    ¬Coincides k := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rintro ⟨m, hm, hmk, hd, he⟩
  rcases hk with rfl | rfl | rfl | rfl <;>
    interval_cases m <;> norm_num at *

private theorem coincides_composite (k : ℕ) (hk : 1 < k) (hnp : ¬k.Prime)
    (he : k ∉ ({4, 8, 10, 25} : Finset ℕ)) : Coincides k := by
  have hk6 : 6 ≤ k := by
    by_contra h
    interval_cases k <;> norm_num at *
  by_cases h3 : 3 ∣ k
  · apply (coincides_iff_divisor k).mpr
    refine ⟨2, by omega, hk6, dvd_mul_right _ _, ?_⟩
    omega
  by_cases h2 : 2 ∣ k
  · have hk12 : 12 ≤ k := by
      by_contra h
      interval_cases k <;> norm_num at *
    apply coincides_of_divisor_mod_one k 4 (by omega) hk12 ?_ (by decide)
    obtain ⟨q, rfl⟩ := h2
    exact ⟨q, by ring⟩
  let p := k.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ k := Nat.minFac_dvd k
  have hp2 : p ≠ 2 := by
    intro h
    exact h2 (h ▸ hpd)
  have hp3 : p ≠ 3 := by
    intro h
    exact h3 (h ▸ hpd)
  have hp5 : 5 ≤ p := by
    by_contra h
    interval_cases p <;> norm_num at *
  obtain ⟨q, hkq⟩ := hpd
  have hpq : p ≤ q := by
    have hs := Nat.minFac_sq_le_self (by omega : 0 < k) hnp
    change p ^ 2 ≤ k at hs
    nlinarith
  have hpr : p % 3 = 1 ∨ p % 3 = 2 := by
    have hpn : ¬3 ∣ p := fun h => h3 (dvd_trans h (Nat.minFac_dvd k))
    omega
  rcases hpr with hr | hr
  · apply coincides_of_divisor_mod_one k p (by omega) (by nlinarith) ?_ hr
    exact dvd_mul_of_dvd_right (Nat.minFac_dvd k) 2
  · have hq6 : 6 ≤ q := by
      by_contra h
      have hq5 : q = 5 := by omega
      have hpeq : p = 5 := by omega
      have hk25 : k = 25 := by nlinarith
      exact he (by simp [hk25])
    apply coincides_of_divisor_mod_one k (2 * p) (by omega) (by nlinarith) ?_ ?_
    · exact ⟨q, by nlinarith [hkq]⟩
    · omega

/-- The unbounded classification conjectured in OEIS A387319. -/
theorem classify (k : ℕ) :
    Coincides k ↔ 1 < k ∧ ¬Nat.Prime k ∧ k ∉ ({4, 8, 10, 25} : Finset ℕ) := by
  constructor
  · intro h
    have hk : 1 < k := by obtain ⟨m, hm, hmk, _⟩ := h; omega
    exact ⟨hk, fun hp => not_coincides_prime k hp h,
      fun he => not_coincides_exception k he h⟩
  · rintro ⟨hk, hnp, he⟩
    exact coincides_composite k hk hnp he

end D5.S3.Arith.Congruence.MultipleOfThreeCoincidence
