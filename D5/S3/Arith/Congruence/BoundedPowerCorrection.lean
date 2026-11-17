/- GID: D5/S3/Arith/Congruence/BoundedPowerCorrection
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/BoundedPowerCorrection
   mirror-E: none(waiver:unbounded-symbolic-mathematics)
   anchors: []
   utility: none
   digest: Bounded representatives on prime-power chains for every power weight at least two. -/

/- The shared induction is moved, not copied, from the square-correction owner.
Its original qualified declaration name and full proof are retained. Both the
square theorem and the uniform family import this common general dependency;
no square-weight instance is imported by the general family. The induction
quantifies over every exponent s>=2 and every bounded integer sequence, and
uses the congruence hypothesis at all prime-power steps.
admission_basis: escape-witness; the bounded-residue induction is the substantive
step, with no correction existence or integrality assumed. utility none: symbolic
unbounded mathematics, with no finite checker or certified instance.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26516 -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.HannaPrimePowerCorrection

/-- The bounded prime-power induction works for every power at least two.
The original square theorem consumes this shared proof. -/
theorem bounded_power_corrections (s : ℕ) (hs : 2 ≤ s) (a : ℕ → ℤ)
    (ha : ∀ m : ℕ, 1 ≤ m → 0 ≤ a m ∧ a m < (m : ℤ))
    (hd : ∀ (p : ℕ), p.Prime → ∀ k : ℕ,
      (p : ℤ) ^ (k + 1) ∣
        ((p ^ (k + 1) : ℕ) : ℤ) ^ s - a (p ^ (k + 1)) -
        (((p ^ k : ℕ) : ℤ) ^ s - a (p ^ k))) :
    ∀ (p r : ℕ), p.Prime → 1 ≤ r → a (p ^ r) = (p : ℤ) - 1 := by
  intro p r hp hr
  have h1 : a 1 = 0 := by
    have := ha 1 le_rfl
    norm_num at this
    omega
  have hpZ : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hall : ∀ k : ℕ, a (p ^ (k + 1)) = (p : ℤ) - 1 := by
    intro k
    induction k with
    | zero =>
      have h := hd p hp 0
      simp only [Nat.zero_add, pow_one, pow_zero, Nat.cast_one, one_pow, h1, sub_zero] at h
      have hz : (p : ℤ) ∣ a p - ((p : ℤ) - 1) := by
        have hsq : (p : ℤ) ∣ (p : ℤ) ^ s := dvd_pow_self _ (by omega)
        convert (hsq.sub h).sub (dvd_refl (p : ℤ)) using 1; ring
      have hb := ha p hp.pos
      have hm := (Int.modEq_iff_dvd.mpr hz).symm.eq
      rw [Int.emod_eq_of_lt hb.1 hb.2,
        Int.emod_eq_of_lt (by omega : 0 ≤ (p : ℤ) - 1) (by omega)] at hm
      simpa using hm
    | succ k ih =>
      have h := hd p hp (k + 1)
      simp only [Nat.add_assoc, show 1 + 1 = 2 from Nat.one_add 1] at h
      have hbig : (p : ℤ) ^ (k + 2) ∣ ((p : ℤ) ^ (k + 2)) ^ s := by
        exact dvd_pow_self _ (by omega)
      have hsmall : (p : ℤ) ^ (k + 2) ∣ ((p : ℤ) ^ (k + 1)) ^ s := by
        rw [← pow_mul]
        exact pow_dvd_pow (p : ℤ) (by nlinarith : k + 2 ≤ (k + 1) * s)
      have hz : (p : ℤ) ^ (k + 2) ∣ a (p ^ (k + 2)) - a (p ^ (k + 1)) := by
        push_cast at h
        convert (hbig.sub hsmall).sub h using 1; ring
      rw [ih] at hz
      have hb := ha (p ^ (k + 2)) (Nat.one_le_pow _ _ hp.pos)
      have hmodpos : 0 < (p : ℤ) ^ (k + 2) := pow_pos (by omega) _
      have hplt : (p : ℤ) - 1 < (p : ℤ) ^ (k + 2) := by
        have ht : (p : ℤ) ≤ (p : ℤ) ^ (k + 2) := le_self_pow₀ (by omega) (by omega)
        omega
      have hm := (Int.modEq_iff_dvd.mpr hz).symm.eq
      rw [Int.emod_eq_of_lt hb.1 (by exact_mod_cast hb.2),
        Int.emod_eq_of_lt (by omega : 0 ≤ (p : ℤ) - 1) hplt] at hm
      simpa [Nat.add_assoc] using hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  exact hall k

end D5.S3.Arith.Congruence.HannaPrimePowerCorrection
