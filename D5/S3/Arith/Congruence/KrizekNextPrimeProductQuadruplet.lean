/- GID: D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Data.Nat.Prime.Infinite, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: Krizek's next-prime product has four prime neighbors exactly at three. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.NormNum

namespace D5.S3.Arith.Congruence.KrizekNextPrimeProductQuadruplet

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable def nextPrime (q : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (q + 1))

noncomputable def Q (q : ℕ) : ℕ := q * nextPrime q

theorem result : ∀ q : ℕ, q.Prime →
    ((Nat.Prime (Q q - 4) ∧ Nat.Prime (Q q - 2) ∧
      Nat.Prime (Q q + 2) ∧ Nat.Prime (Q q + 4)) ↔ q = 3) := by
  intro q hq
  have nextPrime_spec (n : ℕ) :
      n + 1 ≤ nextPrime n ∧ (nextPrime n).Prime := by
    exact Nat.find_spec (Nat.exists_infinite_primes (n + 1))
  have nextPrime_two : nextPrime 2 = 3 := by
    have hle : nextPrime 2 ≤ 3 :=
      Nat.find_min' (Nat.exists_infinite_primes (2 + 1)) (by decide)
    exact Nat.le_antisymm hle (nextPrime_spec 2).1
  have nextPrime_three : nextPrime 3 = 5 := by
    have hle : nextPrime 3 ≤ 5 :=
      Nat.find_min' (Nat.exists_infinite_primes (3 + 1)) (by decide)
    have hge := (nextPrime_spec 3).1
    have hne : nextPrime 3 ≠ 4 := by
      intro h
      have hp := (nextPrime_spec 3).2
      rw [h] at hp
      exact (by decide : ¬ Nat.Prime 4) hp
    omega
  constructor
  · rintro ⟨hsub4, hsub2, hadd2, hadd4⟩
    by_cases hq2 : q = 2
    · subst q
      have : Nat.Prime 4 := by simpa [Q, nextPrime_two] using hsub2
      exact ((by decide : ¬ Nat.Prime 4) this).elim
    by_cases hq3 : q = 3
    · exact hq3
    have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
    have hrPrime : (nextPrime q).Prime := (nextPrime_spec q).2
    have hr7 : 7 ≤ nextPrime q := by
      have hrgt : q < nextPrime q := (Nat.lt_iff_add_one_le).2 (nextPrime_spec q).1
      have hrNe6 : nextPrime q ≠ 6 := by
        intro h
        rw [h] at hrPrime
        exact (by decide : ¬ Nat.Prime 6) hrPrime
      omega
    have hqNotDvd : ¬ 3 ∣ q := by
      intro hdvd
      rcases hq.eq_one_or_self_of_dvd 3 hdvd with h | h
      · norm_num at h
      · exact hq3 h.symm
    have hrNotDvd : ¬ 3 ∣ nextPrime q := by
      intro hdvd
      rcases hrPrime.eq_one_or_self_of_dvd 3 hdvd with h | h
      · norm_num at h
      · omega
    have hqMod : q % 3 = 1 ∨ q % 3 = 2 := by
      have hlt := Nat.mod_lt q (by omega : 0 < 3)
      have hne : q % 3 ≠ 0 := by
        simpa [Nat.dvd_iff_mod_eq_zero] using hqNotDvd
      omega
    have hrMod : nextPrime q % 3 = 1 ∨ nextPrime q % 3 = 2 := by
      have hlt := Nat.mod_lt (nextPrime q) (by omega : 0 < 3)
      have hne : nextPrime q % 3 ≠ 0 := by
        simpa [Nat.dvd_iff_mod_eq_zero] using hrNotDvd
      omega
    have hQ35 : 35 ≤ Q q := by
      change 5 * 7 ≤ q * nextPrime q
      exact Nat.mul_le_mul hq5 hr7
    have hQMod : Q q % 3 = 1 ∨ Q q % 3 = 2 := by
      rcases hqMod with hqMod | hqMod <;>
        rcases hrMod with hrMod | hrMod <;>
        simp [Q, Nat.mul_mod, hqMod, hrMod]
    rcases hQMod with hQMod | hQMod
    · have hdvd : 3 ∣ Q q + 2 := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hQMod]
      rcases hadd2.eq_one_or_self_of_dvd 3 hdvd with h | h
      · norm_num at h
      · omega
    · have hdvd : 3 ∣ Q q - 2 := by
        have hdvdAdd : 3 ∣ Q q + 1 := by
          rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hQMod]
        have hdvdSub : 3 ∣ (Q q + 1) - 3 := Nat.dvd_sub hdvdAdd (dvd_refl 3)
        simpa only [show Q q + 1 - 3 = Q q - 2 by omega] using hdvdSub
      rcases hsub2.eq_one_or_self_of_dvd 3 hdvd with h | h
      · norm_num at h
      · omega
  · rintro rfl
    simpa [Q, nextPrime_three] using
      (by decide : Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19)

#print axioms result

end D5.S3.Arith.Congruence.KrizekNextPrimeProductQuadruplet
