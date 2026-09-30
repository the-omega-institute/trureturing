/- GID: D5/S3/Arith/Congruence/Erdos375ThreeComposites
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:unbounded-open-problem-slice)
   anchors: []
   utility: none
   digest: Three consecutive composite integers admit distinct prime divisors. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.Erdos375ThreeComposites

/--
Erdős problem #375, the first nontrivial three-term case.

If `n + 1`, `n + 2`, and `n + 3` are composite, then each term has a
distinct prime divisor.  The unrestricted Grimm conjecture asks for the
analogous choice for every composite interval; this result only treats
three consecutive terms.
-/
theorem exists_distinct_prime_divisors_of_three_composites {n : ℕ} (hn : 1 ≤ n)
    (h₁ : ¬ Nat.Prime (n + 1)) (h₂ : ¬ Nat.Prime (n + 2))
    (h₃ : ¬ Nat.Prime (n + 3)) :
    ∃ p₁ p₂ p₃ : ℕ,
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧
      p₁ ∣ n + 1 ∧ p₂ ∣ n + 2 ∧ p₃ ∣ n + 3 ∧
      p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ := by
  have hn1 : n ≠ 1 := by
    intro hn1
    subst n
    norm_num at h₁
  have hnplus1 : n + 1 ≠ 1 := by omega
  have hnplus2 : n + 2 ≠ 1 := by omega
  have hnplus3 : n + 3 ≠ 1 := by omega
  obtain ⟨p₁, hp₁, hp₁d⟩ := Nat.exists_prime_and_dvd hnplus1
  obtain ⟨p₂, hp₂, hp₂d⟩ := Nat.exists_prime_and_dvd hnplus2
  obtain ⟨p₃, hp₃, hp₃d⟩ := Nat.exists_prime_and_dvd hnplus3
  have hA2 : 2 < n + 1 := by omega
  have hC2 : 2 < n + 3 := by omega
  have hcop12 : Nat.Coprime (n + 1) (n + 2) := by
    rw [show n + 2 = 1 + (n + 1) by omega, Nat.coprime_add_self_right]
    exact Nat.coprime_one_right _
  have hcop23 : Nat.Coprime (n + 2) (n + 3) := by
    rw [show n + 3 = 1 + (n + 2) by omega, Nat.coprime_add_self_right]
    exact Nat.coprime_one_right _
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hA2 with
    hA4 | ⟨pA, hpA, hpAd, hpAodd⟩
  · rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hC2 with
      hC4 | ⟨pC, hpC, hpCd, hpCodd⟩
    · have hsub : (n + 3) - (n + 1) = 2 := by omega
      have hbad : 4 ∣ 2 := by
        rw [← hsub]
        exact Nat.dvd_sub hC4 hA4
      norm_num at hbad
    · have hp1_ne_pC : p₁ ≠ pC := by
        intro heq
        have hd : pC ∣ 2 := by
          rw [← show (n + 3) - (n + 1) = 2 by omega]
          exact Nat.dvd_sub hpCd (by simpa [heq] using hp₁d)
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h | h
        · exact hpC.ne_one h
        · subst pC
          rcases hpCodd with ⟨k, hk⟩
          omega
      have hp1_ne_p2 : p₁ ≠ p₂ := by
        intro heq
        subst p₂
        have hone : p₁ = 1 := Nat.eq_one_of_dvd_coprimes hcop12 hp₁d hp₂d
        exact hp₁.ne_one hone
      have hp2_ne_pC : p₂ ≠ pC := by
        intro heq
        subst pC
        have hone : p₂ = 1 := Nat.eq_one_of_dvd_coprimes hcop23 hp₂d hpCd
        exact hp₂.ne_one hone
      exact ⟨p₁, p₂, pC, hp₁, hp₂, hpC, hp₁d, hp₂d, hpCd,
        hp1_ne_p2, hp1_ne_pC, hp2_ne_pC⟩
  · have hpA_ne_p₃ : pA ≠ p₃ := by
      intro heq
      have hd : pA ∣ 2 := by
        rw [← show (n + 3) - (n + 1) = 2 by omega]
        exact Nat.dvd_sub (by simpa [heq] using hp₃d) hpAd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h | h
      · exact hpA.ne_one h
      · subst pA
        rcases hpAodd with ⟨k, hk⟩
        omega
    have hpA_ne_p2 : pA ≠ p₂ := by
      intro heq
      subst p₂
      have hone : pA = 1 := Nat.eq_one_of_dvd_coprimes hcop12 hpAd hp₂d
      exact hpA.ne_one hone
    have hp2_ne_p3 : p₂ ≠ p₃ := by
      intro heq
      subst p₃
      have hone : p₂ = 1 := Nat.eq_one_of_dvd_coprimes hcop23 hp₂d hp₃d
      exact hp₂.ne_one hone
    exact ⟨pA, p₂, p₃, hpA, hp₂, hp₃, hpAd, hp₂d, hp₃d,
      hpA_ne_p2, hpA_ne_p₃, hp2_ne_p3⟩

end D5.S3.Arith.Congruence.Erdos375ThreeComposites
