/- GID: D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Tactic.NormNum.Ineq, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: none
   digest: Twin prime pairs centered at both 6n and 12n force n to be one or divisible by five. -/

import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Prime

namespace D5.S3.Arith.Congruence.DaleTwinPrimeAverageMultipleOfFive

def IsMember (n : ℕ) : Prop :=
  1 ≤ n ∧ Nat.Prime (6 * n - 1) ∧ Nat.Prime (6 * n + 1) ∧
    Nat.Prime (12 * n - 1) ∧ Nat.Prime (12 * n + 1)

example : IsMember 1 := by norm_num [IsMember]
example : IsMember 5 := by norm_num [IsMember]
example : ¬ IsMember 2 := by norm_num [IsMember]

theorem dale_a177680 : ∀ n : ℕ, IsMember n → n = 1 ∨ 5 ∣ n := by
  intro n hn
  rcases hn with ⟨hnpos, hp6m, hp6p, hp12m, hp12p⟩
  by_cases h0 : n % 5 = 0
  · exact Or.inr (Nat.dvd_of_mod_eq_zero h0)
  have hr : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    have := Nat.mod_lt n (by decide : 0 < 5)
    omega
  rcases hr with h1 | h2 | h3 | h4
  · have hd : 5 ∣ 6 * n - 1 := by omega
    have heq : 5 = 6 * n - 1 :=
      (hp6m.eq_one_or_self_of_dvd 5 hd).resolve_left (by decide)
    exact Or.inl (by omega)
  · have hd : 5 ∣ 12 * n + 1 := by omega
    have heq : 5 = 12 * n + 1 :=
      (hp12p.eq_one_or_self_of_dvd 5 hd).resolve_left (by decide)
    omega
  · have hd : 5 ∣ 12 * n - 1 := by omega
    have heq : 5 = 12 * n - 1 :=
      (hp12m.eq_one_or_self_of_dvd 5 hd).resolve_left (by decide)
    omega
  · have hd : 5 ∣ 6 * n + 1 := by omega
    have heq : 5 = 6 * n + 1 :=
      (hp6p.eq_one_or_self_of_dvd 5 hd).resolve_left (by decide)
    omega

#print axioms dale_a177680

end D5.S3.Arith.Congruence.DaleTwinPrimeAverageMultipleOfFive
