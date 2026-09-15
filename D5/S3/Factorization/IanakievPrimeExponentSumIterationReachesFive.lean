/- GID: D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive
   generality: G
   mirror-B: D5/B/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: Ianakiev's prime-exponent sum iteration reaches five from every integer above four. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Factorization.IanakievPrimeExponentSumIterationReachesFive

/-- OEIS A008474, the sum of each prime divisor and its exponent. -/
def F (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (p + n.factorization p)

private theorem F_upper : ∀ n : ℕ, 2 ≤ n → F n ≤ n + 1 := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he _
    have hvalue : F (p ^ e) = p + e := by
      rw [F, Nat.primeFactors_pow p he.ne', hp.primeFactors, hp.factorization_pow]
      simp
    rw [hvalue]
    have hpow : ∀ k : ℕ, 0 < k → p + k ≤ p ^ k + 1 := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
          by_cases hk0 : k = 0
          · subst k
            simp
          · have ih' := ih (by omega)
            have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
            have hq2 : 2 ≤ p ^ k := hp.two_le.trans hpk
            have hmul : 2 * p ^ k ≤ p ^ k * p := by
              simpa [mul_comm] using Nat.mul_le_mul_right (p ^ k) hp.two_le
            rw [pow_succ]
            omega
    exact hpow e he
  · omega
  · omega
  · intro a b ha hb hab hA hB _
    have hvalue : F (a * b) = F a + F b := by
      rw [F, F, F, hab.primeFactors_mul,
        Nat.factorization_mul (by omega) (by omega)]
      rw [Finset.sum_union hab.disjoint_primeFactors]
      apply congrArg₂ (fun x y => x + y)
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finsupp.add_apply]
        have hnot : ¬p ∣ b := fun hpb =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) hpb)
        rw [Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finsupp.add_apply]
        have hnot : ¬p ∣ a := fun hpa =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.eq_one_of_dvd_coprimes hab hpa (Nat.dvd_of_mem_primeFactors hp))
        rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
    rw [hvalue]
    have hsum : a + 1 + (b + 1) ≤ a * b + 1 := by
      by_cases ha2 : a = 2
      · subst a
        have hb2 : b ≠ 2 := by
          intro h
          subst b
          norm_num at hab
        omega
      · have ha3 : 3 ≤ a := by omega
        have haeq : a = (a - 3) + 3 := by omega
        have hbeq : b = (b - 2) + 2 := by omega
        rw [haeq, hbeq]
        nlinarith [Nat.zero_le ((a - 3) * (b - 2))]
    exact (Nat.add_le_add (hA (by omega)) (hB (by omega))).trans hsum

private theorem F_lower : ∀ n : ℕ, 5 ≤ n → 5 ≤ F n := by
  have F_at_least_three : ∀ n : ℕ, 2 ≤ n → 3 ≤ F n := by
    have hmul : ∀ a b : ℕ, a.Coprime b → 1 < a → 1 < b →
        F (a * b) = F a + F b := by
      intro a b hab ha hb
      rw [F, F, F, hab.primeFactors_mul,
        Nat.factorization_mul (by omega) (by omega)]
      rw [Finset.sum_union hab.disjoint_primeFactors]
      apply congrArg₂ (fun x y => x + y)
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finsupp.add_apply]
        have hnot : ¬p ∣ b := fun hpb =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) hpb)
        rw [Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finsupp.add_apply]
        have hnot : ¬p ∣ a := fun hpa =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.eq_one_of_dvd_coprimes hab hpa (Nat.dvd_of_mem_primeFactors hp))
        rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
    apply Nat.recOnPosPrimePosCoprime
    · intro p e hp he _
      have hp2 := hp.two_le
      rw [F, Nat.primeFactors_pow p he.ne', hp.primeFactors, hp.factorization_pow]
      simp
      omega
    · omega
    · omega
    · intro a b ha hb hab hA hB _
      rw [hmul a b hab ha hb]
      omega
  have hmul : ∀ a b : ℕ, a.Coprime b → 1 < a → 1 < b →
      F (a * b) = F a + F b := by
    intro a b hab ha hb
    rw [F, F, F, hab.primeFactors_mul,
      Nat.factorization_mul (by omega) (by omega)]
    rw [Finset.sum_union hab.disjoint_primeFactors]
    apply congrArg₂ (fun x y => x + y)
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Finsupp.add_apply]
      have hnot : ¬p ∣ b := fun hpb =>
        (Nat.prime_of_mem_primeFactors hp).ne_one
          (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) hpb)
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Finsupp.add_apply]
      have hnot : ¬p ∣ a := fun hpa =>
        (Nat.prime_of_mem_primeFactors hp).ne_one
          (Nat.eq_one_of_dvd_coprimes hab hpa (Nat.dvd_of_mem_primeFactors hp))
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he hpe
    have hp2 := hp.two_le
    rw [F, Nat.primeFactors_pow p he.ne', hp.primeFactors, hp.factorization_pow]
    simp
    by_cases hp5 : 5 ≤ p
    · omega
    · have hp4 : p ≤ 4 := by omega
      have hpne4 : p ≠ 4 := by
        intro h
        subst p
        exact (by decide : ¬Nat.Prime 4) hp
      rcases (by omega : p = 2 ∨ p = 3) with rfl | rfl
      · have he3 : 3 ≤ e := by
          by_contra h
          have heCases : e = 1 ∨ e = 2 := by omega
          rcases heCases with rfl | rfl <;> norm_num at hpe
        omega
      · have he2 : 2 ≤ e := by
          by_contra h
          have : e = 1 := by omega
          subst e
          norm_num at hpe
        omega
  · omega
  · omega
  · intro a b ha hb hab _ _ _
    rw [hmul a b hab ha hb]
    have haF := F_at_least_three a (by omega)
    have hbF := F_at_least_three b (by omega)
    omega

private theorem F_composite_lt : ∀ n : ℕ,
    4 < n → ¬n.Prime → n ≠ 6 → F n < n := by
  have hmul : ∀ a b : ℕ, a.Coprime b → 1 < a → 1 < b →
      F (a * b) = F a + F b := by
    intro a b hab ha hb
    rw [F, F, F, hab.primeFactors_mul,
      Nat.factorization_mul (by omega) (by omega)]
    rw [Finset.sum_union hab.disjoint_primeFactors]
    apply congrArg₂ (fun x y => x + y)
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Finsupp.add_apply]
      have hnot : ¬p ∣ b := fun hpb =>
        (Nat.prime_of_mem_primeFactors hp).ne_one
          (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) hpb)
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Finsupp.add_apply]
      have hnot : ¬p ∣ a := fun hpa =>
        (Nat.prime_of_mem_primeFactors hp).ne_one
          (Nat.eq_one_of_dvd_coprimes hab hpa (Nat.dvd_of_mem_primeFactors hp))
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he hn4 hnot _
    have hp2 := hp.two_le
    have hvalue : F (p ^ e) = p + e := by
      rw [F, Nat.primeFactors_pow p he.ne', hp.primeFactors, hp.factorization_pow]
      simp
    rw [hvalue]
    have he2 : 2 ≤ e := by
      by_contra h
      have he1 : e = 1 := by omega
      subst e
      exact hnot (by simpa using hp)
    by_cases heq : e = 2
    · subst e
      by_cases hpeq : p = 2
      · subst p
        norm_num at hn4
      · have hp3 : 3 ≤ p := by omega
        calc
          p + 2 < 2 * p := by omega
          _ ≤ p * p := Nat.mul_le_mul_right p (by omega)
          _ = p ^ 2 := by ring
    · have he3 : 3 ≤ e := by omega
      have hpow : ∀ k : ℕ, 3 ≤ k → p + k < p ^ k := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
            by_cases hk3 : 3 ≤ k
            · have ih' := ih hk3
              have hqpos : 0 < p ^ k := pow_pos hp.pos k
              have hmul' : 2 * p ^ k ≤ p ^ k * p := by
                simpa [mul_comm] using Nat.mul_le_mul_right (p ^ k) hp.two_le
              rw [pow_succ]
              omega
            · have hk2 : k = 2 := by omega
              subst k
              calc
                p + (2 + 1) < 4 * p := by omega
                _ = 2 * (2 * p) := by ring
                _ ≤ 2 * (p * p) :=
                  Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right p hp.two_le)
                _ ≤ p * (p * p) := Nat.mul_le_mul_right (p * p) hp.two_le
                _ = p ^ (2 + 1) := by ring
      exact hpow e he3
  · omega
  · omega
  · intro a b ha hb hab _ _ hn4 _ h6
    rw [hmul a b hab ha hb]
    have hFa := F_upper a (by omega)
    have hFb := F_upper b (by omega)
    have harith : a + 1 + (b + 1) < a * b := by
      by_cases ha2 : a = 2
      · subst a
        have hb2 : b ≠ 2 := by
          intro h
          subst b
          norm_num at hab
        have hb3 : b ≠ 3 := by
          intro h
          subst b
          exact h6 (by norm_num)
        have hb4 : b ≠ 4 := by
          intro h
          subst b
          exact (by decide : ¬Nat.Coprime 2 4) hab
        have hb5 : 5 ≤ b := by omega
        omega
      · by_cases hb2 : b = 2
        · subst b
          have ha3 : a ≠ 3 := by
            intro h
            subst a
            exact h6 (by norm_num)
          have ha4 : a ≠ 4 := by
            intro h
            subst a
            exact (by decide : ¬Nat.Coprime 4 2) hab
          have ha5 : 5 ≤ a := by omega
          omega
        · have ha3 : 3 ≤ a := by omega
          have hb3 : 3 ≤ b := by omega
          have haeq : a = (a - 3) + 3 := by omega
          have hbeq : b = (b - 3) + 3 := by omega
          rw [haeq, hbeq]
          nlinarith [Nat.zero_le ((a - 3) * (b - 3))]
    exact (Nat.add_le_add hFa hFb).trans_lt harith

private theorem F_prime_two_step_lt (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) :
    F (F p) < p := by
  have F_two_mul_le (n : ℕ) (hn : 0 < n) : F (2 * n) ≤ F n + 3 := by
    have hsplit (m : ℕ) :
        F m = (∑ p ∈ m.primeFactors, p) + ArithmeticFunction.cardFactors m := by
      rw [F, Finset.sum_add_distrib,
        ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
        Nat.support_factorization]
    rw [hsplit, hsplit, ArithmeticFunction.cardFactors_mul (by norm_num) hn.ne',
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
      Nat.primeFactors_mul (by norm_num) hn.ne', Nat.prime_two.primeFactors]
    by_cases h2 : 2 ∈ n.primeFactors
    · rw [Finset.singleton_union, Finset.insert_eq_of_mem h2]
      omega
    · rw [Finset.singleton_union, Finset.sum_insert h2]
      omega
  have hpvalue : F p = p + 1 := by
    simpa only [pow_one] using
      (show F (p ^ 1) = p + 1 by
        rw [F, Nat.primeFactors_pow p (by norm_num), hp.primeFactors, hp.factorization_pow]
        simp)
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  have hdiv : 2 ∣ p + 1 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  let t := (p + 1) / 2
  have hdecomp : 2 * t = p + 1 := by
    dsimp [t]
    rw [mul_comm]
    exact Nat.div_mul_cancel hdiv
  have ht2 : 2 ≤ t := by omega
  calc
    F (F p) = F (p + 1) := by rw [hpvalue]
    _ = F (2 * t) := by rw [hdecomp]
    _ ≤ F t + 3 := F_two_mul_le t (by omega)
    _ ≤ (t + 1) + 3 := Nat.add_le_add_right (F_upper t ht2) 3
    _ < p := by omega

/-- Ianakiev's A008474 iteration conjecture. -/
theorem ianakiev_a008474 : ∀ m : ℕ, 4 < m → ∃ t : ℕ, F^[t] m = 5 := by
  have hpow : ∀ p e : ℕ, p.Prime → 0 < e → F (p ^ e) = p + e := by
    intro p e hp he
    rw [F, Nat.primeFactors_pow p he.ne', hp.primeFactors, hp.factorization_pow]
    simp
  have hmul : ∀ a b : ℕ, a.Coprime b → 1 < a → 1 < b →
      F (a * b) = F a + F b := by
    intro a b hab ha hb
    rw [F, F, F, hab.primeFactors_mul,
      Nat.factorization_mul (by omega) (by omega)]
    rw [Finset.sum_union hab.disjoint_primeFactors]
    apply congrArg₂ (fun x y => x + y)
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Finsupp.add_apply]
      have hnot : ¬p ∣ b := fun hpb =>
        (Nat.prime_of_mem_primeFactors hp).ne_one
          (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) hpb)
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Finsupp.add_apply]
      have hnot : ¬p ∣ a := fun hpa =>
        (Nat.prime_of_mem_primeFactors hp).ne_one
          (Nat.eq_one_of_dvd_coprimes hab hpa (Nat.dvd_of_mem_primeFactors hp))
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
  have hF6 : F 6 = 7 := by
    calc
      F 6 = F (2 * 3) := by norm_num
      _ = F 2 + F 3 := hmul 2 3 (by decide) (by norm_num) (by norm_num)
      _ = 7 := by rw [show F 2 = 3 by simpa using hpow 2 1 Nat.prime_two (by norm_num),
        show F 3 = 4 by simpa using hpow 3 1 Nat.prime_three (by norm_num)]
  have hF7 : F 7 = 8 := by
    simpa using hpow 7 1 (by decide) (by norm_num)
  have hF8 : F 8 = 5 := by
    simpa using hpow 2 3 Nat.prime_two (by norm_num)
  intro m hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm5 : m = 5
      · subst m
        exact ⟨0, rfl⟩
      by_cases hm6 : m = 6
      · subst m
        refine ⟨3, ?_⟩
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
          hF6, hF7, hF8]
      have hm7 : 7 ≤ m := by omega
      by_cases hp : m.Prime
      · by_cases hp11 : 11 ≤ m
        · have hdesc := F_prime_two_step_lt m hp hp11
          have hFm5 := F_lower m (by omega)
          have hFFm5 := F_lower (F m) hFm5
          obtain ⟨t, ht⟩ := ih (F (F m)) hdesc (by omega)
          refine ⟨t + 2, ?_⟩
          rw [Function.iterate_add_apply]
          simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using ht
        · have hm8 : m ≠ 8 := by
            intro h
            subst m
            exact (by decide : ¬Nat.Prime 8) hp
          have hm9 : m ≠ 9 := by
            intro h
            subst m
            exact (by decide : ¬Nat.Prime 9) hp
          have hm10 : m ≠ 10 := by
            intro h
            subst m
            exact (by decide : ¬Nat.Prime 10) hp
          have hmEq : m = 7 := by omega
          subst m
          refine ⟨2, ?_⟩
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hF7, hF8]
      · have hdesc := F_composite_lt m hm hp hm6
        have hFm5 := F_lower m (by omega)
        obtain ⟨t, ht⟩ := ih (F m) hdesc (by omega)
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_add_apply]
        simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using ht

#print axioms ianakiev_a008474

end D5.S3.Factorization.IanakievPrimeExponentSumIterationReachesFive
