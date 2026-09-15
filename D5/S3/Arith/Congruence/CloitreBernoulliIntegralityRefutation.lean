/- GID: D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Bernoulli]
   utility: none
   digest: Cloitre's A090825 integrality conjecture fails at n = 833. -/

import Mathlib.NumberTheory.Bernoulli

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.CloitreBernoulliIntegralityRefutation

/-- The rational expression defining OEIS A090825. Mathlib's `bernoulli`
uses the convention `B₁ = -1/2`; the index here is always even. -/
def F (n : ℕ) : ℚ :=
  (3 / 2) * (1 / (n : ℚ)) * (2 * n + 1) * (3 ^ n + 1) * bernoulli (2 * n)

/-- The prime sequence A053176: primes `p` for which `2p+1` is composite. -/
def A053176 (p : ℕ) : Prop :=
  Nat.Prime p ∧ ¬ Nat.Prime (2 * p + 1)

/-- Cloitre's 2004 conjecture in OEIS A090825. -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → ¬ Nat.Prime n →
    (∀ p : ℕ, Nat.Prime p → p ∣ n → A053176 p) →
      ∃ z : ℤ, F n = z

/-- The von Staudt-Clausen theorem at index `1666` refutes the conjecture. -/
theorem result : ¬ claim := by
  intro hclaim
  unfold claim at hclaim
  have hpremise : ∀ p : ℕ, Nat.Prime p → p ∣ 833 → A053176 p := by
    intro p hp hpd
    have hprod : p ∣ 7 * (7 * 17) := by
      norm_num at hpd ⊢
      exact hpd
    have hp_eq : p = 7 ∨ p = 17 := by
      rcases hp.dvd_mul.mp hprod with h7 | hrest
      · rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 7)).mp h7 with hp1 | hp7
        · exact (hp.ne_one hp1).elim
        · exact Or.inl hp7
      · rcases hp.dvd_mul.mp hrest with h7 | h17
        · rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 7)).mp h7 with hp1 | hp7
          · exact (hp.ne_one hp1).elim
          · exact Or.inl hp7
        · rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 17)).mp h17 with hp1 | hp17
          · exact (hp.ne_one hp1).elim
          · exact Or.inr hp17
    rcases hp_eq with rfl | rfl <;> unfold A053176 <;> decide +kernel
  obtain ⟨z, hFz⟩ :=
    hclaim 833 (by norm_num) (by decide +kernel) hpremise

  have hfilter :
      (Finset.range 1668).filter (fun p => p.Prime ∧ (p - 1) ∣ 1666) =
        {2, 3, 239, 1667} := by
    have hdivisors :
        Nat.divisors 1666 = {1, 2, 7, 14, 17, 34, 49, 98, 119, 238, 833, 1666} := by
      decide +kernel
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hp, hdvd⟩
      have hmem : p - 1 ∈ Nat.divisors 1666 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      rw [hdivisors] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · have hp_eq : p = 8 := by omega
        subst p
        exact ((show ¬ Nat.Prime 8 by decide +kernel) hp).elim
      · have hp_eq : p = 15 := by omega
        subst p
        exact ((show ¬ Nat.Prime 15 by decide +kernel) hp).elim
      · have hp_eq : p = 18 := by omega
        subst p
        exact ((show ¬ Nat.Prime 18 by decide +kernel) hp).elim
      · have hp_eq : p = 35 := by omega
        subst p
        exact ((show ¬ Nat.Prime 35 by decide +kernel) hp).elim
      · have hp_eq : p = 50 := by omega
        subst p
        exact ((show ¬ Nat.Prime 50 by decide +kernel) hp).elim
      · have hp_eq : p = 99 := by omega
        subst p
        exact ((show ¬ Nat.Prime 99 by decide +kernel) hp).elim
      · have hp_eq : p = 120 := by omega
        subst p
        exact ((show ¬ Nat.Prime 120 by decide +kernel) hp).elim
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · have hp_eq : p = 834 := by omega
        subst p
        exact ((show ¬ Nat.Prime 834 by decide +kernel) hp).elim
      · exact Or.inr (Or.inr (Or.inr (by omega)))
    · rintro (rfl | rfl | rfl | rfl) <;> decide +kernel
  have hsum :
      (∑ p ∈ Finset.range 1668 with p.Prime ∧ (p - 1) ∣ 1666, (1 : ℚ) / p) =
        1 / 2 + 1 / 3 + 1 / 239 + 1 / 1667 := by
    rw [hfilter]
    norm_num
  obtain ⟨t, ht⟩ := Bernoulli.vonStaudt_clausen 833
  rw [hsum] at ht
  have hbernoulli :
      bernoulli 1666 =
        -(1 / (239 : ℚ)) + ((t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667)) := by
    linarith

  let _ : Fact (Nat.Prime 239) := ⟨by decide +kernel⟩
  have h239val : padicValRat 239 (-(1 / (239 : ℚ))) = -1 := by
    rw [padicValRat.neg, one_div, padicValRat.inv]
    change -padicValRat 239 ((239 : ℕ) : ℚ) = -1
    rw [padicValRat.of_nat, padicValNat_self]
    norm_num
  have hrest_nonneg :
      0 ≤ padicValRat 239 ((t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667)) := by
    rw [padicValRat_def, Rat.intCast_sub_den]
    norm_num [padicValNat.eq_zero_of_not_dvd]
  have hbernoulli_val : padicValRat 239 (bernoulli 1666) = -1 := by
    rw [hbernoulli]
    by_cases hrest_zero : (t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667) = 0
    · rw [hrest_zero, add_zero]
      exact h239val
    · have hsum_ne :
          -(1 / (239 : ℚ)) + ((t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667)) ≠ 0 := by
        intro hzero
        have hrest_eq :
            (t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667) = -(-(1 / (239 : ℚ))) := by
          linarith
        have hrest_val :
            padicValRat 239 ((t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667)) = -1 := by
          rw [hrest_eq, padicValRat.neg, h239val]
        omega
      have hval_lt :
          padicValRat 239 (-(1 / (239 : ℚ))) <
            padicValRat 239 ((t : ℚ) - (1 / 2 + 1 / 3 + 1 / 1667)) := by
        rw [h239val]
        omega
      exact (padicValRat.add_eq_of_lt hsum_ne (by norm_num) hrest_zero hval_lt).trans h239val
  have hbernoulli_ne : bernoulli 1666 ≠ 0 := by
    intro hzero
    simp [hzero] at hbernoulli_val

  have hpow_not_dvd : ¬239 ∣ 3 ^ 833 + 1 := by
    intro hdvd
    have hzero : ((3 ^ 833 + 1 : ℕ) : ZMod 239) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod 239) 239 _).mpr hdvd
    norm_num only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hzero
    have hpow : (3 : ZMod 239) ^ 833 = 1 := by decide +kernel
    rw [hpow] at hzero
    exact (show (2 : ZMod 239) ≠ 0 by decide +kernel) hzero
  have ha : (3 / 2 : ℚ) ≠ 0 := by norm_num
  have hb : (1 / 833 : ℚ) ≠ 0 := by norm_num
  have hc : (2 * (833 : ℚ) + 1) ≠ 0 := by norm_num
  have hd : ((3 : ℚ) ^ 833 + 1) ≠ 0 := by positivity
  have hva : padicValRat 239 (3 / 2 : ℚ) = 0 := by
    have h3 : padicValRat 239 ((3 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num)]
      norm_num
    have h2 : padicValRat 239 ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num)]
      norm_num
    rw [div_eq_mul_inv, padicValRat.mul (by norm_num) (by norm_num),
      padicValRat.inv]
    change padicValRat 239 ((3 : ℕ) : ℚ) + -padicValRat 239 ((2 : ℕ) : ℚ) = 0
    rw [h3, h2]
    norm_num
  have hvb : padicValRat 239 (1 / 833 : ℚ) = 0 := by
    rw [one_div, padicValRat.inv]
    change -padicValRat 239 ((833 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hvc : padicValRat 239 (2 * (833 : ℚ) + 1) = 0 := by
    rw [show (2 * (833 : ℚ) + 1) = 1667 by norm_num]
    change padicValRat 239 ((1667 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hvd : padicValRat 239 ((3 : ℚ) ^ 833 + 1) = 0 := by
    have hcast :
        (3 : ℚ) ^ 833 + 1 = ((3 ^ 833 + 1 : ℕ) : ℚ) := by
      norm_num only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpow_not_dvd]
    norm_num
  have hcoefficient_ne :
      (3 / 2 : ℚ) * (1 / 833) * (2 * (833 : ℚ) + 1) * ((3 : ℚ) ^ 833 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd
  have hcoefficient_val :
      padicValRat 239
          ((3 / 2 : ℚ) * (1 / 833) * (2 * (833 : ℚ) + 1) * ((3 : ℚ) ^ 833 + 1)) = 0 := by
    rw [padicValRat.mul (mul_ne_zero (mul_ne_zero ha hb) hc) hd,
      padicValRat.mul (mul_ne_zero ha hb) hc, padicValRat.mul ha hb,
      hva, hvb, hvc, hvd]
    norm_num
  have hFval : padicValRat 239 (F 833) = -1 := by
    change padicValRat 239
      (((3 / 2 : ℚ) * (1 / 833) * (2 * (833 : ℚ) + 1) * ((3 : ℚ) ^ 833 + 1)) *
        bernoulli 1666) = -1
    rw [padicValRat.mul hcoefficient_ne hbernoulli_ne, hcoefficient_val, hbernoulli_val]
    norm_num
  have hz_nonneg : 0 ≤ padicValRat 239 (z : ℚ) := by
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg (padicValInt 239 z)
  rw [hFz] at hFval
  omega

#print axioms result

end D5.S3.Arith.Congruence.CloitreBernoulliIntegralityRefutation
