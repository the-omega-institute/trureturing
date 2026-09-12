/- GID: D5/S3/Factorization/LehmerTotientDichotomy
   generality: G
   mirror-B: D5/B/S3/Factorization/LehmerTotientDichotomy
   mirror-E: none(waiver:symbolic-number-theoretic-structure)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Carmichael]
   utility: none
   digest: Six component consequences of Lehmer's totient divisibility condition. -/

/- Library-search audit (2026-09-11, pinned Mathlib v4.33.0): searches for exact
   statements about prime-square divisibility of a totient, the Lehmer condition,
   and the three-factor bound found no direct upstream theorem. The 4.83 search
   found `Nat.totient_eq_div_primeFactors_mul` and
   `Nat.prod_primeFactors_of_squarefree`, but their composition still requires
   the squarefree cancellation argument and is not an exact upstream hit.

   The six declarations are repository-derived content proofs. Their arguments
   repeat the corresponding private component proofs in
   D5/S3/Arith/Congruence/LehmerTotientStructure; the 4.87 helper there is on an
   arbitrary Finset, while this module states the specialization to n.primeFactors.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace D5.S3.Factorization.LehmerTotientDichotomy

/-- A repeated prime factor contributes that prime to the totient. -/
theorem prime_dvd_totient_of_prime_sq_dvd {p n : ℕ} (hp : p.Prime)
    (hpn : p ^ 2 ∣ n) : p ∣ n.totient := by
  have htot : (p ^ 2).totient ∣ n.totient := Nat.totient_dvd_of_dvd hpn
  have hp_sq : p ∣ (p ^ 2).totient := by
    rw [show 2 = 1 + 1 by omega, Nat.totient_prime_pow_succ hp]
    simp
  exact hp_sq.trans htot

/-- The Lehmer divisibility condition rules out repeated prime factors. -/
theorem squarefree_of_totient_dvd_sub_one {n : ℕ} (hn : 1 < n)
    (hphi : n.totient ∣ n - 1) : Squarefree n := by
  refine Nat.squarefree_iff_prime_squarefree.mpr fun p hp hp_sq_dvd ↦ ?_
  have hp_dvd_n : p ∣ n := (p.dvd_mul_left p).trans hp_sq_dvd
  have hp_dvd_pred : p ∣ n - 1 :=
    (prime_dvd_totient_of_prime_sq_dvd hp (by simpa [pow_two] using hp_sq_dvd)).trans hphi
  exact hp.not_dvd_one <|
    (Nat.dvd_sub_iff_right (by omega) hp_dvd_n).mp hp_dvd_pred

/-- Euler's totient is the product of predecessor factors for a squarefree number. -/
theorem totient_eq_primeFactors_sub_one_prod {n : ℕ} (hn : n ≠ 0)
    (hsq : Squarefree n) :
    n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hsq,
    Nat.div_self hn.bot_lt, one_mul]

/-- A composite Lehmer candidate is odd. -/
theorem odd_of_totient_dvd_sub_one {n : ℕ} (hn : 1 < n)
    (hnp : ¬ n.Prime) (hphi : n.totient ∣ n - 1) : Odd n := by
  by_contra hodd
  have heven_n : Even n := Nat.not_odd_iff_even.mp hodd
  have hn_ne_two : n ≠ 2 := by
    intro h
    exact hnp (h ▸ Nat.prime_two)
  have hn_three : 2 < n := by omega
  have heven_phi : Even n.totient := Nat.totient_even hn_three
  have htwo_phi : 2 ∣ n.totient := even_iff_two_dvd.mp heven_phi
  have htwo_pred : 2 ∣ n - 1 := htwo_phi.trans hphi
  have heven_pred : Even (n - 1) := even_iff_two_dvd.mpr htwo_pred
  obtain ⟨a, ha⟩ := heven_n
  obtain ⟨b, hb⟩ := heven_pred
  omega

private theorem two_pow_card_dvd_prod_sub_one (s : Finset ℕ)
    (heven : ∀ p ∈ s, 2 ∣ p - 1) :
    2 ^ s.card ∣ ∏ p ∈ s, (p - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.card_insert_of_notMem hp, pow_succ', Finset.prod_insert hp]
      exact Nat.mul_dvd_mul (heven p (Finset.mem_insert_self p s))
        (ih fun q hq ↦ heven q (Finset.mem_insert_of_mem hq))

/-- The prime-factor predecessor product supplies the two-adic divisor. -/
theorem two_pow_primeFactors_card_dvd_sub_one {n : ℕ} (hn : 1 < n)
    (hphi : n.totient ∣ n - 1) (hnp : ¬ n.Prime) :
    2 ^ n.primeFactors.card ∣ n - 1 := by
  have hodd := odd_of_totient_dvd_sub_one hn hnp hphi
  have hsq := squarefree_of_totient_dvd_sub_one hn hphi
  have hprod : (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 := by
    rw [← totient_eq_primeFactors_sub_one_prod hsq.ne_zero hsq]
    exact hphi
  have htwo_prod : 2 ^ n.primeFactors.card ∣
      ∏ p ∈ n.primeFactors, (p - 1) := by
    apply two_pow_card_dvd_prod_sub_one
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_ne_two := hodd.ne_two_of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    exact even_iff_two_dvd.mp (hp_prime.even_sub_one hp_ne_two)
  exact htwo_prod.trans hprod

private theorem three_le_primeFactors_card_of_structure {n : ℕ} (hn : 1 < n)
    (hnp : ¬ n.Prime) (hodd : Odd n) (hsq : Squarefree n)
    (hprod : (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1) :
    3 ≤ n.primeFactors.card := by
  by_contra hcard
  have hle : n.primeFactors.card ≤ 2 := by omega
  interval_cases hc : n.primeFactors.card
  · have : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
    simpa [Finset.card_eq_zero.mp hc] using this
  · have hpow : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr hc
    exact hnp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsq, hpow⟩)
  · obtain ⟨p, q, hpq, hfac⟩ := Finset.card_eq_two.mp hc
    have hp_mem : p ∈ n.primeFactors := by rw [hfac]; simp
    have hq_mem : q ∈ n.primeFactors := by rw [hfac]; simp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hp_odd : Odd p := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
    have hq_odd : Odd q := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq_mem)
    have hp_three : 3 ≤ p := hp_prime.odd_iff.mp hp_odd
    have hq_three : 3 ≤ q := hq_prime.odd_iff.mp hq_odd
    have hn_eq : p * q = n := by
      simpa [hfac, hpq] using Nat.prod_primeFactors_of_squarefree hsq
    have hpq_dvd_n : (p - 1) * (q - 1) ∣ n - 1 := by
      simpa [hfac, hpq] using hprod
    have hpq_dvd : (p - 1) * (q - 1) ∣ p * q - 1 := by
      rwa [hn_eq]
    let a := p - 1
    let b := q - 1
    have hp_eq : p = a + 1 := by dsimp [a]; omega
    have hq_eq : q = b + 1 := by dsimp [b]; omega
    have hab_dvd_total : a * b ∣ a * b + (a + b) := by
      simpa [hp_eq, hq_eq, Nat.add_mul, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hpq_dvd
    have hab_dvd_sum : a * b ∣ a + b := by
      apply (Nat.dvd_add_iff_left (dvd_refl (a * b))).mpr
      simpa [Nat.add_comm] using hab_dvd_total
    have ha_two : 2 ≤ a := by dsimp [a]; omega
    have hb_two : 2 ≤ b := by dsimp [b]; omega
    have hab_pos : 0 < a + b := by omega
    have hab_lt : a + b < a * b := by
      rcases lt_or_gt_of_ne hpq with hp_lt | hq_lt
      · have hq_five : 5 ≤ q := by
          obtain ⟨k, hk⟩ := hq_odd
          omega
        have hb_four : 4 ≤ b := by dsimp [b]; omega
        nlinarith [Nat.mul_le_mul (show 1 ≤ a - 1 by omega)
          (show 3 ≤ b - 1 by omega)]
      · have hp_five : 5 ≤ p := by
          obtain ⟨k, hk⟩ := hp_odd
          omega
        have ha_four : 4 ≤ a := by dsimp [a]; omega
        nlinarith [Nat.mul_le_mul (show 3 ≤ a - 1 by omega)
          (show 1 ≤ b - 1 by omega)]
    exact (Nat.not_dvd_of_pos_of_lt hab_pos hab_lt) hab_dvd_sum

/-- A composite Lehmer candidate has at least three distinct prime factors. -/
theorem three_le_primeFactors_card {n : ℕ} (hn : 1 < n)
    (hphi : n.totient ∣ n - 1) (hnp : ¬ n.Prime) :
    3 ≤ n.primeFactors.card := by
  have hodd := odd_of_totient_dvd_sub_one hn hnp hphi
  have hsq := squarefree_of_totient_dvd_sub_one hn hphi
  have hprod : (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 := by
    rw [← totient_eq_primeFactors_sub_one_prod hsq.ne_zero hsq]
    exact hphi
  exact three_le_primeFactors_card_of_structure hn hnp hodd hsq hprod

end D5.S3.Factorization.LehmerTotientDichotomy
