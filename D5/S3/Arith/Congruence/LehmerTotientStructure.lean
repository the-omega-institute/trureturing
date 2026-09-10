/- GID: D5/S3/Arith/Congruence/LehmerTotientStructure
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/LehmerTotientStructure
   mirror-E: none(waiver:symbolic-number-theoretic-structure)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Carmichael]
   utility: none
   digest: Lehmer's totient divisibility condition forces the standard composite structure. -/

import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Tactic

/-!
Library-search audit (2026-09-11): pinned Mathlib v4.33.0 at
db584cd6d46c92f209a44c0f1c829460d327499d has the Carmichael arithmetic
function, its divisibility properties, Euler's totient product formula, and
the prime-factor and squarefree APIs used below. Searches for `IsKorselt`,
`Korselt`, `IsCarmichael`, and an equivalent packaged predicate found none.
Mathlib's later `Nat.IsCarmichael` and `Nat.isCarmichael_iff_korselt` were
introduced after this pin and therefore are not imported here.

The main theorem has proof_shape: content and admission_basis: escape-witness.
Its escape witnesses are the live composite-branch derivations
`squarefree_of_totient_dvd_sub_one` and `three_le_primeFactors_card`, which
retain respectively the prime-square obstruction and the two-prime boundary.
The two final theorems have proof_shape: bind-only and escape_witness: none.
Their directed consumer-to-prerequisite edges are:
* `primeFactors_sub_one_prod_dvd_sub_one` -> `lehmer_totient_structure`;
* `isKorselt_of_totient_dvd_sub_one` -> `lehmer_totient_structure`.

Every declaration is symbolic over arbitrary natural numbers. It performs no
bounded enumeration, numerical certification, or checker computation, which
is the justification for utility none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace D5.S3.Arith.Congruence.LehmerTotientStructure

/-- The squarefree Korselt divisibility condition, including primes. -/
def IsKorselt (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1

private theorem odd_of_totient_dvd_sub_one {n : ℕ} (hn : 1 < n)
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

private theorem squarefree_of_totient_dvd_sub_one {n : ℕ} (hn : 1 < n)
    (hodd : Odd n) (hphi : n.totient ∣ n - 1) : Squarefree n := by
  refine Nat.squarefree_iff_prime_squarefree.mpr fun p hp hp_sq_dvd ↦ ?_
  have hp_dvd_n : p ∣ n := (p.dvd_mul_left p).trans hp_sq_dvd
  have hp_pow_sq_dvd : p ^ 2 ∣ n := by simpa [pow_two] using hp_sq_dvd
  have hp_ne_two : p ≠ 2 := hodd.ne_two_of_dvd_nat hp_dvd_n
  have hp_dvd_totient_sq : p ∣ (p ^ 2).totient := by
    rw [show 2 = 1 + 1 by omega, Nat.totient_prime_pow_succ hp]
    simp
  have hp_dvd_carmichael_sq : p ∣ carmichael (p ^ 2) := by
    rw [carmichael_pow_of_prime_ne_two 2 hp hp_ne_two]
    exact hp_dvd_totient_sq
  have hp_dvd_pred : p ∣ n - 1 :=
    hp_dvd_carmichael_sq.trans
      ((carmichael_dvd hp_pow_sq_dvd).trans ((carmichael_dvd_totient n).trans hphi))
  exact hp.not_dvd_one <|
    (Nat.dvd_sub_iff_right (by omega) hp_dvd_n).mp hp_dvd_pred

private theorem totient_eq_primeFactors_sub_one_prod {n : ℕ} (hsq : Squarefree n) :
    n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hsq,
    Nat.div_self hsq.ne_zero.bot_lt, one_mul]

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

private theorem three_le_primeFactors_card {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    (hodd : Odd n) (hsq : Squarefree n)
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

/-- Lehmer's totient divisibility condition gives primality or the full standard
odd, squarefree, Korselt, product, two-adic, and three-factor structure. -/
theorem lehmer_totient_structure (n : ℕ) (hn : 1 < n) (hphi : n.totient ∣ n - 1) :
    n.Prime ∨
      (Odd n ∧ Squarefree n ∧ IsKorselt n ∧
        (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 ∧
        2 ^ n.primeFactors.card ∣ n - 1 ∧
        3 ≤ n.primeFactors.card) := by
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  · right
    have hodd := odd_of_totient_dvd_sub_one hn hprime hphi
    have hsq := squarefree_of_totient_dvd_sub_one hn hodd hphi
    have hprod : (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 := by
      rw [← totient_eq_primeFactors_sub_one_prod hsq]
      exact hphi
    have hkorselt : IsKorselt n := by
      refine ⟨hsq, fun p hp ↦ ?_⟩
      exact (Finset.dvd_prod_of_mem (fun q : ℕ ↦ q - 1) hp).trans hprod
    have htwo_prod : 2 ^ n.primeFactors.card ∣
        ∏ p ∈ n.primeFactors, (p - 1) := by
      apply two_pow_card_dvd_prod_sub_one
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_ne_two := hodd.ne_two_of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
      exact even_iff_two_dvd.mp (hp_prime.even_sub_one hp_ne_two)
    exact ⟨hodd, hsq, hkorselt, hprod, htwo_prod.trans hprod,
      three_le_primeFactors_card hn hprime hodd hsq hprod⟩

/-- Under Lehmer's condition, the product of one less than every prime factor
divides the predecessor. This is the named companion for theorem 4.85. -/
theorem primeFactors_sub_one_prod_dvd_sub_one (n : ℕ) (hn : 1 < n)
    (hphi : n.totient ∣ n - 1) :
    (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 := by
  rcases lehmer_totient_structure n hn hphi with hp | hcomp
  · simpa [hp.primeFactors]
  · exact hcomp.2.2.2.1

/-- Under Lehmer's condition, the number satisfies the squarefree Korselt
divisibility condition. This is the named companion for theorem 4.86. -/
theorem isKorselt_of_totient_dvd_sub_one (n : ℕ) (hn : 1 < n)
    (hphi : n.totient ∣ n - 1) : IsKorselt n := by
  rcases lehmer_totient_structure n hn hphi with hp | hcomp
  · refine ⟨hp.squarefree, ?_⟩
    intro p hp_mem
    have hp_eq : p = n := by simpa [hp.primeFactors] using hp_mem
    simpa [hp_eq]
  · exact hcomp.2.2.1

#print axioms lehmer_totient_structure
#print axioms primeFactors_sub_one_prod_dvd_sub_one
#print axioms isKorselt_of_totient_dvd_sub_one

end D5.S3.Arith.Congruence.LehmerTotientStructure
