/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/Fermat
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Fermat]
   utility: none
   digest: Divisor sum bounds for odd integers with power-of-two totients. -/

import D5.S3.Factorization.LehmerTotientDichotomy
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree

namespace D5.S3.Arith.MakowskiSchinzel

open Finset
open scoped ArithmeticFunction.sigma

private theorem two_geom_sum (a : ℕ) :
    (∑ i ∈ range a, 2 ^ i) + 1 = 2 ^ a := by
  simpa using geom_sum_mul_add (1 : ℕ) a

/-- A finite selection of Fermat numbers is bounded using its exact exponent sum. -/
theorem fermat_product_bound (I : Finset ℕ) :
    (∏ a ∈ I, Nat.fermatNumber a) + 1 ≤ 2 ^ ((∑ a ∈ I, 2 ^ a) + 1) ∧
      ((∏ a ∈ I, Nat.fermatNumber a) + 1 = 2 ^ ((∑ a ∈ I, 2 ^ a) + 1) ↔
        I = range I.card) := by
  induction I using Finset.induction_on_max with
  | empty => simp
  | insert a I ha ih =>
    have hnot : a ∉ I := fun h => (ha a h).false
    have hsub : I ⊆ range a := fun i hi => mem_range.mpr (ha i hi)
    have hsum : (∑ i ∈ I, 2 ^ i) + 1 ≤ 2 ^ a := by
      have hle := sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => Nat.zero_le (2 ^ i))
      have hgeom := two_geom_sum a
      omega
    let P := ∏ i ∈ I, Nat.fermatNumber i
    let R := 2 ^ ((∑ i ∈ I, 2 ^ i) + 1)
    let F := 2 ^ 2 ^ a
    have hPR : P + 1 ≤ R := ih.1
    have hRF : R ≤ F := Nat.pow_le_pow_right (by decide : 0 < 2) hsum
    have hmul : F * (P + 1) ≤ F * R := Nat.mul_le_mul_left F hPR
    have hrewrite : 2 ^ (2 ^ a + (∑ i ∈ I, 2 ^ i) + 1) = R * F := by
      dsimp [R, F]
      rw [show 2 ^ a + (∑ i ∈ I, 2 ^ i) + 1 =
        ((∑ i ∈ I, 2 ^ i) + 1) + 2 ^ a by omega, pow_add]
    constructor
    · rw [prod_insert hnot, sum_insert hnot, Nat.fermatNumber, hrewrite]
      change (F + 1) * P + 1 ≤ R * F
      nlinarith
    · constructor
      · intro heq
        rw [prod_insert hnot, sum_insert hnot, Nat.fermatNumber, hrewrite] at heq
        change (F + 1) * P + 1 = R * F at heq
        have hPF : P + 1 = F := by nlinarith
        have hRFeq : R = F := by omega
        have hPReq : P + 1 = R := by omega
        have hI : I = range I.card := ih.2.mp hPReq
        have hpower : 2 ^ ((∑ i ∈ I, 2 ^ i) + 1) = 2 ^ 2 ^ a := hRFeq
        have hexp := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hpower
        rw [hI, two_geom_sum] at hexp
        have hcard := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hexp
        rw [card_insert_of_notMem hnot, hcard, hI, hcard, range_add_one]
      · intro hI
        let k := (insert a I).card
        have hset : insert a I = range k := hI
        rw [hset, Nat.prod_fermatNumber, two_geom_sum, Nat.fermatNumber]
        have htwo : 2 ≤ 2 ^ 2 ^ k := Nat.le_self_pow (by positivity : 2 ^ k ≠ 0) 2
        omega

private theorem squarefree_of_odd_totient_two_pow {n E : ℕ} (hn : Odd n)
    (hphi : n.totient = 2 ^ E) : Squarefree n := by
  refine Nat.squarefree_iff_prime_squarefree.mpr ?_
  intro p hp hsq
  have hpdvd : p ∣ n := (dvd_mul_right p p).trans hsq
  have hpow : p ∣ 2 ^ E := by
    rw [← hphi]
    exact D5.S3.Factorization.LehmerTotientDichotomy.prime_dvd_totient_of_prime_sq_dvd
      hp (by simpa only [pow_two] using hsq)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow hpow)
  exact hn.not_two_dvd_nat (hp2 ▸ hpdvd)

/-- An odd integer whose totient is a power of two satisfies the strong divisor-sum bound.
No restriction to the currently known Fermat primes is imposed. -/
theorem odd_le_sigma_totient_of_two_pow {n E : ℕ} (hn : Odd n)
    (hphi : n.totient = 2 ^ E) : n ≤ σ 1 n.totient := by
  classical
  have hsq := squarefree_of_odd_totient_two_pow hn hphi
  let Q := n.primeFactors
  have hfermat (p : ℕ) (hp : p ∈ Q) : ∃ a, p = Nat.fermatNumber a := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hsub : p - 1 ∣ 2 ^ E := by
      rw [← hphi, ← Nat.totient_prime hprime]
      exact Nat.totient_dvd_of_dvd hpdvd
    obtain ⟨k, _, hpk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hsub
    have hpe : p = 2 ^ k + 1 := by have := hprime.two_le; omega
    have hk : k ≠ 0 := by
      intro hk
      have hp2 : p = 2 := by simpa [hk] using hpe
      exact hn.not_two_dvd_nat (hp2 ▸ hpdvd)
    have hprime' : (2 ^ k + 1).Prime := hpe ▸ hprime
    obtain ⟨a, ha⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) hk hprime'
    exact ⟨a, by simpa [Nat.fermatNumber, ha] using hpe⟩
  let f : ℕ → ℕ := fun p =>
    if hp : p ∈ Q then Classical.choose (hfermat p hp) else 0
  have hf (p : ℕ) (hp : p ∈ Q) : p = Nat.fermatNumber (f p) := by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hfermat p hp)
  have hinj : Set.InjOn f Q := by
    intro p hp q hq heq
    rw [hf p hp, hf q hq, heq]
  let I := Q.image f
  have hprod : (∏ a ∈ I, Nat.fermatNumber a) = n := by
    change (∏ a ∈ Q.image f, Nat.fermatNumber a) = n
    rw [prod_image hinj]
    calc
      _ = ∏ p ∈ Q, p := prod_congr rfl fun p hp => (hf p hp).symm
      _ = n := Nat.prod_primeFactors_of_squarefree hsq
  have hphiProd : n.totient = ∏ p ∈ Q, (p - 1) :=
    D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hsq.ne_zero hsq
  have hIphi : 2 ^ (∑ a ∈ I, 2 ^ a) = n.totient := by
    rw [← prod_pow_eq_pow_sum I (fun a => 2 ^ a) 2]
    change (∏ a ∈ Q.image f, 2 ^ 2 ^ a) = n.totient
    rw [prod_image hinj, hphiProd]
    apply prod_congr rfl
    intro p hp
    have hpEq := congrArg (fun z : ℕ => z - 1) (hf p hp)
    simpa only [Nat.fermatNumber, Nat.add_sub_cancel] using hpEq.symm
  have hsigma : σ 1 n.totient + 1 = 2 ^ ((∑ a ∈ I, 2 ^ a) + 1) := by
    rw [← hIphi, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    exact two_geom_sum _
  have hbound := (fermat_product_bound I).1
  rw [hprod, ← hsigma] at hbound
  omega

#print axioms fermat_product_bound
#print axioms odd_le_sigma_totient_of_two_pow

end D5.S3.Arith.MakowskiSchinzel
