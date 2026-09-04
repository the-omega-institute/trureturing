/- GID: D5/S3/Factorization/LehmerTotientDichotomy
   generality: G
   mirror-B: D5/B/S3/Factorization/LehmerTotientDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lehmer's totient divisibility condition yields a prime/composite structural dichotomy. -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.PrimePow

open scoped BigOperators

namespace D5.S3.Factorization.LehmerTotientDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The squarefree divisibility condition in Korselt's criterion. -/
def IsKorselt (n : Nat) : Prop :=
  Squarefree n ∧ ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1

/-- A repeated prime factor contributes that prime to Euler's totient. -/
theorem prime_dvd_totient_of_sq_dvd {p n : Nat} (hp : p.Prime) (h : p ^ 2 ∣ n) :
    p ∣ Nat.totient n := by
  apply dvd_trans ?_ (Nat.totient_dvd_of_dvd h)
  rw [Nat.totient_prime_pow hp (by norm_num)]
  simp

/-- Lehmer's divisibility condition excludes every repeated prime factor. -/
theorem squarefree_of_totient_dvd_pred {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpsq
  have hp_totient : p ∣ Nat.totient n :=
    prime_dvd_totient_of_sq_dvd hp (by simpa [pow_two] using hpsq)
  have hp_pred : p ∣ n - 1 := hp_totient.trans h
  have hp_n : p ∣ n := (dvd_mul_right p p).trans hpsq
  have hp_one : p ∣ n - (n - 1) := Nat.dvd_sub hp_n hp_pred
  have hone : n - (n - 1) = 1 := by omega
  exact hp.not_dvd_one (hone ▸ hp_one)

/-- For a nonzero squarefree number, the totient is the product of `p - 1`. -/
theorem totient_eq_prod_primeFactors_sub_one_of_squarefree {n : Nat}
    (hn : n ≠ 0) (hsq : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hsq]
  rw [Nat.div_self (Nat.pos_of_ne_zero hn), one_mul]

/-- A nonprime number satisfying Lehmer's divisibility condition is odd. -/
theorem odd_of_totient_dvd_pred_of_not_prime {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) (hnPrime : ¬n.Prime) : Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro hnEven
  have hn2 : 2 < n := by
    have hn_ne_two : n ≠ 2 := fun hn_eq => hnPrime (hn_eq ▸ Nat.prime_two)
    omega
  have htwo_totient : 2 ∣ Nat.totient n :=
    even_iff_two_dvd.mp (Nat.totient_even hn2)
  have htwo_pred : 2 ∣ n - 1 := htwo_totient.trans h
  have htwo_one : 2 ∣ n - (n - 1) :=
    Nat.dvd_sub (even_iff_two_dvd.mp hnEven) htwo_pred
  have hone : n - (n - 1) = 1 := by omega
  exact Nat.prime_two.not_dvd_one (hone ▸ htwo_one)

/-- The product form of the totient inherits Lehmer's divisibility condition. -/
theorem prod_primeFactors_sub_one_dvd_pred {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) :
    (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 := by
  have hn0 : n ≠ 0 := by omega
  rw [← totient_eq_prod_primeFactors_sub_one_of_squarefree hn0
    (squarefree_of_totient_dvd_pred hn h)]
  exact h

/-- Lehmer's divisibility condition implies the local Korselt condition. -/
theorem isKorselt_of_totient_dvd_pred {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) : IsKorselt n := by
  refine ⟨squarefree_of_totient_dvd_pred hn h, fun p hp => ?_⟩
  exact (Finset.dvd_prod_of_mem (fun q => q - 1) hp).trans
    (prod_primeFactors_sub_one_dvd_pred hn h)

/-- In the nonprime branch, every prime factor contributes a factor of two. -/
theorem two_pow_card_primeFactors_dvd_pred {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) (hnPrime : ¬n.Prime) :
    2 ^ n.primeFactors.card ∣ n - 1 := by
  have hodd : Odd n := odd_of_totient_dvd_pred_of_not_prime hn h hnPrime
  have htwo_prod :
      (∏ _p ∈ n.primeFactors, 2) ∣ ∏ p ∈ n.primeFactors, (p - 1) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_ne_two : p ≠ 2 := by
      intro hp_eq
      have htwo_n : 2 ∣ n := hp_eq ▸ Nat.dvd_of_mem_primeFactors hp
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo_n)
    rcases hpPrime.odd_of_ne_two hp_ne_two with ⟨k, hk⟩
    use k
    omega
  simpa using htwo_prod.trans (prod_primeFactors_sub_one_dvd_pred hn h)

/-- A composite number satisfying Lehmer's divisibility condition has at least three prime factors. -/
theorem three_le_card_primeFactors {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) (hnPrime : ¬n.Prime) :
    3 ≤ n.primeFactors.card := by
  have hnTwo : 2 ≤ n := by omega
  have hsq : Squarefree n := squarefree_of_totient_dvd_pred hn h
  have hodd : Odd n := odd_of_totient_dvd_pred_of_not_prime hn h hnPrime
  have hnotPrimePow : ¬IsPrimePow n := by
    intro hpp
    exact hnPrime (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsq, hpp⟩)
  have hnontrivial : n.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hnTwo).mp hnotPrimePow
  by_contra hcardThree
  have hcardTwo : n.primeFactors.card = 2 := by
    have hone : 1 < n.primeFactors.card :=
      Finset.one_lt_card_iff_nontrivial.mpr hnontrivial
    omega
  obtain ⟨p, q, hpq, hpFactors⟩ := Finset.card_eq_two.mp hcardTwo
  have hpMem : p ∈ n.primeFactors := by simp [hpFactors]
  have hqMem : q ∈ n.primeFactors := by simp [hpFactors]
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqMem
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    have htwo_n : 2 ∣ n := hp_eq ▸ Nat.dvd_of_mem_primeFactors hpMem
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo_n)
  have hq_ne_two : q ≠ 2 := by
    intro hq_eq
    have htwo_n : 2 ∣ n := hq_eq ▸ Nat.dvd_of_mem_primeFactors hqMem
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo_n)
  have hpThree : 3 ≤ p := hpPrime.odd_iff.mp (hpPrime.odd_of_ne_two hp_ne_two)
  have hqThree : 3 ≤ q := hqPrime.odd_iff.mp (hqPrime.odd_of_ne_two hq_ne_two)
  have hnProd : p * q = n := by
    simpa [hpFactors, hpq] using Nat.prod_primeFactors_of_squarefree hsq
  have hprodDvd : (p - 1) * (q - 1) ∣ n - 1 := by
    simpa [hpFactors, hpq] using prod_primeFactors_sub_one_dvd_pred hn h
  have hbound : n - 1 < 2 * ((p - 1) * (q - 1)) := by
    have hpEq : p = (p - 1) + 1 := by omega
    have hqEq : q = (q - 1) + 1 := by omega
    have hnEq : n = (n - 1) + 1 := by omega
    rw [hpEq, hqEq] at hnProd hpq
    rw [hnEq] at hnProd
    rcases lt_or_gt_of_ne hpq with hpLt | hqLt <;> nlinarith
  rcases hprodDvd with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra hkZero
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
    omega
  have hkLt : k < 2 := by
    by_contra hkTwo
    have hkTwo' : 2 ≤ k := by omega
    have hle : 2 * ((p - 1) * (q - 1)) ≤ n - 1 := by
      calc
        2 * ((p - 1) * (q - 1)) ≤ (p - 1) * (q - 1) * k := by
          nlinarith
        _ = n - 1 := hk.symm
    exact (Nat.not_lt_of_ge hle) hbound
  have hkOne : k = 1 := by omega
  rw [hkOne, mul_one] at hk
  have hpEq : p = (p - 1) + 1 := by omega
  have hqEq : q = (q - 1) + 1 := by omega
  have hnEq : n = (n - 1) + 1 := by omega
  rw [hpEq, hqEq] at hnProd
  rw [hnEq] at hnProd
  nlinarith

/-- A number satisfying Lehmer's divisibility condition is prime, or it has the full
composite structural package. -/
theorem totient_dvd_pred_dichotomy {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) :
    n.Prime ∨
      (Odd n ∧ Squarefree n ∧ IsKorselt n ∧
        (∏ p ∈ n.primeFactors, (p - 1)) ∣ n - 1 ∧
        2 ^ n.primeFactors.card ∣ n - 1 ∧
        3 ≤ n.primeFactors.card) := by
  by_cases hnPrime : n.Prime
  · exact Or.inl hnPrime
  · exact Or.inr ⟨
      odd_of_totient_dvd_pred_of_not_prime hn h hnPrime,
      squarefree_of_totient_dvd_pred hn h,
      isKorselt_of_totient_dvd_pred hn h,
      prod_primeFactors_sub_one_dvd_pred hn h,
      two_pow_card_primeFactors_dvd_pred hn h hnPrime,
      three_le_card_primeFactors hn h hnPrime⟩

example : 1 < 2 ∧ Nat.totient 2 ∣ 2 - 1 := by decide

example : 1 < 7 ∧ Nat.totient 7 ∣ 7 - 1 := by decide

example :
    (7 : Nat).Prime ∨
      (Odd 7 ∧ Squarefree 7 ∧ IsKorselt 7 ∧
        (∏ p ∈ (7 : Nat).primeFactors, (p - 1)) ∣ 7 - 1 ∧
        2 ^ (7 : Nat).primeFactors.card ∣ 7 - 1 ∧
        3 ≤ (7 : Nat).primeFactors.card) := by
  exact Or.inl (by decide)

example : ¬(Nat.totient 15 ∣ 15 - 1) := by decide

end D5.S3.Factorization.LehmerTotientDichotomy
