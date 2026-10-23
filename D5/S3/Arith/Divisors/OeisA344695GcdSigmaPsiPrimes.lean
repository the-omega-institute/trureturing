/- GID: D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The prime values of gcd of the divisor sum and Dedekind psi are the odd primes. -/

/-
admission_basis: open-problem-resolution (#18688; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19807
Declaration classification (same-delivery helpers expanded to upstream facts):
  psi, a, claim: proof_shape: bind-only (source definitions); consumers: result and its helpers.
  psi_prod: proof_shape: bind-only; consumer: not_two; Direct frozen dependencies: none.
  geom_mod_one: proof_shape: bind-only; consumer: witness_value; Direct frozen dependencies: none.
  geom_mod_self: proof_shape: bind-only; consumer: witness_value; Direct frozen dependencies: none.
  geom_mod_succ: proof_shape: bind-only; consumers: odd_exp_dvd_sigma, witness_value;
    Direct frozen dependencies: none.
  odd_exp_dvd_sigma: proof_shape: bind-only; consumer: not_two; Direct frozen dependencies: none.
  not_two: proof_shape: bind-only; consumer: result; Direct frozen dependencies: parity below.
  witness_value: proof_shape: bind-only; consumer: result; Direct frozen dependencies: none.
  result: proof_shape: bind-only; Direct frozen dependencies: parity below.
Direct frozen dependencies:
  D5/S3/Arith/KrizekTriangularSquareSigmaParity.sigma_odd_iff_square_or_twice_square
  declaration statement_id: sha256:95aab7cca3af8622c133f3f2b676ee143c6991b94d61476aecaf213c77489dab
The square/nonsquare split uses divisor-sum parity and odd-exponent divisibility.
For an odd prime q, a prime r congruent to 1 modulo q(q+1)(q^2+q+1)
produces n=q^2*r^(q-1); geometric-sum congruences make the gcd exactly q.
All proof steps are upstream instantiation, logical assembly and arithmetic normalization.
Utility is none: no finite enumeration, certified instance, checker or numerical reduction
is declared; the assertions range over arbitrary natural numbers and primes.
The definitions are the expressions in #18688, with the namespace matching this file.
-/

import D5.S3.Arith.KrizekTriangularSquareSigmaParity
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Algebra.BigOperators.ModEq

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes

open ArithmeticFunction

/-- A001615, the Dedekind psi function `n * Product_{p|n, p prime} (1 + 1/p)`, written over `ℕ` as
`(n / Product_{p|n} p) * Product_{p|n} (p + 1)`. -/
def psi (n : ℕ) : ℕ := n / (∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p + 1)

/-- A344695: `a(n) = gcd(sigma(n), psi(n))`. -/
def a (n : ℕ) : ℕ := Nat.gcd (sigma 1 n) (psi n)

/-- A344695 ("Conjecture: the set of primes that appear in the sequence is A065091 (the odd primes)."). -/
def claim : Prop := ∀ q : ℕ, q.Prime → ((∃ n : ℕ, 1 ≤ n ∧ a n = q) ↔ Odd q)

open Finset ArithmeticFunction

private theorem psi_prod {n : ℕ} (hn : n ≠ 0) :
    psi n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) := by
  classical
  have hrad : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp
  have hmul : (∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1)) *
      (∏ p ∈ n.primeFactors, p) = n := by
    calc
      _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        rw [← pow_succ]
        congr 1
        have hz : n.factorization p ≠ 0 := by
          exact Finsupp.mem_support_iff.mp
            (by simpa only [Nat.support_factorization] using hp)
        exact Nat.succ_pred_eq_of_ne_zero hz
      _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm
  have hdiv : n / (∏ p ∈ n.primeFactors, p) =
      ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := by
    exact Nat.div_eq_of_eq_mul_left hrad hmul.symm
  rw [psi, hdiv, Finset.prod_mul_distrib]

private theorem geom_mod_one {r m : ℕ} (hr : Nat.ModEq m r 1) (k : ℕ) :
    Nat.ModEq m (∑ i ∈ range k, r ^ i) k := by
  simpa using Nat.ModEq.sum (s := range k) (fun i _ => hr.pow i)

private theorem geom_mod_self (r k : ℕ) :
    Nat.ModEq r (∑ i ∈ range (k + 1), r ^ i) 1 := by
  simpa only [geom_sum_succ] using
    (Nat.ModEq.modulus_mul_add (m := r) (a := ∑ i ∈ range k, r ^ i) (b := 1))

private theorem geom_mod_succ (r k : ℕ) :
    Nat.ModEq (r + 1) (∑ i ∈ range k, r ^ i) (if Even k then 0 else 1) := by
  have h : Int.ModEq (r + 1) (r : ℤ) (-1) := by
    simpa using (Int.modEq_sub (r : ℤ) (-1))
  have hs := Int.ModEq.sum (s := range k) (fun i _ => h.pow i)
  rw [neg_one_geom_sum] at hs
  exact_mod_cast hs

private theorem odd_exp_dvd_sigma {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors)
    (he : Odd (n.factorization p)) : p + 1 ∣ sigma 1 n := by
  have hd : p + 1 ∣ ∑ i ∈ range (n.factorization p + 1), p ^ i := by
    have h := geom_mod_succ p (n.factorization p + 1)
    have hev : Even (n.factorization p + 1) := he.add_one
    simpa only [ite_eq_left hev, Nat.modEq_zero_iff_dvd] using h
  have hs : sigma 1 n = ∏ p ∈ n.primeFactors,
      ∑ i ∈ range (n.factorization p + 1), p ^ i := by
    simpa using ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hn
  rw [hs]
  exact hd.trans (Finset.dvd_prod_of_mem _ hp)

private theorem not_two {n : ℕ} (hn : 1 ≤ n) : a n ≠ 2 := by
  classical
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  by_cases hsq : IsSquare n
  · have ho := (D5.S3.Arith.KrizekTriangularSquareSigmaParity.sigma_odd_iff_square_or_twice_square
      n hn).mpr (Or.inl hsq)
    intro ha
    have h2 : 2 ∣ sigma 1 n := by
      rw [← ha]
      exact Nat.gcd_dvd_left _ _
    exact ho.not_two_dvd_nat h2
  · have he : ∃ p, p.Prime ∧ ¬Even (n.factorization p) := by
      by_contra h
      apply hsq
      apply Nat.isSquare_iff_even_factorization.mpr
      intro p hp
      by_contra he
      exact h ⟨p, hp, he⟩
    obtain ⟨p, hp, he⟩ := he
    have heo := Nat.not_even_iff_odd.mp he
    have hmem : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      intro hz
      simp [hz] at he
    have hpsi : p + 1 ∣ psi n := by
      rw [psi_prod hn0]
      exact (dvd_mul_left (p + 1) _).trans (Finset.dvd_prod_of_mem _ hmem)
    have hg : p + 1 ∣ a n := Nat.dvd_gcd (odd_exp_dvd_sigma hn0 hmem heo) hpsi
    intro ha
    rw [ha] at hg
    have := Nat.le_of_dvd (by decide : 0 < 2) hg
    have := hp.two_le
    omega

private theorem witness_value {q r : ℕ} (hq : q.Prime) (hqo : Odd q) (hr : r.Prime)
    (hgt : q ^ 2 + q + 1 < r)
    (hmod : Nat.ModEq (q * (q + 1) * (q ^ 2 + q + 1)) r 1) :
    a (q ^ 2 * r ^ (q - 1)) = q := by
  let S := q ^ 2 + q + 1
  let T := ∑ i ∈ range q, r ^ i
  have hq2 : 2 ≤ q := hq.two_le
  have hqr : q ≠ r := by omega
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  have hSgeom : S = ∑ i ∈ range 3, q ^ i := by
    dsimp [S]
    simp [Finset.sum_range_succ]
    omega
  have hqp : Nat.ModEq (q + 1) r 1 := hmod.of_dvd (by
    exact dvd_mul_of_dvd_left (dvd_mul_left (q + 1) q) S)
  have hqmod : Nat.ModEq q r 1 := hmod.of_dvd (dvd_mul_of_dvd_left (dvd_mul_right q (q + 1)) S)
  have hSmod : Nat.ModEq S r 1 := hmod.of_dvd (dvd_mul_left S (q * (q + 1)))
  have hsigma : sigma 1 (q ^ 2 * r ^ (q - 1)) = S * T := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow 2 (q - 1)),
      ArithmeticFunction.sigma_one_apply_prime_pow hq,
      ArithmeticFunction.sigma_one_apply_prime_pow hr]
    rw [show q - 1 + 1 = q by omega, ← hSgeom]
  have hpsi : psi (q ^ 2 * r ^ (q - 1)) = q * ((q + 1) * r ^ (q - 2) * (r + 1)) := by
    have hpf : (q ^ 2 * r ^ (q - 1)).primeFactors = {q, r} := by
      rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hr.ne_zero),
        Nat.primeFactors_prime_pow (by decide) hq,
        Nat.primeFactors_prime_pow (Nat.sub_ne_zero_iff_lt.mpr hq2) hr]
      rfl
    have hquot : q ^ 2 * r ^ (q - 1) / (q * r) = q * r ^ (q - 2) := by
      have heq : q ^ 2 * r ^ (q - 1) = (q * r ^ (q - 2)) * (q * r) := by
        rw [show q - 1 = (q - 2) + 1 by omega, pow_succ]
        ring
      exact Nat.div_eq_of_eq_mul_left (Nat.mul_pos hq.pos hr.pos) heq
    have hnot : q ∉ ({r} : Finset ℕ) := Finset.notMem_singleton.mpr hqr
    simp only [psi, hpf, Finset.prod_insert hnot, Finset.prod_singleton]
    rw [hquot]
    ring
  have hSqp : Nat.Coprime S (q + 1) := by
    have h := geom_mod_succ q 3
    rw [← hSgeom] at h
    exact h.gcd_eq.trans (Nat.gcd_one_left _)
  have hSr : Nat.Coprime S r := by
    apply Nat.Coprime.symm
    apply hr.coprime_iff_not_dvd.mpr
    exact Nat.not_dvd_of_pos_of_lt (by dsimp [S]; omega) hgt
  have hSodd : Odd S := ((hqo.pow : Odd (q ^ 2)).add_odd hqo).add_one
  have hSrp : Nat.Coprime S (r + 1) := by
    have h : Nat.ModEq S (r + 1) 2 := by
      simpa using hSmod.add (Nat.ModEq.refl 1)
    apply Nat.Coprime.symm
    change Nat.gcd (r + 1) S = 1
    rw [h.gcd_eq]
    exact Nat.coprime_two_left.mpr hSodd
  have hTqp : Nat.Coprime T (q + 1) := by
    have h := geom_mod_one hqp q
    change Nat.gcd T (q + 1) = 1
    rw [h.gcd_eq]
    simp
  have hTr : Nat.Coprime T r := by
    have h := geom_mod_self r (q - 1)
    rw [show q - 1 + 1 = q by omega] at h
    exact h.gcd_eq.trans (Nat.gcd_one_left _)
  have hTrp : Nat.Coprime T (r + 1) := by
    have h := geom_mod_succ r q
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr hqo)] at h
    exact h.gcd_eq.trans (Nat.gcd_one_left _)
  have hB : Nat.Coprime ((q + 1) * r ^ (q - 2) * (r + 1)) (S * T) := by
    exact (((hSqp.symm.mul_right hTqp.symm).mul_left
      ((hSr.symm.mul_right hTr.symm).pow_left (q - 2))).mul_left
      (hSrp.symm.mul_right hTrp.symm))
  have hqT : q ∣ T := by
    have h := geom_mod_one hqmod q
    exact Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl q)))
  rw [a, hsigma, hpsi, Nat.gcd_comm, mul_comm q,
    Nat.gcd_mul_of_coprime_of_dvd hB (dvd_mul_of_dvd_right hqT S)]

theorem result : D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes.claim := by
  intro q hq
  constructor
  · rintro ⟨n, hn, ha⟩
    apply hq.odd_of_ne_two
    intro h2
    exact not_two hn (ha.trans h2)
  · intro hqo
    have hM : q * (q + 1) * (q ^ 2 + q + 1) ≠ 0 := by
      have := hq.pos
      positivity
    obtain ⟨r, hr, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (q ^ 2 + q + 1) hM
    refine ⟨q ^ 2 * r ^ (q - 1), ?_, witness_value hq hqo hr hgt hmod⟩
    exact Nat.one_le_of_lt (Nat.mul_pos (pow_pos hq.pos 2) (pow_pos hr.pos (q - 1)))


end D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes
