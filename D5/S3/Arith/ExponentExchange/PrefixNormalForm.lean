/- GID: D5/S3/Arith/ExponentExchange/PrefixNormalForm
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/PrefixNormalForm
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: A smaller integer with as many primes and non-increasing exponents has larger sigma. -/

import D5.S3.Arith.ExponentExchange.IntegerSwap

/-! Repeated prime exponent exchanges move every positive integer to a normal form whose
exponents do not increase along the primes. Each exchange lowers the integer and raises
`σ(n)/n`; it moves a prime power between two primes coprime to the remaining cofactor, so
the number of distinct prime factors is unchanged. A normal form has an initial segment of
the primes as support. -/

namespace D5.S3.Arith.ExponentExchange.PrefixNormalForm

open D5.S3.Arith.ExponentExchange.IntegerSwap

private theorem card_primeFactors_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p ^ a).primeFactors.card = if a = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [Nat.primeFactors_prime_pow ha.ne' hp, if_neg ha.ne', Finset.card_singleton]

/-- The distinct prime count of `t * p^a * q^b` with `t` coprime to `p * q`. -/
private theorem card_primeFactors_two_powers {t p q : ℕ} (a b : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hcop : Nat.gcd t (p * q) = 1) :
    (t * p ^ a * q ^ b).primeFactors.card =
      t.primeFactors.card + (if a = 0 then 0 else 1) + (if b = 0 then 0 else 1) := by
  have hco : t.Coprime (p * q) := hcop
  have htp : t.Coprime p := hco.coprime_dvd_right (dvd_mul_right p q)
  have htq : t.Coprime q := hco.coprime_dvd_right (dvd_mul_left q p)
  have hpq' : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have h1 : t.Coprime (p ^ a) := htp.pow_right a
  have h2 : (t * p ^ a).Coprime (q ^ b) :=
    Nat.coprime_mul_iff_left.mpr ⟨htq.pow_right b, hpq'.pow a b⟩
  rw [h2.primeFactors_mul, Finset.card_union_of_disjoint h2.disjoint_primeFactors,
    h1.primeFactors_mul, Finset.card_union_of_disjoint h1.disjoint_primeFactors,
    card_primeFactors_prime_pow hp, card_primeFactors_prime_pow hq]

/-- Every positive integer `n` has a companion `m ≤ n` with the same number of distinct prime
factors, exponents non-increasing along the primes, and `σ(n)/n ≤ σ(m)/m`. -/
theorem exists_antitone_exponent_form {n : ℕ} (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ m.primeFactors.card = n.primeFactors.card ∧
      (∀ p q : ℕ, p.Prime → q.Prime → p < q → m.factorization q ≤ m.factorization p) ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ (ArithmeticFunction.sigma 1 m : ℝ) / m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      n.factorization q ≤ n.factorization p
  · exact ⟨n, hn, le_rfl, rfl, hanti, le_rfl⟩
  simp only [not_forall, not_le] at hanti
  obtain ⟨p, q, hp, hq, hpq, hlt⟩ := hanti
  obtain ⟨-, hcop, hdecomp, ⟨hpos, hsmall⟩, hZ⟩ := prime_exponent_swap hn hp hq hpq hlt
  obtain ⟨m, hm1, hmle, hcard, hmanti, hmZ⟩ := ih _ hsmall hpos
  refine ⟨m, hm1, hmle.trans hsmall.le, ?_, hmanti, hZ.le.trans hmZ⟩
  rw [hcard, card_primeFactors_two_powers _ _ hp hq hpq.ne hcop]
  conv_rhs => rw [hdecomp, card_primeFactors_two_powers _ _ hp hq hpq.ne hcop]
  omega

end D5.S3.Arith.ExponentExchange.PrefixNormalForm
