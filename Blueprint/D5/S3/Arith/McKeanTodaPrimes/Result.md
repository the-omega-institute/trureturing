# Counterexamples to McKean's Conjecture 5.6

## Abstract

Both denominator-based assertions about Toda primes fail.

**Definition 1.1 (Toda primes).**

$$\forall n \in \mathbb{N} ,\; \operatorname{todaPrimes} \left(n\right) = \operatorname{Finset.filter} \left(\lambda (p: \mathbb{N} ) \mapsto ((\operatorname{Nat.Prime} \left(p\right)) \land ((\operatorname{Odd} \left(p\right)) \land (((p - 1) \mid ((4) \cdot (n))) \land (\operatorname{Nat.Coprime} \left(p, \operatorname{Nat.div} \left((4) \cdot (n), p - 1\right)\right))))), \operatorname{Finset.range} \left((4) \cdot (n) + 2\right)\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.todaPrimes` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

§1, printed p. 1: “Definition 1.1. Let n be an integer. A Toda prime of n is an odd prime p such that p − 1 | 4n and gcd(p, 4n/(p−1)) = 1. Denote the set of Toda primes of n by T (n) (see Table 1), and let t(n) := |T (n)| (see Figure 1).” For positive n, divisibility and primality imply p−1≤4n, hence p<4n+2. The range therefore omits no Toda prime. At n=0 the quotient is zero, and a prime is not coprime to zero, so the set is empty. The natural-number domain suffices to contradict the positive-integer assertion.

**Definition 1.2 (Number of Toda primes).**

$$\forall n \in \mathbb{N} ,\; \operatorname{t} \left(n\right) = \operatorname{Finset.card} \left(\operatorname{todaPrimes} \left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.t` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

The cardinality is exactly t(n) in Definition 1.1, §1, printed p. 1.

**Definition 1.3 (Reduced Bernoulli denominator).**

$$\forall k \in \mathbb{N} ,\; \operatorname{bernDen} \left(k\right) = \operatorname{Rat.den} \left(\operatorname{bernoulli} \left(k\right)\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.bernDen` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

Dk is the reduced positive denominator of Bk. Mathlib uses B1=−1/2; all Bernoulli indices in the counterexamples are positive and even.

**Definition 1.4 (Prime predecessors dividing an index).**

$$\forall k \in \mathbb{N} ,\; \operatorname{denominatorPrimes} \left(k\right) = \operatorname{Finset.filter} \left(\lambda (p: \mathbb{N} ) \mapsto ((\operatorname{Nat.Prime} \left(p\right)) \land ((p - 1) \mid (k))), \operatorname{Finset.range} \left(k + 2\right)\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.denominatorPrimes` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

§5.1, printed p. 8: “Notation 5.5. Given an even integer 2m, let P (2m) denote the set of primes such that p − 1 | 2m, so that D₂ₘ = ∏ₚ∈P(2m) p. Let F (d) = min{2m > 0 : D₂ₘ = d} [PW23].” For k>0, any prime with p−1 dividing k satisfies p<k+2. The finite range is exhaustive.

**Definition 1.5 (The denominator-invariance assertion).**

$$clauseI = \left(\forall a \in \mathbb{N} ,\; \forall m \in \mathbb{N} ,\; (0 < a) \Rightarrow ((0 < m) \Rightarrow ((\forall k \in \mathbb{N} ,\; (0 < k) \Rightarrow ((\operatorname{Even} \left(k\right)) \Rightarrow ((k < (4) \cdot (a)) \Rightarrow (\neg (\operatorname{bernDen} \left(k\right) = \operatorname{bernDen} \left((4) \cdot (a)\right)))))) \Rightarrow ((\operatorname{bernDen} \left(((4) \cdot (a)) \cdot (m)\right) = \operatorname{bernDen} \left((4) \cdot (a)\right)) \Rightarrow (\operatorname{todaPrimes} \left((a) \cdot (m)\right) = \operatorname{todaPrimes} \left(a\right)))))\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.clauseI` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

Conjecture 5.6(i), §5.1, printed p. 8: “If F (d) = 4a for some integer a, then T (am) = T (a) whenever D₄ₐₘ = D₄ₐ.” The hypothesis F(bernDen(4a))=4a is encoded equivalently by excluding every smaller positive even index with that denominator. The equality bernDen(4a)=d is automatic for d=bernDen(4a). No choice of a first index is needed.

**Definition 1.6 (The denominator-change assertion).**

$$clauseII = \left(\forall a \in \mathbb{N} ,\; \forall m \in \mathbb{N} ,\; (0 < a) \Rightarrow ((0 < m) \Rightarrow ((\neg (\operatorname{bernDen} \left(((4) \cdot (a)) \cdot (m)\right) = \operatorname{bernDen} \left((4) \cdot (a)\right))) \Rightarrow (\operatorname{t} \left(a\right) \le \operatorname{t} \left((a) \cdot (m)\right))))\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.clauseII` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

Conjecture 5.6(ii), §5.1, printed p. 8: “If D₄ₐₘ ≠ D₄ₐ = d, then t(am) ≥ t(a).” Both multipliers are positive natural numbers.

**Definition 1.7 (The full two-clause conjecture).**

$$claim = \left((clauseI) \land (clauseII)\right)$$

*Formalization.* `D5/S3/Arith/McKeanTodaPrimes/Result.claim` (`✓ std3`).

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

§5.1, printed p. 8: “Conjecture 5.6. Let d be a Bernoulli denominator. (i) If F (d) = 4a for some integer a, then T (am) = T (a) whenever D₄ₐₘ = D₄ₐ. (ii) If D₄ₐₘ ≠ D₄ₐ = d, then t(am) ≥ t(a).” The assertion is the conjunction of both clauses with positive a and m. The two clauses are separately refuted below.

**Theorem 1.8 (The range is exhaustive).**

$$\forall k \in \mathbb{N} ,\; \forall p \in \mathbb{N} ,\; (0 < k) \Rightarrow ((p \in \operatorname{denominatorPrimes} \left(k\right)) \Leftrightarrow ((\operatorname{Nat.Prime} \left(p\right)) \land ((p - 1) \mid (k))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.memDenominatorPrimes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive divisor of k is at most k. This gives the stated membership condition without a range restriction.

**Theorem 1.9 (The exact denominator product).**

$$\forall k \in \mathbb{N} ,\; (0 < k) \Rightarrow (\operatorname{bernDen} \left((2) \cdot (k)\right) = \prod_{p \in \operatorname{denominatorPrimes} \left((2) \cdot (k)\right)} p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.denominatorFormula` (`✓ std3`). ∎

*Citation.* Stephen McKean (2025). *Toda primes*. URL: <https://arxiv.org/abs/2511.19744v1>.

*Commentary.*

Bernoulli.vonStaudt_clausen expresses B(2k) as an integer minus the prime reciprocal sum. Finset.Rat.den_sum_dvd_prod_den bounds its denominator by the prime product. Each prime in the product divides the denominator by Bernoulli.dvd_den_bernoulli. Nat.coprime_primes and Finset.prod_dvd_of_isRelPrime give divisibility by their product. Antisymmetry gives equality. This is the denominator identity in Notation 5.5, §5.1, printed p. 8.

**Theorem 1.10 (Coprimality removes the prime factors of n).**

$$\forall n \in \mathbb{N} ,\; (0 < n) \Rightarrow (\operatorname{todaPrimes} \left(n\right) = \operatorname{Finset.filter} \left(\lambda (p: \mathbb{N} ) \mapsto ((\operatorname{Odd} \left(p\right)) \land (\neg ((p) \mid (n)))), \operatorname{denominatorPrimes} \left((4) \cdot (n)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.todaReduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nat.not_dvd_of_pos_of_lt excludes p dividing p−1. Nat.prime_eq_prime_of_dvd_pow reduces a prime divisor of 4 to 2, which oddness excludes. Nat.mul_div_cancel' gives (p−1)(4n/(p−1))=4n; Nat.Prime.dvd_mul and Nat.Prime.coprime_iff_not_dvd then make coprimality with the quotient equivalent to p not dividing n.

**Theorem 1.11 (A proper divisor proves compositeness).**

$$\forall q \in \mathbb{N} ,\; \forall c \in \mathbb{N} ,\; (1 < c) \Rightarrow ((c < q) \Rightarrow ((\operatorname{Nat.mod} \left(q, c\right) = 0) \Rightarrow (\neg (\operatorname{Nat.Prime} \left(q\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.compositeByMod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nat.not_prime_of_dvd_of_lt excludes a number with a divisor strictly between one and itself. Nat.dvd_of_mod_eq_zero supplies the divisor from the zero residue. This excludes the unwanted divisor successors.

**Theorem 1.12 (Only four divisor successors can be prime).**

$$\forall a \in \mathbb{N} ,\; \forall q \in \mathbb{N} ,\; (\operatorname{Nat.Prime} \left(a\right)) \Rightarrow ((\operatorname{Nat.mod} \left(a, 30\right) = 23) \Rightarrow ((\operatorname{Nat.Prime} \left((2) \cdot (a) + 1\right)) \Rightarrow ((\operatorname{Nat.Prime} \left(q\right)) \Rightarrow (((q - 1) \mid (((4) \cdot (a)) \cdot ((2) \cdot (a) + 1))) \Rightarrow ((q = 2) \lor ((q = 3) \lor ((q = 5) \lor (q = (2) \cdot (a) + 1))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.familyCandidates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

exists_dvd_and_dvd_of_dvd_mul decomposes a divisor of 4a(2a+1) into divisors of 4, a and 2a+1. Nat.dvd_prime_pow classifies the divisors of 4, giving twelve candidates. The unwanted successors are even or divisible by 3 or 5. The residue a≡23 modulo 30 gives a≡1 modulo 2, a≡2 modulo 3 and a≡3 modulo 5.

**Theorem 1.13 (Both denominator prime sets coincide).**

$$\forall a \in \mathbb{N} ,\; (\operatorname{Nat.Prime} \left(a\right)) \Rightarrow ((\operatorname{Nat.mod} \left(a, 30\right) = 23) \Rightarrow ((\operatorname{Nat.Prime} \left((2) \cdot (a) + 1\right)) \Rightarrow ((\operatorname{denominatorPrimes} \left((4) \cdot (a)\right) = \{2,3,5,(2) \cdot (a) + 1\}) \land (\operatorname{denominatorPrimes} \left(((4) \cdot (a)) \cdot ((2) \cdot (a) + 1)\right) = \{2,3,5,(2) \cdot (a) + 1\}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.familyPrimeSets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four possible primes 2,3,5,2a+1 all occur. Every divisor successor for 4a is also one for 4a(2a+1).

**Theorem 1.14 (Prime divisibility of an even-index denominator).**

$$\forall k \in \mathbb{N} ,\; \forall p \in \mathbb{N} ,\; (0 < k) \Rightarrow ((\operatorname{Even} \left(k\right)) \Rightarrow ((\operatorname{Nat.Prime} \left(p\right)) \Rightarrow (((p) \mid (\operatorname{bernDen} \left(k\right))) \Leftrightarrow ((p - 1) \mid (k)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.primeDenIff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the product formula and prime divisibility of a finite product. A prime dividing another prime is equal to it.

**Theorem 1.15 (The first even index is 4a).**

$$\forall a \in \mathbb{N} ,\; (\operatorname{Nat.Prime} \left(a\right)) \Rightarrow ((\operatorname{Nat.mod} \left(a, 30\right) = 23) \Rightarrow ((\operatorname{Nat.Prime} \left((2) \cdot (a) + 1\right)) \Rightarrow (\forall k \in \mathbb{N} ,\; (0 < k) \Rightarrow ((\operatorname{Even} \left(k\right)) \Rightarrow ((\operatorname{bernDen} \left(k\right) = (30) \cdot ((2) \cdot (a) + 1)) \Rightarrow ((4) \cdot (a) \le k))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.familyMinimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

primeDenIff applied to 5 and 2a+1 forces 4 dividing k and 2a dividing k. Writing k=2ar, Nat.mul_dvd_mul_iff_left cancels a factor of 2 from 4 dividing k. The odd residue of a then forces r to be even. Nat.pos_of_mul_pos_left gives r>0, and Nat.le_of_dvd gives r≥2, hence k≥4a.

**Theorem 1.16 (The prime family contradicting invariance).**

$$\forall a \in \mathbb{N} ,\; (\operatorname{Nat.Prime} \left(a\right)) \Rightarrow ((\operatorname{Nat.mod} \left(a, 30\right) = 23) \Rightarrow ((\operatorname{Nat.Prime} \left((2) \cdot (a) + 1\right)) \Rightarrow ((\operatorname{bernDen} \left((4) \cdot (a)\right) = (30) \cdot ((2) \cdot (a) + 1)) \land ((\operatorname{bernDen} \left(((4) \cdot (a)) \cdot ((2) \cdot (a) + 1)\right) = (30) \cdot ((2) \cdot (a) + 1)) \land ((\forall k \in \mathbb{N} ,\; (0 < k) \Rightarrow ((\operatorname{Even} \left(k\right)) \Rightarrow ((k < (4) \cdot (a)) \Rightarrow (\neg (\operatorname{bernDen} \left(k\right) = (30) \cdot ((2) \cdot (a) + 1)))))) \land ((\operatorname{todaPrimes} \left(a\right) = \{3,5,(2) \cdot (a) + 1\}) \land (\operatorname{todaPrimes} \left((a) \cdot ((2) \cdot (a) + 1)\right) = \{3,5\})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime a≡23 modulo 30 whose successor 2a+1 is prime, both denominators equal 30(2a+1), their first positive even index is 4a, and multiplication by 2a+1 removes exactly that Toda prime. The assumptions describe a family; infinitude of its members is not asserted.

**Theorem 1.17 (The strict decrease at 11 times 5).**

$$(\operatorname{bernDen} \left(44\right) = 690) \land ((\operatorname{bernDen} \left(220\right) = 7590) \land ((\operatorname{todaPrimes} \left(11\right) = \{3,5,23\}) \land (\operatorname{todaPrimes} \left(55\right) = \{3,23\})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.witnessII` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product formula gives the denominators 690 and 7590. Direct finite evaluation gives the Toda sets {3,5,23} and {3,23}; the cardinality decreases from three to two. No Bernoulli number at index 220 is directly evaluated.

**Theorem 1.18 (Clause (i) is false).**

$$\neg (clauseI)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.refuteI` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family member a=23, m=47 has first even denominator index 92, unchanged denominator 1410 and unequal Toda sets.

**Theorem 1.19 (Clause (ii) is false).**

$$\neg (clauseII)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.refuteII` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a=11, m=5, the denominator changes from 690 to 7590 while the cardinality decreases from three to two.

**Theorem 1.20 (Both clauses are false).**

$$(\neg (clauseI)) \land (\neg (clauseII))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.refutedClauses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first counterexample preserves the denominator and violates invariance. The second changes the denominator and violates monotonicity.

**Theorem 1.21 (Conjecture 5.6 is refuted).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/McKeanTodaPrimes/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/mckean-2025-toda-primes-conjecture` (refuted) by `D5/S3/Arith/McKeanTodaPrimes/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mckean-2025-toda-primes-conjecture","declaration_gid":"D5/S3/Arith/McKeanTodaPrimes/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Both component assertions are false, so their conjunction is false. Question 1.2 and Conjecture 1.3 about existence of Toda primes are not settled.

## References

- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.bernDen`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.claim`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.clauseI`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.clauseII`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.compositeByMod`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.denominatorFormula`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.denominatorPrimes`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.family`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.familyCandidates`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.familyMinimum`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.familyPrimeSets`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.memDenominatorPrimes`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.primeDenIff`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.refuteI`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.refuteII`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.refutedClauses`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.result`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.t`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.todaPrimes`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.todaReduction`
- Truth anchor: `D5/S3/Arith/McKeanTodaPrimes/Result.witnessII`
