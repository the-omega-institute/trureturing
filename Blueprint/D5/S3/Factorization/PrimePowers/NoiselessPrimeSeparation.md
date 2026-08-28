# Noiseless Prime Separation

## Abstract

Prime congruence distinguishes exactly away from divisors of the difference.

**Theorem 1.1 (Every nondividing modulus separates).**

$$\forall p \in \mathbb{N}, n, m \in \mathbb{Z},\\\neg(p \mid n - m) \Rightarrow \neg\operatorname{ModEq}(p, n, m).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.nondividing_modulus_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integer inputs n and m and every natural modulus p, failure of p to divide n minus m forces the two inputs to be incongruent modulo p. Primality and p at least two are not used.

**Theorem 1.2 (Every dividing modulus fails to separate).**

$$\forall p \in \mathbb{N}, n, m \in \mathbb{Z},\\p \mid n - m \Rightarrow \operatorname{ModEq}(p, n, m).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.dividing_modulus_does_not_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The converse is exact: if p divides n minus m, then n and m are congruent modulo p. This direction also needs no primality.

**Theorem 1.3 (A prime distinguishes every distinct integer pair).**

$$\forall n, m \in \mathbb{Z}, n \neq m \Rightarrow\\\exists p \in \mathbb{N}, \operatorname{Prime}(p) \land \neg\operatorname{ModEq}(p, n, m).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.distinct_integers_have_distinguishing_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n not equal to m, Euclid's theorem supplies a prime larger than the absolute difference. Such a prime cannot divide the difference, so the pointwise criterion makes it a distinguishing coordinate.

**Theorem 1.4 (Only finitely many primes fail to distinguish).**

$$\forall n, m \in \mathbb{Z}, n \neq m \Rightarrow\\\operatorname{Finite}(\{p \in \mathbb{N} \mid \operatorname{Prime}(p) \land \operatorname{ModEq}(p, n, m)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.indistinguishing_primes_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When n and m differ, every indistinguishing prime belongs to the finite primeFactors finset of the nonzero absolute difference. Thus almost every prime coordinate separates the pair.

**Lemma 1.5 (Distinctness is necessary).**

$$\neg(\exists p \in \mathbb{N}, \operatorname{Prime}(p) \land \neg\operatorname{ModEq}(p, 0, 0)) \land \operatorname{Infinite}(\{p \in \mathbb{N} \mid \operatorname{Prime}(p) \land \operatorname{ModEq}(p, 0, 0)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.distinctness_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the concrete pair zero and zero no prime distinguishes the inputs, and every prime is indistinguishing. This simultaneously refutes existence and finiteness when distinctness is removed.

**Lemma 1.6 (Nondivisibility is necessary for separation).**

$$2 \mid 4 - 0 \land \operatorname{ModEq}(2, 4, 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.nondivisibility_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two divides four minus zero, and four is congruent to zero modulo two. This concrete pair prevents deletion of the nondivisibility premise.

**Lemma 1.7 (Divisibility is necessary for nonseparation).**

$$\neg(2 \mid 1 - 0) \land \neg\operatorname{ModEq}(2, 1, 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.divisibility_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two does not divide one minus zero, and one is not congruent to zero modulo two. This concrete pair prevents deletion of the divisibility premise from the converse.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.distinct_integers_have_distinguishing_prime`
- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.distinctness_hypothesis_is_necessary`
- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.dividing_modulus_does_not_separate`
- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.divisibility_hypothesis_is_necessary`
- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.indistinguishing_primes_finite`
- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.nondividing_modulus_separates`
- Truth anchor: `D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.nondivisibility_hypothesis_is_necessary`
