# Existence of Prime Factorization

## Abstract

Every natural number greater than one is a product of finitely many primes.

**Theorem 1.1 (Every natural number above one is a product of primes).**

$$\forall n\in\mathbb{N},\ n>1 \Rightarrow \exists\, l,\ (\forall p\in l,\ p\ \text{prime}) \land \prod l = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeFactorization.exists_prime_factorization` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

Every natural number greater than one factors as a product of finitely many prime numbers. This is the existence half of the fundamental theorem of arithmetic (uniqueness is a separate statement). The formal claim fixes the natural-number carrier and exhibits an explicit finite list whose entries are all prime and whose product is the given number, so the hypothesis is a genuine bound and the conclusion a genuine existential, not a hollow or vacuous statement; since the product of the empty list is one, the bound n > 1 forces the witnessing list to be non-empty. The proof discharges the claim through Mathlib's prime-factors list, its all-prime membership lemma, and its product identity; the deposited atom asserts the truth of the statement, and the proof route may differ from the source's minimal-counterexample argument. Original numerical-certificate disposition: the source theorem is a purely existential factorization statement and contains no numerical certificate.
