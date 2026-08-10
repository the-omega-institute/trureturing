# Uniqueness of Prime Factorization

## Abstract

Prime factorization of a natural number is unique up to permutation.

**Theorem 1.1 (Prime factorizations of the same number are permutations of each other).**

$$(\forall p\in l_1,\ p\ \text{prime}) \land (\forall p\in l_2,\ p\ \text{prime}) \land \prod l_1 = \prod l_2 \Rightarrow l_1 \sim l_2$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/UniqueFactorization.prime_factorization_unique` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

Prime factorization is unique up to rearrangement: any two finite lists of prime numbers with the same product are permutations of each other. This is the uniqueness half of the fundamental theorem of arithmetic; the existence half is deposited separately. The formal claim quantifies over two lists of naturals, requires every entry of each to be prime and the two products to agree, and concludes a genuine list permutation, so nothing is normalized away before the comparison and the statement is not hollow. The proof is a thin honest wrapper over pinned Mathlib: each list is identified with the canonical prime-factor list of the common product by Mathlib's canonical-list uniqueness lemma, and the two identifications compose into the permutation; the deposited atom asserts the truth of the statement, and this route differs from the source's minimal-counterexample argument. Original numerical-certificate disposition: the source theorem is a purely universal uniqueness statement and contains no numerical certificate.

## References

- Truth anchor: `D5/S3/Factorization/UniqueFactorization.prime_factorization_unique`
