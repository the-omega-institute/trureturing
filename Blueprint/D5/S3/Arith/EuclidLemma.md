# Euclid's Lemma on the Prime Axis

## Abstract

A prime dividing a product of two naturals divides one of the factors.

**Lemma 1.1 (A prime dividing a product divides a factor).**

$$\forall p,a,b\in\mathbb{N},\ p\ \text{prime} \land p \mid a\cdot b \Rightarrow p \mid a \lor p \mid b$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

For natural numbers, a prime that divides a product divides at least one factor. This is the classical Euclid lemma and the first building block of the two-axis norm reading exemplar; the source volume derives it from the additivity of the prime-exponent valuation on the free commutative monoid of the prime axis. The formal statement fixes the natural-number carrier and the standard divisibility relation, so the hypothesis is genuine primality and a genuine product divisibility, not a hollow or vacuous premise. The proof discharges the claim through Mathlib's Nat.Prime.dvd_mul, which supplies the equivalence for a prime; the deposited atom asserts the truth of the statement, and the proof route may differ from the source's valuation-additivity derivation. Original numerical-certificate disposition: the source lemma is a purely logical divisibility implication and contains no numerical certificate.

## References

- Truth anchor: `D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul`
