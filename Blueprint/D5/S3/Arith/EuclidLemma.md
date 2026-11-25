# Euclid's Lemma on the Prime Axis

## Abstract

A prime dividing a product of two naturals divides one of the factors.

**Lemma 1.1 (A prime dividing a product divides a factor).**

$$\forall p,a,b\in\mathbb{N},\ p\ \text{prime} \land p \mid a\cdot b \Rightarrow p \mid a \lor p \mid b$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

For natural numbers, a prime that divides a product divides at least one factor. This is the classical Euclid lemma and the first building block of the two-axis norm reading exemplar; the source volume derives it from the additivity of the prime-exponent valuation on the free commutative monoid of the prime axis. The proof reads Mathlib primality through the D5 divisor characterization. Since gcd(p,a) divides p, it equals one or p. In the first case Bézout's identity gives divisibility of b. In the second case p divides a.

## References

- Truth anchor: `D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul`
