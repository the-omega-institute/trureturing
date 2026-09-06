# Strict Exponent Exchange

## Abstract

Assigning the larger exponent to the smaller real base strictly increases the product of reciprocal geometric sums.

**Definition 1.1 (Reciprocal geometric sum).**

$$\forall r \in \mathbb{R}, \forall k \in \mathbb{N}, f\left(r, k\right) = \sum_{i=0}^{k} \frac{1}{r}^{i}$$

*Formalization.* `D5/S3/Arith/RobinExponentSwap.reciprocalGeomSum` (`✓ std3`).

*Citation.* Leonidas Alaoglu and Paul Erdos (1944). *On highly composite and similar numbers*. DOI: [10.2307/1990319](https://doi.org/10.2307/1990319).

*Commentary.*

The notation f denotes reciprocalGeomSum. Its index set includes both zero and k, so it contains k + 1 terms and its constant term is one. At a prime base this is the usual local factor in the normalized divisor sum. The definition uses Lean's total real inverse; the comparison below restricts both bases to be greater than one.

**Theorem 1.2 (Larger exponents favor smaller bases).**

$$\begin{aligned}\forall p, q \in \mathbb{R}, \forall a, b \in \mathbb{N},\\(1 < p < q \land a < b) \Rightarrow\\f\left(p, a\right) \cdot f\left(q, b\right) < f\left(p, b\right) \cdot f\left(q, a\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RobinExponentSwap.reciprocal_geom_sum_swap_strict` (`✓ std3`). ∎

*Citation.* Leonidas Alaoglu and Paul Erdos (1944). *On highly composite and similar numbers*. DOI: [10.2307/1990319](https://doi.org/10.2307/1990319).

*Commentary.*

The statement quantifies over every pair of real bases p and q and every pair of natural exponents a and b, including a = 0. It assumes exactly 1 < p, p < q, and a < b. The right-hand product pairs the larger exponent with the smaller base. Both prefix sums are positive, so positive cross multiplication also gives f(q,b)/f(q,a) < f(p,b)/f(p,a).

The proof compares every term of a fixed prefix against each new tail exponent. The strict ordering of the positive inverse bases gives a strict power comparison because every tail exponent exceeds every prefix exponent. Finite summation and induction on the larger exponent produce the displayed result.

This is the local exchange inequality in the classical superabundant-number argument, stated with arbitrary real bases. It proves only the strict increase of the two local factors. The integer-size decrease, record-point construction, nonincreasing factorization of record points, and Robin criterion are not conclusions of this module.

## References

- Truth anchor: `D5/S3/Arith/RobinExponentSwap.reciprocalGeomSum`
- Truth anchor: `D5/S3/Arith/RobinExponentSwap.reciprocal_geom_sum_swap_strict`
