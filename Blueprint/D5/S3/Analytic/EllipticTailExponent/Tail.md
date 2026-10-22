# Finite products and the sine remainder

## Abstract

Elliptic coefficient tails

**Definition 1.1 (Normalized coefficients).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Tail.d`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Tail.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural k and real a, d k a is the product of a+j times the product of 1-a+j over 0 <= j < k, divided by (k!)^2.

**Definition 1.2 (Truncation summands).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Tail.t`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Tail.t` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The summand t k a is a d k a/(k+1). It is nonnegative for 0<a<=1/2. The finite truncation S n a sums these terms for 0<=k<=n.

**Theorem 1.3 (Finite Euler product).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Tail.d_product`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Tail.d_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and every real a, (N+1)d(N+1,a) equals a(1-a/(N+1)) times the product of 1-a^2/(j+1)^2 over 0<=j<N. The normalized coefficient recurrence gives the identity by induction.

**Theorem 1.4 (The analytic remainder as a coefficient tail).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Tail.tail_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Tail.tail_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every real a with 0<a<=1/2, sin(pi a)/(pi(1-a))-S n a equals the convergent sum of t(k+n+1,a) over natural k. The coefficient recurrence telescopes the finite sum to its weighted endpoint. The finite Euler product converges by the sine product theorem; nonnegativity identifies the sum, and removing the first n+1 terms gives the stated remainder.

## References

- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Tail.d`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Tail.d_product`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Tail.t`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Tail.tail_eq_tsum`
- Dependency: [D5/S3/Analytic/EllipticTailExponent/Defs](Defs.md)
