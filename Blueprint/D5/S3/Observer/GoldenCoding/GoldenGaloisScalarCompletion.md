# Golden Galois Scalar Completion

## Abstract

Golden conjugation fixes exactly rational scalars and retains symmetric data.

**Theorem 1.1 (Golden conjugation fixes exactly the rational scalars).**

$$let K = \operatorname{QuadraticAlgebra}\left(\operatorname{Rational}\left(\right), 5, 0\right); let phi = \operatorname{mk}\left(\frac{1}{2}, \frac{1}{2}\right); let phiPrime = \operatorname{mk}\left(\frac{1}{2}, \operatorname{neg}\left(\frac{1}{2}\right)\right); \left(\left(\left(\left(\left(\forall c \in K,\; \operatorname{star}\left(c\right) = c \Leftrightarrow \left(\exists q \in \operatorname{Rational}\left(\right),\; c = \operatorname{algebraMap}\left(\operatorname{Rational}\left(\right), K, q\right)\right)\right) \land \left(\neg \operatorname{star}\left(phi\right) = phi\right)\right) \land \left(\neg \operatorname{star}\left(phiPrime\right) = phiPrime\right)\right) \land phi + phiPrime = 1\right) \land phi \cdot phiPrime = \operatorname{neg}\left(1\right)\right) \land \operatorname{square}\left(phi - phiPrime\right) = 5$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenGaloisScalarCompletion.golden_galois_scalar_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical rational quadratic algebra with generator squaring to five. The two golden conjugates are constructed in its rational coordinates as (1/2,1/2) and (1/2,-1/2).

Quadratic conjugation negates the second coordinate, so a fixed element has zero second coordinate and is exactly in the rational algebra-map range. Direct coordinate calculations prove that neither golden conjugate is fixed and establish their sum, product, and squared difference.

The source's qualitative statement that bare golden values usually disappear after completion has no quantified predicate. It is therefore commentary rather than an additional universal clause.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenGaloisScalarCompletion.golden_galois_scalar_completion`
