# A positive mixture of rational kernels

## Abstract

Rational partial fractions for the signed Bernoulli remainder.

**Theorem 1.1 (The series representation).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.P_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.P_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural m and n and every positive real t, P(m,n,t) equals twice the sum over natural k of t^(m+2n) divided by (pi(k+1))^(2n) and by t^2+(pi(k+1))^2. Every weight is positive.

Substitution of an imaginary argument in the cotangent partial fractions gives the case n=0. The even zeta values identify each successive Bernoulli coefficient. Subtraction and the finite geometric identity then give the remainder for every n. All series equalities are obtained from convergent series.

**Theorem 1.2 (Convergence of the derivative series).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.hasSum_iteratedDeriv_P`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.hasSum_iteratedDeriv_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural derivative order r and all natural m and n, the series obtained by differentiating the rational kernels r times converges at each positive real t. Its sum is half the r-th derivative of P(m,n) at t.

The imaginary part of a complex linear reciprocal gives the quadratic reciprocal. Its r-th derivative has absolute value at most r! divided by a^(r+2) for positive a. The product rule gives uniform bounds on bounded real intervals. The resulting majorants are constant multiples of the convergent reciprocal-square series.

**Theorem 1.3 (Differentiation of the representation).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.iteratedDeriv_P`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.iteratedDeriv_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r, the r-th derivative of P(m,n) at a positive t equals twice the sum of the r-th derivatives of the rational kernels with the same weights. This includes all orders through m+2n-1.

The original remainder agrees with its rational series on a neighborhood of every positive argument. Neighborhood invariance of iterated derivatives transfers the termwise derivative identity to the pinned remainder, without imposing any condition on its value at zero.

## References

- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.P_eq_tsum`
- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.hasSum_iteratedDeriv_P`
- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/PartialFraction.iteratedDeriv_P`
- Dependency: [D5/S3/Analytic/CothBernoulliDegree/Defs](Defs.md)
