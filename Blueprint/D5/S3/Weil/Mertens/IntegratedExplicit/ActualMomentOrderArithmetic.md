# Actual-K scalar endpoint

## Abstract

Exact scalar order arithmetic for the original actual-K moment endpoint.

**Theorem 1.1 (Original moment order scalar bounds).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.q_scalar_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.q_scalar_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original ceiling N(C, alpha, D), with C at least one and D positive, the order is at least one and N/D is at least eight. The exact curvature payment is at most one eighth, and the logarithmic ceiling pays beta plus the Euler and endpoint constants with the retained one fifth margin. The definition keeps the original max, ceiling, inclusive moment degree, and all degenerate finite families.

**Theorem 1.2 (Original leading-one order asymptotic).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.leading_one`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.leading_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive alpha and C at least one, the original order satisfies log(N/D)/exp(D/2) tending to one as D tends to infinity. The proof retains the original beta, ceiling squeeze, and both decaying exponential terms without asserting a sublinear order or an RH endpoint.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.leading_one`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.q_scalar_bounds`
