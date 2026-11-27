# An exact finite rational criterion for the Riemann hypothesis

## Abstract

An exact finite rational criterion for the Riemann hypothesis

**Theorem 1.1 (Scalar growth from a zero-free half-plane).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedScalarUpper.scalar_growth_of_zero_free`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedScalarUpper.scalar_growth_of_zero_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1/2 ≤ θ < 1, nonvanishing of zeta on Re(s) > θ away from 1 gives a bound by C N^(θ+ε) at every positive natural N for every ε > 0. Summation by parts writes the weighted scalar in terms of ordinary Möbius prefix differences and increments of the kernel. Each increment is at most a Lipschitz constant divided by N.

**Theorem 1.2 (Equivalence with square-root growth).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedScalarUpper.rh_iff_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedScalarUpper.rh_iff_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis holds exactly when, for every ε > 0, the finite rational scalar has absolute value at most C N^(1/2+ε) for some nonnegative C and all positive natural N. The forward direction uses the ordinary Möbius prefix estimate at θ = 1/2 and the reverse direction uses the Mellin product.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedScalarUpper.rh_iff_scalar`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedScalarUpper.scalar_growth_of_zero_free`
- Dependency: [D5/S3/Weil/Analytic/NymanFixedRationalScalar](NymanFixedRationalScalar.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusShortAverage](../ZetaPntBounds/MobiusShortAverage.md)
