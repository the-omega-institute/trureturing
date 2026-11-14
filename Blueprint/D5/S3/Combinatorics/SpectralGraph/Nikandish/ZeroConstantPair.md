# The entire zero-constant endpoint family.

## Abstract

The entire zero-constant endpoint family.

Source: four-prime-zero-constant, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.

**Theorem 1.1 (The exact universal Bezout-eight identity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.denominator_bezout`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.denominator_bezout` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The source N and D polynomials satisfy the complete ring identity; D is odd and at least three for integer a>=2.

**Theorem 1.2 (The sole positive rational candidate is never integer).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.denominator_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.denominator_obstruction` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The entire integer a>=2 domain excludes N-Dc=0 by the odd denominator and exact Bezout identity, without a tail bound.

**Theorem 1.3 (The exact whole-operator root-two factorization).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.factor_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.factor_two` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For b=(a-1)(2a-1), the characteristic endpoint factors as 2a(a-1)c(N-Dc). Polynomial c=0 is an interpolation boundary, never a positive graph example.

**Theorem 1.4 (Full real free-tail interval).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.low_eigenpair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.low_eigenpair` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all real a>=2 and c>=a the genuine operator has an eigenpair in (1,3), retaining c=a and both tail orderings.

**Theorem 1.5 (Actual ideal-graph nonintegrality on the full family).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.actual_nonintegral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.actual_nonintegral` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All natural a>=2 and c>=a on arbitrary distinct primes are covered. No tail coprimality is assumed and no general integrality criterion follows.

**Theorem 1.6 (The genuine full-operator minimum in (1,3)).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.minimum_window`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.minimum_window` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=2 and c>=a, the minimum comparison includes every real eigenpair of the full source operator. The integer endpoint-two obstruction remains a separate arithmetic theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.actual_nonintegral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.denominator_bezout`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.denominator_obstruction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.factor_two`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.low_eigenpair`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair.minimum_window`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairedTensorMinimum](PairedTensorMinimum.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants](../PairedIdealIntersectionDeterminants.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift](../PairedIdealIntersectionLift.md)
