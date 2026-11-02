# Original Complementary Period Wronskian

## Abstract

The original complementary period has an exact Wronskian and quotient derivative on the complex lens.

**Theorem 1.1 (The exact complementary Wronskian on the lens).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialWronskian.original_wronskian`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialWronskian.original_wronskian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex x with ||x||<1 and ||1-x||<1, the literal original period F(x)=OriginalHalfBinomialPeriod.period(x) satisfies x(1-x)(F'(x)F(1-x)+F(x)F'(1-x))=1/pi. The statement is on the intersection of the two open unit disks, so both native Picard-Fuchs equations apply directly. The nonzero constant is derived from Abel's Wronskian calculation, the original real integral and the native log(16) endpoint; it is not assumed as a premise.

The proof first shows the Wronskian expression has zero derivative by substituting both original Picard-Fuchs equations. Convexity and connectedness of the lens make it constant. Reality on the midpoint is obtained from the original real integral. The real quotient derivative and the exact complementary endpoint limit determine the Abel constant as 1/pi, including its sign. No continuation across either lens boundary, source or charge covariance, Q/C-flow, string, or AdS/CFT claim is included.

**Definition 1.2 (The original complementary period ratio).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialWronskian.tau`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialWronskian.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio tau(x) is defined literally as i times the complementary original period divided by the original period, with both periods evaluated at x and 1-x respectively. It is an actual complex function on points where the denominator period is nonzero; the derivative theorem below supplies the nonvanishing on the lens.

**Theorem 1.3 (The exact quotient derivative and denominator nonvanishing).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialWronskian.original_tau_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialWronskian.original_tau_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every x with ||x||<1 and ||1-x||<1, the actual denominator pi*x*(1-x)*F(x)^2 is nonzero and tau has complex derivative -i/(pi*x*(1-x)*F(x)^2). The factors x and 1-x are nonzero because the two strict lens inequalities exclude the endpoints, pi is nonzero, and the native disk nonvanishing theorem supplies F(x) != 0.

The derivative is obtained by differentiating the literal quotient and the complementary composition, then substituting the exact Wronskian. The result is restricted to the full complex lens and does not assert an analytic continuation beyond it or any physical source, charge, C-flow, string, or AdS/CFT interpretation.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialWronskian.original_tau_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialWronskian.original_wronskian`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialWronskian.tau`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialEndpoint](OriginalHalfBinomialEndpoint.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity](../VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.md)
