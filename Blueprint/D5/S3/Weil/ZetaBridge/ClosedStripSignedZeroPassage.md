# The full signed zero sum under a closed-strip envelope

## Abstract

Pass to the actual complete signed Weil zero sum using the existing zeta zero-count summability and one uniform transform envelope.

**Theorem 1.1 (Retain actual zeros, multiplicities and conjugate arguments).**

Lean statement: `D5/S3/Weil/ZetaBridge/ClosedStripSignedZeroPassage.actual_zeta_signed_zero_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ClosedStripSignedZeroPassage.actual_zeta_signed_zero_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V_n converge pointwise to U on the full closed strip |Im z|<=1/2, with the same nonnegative D bounding each |V_n(z)| by D/(1+(Re z)^2). The complete actual zeta-zero series with terms m_rho V_n(gamma_rho) times the conjugate of V_n(conjugate gamma_rho) is summable at every n; the corresponding U series is summable, and the series converge.

The actual closed-strip bound gives 1+|gamma|^2 <= (5/4)(1+(Re gamma)^2)^2. Thus every term is bounded by (5D^2/4) m_rho/(1+|gamma_rho|^2). The existing actual ZetaSeam zero-summability theorem pays this majorant, and dominated convergence for series pays the limit. No new contour or zero-count argument is introduced.

The original signed complex product is retained at every zero. It is not replaced by an absolute square, and no critical-line premise, positivity conclusion, extension to an arbitrary physical domain or RH claim is made.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ClosedStripSignedZeroPassage.actual_zeta_signed_zero_tendsto`
- Dependency: [D5/S3/Weil/ZetaExplicit/ZeroSummability](../ZetaExplicit/ZeroSummability.md)
