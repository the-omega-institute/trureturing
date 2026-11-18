# Original Gaussian Kernel Parity and Positive-Sector Uniqueness

## Abstract

Original Gaussian Kernel Parity and Positive-Sector Uniqueness

The external columns and internal matrix entries have monomial sign factors. The remaining explicit odd-resolvent factors depend on z squared. Every internal sign occurs twice in the literal contractions, including the full square-resolvent identity contribution.

The coefficient equations are those of the positive-sector operators L_u-L_v and z partial_z-L_u-L_v, where L_u=u(1-u) partial_u+(1-3u)/2. They exclude precisely the odd-z diagonal resonance. Uniqueness is proved conditionally on Taylor extraction; existence of a common solution for arbitrary right-hand sides is not claimed.

The existing displacement_differential and radial_differential theorems act on the original kernelMode and full externalT. Their conversion to the coefficient hypotheses, with the actual negative-zero rows canceled, remains to be proved. A complete analytic candidate, normalized branches and removable singularities, verification of both equations and boundaries, and equality in every signed sector remain separate obligations. Literal parity and the coefficient induction alone do not identify the complete kernels.

**Theorem 1.1 (externalJ_neg).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalJ_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalJ_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every literal external J mode is even for all signs, natural labels and complex z. The summands agree before any convergence hypothesis is imposed.

**Theorem 1.2 (externalT_neg).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every literal full T mode is even for all signs, natural labels and complex z. The proof treats both the direct identity pairing and the triple sum.

**Theorem 1.3 (kernelMode_neg).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.kernelMode_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.kernelMode_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either J or T and every sign sector, the actual two-mode generator is even in z for all complex external variables.

**Theorem 1.4 (positive_even_coefficients_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.positive_even_coefficients_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.positive_even_coefficients_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex array c(p,q,k), zero odd coefficients and the two displayed homogeneous frequency and radial recurrences force every coefficient to vanish. Negative external indices are represented by explicit zero branches. Strong induction on p+q uses p-q off the diagonal; on the diagonal, k-2p-1 cannot vanish at an even exponent.

**Theorem 1.5 (externalT_positive_germ_unique).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a candidate be even in z for every natural pair of output labels. If its difference from the literal full externalT has the stated scalar Taylor expansions at zero and those coefficients satisfy both homogeneous recurrences with zero negative-index boundaries, then each literal output/output mode equals the candidate on a neighborhood of zero. No equality is assumed, and no diagonal initial values are needed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalJ_neg`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_neg`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.kernelMode_neg`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.positive_even_coefficients_zero`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums](OriginalGaussianExternalRadialSums.md)
