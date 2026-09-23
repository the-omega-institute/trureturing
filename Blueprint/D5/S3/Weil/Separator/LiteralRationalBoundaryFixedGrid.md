# Semantic Certificate for a Literal Rational Fixed Grid

## Abstract

Every computed fixed grid for the literal same-H family is checker-valid and semantically encloses its half-line pole-boundary integral.

**Theorem 1.1 (The computed fixed grid encloses the exact half-line integral).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid.fixedGridSemanticCertified`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid.fixedGridSemanticCertified` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural radius R and arbitrary rational p, q and dyadic depths, the theorem consumes exactly boundaryGrid R p q k s. Every cell expression and the final expression pass their checkers, and the assembled payload is valid.

The real and imaginary rational intervals enclose the half-line integral of the literal function smoothTransition(2-|x|/R) times rationalEvenPolynomial p q x. Signed four-corner interval multiplication is retained throughout, and completed squaring uses the explicit positive, negative, and zero-crossing branches. The resulting interval encloses twice the complex norm square.

This fixed-grid theorem does not choose a precision depth or prove a full-line identity. It does not certify compact, prime, or Archimedean intervals, assert an off-line zero, extract a negative witness, or prove the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid.fixedGridSemanticCertified`
- Dependency: [D5/S3/Weil/Separator/LiteralRationalBoundaryGrid](LiteralRationalBoundaryGrid.md)
- Dependency: [D5/S3/Weil/TestFunctions/RationalCutoffApproximation](../TestFunctions/RationalCutoffApproximation.md)
