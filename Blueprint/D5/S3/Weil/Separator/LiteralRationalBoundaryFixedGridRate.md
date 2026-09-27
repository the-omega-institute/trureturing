# Rate Certificate for a Literal Rational Fixed Grid

## Abstract

The literal rational fixed grid has an explicit mesh-plus-scalar dyadic width rate.

**Theorem 1.1 (Explicit mesh and scalar error budgets).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate.fixedGridRateCertified`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate.fixedGridRateCertified` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the exact payload built by boundaryGrid R p q k s, the theorem derives rational amplitude caps for all four endpoints of the real and imaginary integral intervals. Polynomial value and derivative bounds, cutoff and exponential bounds, and a telescoping cell estimate produce explicit constants Cmesh and Cscalar.

The completed-square width is at most Cmesh/2^k plus Cscalar*(1/2)^s. Both the mesh error and scalar-enclosure error are proved for the computed signed payload; neither is accepted from the caller.

This rate controls only the pole-boundary enclosure for the literal same-H family. It does not certify compact, prime, or Archimedean intervals, assert an off-line zero, extract a negative witness, or prove the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate.fixedGridRateCertified`
- Dependency: [D5/S3/Weil/Separator/LiteralRationalBoundaryGrid](LiteralRationalBoundaryGrid.md)
