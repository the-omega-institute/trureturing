# Signed Gaussian J Spatial Equation

## Abstract

Signed Gaussian J Spatial Equation

The regular J candidate and its chart expression have equal values away from the chart poles. The chart derivatives retain the original nonzero modeB(e)*modeB(f) term. Joint analyticity extends the equation across the same-sign diagonal; mixed chart poles are excluded by the original disk bounds.

**Theorem 1.1 (candidateJ_original_displacement).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean label pair and real 0<r<1, with norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, the signed J candidate satisfies the exact original spatial displacement equation, with the original sources, modeA, modeH, central derivative divided by period, and the additive term modeB(e)*modeB(f). Axes, origin and diagonal are included.

**Theorem 1.2 (candidateJ_cleared).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_cleared`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_cleared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-domain polynomial-cleared J identity consumes the existing private chart. Same-sign diagonals follow directly from the actual source square; mixed poles are excluded by the source domain. This helper is consumed by all-natural-mode finite identification.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_cleared`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource](CandidateSource.md)
