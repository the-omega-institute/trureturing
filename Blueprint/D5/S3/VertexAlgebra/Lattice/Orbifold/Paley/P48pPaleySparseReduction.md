# Anchoring P48p Paley Inputs

## Abstract

Every nonzero Paley input can be anchored with both graph weights preserved.

**Theorem 1.1 (Projective moves and a global sign give an anchored row).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseReduction.exists_anchored_paleyRow`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseReduction.exists_anchored_paleyRow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A projective move followed by an optional global sign fixes the infinity coefficient to one and preserves both input and output Hamming weights. Weight one uses only infinity, weight two uses infinity and zero, and weight at least three also occupies one.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseReduction.exists_anchored_paleyRow`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyTripleNormalization](P48pPaleyTripleNormalization.md)
