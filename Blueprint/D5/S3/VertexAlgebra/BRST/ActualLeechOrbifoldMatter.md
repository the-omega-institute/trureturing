# Virasoro matter on the actual Leech orbifold

## Abstract

The assembled Leech orbifold stress field supplies Virasoro matter of central charge 24.

**Theorem 1.1 (Stress modes on both sectors).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.mode_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.mode_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer n and orbifold state x, the coefficient at n+1 of the assembled field at the fixed stress state acts on the underlying fixed component by the Leech Sugawara mode n, and on the negative twisted component by the corrected tensor half-Fock mode n. Both use the actual inverse Gram matrix. The twisted extraction uses doubled exponent −2n−4 and retains the rank/16 term in mode zero.

**Theorem 1.2 (Central charge 24).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.virasoro`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers m and n, the commutator of the two assembled modes is (m−n) times mode m+n plus the identity multiplied by (24/12)(m³−m) when m+n is zero, with zero central term otherwise.

**Theorem 1.3 (Statewise truncation).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.positive_mode_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.positive_mode_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every orbifold state x there is an integer B such that mode n annihilates x for every integer n greater than B.

**Definition 1.4 (Orbifold matter datum).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.matter`

*Formalization.* `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.matter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual fixed and negative twisted sectors, assembled stress modes, charge 24, Virasoro commutator and statewise truncation give the matter datum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.matter`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.mode_apply`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.positive_mode_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter.virasoro`
- Dependency: [D5/S3/VertexAlgebra/BRST/VirasoroBRST](VirasoroBRST.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic](../Lattice/ActualLeechHyperbolic.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation](../TwistedGround/Orbifold/OriginalOrbifoldTranslation.md)
