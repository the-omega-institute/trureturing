# Critical matter on the orbifold and hyperbolic lattice

## Abstract

The literal Leech orbifold and hyperbolic lattice field give critical matter.

**Definition 1.1 (Hyperbolic lattice matter).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.hyperbolicMatter`

*Formalization.* `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.hyperbolicMatter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standalone even hyperbolic plane with Gram matrix U has U as its inverse. Its Sugawara field gives integer Virasoro modes of central charge 2. Hahn order gives statewise positive-mode truncation.

**Definition 1.2 (Central charge 26).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.matter`

*Formalization.* `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.matter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the tensor product of the actual orbifold carrier and hyperbolic lattice carrier, each mode is the sum of the two original modes acting on their respective factors. These actions commute across factors. The central terms add to 26, and tensor induction gives a positive-mode bound for every state.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.hyperbolicMatter`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.matter`
- Dependency: [D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter](ActualLeechOrbifoldMatter.md)
