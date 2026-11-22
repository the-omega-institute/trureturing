# C2-Cofiniteness of the Leech Extension

## Abstract

The relative odd quotient and the intrinsic C2 quotient of the assembled Leech extension are finite dimensional over the complex numbers.

**Theorem 1.1 (Finite dimensionality of the two quotients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/Cofiniteness.leech_c2_cofinite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/Cofiniteness.leech_c2_cofinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a nonzero negative twisted state. The difference-one spanning theorem gives strictly increasing mode words in a finite set of homogeneous fixed-source representatives. The fixed-source field has an upper mode cutoff on the chosen state, uniform over the representatives. A word meeting the cutoff vanishes because its largest mode acts first.

A word with smallest index at most minus two has zero relative quotient class by fixed_odd_mode_mem_relativeOddC2. Each remaining word has distinct indices in the finite interval from minus one to the cutoff, excluding the cutoff. Tuples of bounded length in the product of that interval and the representative set therefore give a finite family whose quotient classes span. The zero carrier case has a zero quotient.

The fixed-sector C2 quotient is finite dimensional. The surjective sector comparison then gives finite dimensionality of the intrinsic extension quotient, whose C2 subspace uses minus-two products of arbitrary extension states.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/Cofiniteness.leech_c2_cofinite`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction](../ActualLeechRelativeOddAction.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/ActualLeech](ActualLeech.md)
