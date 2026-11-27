# Degrees and parity in the neighbor list

## Abstract

Cubicity and exterior evenness constrain neighbor bits and their prefix parity.

**Theorem 1.1 (Among four axes some neighbor is omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.upperDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.upperDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An occupied vertex has three occupied neighbors, so four distinct axes cannot all lead to occupied vertices.

**Theorem 1.2 (Among seven axes some neighbor is occupied).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.lowerDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.lowerDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an occupied vertex, only six axes can lead to omitted vertices.

**Theorem 1.3 (Final neighbor parity equals occupancy).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.prefixParity_last`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.prefixParity_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The last prefix contains all nine directions. Its degree is odd at an occupied vertex and even at an exterior vertex. The prefix starts with the first neighbor bit and updates by exclusive-or with the next neighbor bit.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.lowerDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.prefixParity_last`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics.upperDegree`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactNormalized](Q9SharedContactNormalized.md)
