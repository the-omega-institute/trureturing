# Clauses satisfied by the cube supports

## Abstract

Normalized shared-contact supports satisfy the degree, parity and geometric clauses.

**Theorem 1.1 (Upper degree clauses).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.upperClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.upperClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The valuation makes each vertex bit equal to support membership. Four distinct occupied neighbors would violate cubicity.

**Theorem 1.2 (Lower degree clauses).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.lowerClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.lowerClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Seven omitted neighbors at an occupied vertex would violate cubicity.

**Theorem 1.3 (Each prefix parity extends by exclusive-or).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.parityClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.parityClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix variables store successive parities of occupied neighbors. At the last coordinate the output is the occupancy bit. The four clauses give the truth table for one such update.

**Theorem 1.4 (Square exclusion clauses).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.squareClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.squareClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

XOR with one coordinate bit gives the corresponding cube neighbor. The four occupied vertices would form a square.

**Theorem 1.5 (Separation clauses).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.separationClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.separationClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two supports cannot contain both vertices of a cross-pair at distance at most two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.lowerClause`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.parityClause`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.separationClause`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.squareClause`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF.upperClause`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics](Q9SharedContactClauseSemantics.md)
