# Geometric clauses for opposing stars

## Abstract

Normalized opposing-star geometry supplies the inputs of the distance-two refutations.

**Theorem 1.1 (Geometric clauses for opposing stars).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF.oddExteriorPairClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF.oddExteriorPairClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polarity and ordered neighbor clauses reuse the signed cube support rules. For a contact starting at odd parity, a two-axis displacement containing an exterior axis would be outside the tight family. This supplies the forbidden cross-support clause needed by the certificates.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF.oddExteriorPairClause`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF](Q9SharedContactCNF.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoNormalized](Q9TightDistanceTwoNormalized.md)
