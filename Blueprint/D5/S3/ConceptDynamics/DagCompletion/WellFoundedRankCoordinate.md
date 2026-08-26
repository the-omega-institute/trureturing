# Well-Founded Rank Coordinate

## Abstract

Every well-founded dependency relation has a canonical strict ordinal rank coordinate.

**Theorem 1.1 (Canonical well-founded rank is strict).**

$$\forall edge: V \to V \to Prop,\\{}\forall wellFounded: \operatorname{WellFounded}\left(edge\right),\\{}\operatorname{StrictDependencyCoordinate}\left(edge, \operatorname{dependencyRank}\left(wellFounded\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/WellFoundedRankCoordinate.dependencyRank_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a well-founded dependency relation, assign each node the ordinal rank of its accessibility proof. Every direct dependency edge strictly increases this canonical rank.

The well-foundedness premise is explicit. The theorem packages strictness as StrictDependencyCoordinate and does not claim the rank map is injective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/WellFoundedRankCoordinate.dependencyRank_strict`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate](../DagSemantics/StrictDependencyCoordinate.md)
