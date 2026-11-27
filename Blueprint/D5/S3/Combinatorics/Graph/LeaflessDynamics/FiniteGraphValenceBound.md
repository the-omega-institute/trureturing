# A valence bound for forward Bowen balls on finite graphs

## Abstract

A valence bound for forward Bowen balls on finite graphs

**Theorem 1.1 (Forward Bowen order at most one below the maximum valence).**

Lean statement: `D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound.forwardBowenBound_of_stronglyTransitive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound.forwardBowenBound_of_stronglyTransitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the maximum valence of a nontrivial connected finite graph be at most D, with D at least two. A continuous strongly transitive finitely positively expansive map has a uniform positive radius at which each forward Bowen ball contains at most D minus one points.

Strong transitivity supplies an image passing through each vertex from an open edge. The absence of folds in the open edge gives an immersed path whose image contains two incident arms at the vertex. Distinct points on that path separate at a uniform scale. Each remaining arm can contribute at most one point at that scale. Away from vertices the entire Bowen ball lies in a short edge interval and contains at most one point.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound.forwardBowenBound_of_stronglyTransitive`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs](../../../../S1/Dynamics/Shadowing/FiniteGraphBowenArcs.md)
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold](../../../../S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold.md)
- Dependency: [D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivisionRealization](TripleEdgeSubdivisionRealization.md)
