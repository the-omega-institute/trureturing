# Sharp finite positive expansivity for transitive finite graphs

## Abstract

Sharp finite positive expansivity for transitive finite graphs

**Theorem 1.1 (A transitive map has forward Bowen order at most one below the maximum valence).**

Lean statement: `D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphTransitiveValence.forwardBowenBound_of_transitive_multigraph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphTransitiveValence.forwardBowenBound_of_transitive_multigraph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite connected graph with at least one edge have maximum valence at most D, with D at least two. A continuous topologically transitive finitely positively expansive self-map has a positive scale at which each forward Bowen ball has at most D minus one points. Loops count twice in the valence.

The forward images of an arc in a nonempty open set miss at most a finite totally invariant set, which finite positive expansivity and transitivity force to be empty. This gives pointwise strong transitivity and allows the two-arm count in the affine subdivision to be transported to the original graph. The parallel-edge construction attains the bound for every D at least three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphTransitiveValence.forwardBowenBound_of_transitive_multigraph`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller](../../../../S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller.md)
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier](../../../../S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier.md)
- Dependency: [D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound](FiniteGraphValenceBound.md)
