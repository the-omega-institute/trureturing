# Forests suffice for marked parity support

## Abstract

Reduce simultaneous coordinate budgets to an acyclic marked parity support.

**Theorem 1.1 (Coordinate budgets via a forest).**

$$(\operatorname{Even}\left(n + 2\right) \land \operatorname{Odd}\left(k\right)) \Rightarrow (\operatorname{SeedCountsWithin}\left(n, k, z\right) \Leftrightarrow \operatorname{MarkedForestWithin}\left(n, k, z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedForest.forest_support_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension n plus two, the seed side asks for one equivariant uniform seed action with every coordinate fixed count bounded by its corresponding budget. The forest side uses the marked binary support and base margins from the marked support criterion. It also requires the graph of the selected binary entries to be acyclic.

Delete the edges of a cycle. Every affected row or column loses two selected cells. If the cycle uses the marked cell, its base mass changes from one to two. The net base mass at each of its endpoints keeps its previous value. Other affected margins decrease by two.

The marked column contributes just as before, and each ordinary coordinate contribution can only decrease. A feasible subtable with the fewest selected cells is therefore acyclic. Every marked forest supplies a seed action by the binary criterion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedForest.forest_support_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedSupport](ParitySeedSupport.md)
