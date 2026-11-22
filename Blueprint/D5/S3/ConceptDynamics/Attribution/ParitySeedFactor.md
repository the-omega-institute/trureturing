# Parity factors for coordinate budgets

## Abstract

Express simultaneous coordinate budgets through degree constraints and additive edge counts.

**Theorem 1.1 (Coordinate budgets via a parity factor).**

$$(\operatorname{Even}\left(n + 2\right) \land \operatorname{Odd}\left(k\right)) \Rightarrow (\operatorname{SeedCountsWithin}\left(n, k, b\right) \Leftrightarrow \operatorname{MarkedFactorWithin}\left(n, k, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedFactor.parity_factor_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension n plus two, the seed side asks for one equivariant uniform seed action with every coordinate fixed count bounded by its budget b.

The factor side chooses a marked odd column and a Boolean indicating whether the marked cell was selected. The residual bipartite support excludes the edge between the all-ones row and that column. When the bit is true, both endpoints have even degree at most k minus one. When it is false, k is at least three and both endpoints have odd degree at most k minus two. Every other vertex has odd degree at most k.

For each coordinate, the count is four times the sum of the marked-column membership indicator and the number of residual edges whose row is other than the all-ones row and whose two endpoints both contain the coordinate. Each count must be at most the corresponding budget.

Remove the marked edge and retain its bit. In each affected margin, the original base mass equals the residual degree plus one for a true bit or plus two for a false bit. Restoring the bit reverses this construction. Both operations preserve the coordinate counts of the marked support.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedFactor.parity_factor_budget_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedSupport](ParitySeedSupport.md)
