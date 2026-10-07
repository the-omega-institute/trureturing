# Straight continuations and finite path counts

## Abstract

For every fixed relative ordering, complete ordered deletion from the single parent blocker has at least one path at every depth. Complete counts and geometric-memory counts at every positive radius are bounded by three to the depth, including depth zero.

Let P be the singleton integer-grid blocker at (-1, 0). Ccomplete(a, n) is pathCount for completeStep, with the constant policy selecting a at every history and blocker set, depth n, empty initial history and initial blockers P. Cmemory(r, a, n) uses geometricStep r with exactly the same policy, depth, history and initial blockers. The six values of a are the six relative neighbor orderings; r is a natural-number retention radius.

**Theorem 1.1 (Positive complete counts and uniform upper bounds).**

$$\forall a \in \operatorname{Fin}\left(6\right),\; \forall n \in \mathbb{N},\; (1 \le \operatorname{Ccomplete}\left(a, n\right) \land (\operatorname{Ccomplete}\left(a, n\right) \le 3^{n} \land (\forall r \in \mathbb{N},\; 1 \le r \Rightarrow (\operatorname{Cmemory}\left(r, a, n\right) \le 3^{n}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/CompleteStraightPathCounts.complete_straight_path_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward direction is (1, 0). If every recorded blocker has first coordinate at most zero, this direction is available. Every newly deleted point is either the current origin or a candidate neighbor, so its first coordinate is at most one, independently of the ordering. The forward recentering subtracts one from that coordinate. Thus the actual complete update preserves the weak left half-plane. Induction on depth retains the forward summand in the recursive path count, starting from P; at depth zero the count is one.

The fixed-order block bound with zero full blocks bounds every positive-radius memory count by three to the depth. Complete-count domination by radius-one memory then supplies the complete upper bound. These are finite-depth integer bounds and do not assert any growth-rate limit or interchange of infima.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/CompleteStraightPathCounts.complete_straight_path_bounds`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds](MemoryBlockBounds.md)
