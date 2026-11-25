# A single parity equation for exact factors at residual rank two

## Abstract

One binary linear parity equation selects the target switching class among exact factors at residual rank two.

**Theorem 1.1 (A linear edge functional selects the reference switching class).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedRankTwoParity.exact_factor_switching_iff_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedRankTwoParity.exact_factor_switching_iff_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite bipartite graph have binary incidence B. Its residual switching space is the kernel of B modulo the cycles in the range of its transpose. Fix integer target degrees, an edge set F realizing those degrees, and a reference edge set w₀ with the same degree parities in a different switching class. If the residual dimension is two, there is one binary linear edge functional ℓ such that every edge set F′ realizing the integer target degrees lies in the switching class of w₀ exactly when ℓ(F + F′) = 1.

Summing incidence on one side counts each edge once. As a result, every cycle has even weight and all exact factors have equal weight. On a cycle c, half its weight plus the overlap with F, taken modulo two, has polar form given by the binary dot product. The equal weights force this quadratic function to vanish on every difference F + F′.

The cycle dot product has radical equal to the bicycles. With the target class as the first basis vector of the two-dimensional quotient, its indicator is x(1 + y). The indicator has the same polar form as the cycle quadratic. Adding the two gives a linear functional on cycles, which extends to the edge space.

Hong, Wu and Xia ask for the value of f₂(Q₉) in Problem 2. The parity equation applies to folded instances whose bipartite incidence and exact degree targets meet the hypotheses. https://arxiv.org/html/2610.09483v1#Thmproblem2

For the separate algorithmic step, Hörsch, Imolay, Mizutani, Oki and Schwarcz give a polynomial-time algorithm for nonzero perfect b-matchings in bipartite graphs in Theorem 3.15. A forced edge in a disjoint component with label ℓ(F) makes the nonzero total label condition exactly the equation ℓ(F + F′) = 1. https://arxiv.org/html/2402.16259#S3.Thmtheorem15

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedRankTwoParity.exact_factor_switching_iff_parity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank](Q9FoldedCycleRank.md)
