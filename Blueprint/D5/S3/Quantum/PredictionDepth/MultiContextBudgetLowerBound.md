# Multi-Context Budget Lower Bound

## Abstract

Informationally complete normalized contexts obey a dimension lower bound.

**Theorem 1.1 (Normalized contexts require enough independent outcomes).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}\left(d\right),\\{}C: \operatorname{Type}, \operatorname{Fintype}\left(C\right),\\{}n: C \to \mathbb{N},\\{}E: \forall x: C, \operatorname{Fin}\left(\operatorname{n}\left(x\right)+1\right) \to \operatorname{traceZeroHermitian}\left(d\right),\\{}\forall x: C, \sum_{j\in \operatorname{Fin}\left(\operatorname{n}\left(x\right)+1\right)} E\left(x, j\right) = 0,\\{}\operatorname{Injective}\left((\rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right) \mapsto (x: C \mapsto (j: \operatorname{Fin}\left(\operatorname{n}\left(x\right)+1\right) \mapsto \Re \operatorname{Tr}\left(\operatorname{matrix}\left(\rho\right) E\left(x, j\right)\right))))\right) \Rightarrow\\{}d^{2}-1 \leq \sum_{x\in C} \operatorname{n}\left(x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound.multi_context_budget_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outcome directions live on the canonical real trace-zero Hermitian carrier. Each context has n_x plus one outcomes, and normalization makes their centered directions sum to zero.

Injectivity is stated on positive trace-one density states. The canonical completeness equivalence turns it into full span. Dropping the last outcome of every context preserves that span, so its cardinality bounds the carrier dimension d squared minus one.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound.multi_context_budget_lower_bound`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
