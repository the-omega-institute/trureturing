# Finite Future Split Budget

## Abstract

Finite future refinements obey pair and class-count split budgets.

**Theorem 1.1 (Finite refinements consume a bounded split budget).**

$$\forall X \in Type, B \in Type, finiteX \in \operatorname{Finite}\left(X\right), s \in \mathbb{N}, C \in \operatorname{Fin}\left(s+1\right) \to \operatorname{Concept}\left(X, B\right), strict \in \left(\forall i \in \operatorname{Fin}\left(s\right),\; \operatorname{StrictlyRefines}\left(\operatorname{C}\left(\operatorname{castSucc}\left(i\right)\right), \operatorname{C}\left(\operatorname{succ}\left(i\right)\right)\right)\right),\; s \le \operatorname{choose}\left(\lvert X\rvert, 2\right) \land s \le \lvert X\rvert - \lvert \operatorname{range}\left(\operatorname{C}\left(0\right)\right)\rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/FiniteFutureSplitBudget.finite_future_split_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readouts form a finite chain on the same state carrier. Each strict step preserves existing distinctions and splits at least one old observation class.

The frozen strict-refinement theorem gives the sharp class-count deficit. A nonempty initial image removes one state from that deficit, and the binomial recurrence bounds the remainder by the number of unordered distinct state pairs; the empty carrier is handled separately.

## References

- Truth anchor: `D5/S3/Observer/Budget/FiniteFutureSplitBudget.finite_future_split_budget`
- Dependency: [D5/S3/ConceptDynamics/Refinement/StrictRefinementBound](../../ConceptDynamics/Refinement/StrictRefinementBound.md)
