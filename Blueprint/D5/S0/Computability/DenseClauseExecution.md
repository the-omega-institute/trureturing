# Restored Dense Word Execution

## Abstract

Actual dictionary construction and lookup produce a clean dense word.

**Theorem 1.1 (Restored Dense Word Execution).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{denseMachine}\right), \operatorname{initList}\left(\mathit{denseMachine}, w\right), \operatorname{some}\left(\operatorname{haltList}\left(\mathit{denseMachine}, \operatorname{denseConverted}\left(w\right)\right)\right), \operatorname{denseRunClock}\left(w\right)\right)\right) \land \left(\forall F \in \mathit{ConventionalFormula},\; \operatorname{readWord}\left(w\right) = \operatorname{some}\left(F\right) \Rightarrow \left(w = \operatorname{formulaWord}\left(F\right) \land \left(\forall c \in \mathit{Clause},\; c \in F \Rightarrow \operatorname{length}\left(c\right) \le 3\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DenseClauseExecution.denseExecution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual parser phase is followed by rightmost dictionary deduplication, dimension writing, restored first-index lookups, literal copying, dictionary draining and output reversal. Every raw word reaches the exact clean haltList containing denseConverted within the phase-by-phase denseRunClock. Malformed input takes the actual drain and zero-variable empty-clause source branch. Accepted input has its full original spelling and clause width; the semantic refinement then supplies the quadratic clock and count transport.

## References

- Truth anchor: `D5/S0/Computability/DenseClauseExecution.denseExecution`
- Dependency: [D5/S0/Computability/DenseClauseMachine](DenseClauseMachine.md)
