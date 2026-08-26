# Agenda Power in a Majority Cycle

## Abstract

Changing only the order of sequential pairwise comparisons can make any candidate win the fixed three-voter majority cycle.

**Theorem 1.1 (Every candidate wins under a suitable valid agenda).**

$$\left(\forall w \in \operatorname{Fin}\left(3\right),\; \exists g \in Agenda,\; \operatorname{ValidAgenda}\left(g\right) \land \operatorname{sequentialWinner}\left(majorityPrefers, g\right) = w\right) \land \left(\exists g \in Agenda, h \in Agenda,\; \operatorname{ValidAgenda}\left(g\right) \land \left(\operatorname{ValidAgenda}\left(h\right) \land \left(\left(\neg g = h\right) \land \left(\neg \operatorname{sequentialWinner}\left(majorityPrefers, g\right) = \operatorname{sequentialWinner}\left(majorityPrefers, h\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/AgendaPower.agenda_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preference profile and pairwise-majority rule are inherited unchanged from the canonical three-voter cycle. An agenda merely chooses which two distinct candidates meet first and which candidate remains for the final comparison.

The orders 0-then-1 with 2 remaining, 1-then-2 with 0 remaining, and 2-then-0 with 1 remaining yield 2, 0, and 1 respectively. Thus every candidate is attainable, while two valid orders demonstrably return different winners under the same rule.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/AgendaPower.agenda_power`
- Dependency: [D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder](MajorityCycleNotScalarOrder.md)
