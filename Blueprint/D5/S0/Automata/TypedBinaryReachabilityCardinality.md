# Reachability Cardinality in Binary Typed DFAOs

## Abstract

In a reachable binary Zeckendorf-typed partial DFAO, every previous-one state has a distinct previous-zero predecessor under input one, hence the previous-one fiber has no more states than the previous-zero fiber.

**Theorem 1.1 (Every reachable previous-one state has a previous-zero predecessor).**

$$\exists s, \operatorname{stateType}(s) = \operatorname{previousZero}() \land \operatorname{step}(s, 1) = \operatorname{some}(t)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TypedBinaryReachabilityCardinality.reachable_previousOne_has_one_predecessor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A run ending in a previous-one state cannot be empty. Decomposing its input at the final symbol and using the typed transition law shows that the final symbol is one and that the predecessor state has previous-zero type.

**Theorem 1.2 (The previous-one fiber has no more states than the previous-zero fiber).**

$$\operatorname{card}(\operatorname{PreviousOneState}(M)) \leq \operatorname{card}(\operatorname{PreviousZeroState}(M))$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TypedBinaryReachabilityCardinality.previousOne_card_le_previousZero_card_of_allStatesReachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose one previous-zero predecessor for every previous-one state. Determinism makes this choice injective, because one source state on the same input symbol cannot reach two distinct targets.

The result removes every exact reachable type split with more previous-one than previous-zero states before SAT search. It does not by itself exclude balanced or previous-zero-heavy splits.

## References

- Truth anchor: `D5/S0/Automata/TypedBinaryReachabilityCardinality.previousOne_card_le_previousZero_card_of_allStatesReachable`
- Truth anchor: `D5/S0/Automata/TypedBinaryReachabilityCardinality.reachable_previousOne_has_one_predecessor`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](TypedPartialDFAOOverBase.md)
