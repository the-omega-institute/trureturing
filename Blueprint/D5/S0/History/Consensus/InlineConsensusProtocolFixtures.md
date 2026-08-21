# Inline Consensus Protocol Fixtures

## Abstract

Router-ready states admit route-transition witnesses governed by inlineConsensusModel.

**Theorem 1.1 (Router-ready states admit routed transitions).**

$$\operatorname{RouterTransitionsExhaustive}\left(inlineConsensusModel\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.router_transitions_are_exhaustive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RouterTransitionsExhaustive inlineConsensusModel expands to three universally quantified implications. DesignRouterReady, ReviewRouterReady, and TerminationRouterReady are each parameterized by inlineConsensusModel; under the corresponding readiness hypothesis, the theorem constructs a nonempty DesignRouteTransition, ReviewRouteTransition, or TerminationRouteTransition with that same model.

Each witness contains an inlineConsensusModel.transition step. The design event is selected by the model's designRoute, while the review and termination witnesses record an output equal to the corresponding model router result. The proposition makes no transition claim for an arbitrary state that does not satisfy the relevant readiness structure, and it does not quantify over arbitrary models.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.router_transitions_are_exhaustive`
- Dependency: [D5/S0/History/Consensus/InlineConsensusExecution](InlineConsensusExecution.md)
