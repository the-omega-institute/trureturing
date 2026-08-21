# Inline Consensus Protocol Fixtures

## Abstract

Router-ready design, review, and termination states admit routed protocol transitions.

**Theorem 1.1 (Router-ready states admit routed transitions).**

$$(\forall config, state, situation,\ \operatorname{DesignRouterReady}\left(config, state, situation\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{DesignRouteTransition}\left(config, state, situation\right)\right))\\ \land (\forall config, state, results,\ \operatorname{ReviewRouterReady}\left(config, state, results\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{ReviewRouteTransition}\left(config, state, results\right)\right))\\ \land (\forall config, state, observation,\ \operatorname{TerminationRouterReady}\left(config, state, observation\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{TerminationRouteTransition}\left(config, state, observation\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.router_transitions_are_exhaustive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three conjuncts are conditional on DesignRouterReady, ReviewRouterReady, and TerminationRouterReady respectively. Under those hypotheses the theorem constructs a nonempty DesignRouteTransition, ReviewRouteTransition, or TerminationRouteTransition for the supplied situation, results, or observation.

Each transition contains a ProtocolStep, and the review and termination transitions record an output equal to the corresponding router result. The proposition makes no transition claim for an arbitrary state that does not satisfy the relevant readiness structure.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.router_transitions_are_exhaustive`
- Dependency: [D5/S0/History/Consensus/InlineConsensusExecution](InlineConsensusExecution.md)
