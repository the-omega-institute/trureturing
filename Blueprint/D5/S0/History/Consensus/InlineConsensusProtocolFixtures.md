# Inline Consensus Protocol Fixtures

## Abstract

Named protocol executions witness every design, review, and termination router exit.

**Theorem 1.1 (Router transitions are exhaustive).**

$$RouterTransitionsExhaustive$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.router_transitions_are_exhaustive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RouterTransitionsExhaustive is the conjunction of three propositions: every DesignExit has a nonempty DesignRouteTransition, every ReviewExit has a nonempty ReviewRouteTransition, and every TerminationExit has a nonempty TerminationRouteTransition.

The proof assembles named ProtocolStep fixtures for implementation, successful and exhausted convergence, stalled and fake-consensus design exits, repair, termination candidacy, user decision and repeated review, and all four termination exits. It proves transition-level inhabitation, not that every arbitrary protocol state can take every route.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.router_transitions_are_exhaustive`
- Dependency: [D5/S0/History/Consensus/InlineConsensusExecution](InlineConsensusExecution.md)
