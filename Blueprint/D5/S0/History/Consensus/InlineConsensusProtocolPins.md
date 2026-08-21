# Inline Consensus Protocol Pins

## Abstract

Aggregate mutation pins for the complete inline consensus protocol contract.

**Theorem 1.1 (The required inline-consensus fixture suite is pinned).**

$$RequiredFixtureSuite$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.required_fixture_suite_is_pinned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RequiredFixtureSuite is the conjunction declared in Lean. It includes the stage and carrier equations, disclosure and completion contracts, internal model wiring, Boolean correspondences, router optimality, bounded-run guarantees, named executable and negative fixtures, and the clause, permit-freshness, carrier-governance, and executable-routing pins.

The proof supplies each conjunct from a named Lean theorem and also supplies ClauseObject for every ClauseId. The displayed proposition is the named RequiredFixtureSuite itself; it does not strengthen that conjunction or claim correspondence to any external protocol prose.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.required_fixture_suite_is_pinned`
- Dependency: [D5/S0/History/Consensus/InlineConsensusProtocolFixtures](InlineConsensusProtocolFixtures.md)
