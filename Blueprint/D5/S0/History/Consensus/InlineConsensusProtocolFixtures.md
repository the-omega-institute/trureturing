# Inline Consensus Protocol Fixtures

## Abstract

Named fixtures exercise the fail-closed inline-consensus protocol and are consumed by one aggregate theorem.

**Theorem 1.1 (Required fixtures are aggregate-pinned).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.required_fixture_suite_is_pinned`

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.required_fixture_suite_is_pinned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjunction consumes the termination rows, both competitor witnesses, all five completion failures, forbidden-proxy rejection, the correlated-prior countermodel, carrier-selection rows, the review truth table, fixed role-cardinality checks, all-reject review routing, unauthorized-budget rejection, and the unavailable-isolation execution and finish prohibition. It pins internal model behavior only; correspondence to the external sshx prose remains the digest-pinned snapshot claim in Inline Consensus Optimality.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolFixtures.required_fixture_suite_is_pinned`
- Dependency: [D5/S0/History/Consensus/InlineConsensusOptimality](InlineConsensusOptimality.md)
