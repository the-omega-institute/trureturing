# Inline Consensus Protocol Pins

## Abstract

The module's sole public theorem discharges every indexed protocol clause.

**Theorem 1.1 (The required inline-consensus fixture suite is pinned).**

$$\forall clause,\ \operatorname{ClauseObject}\left(clause\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.required_fixture_suite_is_pinned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RequiredFixtureSuite unfolds to forall clause, ClauseObject clause. ClauseId has ten constructors, and ClauseObject defines one proposition for each constructor.

The theorem proves exactly that quantified family. Its intermediate fixture obligations are local proofs inside required_fixture_suite_is_pinned, not standalone public declarations.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.required_fixture_suite_is_pinned`
- Dependency: [D5/S0/History/Consensus/InlineConsensusProtocolFixtures](InlineConsensusProtocolFixtures.md)
