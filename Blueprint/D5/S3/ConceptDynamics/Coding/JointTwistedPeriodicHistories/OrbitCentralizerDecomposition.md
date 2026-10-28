# Orbit--centralizer decomposition of joint twisted returns

## Abstract

The joint twisted coefficient count is an orbit sum weighted by the centralizer cardinality.

The existing signed-gcd cardinality is a raw sum over the group coordinate. The new result reindexes that sum through the finite conjugation action and counts each orbit element with the stabilizer, identified here with the centralizer.

**Theorem 1.1 (Orbit--centralizer weighted coefficient count).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.jointTwistedPeriod_card_orbit_centralizer`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.jointTwistedPeriod_card_orbit_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every compatible pair of twisted returns, the diagonal coefficient sum equals the sum over the conjugation orbit of the signed gcd twist, with the cardinality of its centralizer multiplying each coefficient.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.jointTwistedPeriod_card_orbit_centralizer`
- Dependency: [D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories](TwistedJointPeriodicHistories.md)
