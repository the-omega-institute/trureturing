# Orbit--centralizer decomposition of joint twisted returns

## Abstract

The joint twisted coefficient count is an orbit sum weighted by the centralizer cardinality.

The existing signed-gcd cardinality is a raw sum over the group coordinate. The new result reindexes that sum through the finite conjugation action and counts each orbit element with the stabilizer, identified here with the centralizer. The reusable action theorem below is the abstract orbit--stabilizer sum identity; the conjugation calculation consumes it.

**Theorem 1.1 (Finite action orbit--stabilizer sum).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.orbit_sum_eq_stabilizer_nsmul_sum`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.orbit_sum_eq_stabilizer_nsmul_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite group action and any additive-monoid-valued function, summing over all group elements equals summing over the orbit, with the stabilizer cardinality acting by repeated addition on each value.

**Theorem 1.2 (Orbit--centralizer weighted coefficient count).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.jointTwistedPeriod_card_orbit_centralizer`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.jointTwistedPeriod_card_orbit_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every compatible pair of twisted returns, the diagonal coefficient sum equals the sum over the conjugation orbit of the signed gcd twist, with the cardinality of its centralizer multiplying each coefficient.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.jointTwistedPeriod_card_orbit_centralizer`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.orbit_sum_eq_stabilizer_nsmul_sum`
- Dependency: [D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories](TwistedJointPeriodicHistories.md)
