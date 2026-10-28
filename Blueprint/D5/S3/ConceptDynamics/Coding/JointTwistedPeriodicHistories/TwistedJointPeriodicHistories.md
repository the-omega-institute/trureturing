# Joint twisted periodic histories

## Abstract

Joint twisted returns reduce to one signed gcd return in an arbitrary finite group.

For a GroupMat C and natural parameters d,a,b, JointTwistedPeriod records one actual expanded history satisfying the h-twist at d*a and the g-twist at d*b. The coefficients a.gcdA b and a.gcdB b are the signed Bezout coefficients for the natural gcd.

**Definition 1.1 (The joint return carrier).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.JointTwistedPeriod`

*Formalization.* `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.JointTwistedPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier retains the actual history and both shift equations, including all numbered parallel edges and the left group-coordinate action.

**Theorem 1.2 (Joint returns force noncommutative compatibility).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.joint_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.joint_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single actual history carrying both returns forces Commute h g and h^b=g^a by comparing the same signed-time coordinate in the two orders.

**Theorem 1.3 (Two returns imply the signed gcd return).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.joint_to_gcd`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.joint_to_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bezout signed recovery combines the two return equations into a return at time d with twist h^(a.gcdA b)*g^(a.gcdB b).

**Theorem 1.4 (History-preserving gcd equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.jointGcdEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.jointGcdEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under commutation and the power relation, signed recovery reconstructs both original returns from the gcd return, yielding an equivalence of actual-history subtypes.

**Theorem 1.5 (Exact joint coefficient count).**

Lean statement: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.jointTwistedPeriod_card`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.jointTwistedPeriod_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and compatible twists, the joint carrier has the existing diagonal conjugacy sum at the gcd time.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.JointTwistedPeriod`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.jointGcdEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.jointTwistedPeriod_card`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.joint_compatibility`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.joint_to_gcd`
- Dependency: [D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories](../TwistedPeriodicHistories.md)
