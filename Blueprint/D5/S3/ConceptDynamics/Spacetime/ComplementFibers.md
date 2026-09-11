# Opposite Fibers and Scalar Sections

## Abstract

Balanced finite histories occupy opposite readout fibers, and scalar sections lose history.

**Theorem 1.1 (Canonical complements lie in the opposite readout fiber).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.representative_complement_mem_oppositeFiber`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.representative_complement_mem_oppositeFiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual canonical archive is balanced, so the B1 complement theorem places its context-preserving event complement in the numerical opposite fiber, for every d.

**Theorem 1.2 (A nonempty balanced context has distinct empty and full fiber members).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.empty_full_fiber_members_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.empty_full_fiber_members_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Balance makes the empty and full selections both read zero, hence both belong to Opp(empty). Nonemptiness of the current region proves the two dependent selections are distinct.

**Theorem 1.3 (The exact integer representatives form a scalar right inverse).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.balancedSection_rightInverse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.balancedSection_rightInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The section is the balanced wrapper around the literal representative archive. Its readout is n by the canonical representative theorem, so it is a right inverse of scalar readout on BalancedRich d for every d, including the source d=3.

**Theorem 1.4 (Every scalar right inverse has the frozen lift-square law).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.sectionLift_square_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.sectionLift_square_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any dimension d and any section s into BalancedRich d, applying the exact frozen sectionLift_square theorem to L(X)=s(-q(X)) gives L squared equal to s composed with q. The companion involutivity criterion is a direct application of frozen sectionLift_involutive_iff_leftInverse in every d.

**Theorem 1.5 (No scalar section recovers every balanced history).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.scalar_recovery_refuted`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.scalar_recovery_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty canonical zero history and the empty selection in the one-event-pair canonical context are distinct balanced rich histories with equal readout zero. The general witness compares archive cardinalities zero and two in every d. The closed scalar recovery claim concerns BalancedRich 3; its negation uses these actual histories at d=3. The general section is not a left inverse, and its complement lift is not involutive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.balancedSection_rightInverse`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.empty_full_fiber_members_distinct`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.representative_complement_mem_oppositeFiber`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.scalar_recovery_refuted`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementFibers.sectionLift_square_readout`
- Dependency: [D5/S3/ConceptDynamics/Negation/ComplementFiberLift](../Negation/ComplementFiberLift.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementCharge](ComplementCharge.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives](IntegerRepresentatives.md)
