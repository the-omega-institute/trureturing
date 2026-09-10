# Complement and Background Charge

## Abstract

Context-preserving event complement has an affine signed readout and negates it exactly under balance.

**Theorem 1.1 (The exact signed complement formula).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.complement_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.complement_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each archived event contributes positive or negative one. Readout sums only selected events; background charge sums the current region. The formula applies Mathlib's finite-sum subtraction theorem with the actual selection containment proof.

**Theorem 1.2 (Balance is exactly the negation guard).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.balanced_iff_complement_negates`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.balanced_iff_complement_negates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero background charge suffices by the affine formula; the empty selection proves necessity. Balance concerns the current region, not every archived event. Complement retains the complete context and is involutive.

**Theorem 1.3 (The readout counts signed events).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.charge_eq_signed_card`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.charge_eq_signed_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum is the integer difference of positive and negative event counts. Numerical opposite fibers reuse the existing complement-fiber API and remain sets of selections. Arithmetic inverses and quotient operations are later constructions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.balanced_iff_complement_negates`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.charge_eq_signed_card`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ComplementCharge.complement_readout`
- Dependency: [D5/S0/History/Spacetime/ArchiveCarrier](../../../S0/History/Spacetime/ArchiveCarrier.md)
- Dependency: [D5/S3/ConceptDynamics/Negation/ComplementFiberLift](../Negation/ComplementFiberLift.md)
