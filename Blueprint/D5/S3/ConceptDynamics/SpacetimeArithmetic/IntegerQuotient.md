# Balanced histories modulo signed readout form the integer ring

## Abstract

Balanced histories modulo signed readout form the integer ring.

Formula limitation: these dependent history and quotient declarations are presented through resolving Lean declaration handles. WithoutFormula supplies no independent formula transcription; the Lean declarations specify the exact statements.

**Definition 1.1 (Balanced histories modulo signed readout form the integer ring).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.readoutRingEquiv`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.readoutRingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is Quotient of the kernel of balancedQ on the actual BalancedRich d. The fixed balancedSection is a right inverse. Mathlib transfers the integer ring structure onto this quotient and provides the readout ring equivalence. No ring is assigned to either raw carrier.

**Theorem 1.2 (Numerical equivalence is exactly equality of classes).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.class_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.class_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient identifies precisely histories with equal signed readout.

**Theorem 1.3 (Zero is the fixed empty representative class).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.zero_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.zero_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quotient zero is the class of balancedSection d 0, whose underlying history is representative d 0.

**Theorem 1.4 (One is the fixed value-one representative class).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.one_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.one_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quotient one is the class of balancedSection d 1.

**Theorem 1.5 (Addition is induced by native parallel composition).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.add_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.add_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all balanced histories the sum of their classes equals the class of the B2 parallelBalanced operation.

**Theorem 1.6 (Multiplication is induced by the archive-preserving product).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.mul_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.mul_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all balanced histories the product of their classes equals the class of the B2 productBalanced operation.

**Theorem 1.7 (Negation is induced by event complement).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.neg_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.neg_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative of each class is the class of its B1 native complementBalanced history.

**Theorem 1.8 (The specified action uniquely determines the ring equivalence).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.readoutRingEquiv_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.readoutRingEquiv_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any ring equivalence to Int acting as balancedQ on every representative class equals readoutRingEquiv. The preceding readout_unique theorem proves this even among functions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.add_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.class_eq_iff`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.mul_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.neg_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.one_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.readoutRingEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.readoutRingEquiv_unique`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.zero_class`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementFibers](../Spacetime/ComplementFibers.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/GeneratedProduct](../Spacetime/GeneratedProduct.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ParallelComposition](../Spacetime/ParallelComposition.md)
