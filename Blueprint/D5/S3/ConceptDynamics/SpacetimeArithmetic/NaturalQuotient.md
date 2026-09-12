# Retain the nonnegative balanced history domain

## Abstract

Retain the nonnegative balanced history domain.

Formula limitation: these dependent history and quotient declarations are presented through resolving Lean declaration handles. WithoutFormula supplies no independent formula transcription; the Lean declarations specify the exact statements.

**Definition 1.1 (Retain the nonnegative balanced history domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.NonnegativeHistory`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.NonnegativeHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NonnegativeHistory d is the subtype of actual BalancedRich d satisfying zero at most balancedQ. Histories, archive fields, and the nonnegative guard remain present before quotienting.

**Theorem 1.2 (Natural readout has exactly the signed equality kernel).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.numerical_iff_signed`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.numerical_iff_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On this nonnegative domain, casting naturalQ back to Int returns balancedQ. Thus the quotient kernel of naturalQ is precisely equality of signed readouts.

**Definition 1.3 (The actual nonnegative quotient is the natural semiring).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.readoutSemiringEquiv`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.readoutSemiringEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The section uses representative d n for each natural n. Its right-inverse law gives the Mathlib quotient equivalence; semiring structure is transferred only onto that quotient.

**Theorem 1.4 (Zero is the fixed natural zero class).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.zero_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.zero_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural quotient zero is the class of naturalSection d 0.

**Theorem 1.5 (One is the fixed natural one class).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.one_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.one_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural quotient one is the class of naturalSection d 1.

**Theorem 1.6 (Native parallel composition induces natural addition).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.add_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.add_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

parallelNonnegative retains parallelBalanced together with its proved nonnegative readout. Its quotient class is the sum of the input classes.

**Theorem 1.7 (Native product induces natural multiplication).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.mul_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.mul_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

productNonnegative retains productBalanced together with its proved nonnegative readout. Its quotient class is the product of the input classes.

**Theorem 1.8 (Complement stays nonnegative exactly at zero readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.complement_nonnegative_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.complement_nonnegative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative balanced history, native complement is still nonnegative if and only if its original readout is zero.

**Theorem 1.9 (Native complement is not closed on the nonnegative domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.complement_not_closed`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.complement_not_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every spatial dimension, applying the preceding criterion to naturalSection d 1 refutes universal complement closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.NonnegativeHistory`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.add_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.complement_nonnegative_iff`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.complement_not_closed`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.mul_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.numerical_iff_signed`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.one_class`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.readoutSemiringEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.zero_class`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementFibers](../Spacetime/ComplementFibers.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/GeneratedProduct](../Spacetime/GeneratedProduct.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ParallelComposition](../Spacetime/ParallelComposition.md)
