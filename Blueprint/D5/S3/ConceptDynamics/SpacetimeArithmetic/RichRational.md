# Rich Rational Histories

## Abstract

Actual guarded pairs of balanced histories support exact rational arithmetic.

Formula projection does not express the dependent archive carriers here. The resolving Lean handles carry the typed statements; this narrative supplies no separate formula.

**Definition 1.1 (Two balanced histories and a nonzero denominator).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.Fraction`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.Fraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each component is a balanced rich history with its actual archive, context and selection. The stored denominator proof states that its integer readout is nonzero. Rational readout divides the two integer readouts in Rat.

**Theorem 1.2 (Cross-products characterize equal readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.cross_iff_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.cross_iff_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer cross-product equality is equivalent to rational readout equality by injective integer casts and the standard fraction cancellation theorem. The kernel setoid is on these actual pairs; its equivalence laws give reflexivity, symmetry and transitivity.

**Theorem 1.3 (The inverse guard is numerical nonzeroness).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.inverse_guard_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.inverse_guard_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator must read nonzero for the guarded inverse to swap the two histories. Division has the same condition on the divisor numerator. Both guards are invariant under cross-product equivalence.

**Theorem 1.4 (Native addition has the exact sum readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.add_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.add_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator is the parallel composition of the product of the first numerator with the second denominator, followed by the product of the second numerator with the first denominator. The denominator is the product of the two denominators. Closure and the equation use the actual B2 operations.

**Theorem 1.5 (Native multiplication has the exact product readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.mul_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.mul_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator multiplies the two numerators and the denominator multiplies the two denominators, retaining the generated product archives. Nonzero integer products give denominator closure.

**Theorem 1.6 (Event complement negates the readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.neg_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.neg_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator uses B1 event complement in its balanced context. The denominator is retained literally.

**Theorem 1.7 (Guarded swapping gives the reciprocal readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.inv_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.inv_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse swaps numerator and denominator and requires the numerator readout to be nonzero. This partial rich operation is not extended at zero.

**Theorem 1.8 (Guarded cross-products give the division readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.div_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.div_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Division uses the first numerator times the divisor denominator over the first denominator times the divisor numerator. The divisor-numerator guard makes that denominator nonzero. Congruence is proved with guards for both representatives.

**Theorem 1.9 (Integer embedding keeps the input history).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.integerEmbedding_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.integerEmbedding_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator is exactly the supplied balanced history. The denominator is the arbitrary-d canonical representative of one. Its rational readout is the integer cast of the supplied history readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.Fraction`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.add_readout`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.cross_iff_readout`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.div_readout`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.integerEmbedding_readout`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.inv_readout`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.inverse_guard_iff`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.mul_readout`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.neg_readout`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementFibers](../Spacetime/ComplementFibers.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/GeneratedProduct](../Spacetime/GeneratedProduct.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ParallelComposition](../Spacetime/ParallelComposition.md)
