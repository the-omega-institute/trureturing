# Signed congruence for the fixed positive-lift cochain

## Abstract

CountedLocalizedGyrationResidue

**Theorem 1.1 (Signed congruence for the fixed positive-lift cochain).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a commutative ring L equipped with reduction rho to ZMod of three to the power e plus one, each matrix entry is lifted to its natural residue plus that modulus. The canonical cochain is the same signed integer gyration polynomial evaluated at these strictly positive representatives, reduced modulo three. Here e is at least the three-adic valuation of the factorial of twice the period. Any signed integer pair with the same reductions gives the same value, by the explicit accepted integral numerator and the clearing-denominator theorem.

**Theorem 1.2 (One rectangular family satisfies the triangle).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift R, U and V separately. Products of their lifts have the correct reductions because rho and integer reduction are ring homomorphisms. Signed agreement compares the cochain on each product with its integer value even when an intermediate dimension vanishes. The nonnegative integer triangle then yields the rectangular localized triangle. The construction is uniform over all dimensions, including zero, and every nonzero period divisible by three.

**Theorem 1.3 (Agreement with actual primitive-path forward gyration).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At natural counted matrices mapped into L through the integers, signed agreement reduces the canonical cochain to the accepted integer lift. Equality of signed and natural binomial coefficients and the accepted original-path comparison identify it with the actual relativeForwardGyration after the quotient to ZMod 3. Zero entries are retained.

**Definition 1.4 (The fixed dyadic specialization).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical dyadic value uses the universal localization reduction at the three-adic valuation of the factorial of twice the period. The three generic theorems apply to this same specialization, giving signed integer agreement, the full rectangular triangle and agreement with actual nonnegative orbit gyration. The localization's integer embedding agrees with the embedding induced by its ring structure, by uniqueness of ring homomorphisms from the integers. No separate period or square wrapper is needed. These arguments use classical integer-valued polynomial congruences and localization; they assert no novelty, full mod-six law, image exhaustion, or original-h SGCC completion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_nonnegative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer](CountedPositiveTriangleLocalizedConsumer.md)
