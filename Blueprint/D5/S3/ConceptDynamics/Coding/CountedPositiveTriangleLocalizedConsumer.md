# The same signed integer gyration lift

## Abstract

CountedPositiveTriangleLocalizedConsumer

**Theorem 1.1 (Congruence after clearing a denominator).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerValues_mod_three`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerValues_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a rational multivariate polynomial, Q an integer polynomial, and D a nonzero integer with Q mapped to the rationals equal to D P. At both signed integer tuples x and y, the evaluations of P must be integers a and b. If every coordinate agrees modulo three to the power e plus one, where e bounds the three-adic valuation of D, then a and b agree modulo three. No positivity, finite-variable, or localization hypothesis is needed for this theorem.

Integer polynomial evaluation respects reduction, so three to the power e plus one divides D times the difference b minus a. If that difference is zero the result is immediate; otherwise additivity of the three-adic valuation and the denominator bound imply that its valuation is at least one. This is the classical clearing-denominator congruence argument. No ring map from the rational coefficients to ZMod is used.

**Theorem 1.2 (Reduction from the dyadic localization).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.dyadicReduction`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.dyadicReduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two is a unit modulo every positive power of three. The universal property of localization therefore extends integer reduction to the localization of the integers away from two. Its restriction to every integer is the usual residue. This helper supplies the actual dyadic reduction used by the canonical rectangular cochain.

**Definition 1.3 (The same signed integer gyration lift).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer value at a compatible rectangular pair is exactly the accepted signedGyrationLift applied to the two matrices through Sum.elim. Its binomial-coefficient formula is integer valued on arbitrary signed tuples. It agrees on natural tuples with the accepted order-type lift; no new invariant is substituted.

**Theorem 1.4 (Transport the actual triangle to the integer lift).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The accepted equality between actual relative forward gyration and the order-type lift, followed by integer-cast compatibility, transports the proved numbered-path triangle modulo three. The same n,m,p and nonzero period divisible by three remain in scope.

**Theorem 1.5 (Include zero entries and empty intermediate dimensions).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise toNat recovers a nonnegative integer matrix exactly. Matrix.map_mul transports all three products back to the natural counted triangle. The equality of the signed and natural binomial lifts then proves the integer triangle on nonnegative entries. Products may vanish when the intermediate dimension is zero, which is why this nonnegative statement is used instead of strict positivity of products.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.dyadicReduction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerValues_mod_three`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGyrationPolynomial](CountedGyrationPolynomial.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree](CountedPositiveTriangleModThree.md)
