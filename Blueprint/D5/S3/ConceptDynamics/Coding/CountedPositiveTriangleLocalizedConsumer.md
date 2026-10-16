# The same signed integer gyration lift

## Abstract

CountedPositiveTriangleLocalizedConsumer

**Definition 1.1 (The same signed integer gyration lift).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer value at a compatible rectangular pair is exactly the accepted signedGyrationLift applied to the two matrices through Sum.elim. Its binomial-coefficient formula is integer valued on arbitrary signed tuples. It agrees on natural tuples with the accepted order-type lift; no new invariant is substituted.

**Theorem 1.2 (Transport the actual triangle to the integer lift).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The accepted equality between actual relative forward gyration and the order-type lift, followed by integer-cast compatibility, transports the proved numbered-path triangle modulo three. The same n,m,p and nonzero period divisible by three remain in scope.

**Theorem 1.3 (Include zero entries and empty intermediate dimensions).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise toNat recovers a nonnegative integer matrix exactly. Matrix.map_mul transports all three products back to the natural counted triangle. The equality of the signed and natural binomial lifts then proves the integer triangle on nonnegative entries. Products may vanish when the intermediate dimension is zero, which is why this nonnegative statement is used instead of strict positivity of products.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGyrationPolynomial](CountedGyrationPolynomial.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree](CountedPositiveTriangleModThree.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/LocalizedCocycle](LocalizedCocycle.md)
