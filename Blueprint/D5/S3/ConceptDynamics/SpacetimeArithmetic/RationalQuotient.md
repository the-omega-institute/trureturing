# The Rational Field Quotient

## Abstract

The quotient of actual rich fractions is the standard rational field via its reduced section.

Formula projection does not express the dependent archive carriers here. The resolving Lean handles carry the typed statements; this narrative supplies no separate formula.

**Theorem 1.1 (The reduced rational section is a right inverse).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rationalSection_rightInverse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rationalSection_rightInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator is balancedSection d r.num and the denominator is balancedSection d r.den, using Rat's reduced coordinates. Rat.num_div_den proves the right inverse; zero is literally the canonical zero-over-one pair.

**Theorem 1.2 (The canonical denominator is positive and the coordinates are coprime).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rationalSection_reduced`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rationalSection_reduced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rat.den_pos and Rat.reduced give the positive denominator and coprime absolute integer coordinates after the balanced section readout equations.

**Theorem 1.3 (Reduced positive coordinates are unique).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.reduced_coordinates_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.reduced_coordinates_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rat.div_int_inj proves that any coprime integer coordinates with a positive denominator and the same rational value equal Rat.num and Rat.den. This uniqueness does not identify arbitrary histories.

**Definition 1.4 (The actual kernel quotient is equivalent to Rat).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rational_quotient_equiv`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rational_quotient_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Setoid.quotientKerEquivOfRightInverse is applied directly to the full Fraction d carrier, its readout and the proved canonical section. The forward map sends each class to its readout.

**Definition 1.5 (Field structure is transported along the equivalence).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rational_field_equiv`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rational_field_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equiv.field supplies the field instance on the kernel quotient, and Equiv.ringEquiv gives the ring equivalence to Rat. Class addition, multiplication and negation are proved to agree with the native rich formulas.

**Theorem 1.6 (Quotient inverse agrees on the legal rich domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.class_inv`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.class_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of the guarded native inverse equals the field inverse. The field convention at zero is part of the quotient field and does not extend the partial rich operation.

**Theorem 1.7 (Quotient division agrees on the legal rich domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.class_div`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.class_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of the native cross-product division equals field division. The two quotient-domain theorems identify the rich guards with nonzero quotient classes.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.class_div`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.class_inv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rationalSection_reduced`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rationalSection_rightInverse`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rational_field_equiv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.rational_quotient_equiv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.reduced_coordinates_unique`
- Dependency: [D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational](RichRational.md)
