# Exact polynomial coefficient provenance

## Abstract

Exact polynomial coefficient provenance.

**Theorem 1.1 (Finite coefficient representations).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientPolynomial_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientPolynomial_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every rational polynomial has a finite ascending coefficient list. Constants use singleton lists, addition uses recursive coefficient addition, and multiplication by X inserts a leading zero. Trailing zeros are allowed.

**Theorem 1.2 (Even polynomial coefficients).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.evenized_coefficients_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.evenized_coefficients_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating alternating coefficients represents substitution of -X. Averaging that list with the original list therefore represents one half of p(X)+p(-X), including the empty list.

**Theorem 1.3 (Expression provenance).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientsOfExpr_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientsOfExpr_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the executable expression parser returns a coefficient list, the corresponding semantic polynomial is exactly coefficientPolynomial of that list. The induction handles constants, the variable, sums, negations, products and squares; inversion is rejected.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientPolynomial_surjective`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientsOfExpr_sound`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Coefficients.evenized_coefficients_sound`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic](Scalar/Logistic.md)
- Dependency: [D5/S3/Weil/TestFunctions/RationalCutoffApproximation](../../TestFunctions/RationalCutoffApproximation.md)
