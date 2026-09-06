# Stanley's Ternary Unique Coefficients

## Abstract

Unique coefficients in Stanley's ternary products satisfy a cubic recurrence.

**Definition 1.1 (The weight sequence).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.G`

*Formalization.* `D5/S1/Digit/StanleyTribleUniqueCoefficients.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weights start at one and three. Each subsequent weight is twice the sum of the two preceding weights.

**Definition 1.2 (The polynomial in the question).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.product`

*Formalization.* `D5/S1/Digit/StanleyTribleUniqueCoefficients.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every index below n, the product contains the factor whose three monomials have exponents zero, the weight, and twice the weight. The coefficient semiring is the natural numbers.

**Definition 1.3 (Count coefficients equal to one).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c`

*Formalization.* `D5/S1/Digit/StanleyTribleUniqueCoefficients.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the actual polynomial support by coefficient equal to one and take its cardinality. The definition is not a surrogate sequence specified by the desired recurrence.

**Theorem 1.4 (Translated multiplicities are polynomial coefficients).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_eq_coeff`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_eq_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending a digit adds three translated coefficient functions. Induction, using Mathlib's coefficient formula for multiplication by a power of X, identifies this recursion with the product.

**Theorem 1.5 (The support has no holes).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_pos`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplicity is positive exactly between zero and the span, inclusive. The span is twice the sum of the preceding weights. It is strictly smaller than the next weight and than twice the current weight, so three translated supports never meet.

**Theorem 1.6 (The overlap is two levels shorter).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.span_overlap`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.span_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The span two levels later equals the corresponding weight plus the original span. Thus the overlap-prefix count at that later level reduces to the surviving lower part of the original level.

**Theorem 1.7 (The empty product).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_zero`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is exactly one coefficient equal to one.

**Theorem 1.8 (One factor).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_one`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are exactly three coefficients equal to one.

**Theorem 1.9 (Two factors).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_two`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are exactly nine coefficients equal to one.

**Theorem 1.10 (Stanley's recurrence for every natural index).**

Lean statement: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The count at n plus three, the count at n plus one, and the count at n sum to three times the count at n plus two. The proof tracks the total count and the unique coefficients in the overlap prefix. Positivity kills uniqueness on each overlap; reflection pairs the outer intervals. The total at the next level plus four times the overlap-prefix count equals three times the current total. The overlap-prefix counts two levels apart sum to the current total. Eliminating these auxiliary counts proves the recurrence, without bounding or classifying the larger multiplicities.

## References

- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.G`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_one`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_recurrence`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_two`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.c_zero`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_eq_coeff`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_pos`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.product`
- Truth anchor: `D5/S1/Digit/StanleyTribleUniqueCoefficients.span_overlap`
