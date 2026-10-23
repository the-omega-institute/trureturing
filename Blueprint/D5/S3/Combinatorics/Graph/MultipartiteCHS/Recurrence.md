# Multipartite CHS recurrence

## Abstract

Elementary symmetric polynomials of part sizes and reciprocal coefficients.

The module proves nonnegativity of every coefficient and strict positivity of the even coefficients when there are at least two positive parts. The extremal comparison is proved in the Extremal module and transferred to CHS norms in the Result module.

**Definition 1.1 (Elementary symmetric part sum).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.esymmParts`

*Formalization.* `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.esymmParts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a part-size function a, esymmParts a j sums the products over all j-element subsets of the part indices.

**Definition 1.2 (Reciprocal coefficient sequence).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH`

*Formalization.* `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

recH is defined by strong induction. Its constant coefficient is one, and each positive degree is obtained by the finite convolution with the coefficients (j minus one) times esymmParts a j.

**Theorem 1.3 (Constant coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal coefficient sequence starts at one.

**Theorem 1.4 (Coefficient recurrence).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive coefficient is the sum of the lower coefficients weighted by the elementary symmetric part sums.

**Theorem 1.5 (Nonnegative coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All reciprocal coefficients are nonnegative over the real numbers.

**Theorem 1.6 (Positive even coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_two_mul_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_two_mul_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least two positive parts, every positive even coefficient is strictly positive.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.esymmParts`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_nonneg`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_two_mul_pos`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_zero`
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs](Defs.md)
