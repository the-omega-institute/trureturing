# Isolating a coordinate in a matching

## Abstract

Each matching uses the chosen coordinate once, so its polynomial is at most linear in that coordinate.

**Definition 1.1 (Remaining coordinates).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.Rest`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.Rest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remaining coordinate set omits the distinguished index.

**Definition 1.2 (Coefficient ring).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.Coeff`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.Coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficients are complex multivariate polynomials in the remaining coordinates.

**Definition 1.3 (Single-variable presentation).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.isolate`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.isolate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chosen variable is extracted as the outer polynomial variable via the option-type decomposition.

**Theorem 1.4 (The distinguished variable).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_self`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variable at the chosen index becomes the outer indeterminate.

**Theorem 1.5 (A remaining variable).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_other`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A variable at a different index becomes a constant coefficient in the outer polynomial.

**Theorem 1.6 (Evaluation after isolation).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.eval_isolate`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.eval_isolate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation at the full assignment equals evaluation of the outer polynomial after evaluating its coefficients at the remaining assignment.

**Theorem 1.7 (Prime coordinate differences).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.diff_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.diff_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An oriented difference of two distinct variables is prime. Isolate the second variable to turn the factor into a monic linear polynomial.

**Theorem 1.8 (Different unordered pairs give independent factors).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.diff_not_dvd_of_edges_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.diff_not_dvd_of_edges_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Collapse the two coordinates of the divisor to one value and keep the coordinates of the other edge apart. The divisor vanishes but the other factor does not.

**Definition 1.9 (Vertices away from an edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.remainingVertex`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.remainingVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each endpoint of a different matching edge survives removal of the distinguished vertex.

**Definition 1.10 (Product off the distinguished edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.remainingProduct`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.remainingProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product uses precisely the edges other than the distinguished edge.

**Theorem 1.11 (Isolation at the first endpoint).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear coefficient is the negative of the remaining product. The constant coefficient is the second endpoint variable times the remaining product.

**Theorem 1.12 (Isolation at the second endpoint).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear coefficient is the remaining product. The constant coefficient is the negative of the first endpoint variable times the remaining product.

**Theorem 1.13 (Linearity in every coordinate).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.matching_exists_linear`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.matching_exists_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Find the matching edge and endpoint containing the chosen coordinate and apply its ordered isolation formula.

**Theorem 1.14 (Transport of matching factors).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.rename_matchingPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.rename_matchingPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Renaming the polynomial variables composes the endpoint labeling with the permutation.

**Theorem 1.15 (Linearity after a permutation).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.rename_F_exists_linear`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.rename_F_exists_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of the two transported matching products is at most linear in the chosen coordinate.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.Coeff`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.Rest`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.diff_not_dvd_of_edges_ne`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.diff_prime`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.eval_isolate`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.isolate`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_other`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_self`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.matching_exists_linear`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_left`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_right`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.remainingProduct`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.remainingVertex`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.rename_F_exists_linear`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.rename_matchingPolynomial`
- Dependency: [D5/S3/Geometry/KozakiKakeiMatching](KozakiKakeiMatching.md)
