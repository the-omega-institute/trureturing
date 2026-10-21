# Boolean Effective Images Have a Surjective Slice

## Abstract

A surjective Boolean effective image has a surjective row or column, and the converse holds.

**Theorem 1.1 (Surjective image iff a row or column is surjective).**

$$\forall A, B: \operatorname{Type}, [\operatorname{Nonempty}(A)], [\operatorname{Nonempty}(B)], psi: A \to \left(B \to Bool\right), \operatorname{Surjective}((\lambda p: \operatorname{Prod}(A, B) \mapsto psi\left(\operatorname{fst}(p), \operatorname{snd}(p)\right))) \iff ((\exists b: B, \operatorname{Surjective}((\lambda a: A \mapsto psi\left(a, b\right)))) \lor (\exists a: A, \operatorname{Surjective}((\lambda b: B \mapsto psi\left(a, b\right))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/BooleanCompanionMinimality.binary_effective_image_surjective_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty source alphabets A and B, let psi:A times B to Bool be a binary companion. Its uncurry map is surjective exactly when at least one fixed row or one fixed column is surjective onto Bool.

For the forward implication, if no row is surjective then every row is constant, and two global output witnesses force every column to be surjective. In the reverse implication, each slice witness directly supplies a preimage in the product.

This equivalence concerns the effective image. Response-width comparisons for arbitrary endpoint orders and minimality of the number of companion maps require additional results about those orders and widths.

## References

- Truth anchor: `D5/S3/Observer/Separation/BooleanCompanionMinimality.binary_effective_image_surjective_iff`
