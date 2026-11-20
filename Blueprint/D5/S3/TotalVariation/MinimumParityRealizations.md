# Classifying and counting labelled minimum-size realizations

## Abstract

The labelled minimum-size realizations of an affine independent-bit law admit an exact count.

**Definition 1.1 (The coordinates of a minimum-size realization).**

Lean statement: `D5/S3/TotalVariation/MinimumParityRealizations.minimumPresentationsEquiv`

*Formalization.* `D5/S3/TotalVariation/MinimumParityRealizations.minimumPresentationsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix an affine independent-bit law on a finite vector space over the binary field, presented by a finite input family with absolute biases at most one. Let H be the subgroup spanned by its fair columns. An active column is a nonzero class modulo H whose recovered absolute bias is strictly less than one. Fix a finite set of labels of size equal to the minimum input count.

There is an equivalence between presentations of the same mass function at those labels and the following choices. Inject the active classes into the labels. Assign a basis of H to the unused labels. For each active class, choose a column representative and a sign for the recovered bias. Choose one representative of the offset coset after the negative columns of the reference presentation have been added to its offset. Subtract the newly chosen negative columns from that representative to obtain the raw offset.

Equality in the minimum-input bound forces the fair columns to be a basis and forces exactly one nonfair input over each active class. Conversely, the choices fix the grouped absolute products, the sign on all surviving characters, and the vanishing of the remaining moments. Character inversion recovers equality of the mass function at every point.

**Theorem 1.2 (The exact number of labelled minimum-size realizations).**

Lean statement: `D5/S3/TotalVariation/MinimumParityRealizations.minimum_presentations_card`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/MinimumParityRealizations.minimum_presentations_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, let h be the dimension of H, b the number of active classes, and n the number of labels. The cardinality of the type of labelled realizations is the product of n factorial divided by h factorial, the ordered-basis count given by the product of 2 to the h minus 2 to the j for j from zero through h minus one, the subgroup size to the power b plus one, and 2 to the power b. The empty product is one. The four factors count label placements, fair bases, representatives of the active classes and the offset coset, and independent signs.

## References

- Truth anchor: `D5/S3/TotalVariation/MinimumParityRealizations.minimumPresentationsEquiv`
- Truth anchor: `D5/S3/TotalVariation/MinimumParityRealizations.minimum_presentations_card`
- Dependency: [D5/S3/TotalVariation/MinimumParityInputs](MinimumParityInputs.md)
