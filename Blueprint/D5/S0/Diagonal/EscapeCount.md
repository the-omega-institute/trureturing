# Diagonal Escape Count

## Abstract

Finite diagonal listings admit an exact count of those escaped by self-application.

**Lemma 1.1 (Landing on the diagonal produces a fixed point).**

$$\operatorname{g}\left(\mathit{a0}\right) = \operatorname{diagonal}\left(f, g\right) \Rightarrow \operatorname{f}\left(\operatorname{g}\left(\mathit{a0}, \mathit{a0}\right)\right) = \operatorname{g}\left(\mathit{a0}, \mathit{a0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EscapeCount.diagonal_landing_fixed` (`✓ std3`). ∎

*Citation.* F. William Lawvere (1969). *Diagonal arguments and cartesian closed categories*. DOI: [10.1007/BFb0080769](https://doi.org/10.1007/BFb0080769).

*Commentary.*

If a listed row equals its twisted diagonal, evaluating that equality at the row's own address shows that the diagonal entry is fixed by the twist. This is the set-level landing step in Lawvere's qualitative diagonal fixed-point argument.

**Theorem 1.2 (Escaped listings have an exact cardinality).**

$$\operatorname{card}\left(\operatorname{escapedListings}\left(f\right)\right) = \left(\operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right)} - \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)\right)^{\operatorname{card}\left(A\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EscapeCount.escaped_listing_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite address and value types, the number of listings whose twisted diagonal is absent from the listing is the address-cardinality power of the number of value functions minus the fixed points of the twist. The proof separates each listing into its diagonal and independent off-diagonal row blocks.

## References

- Truth anchor: `D5/S0/Diagonal/EscapeCount.diagonal_landing_fixed`
- Truth anchor: `D5/S0/Diagonal/EscapeCount.escaped_listing_card`
