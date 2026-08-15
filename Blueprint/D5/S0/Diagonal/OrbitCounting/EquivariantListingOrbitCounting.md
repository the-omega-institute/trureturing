# Orbit Counting for Equivariant Listings

## Abstract

Equivariant listings are functions on diagonal-action orbits, whose number is given by Burnside averaging.

**Theorem 1.1 (Equivariant listings are counted by diagonal-action orbits).**

$$\operatorname{card}\left(\operatorname{EquivariantListing}\left(G, A, Y\right)\right) = \operatorname{card}\left(Y\right)^{\operatorname{card}\left(\operatorname{OrbitIndex}\left(G, \operatorname{prod}\left(A, A\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting.equivariant_listing_card_orbits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Simultaneous transport acts diagonally on ordered address pairs. Equivariance says exactly that a listing is constant on each orbit, so choosing an arbitrary Y-value for every orbit gives all and only the equivariant listings.

**Theorem 1.2 (Burnside average is the equivariant-listing exponent).**

$$\operatorname{card}\left(\operatorname{EquivariantListing}\left(G, A, Y\right)\right) = \operatorname{card}\left(Y\right)^{\operatorname{natDiv}\left(\operatorname{sumFixedDiagonalPairs}\left(G, A\right), \operatorname{card}\left(G\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting.equivariant_listing_card_burnside` (`✓ std3`). ∎

*Citation.* J. H. van Lint and R. M. Wilson (2001). *A Course in Combinatorics*. DOI: [10.1017/cbo9780511987045](https://doi.org/10.1017/cbo9780511987045).

*Commentary.*

Burnside's lemma identifies the number of diagonal-action orbits with the sum, over group elements, of the number of fixed ordered address pairs divided in Nat by the group cardinality. Mathlib's exact Burnside theorem proves the divisibility and the average identity; the repository orbit equivalence turns that orbit count into the exponent of card(Y).

## References

- Truth anchor: `D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting.equivariant_listing_card_burnside`
- Truth anchor: `D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting.equivariant_listing_card_orbits`
- Dependency: [D5/S0/Diagonal/EquivariantEscape](../EquivariantEscape.md)
