# Equivariant Diagonal Escape

## Abstract

Equivariant diagonal escape counts factor exactly over the action orbits.

**Lemma 1.1 (Equivariant diagonals are orbit-constant).**

$$\operatorname{g}\left(\operatorname{smul}\left(\mathit{sigma}, a\right), \operatorname{smul}\left(\mathit{sigma}, a\right)\right) = \operatorname{g}\left(a, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EquivariantEscape.equivariant_diagonal_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Simultaneous equivariance in the row and column coordinates makes the diagonal value unchanged under transport by any group element. Thus each address orbit contributes one diagonal coordinate.

**Theorem 1.2 (Equivariant escape counts factor by address orbit).**

$$\operatorname{card}\left(\operatorname{escapedEquivariantListings}\left(f\right)\right) = \operatorname{productOrbits}\left(\operatorname{card}\left(Y\right)^{\mathit{omega}_{i}} - \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right), i\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose explicit stabilizer-orbit coordinates for the equivariant listings. After revealing the orbit-diagonal values, each address orbit has one forbidden off-diagonal row exactly when its diagonal value is fixed by the twist. Finite sums of these independent row choices separate into the product of card(Y)^omega_i minus the fixed-point count.

**Theorem 1.3 (Transitive actions have one escape factor).**

$$\operatorname{card}\left(\operatorname{escapedEquivariantListings}\left(f\right)\right) = \operatorname{card}\left(Y\right)^{\mathit{omega}_{i}} - \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EquivariantEscape.transitive_equivariant_escaped_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a transitive action the address-orbit quotient has one element, so the general product reduces to the single factor determined by the stabilizer-orbit count.

**Theorem 1.4 (Trivial orbit data recovers the free count).**

$$\operatorname{productAddresses}\left(\operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right)} - \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)\right) = \operatorname{card}\left(\operatorname{escapedListings}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EquivariantEscape.trivial_action_recovers_escaped_listing_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every address is its own orbit and each stabilizer-orbit block has the full address cardinality, the product side is the frozen unrestricted escaped-listing count.

## References

- Truth anchor: `D5/S0/Diagonal/EquivariantEscape.equivariant_diagonal_constant`
- Truth anchor: `D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card`
- Truth anchor: `D5/S0/Diagonal/EquivariantEscape.transitive_equivariant_escaped_card`
- Truth anchor: `D5/S0/Diagonal/EquivariantEscape.trivial_action_recovers_escaped_listing_card`
