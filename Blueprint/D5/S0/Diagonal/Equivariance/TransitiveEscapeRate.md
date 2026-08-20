# Transitive Escape Rate

## Abstract

A transitive equivariant ensemble escapes at rate one minus k over n to the omega.

An equivariant listing is determined by its orbit coordinates: one value on the diagonal of each row orbit, and the remaining stabilizer orbit coordinates. For a transitive action there is a single row orbit, so the ensemble has exactly as many members as there are assignments to the stabilizer orbits of one address.

The escaped members of that ensemble were already counted; what was missing was the size of the ensemble itself, without which the quotient the source states cannot be formed. The orbit decomposition carries a bijection but asserts no cardinality, and the corresponding lemma inside the frozen counting module is private, so the count is re-derived here rather than reused.

Dividing gives the rate the source records. The three readings it lists are instances of that quotient, and all three take the identity twist, so they vary the group and not the twist. The source also records the general nontransitive case as open, and nothing here claims it.

**Lemma 1.1 (Every stabilizer orbit index carries the diagonal).**

$$0 < \operatorname{card}\left(\operatorname{StabilizerOrbit}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.stabilizerOrbit_card_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal orbit is a member, so the stabilizer orbit count is positive and the exponent arithmetic below never underflows.

**Lemma 1.2 (Orbit coordinates number n to the orbit count).**

$$\operatorname{card}\left(\mathit{EquivariantListing}\right) = n^{\mathit{omega}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.orbitParameters_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A diagonal value together with the off-diagonal stabilizer orbit coordinates gives one factor of the alphabet size for every stabilizer orbit of the index.

**Theorem 1.3 (The transitive ensemble has n to the omega members).**

$$\operatorname{card}\left(\mathit{EquivariantListing}\right) = n^{\mathit{omega}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.transitive_equivariant_listing_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transitivity makes the row orbit index unique, so the product over row orbits collapses to the single factor at any chosen index.

**Lemma 1.4 (The escaped fraction is one minus the fixed fraction).**

$$\operatorname{P}\left(\mathit{esc}\right) = 1 - \frac{k}{n^{\mathit{omega}}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.escaped_fraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dividing a difference of naturals by the larger one is the same as subtracting the quotient from one, which is the arithmetic step carrying the count into the rate the source writes.

**Lemma 1.5 (The three recorded readings).**

$$\operatorname{P}\left(\mathit{esc}\right) = 1 - \frac{k}{n^{\mathit{omega}}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.worked_rates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The regular three point, regular four point, and nonregular three point readings, each written as one minus the fixed fraction. All three take the identity twist.

**Theorem 1.6 (The transitive escape rate packaged).**

$$\operatorname{card}\left(\mathit{EquivariantListing}\right) = n^{\mathit{omega}} \land \left(\operatorname{card}\left(\operatorname{Escaped}\left(f\right)\right) = n^{\mathit{omega}} - k \land \operatorname{P}\left(\mathit{esc}\right) = 1 - \frac{k}{n^{\mathit{omega}}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.transitive_equivariant_escape_rate_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One conjunction carrying the exact rate: the ensemble size, the escaped count, the quotient identity, and the three recorded readings. The displayed formula shows the first three; the fourth conjunct is the readings named above.

## References

- Truth anchor: `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.escaped_fraction`
- Truth anchor: `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.orbitParameters_card`
- Truth anchor: `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.stabilizerOrbit_card_pos`
- Truth anchor: `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.transitive_equivariant_escape_rate_package`
- Truth anchor: `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.transitive_equivariant_listing_card`
- Truth anchor: `D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.worked_rates`
- Dependency: [D5/S0/Diagonal/EquivariantEscape](../EquivariantEscape.md)
