# General Equivariant Escape Probability

## Abstract

Uniform equivariant escape probability factors over every address orbit.

**Theorem 1.1 (General equivariant escape probability).**

$$\operatorname{PescEq}\left(f\right) = \frac{\prod_{i \in \operatorname{Orb}\left(A\right)} (\operatorname{card}\left(Y\right)^{omega_i} - \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right))}{\prod_{i \in \operatorname{Orb}\left(A\right)} \operatorname{card}\left(Y\right)^{omega_i}}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/GeneralEquivariantEscape.general_equivariant_escape_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let i range over the G-orbits of addresses. The supplied orbit decomposition identifies equivariant listings with diagonal and stabilizer-orbit row parameters while preserving the escape predicate. If omega_i is the number of stabilizer orbits, n is the cardinality of Y, and k is the number of fixed points of f, then orbit i contributes n^omega_i total choices and n^omega_i-k escaping choices.

The imported orbit-product count gives the numerator. Counting the same public parameter equivalence gives the denominator, and the pinned uniform-PMF theorem converts their cardinality ratio into the displayed outer-measure probability.

Repository searches found only the transitive probability theorem. Pinned Mathlib supplies PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_pi, and the finite product arithmetic, but no packaged equivariant orbit-decomposition probability formula.

**Theorem 1.2 (The transitive formula is a corollary).**

$$\operatorname{PescEq}\left(f\right) = 1 - \frac{\operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)}{\operatorname{card}\left(Y\right)^{omega_i}}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/GeneralEquivariantEscape.general_orbit_product_eq_frozen_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a transitive action the orbit index is a singleton. Applying the general theorem collapses both finite products to the factor at any chosen orbit representative i, after which the denominator is nonzero and the ratio is 1-k/n^omega_i. Thus the frozen transitive formula is obtained as a specialization rather than reproved by a separate counting argument.

## References

- Truth anchor: `D5/S0/Diagonal/Probability/GeneralEquivariantEscape.general_equivariant_escape_probability`
- Truth anchor: `D5/S0/Diagonal/Probability/GeneralEquivariantEscape.general_orbit_product_eq_frozen_transitive`
- Dependency: [D5/S0/Diagonal/Probability/EquivariantEscape](EquivariantEscape.md)
