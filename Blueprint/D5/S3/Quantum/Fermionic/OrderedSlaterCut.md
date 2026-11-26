# Slater determinant marginals at an ordered cut

## Abstract

Slater determinant marginals at an ordered cut

A finite linearly ordered set of sites is partitioned into a retained set and its complement. Both sides can be empty. The matrix of occupied orbitals has one column per particle. Each side keeps its full occupation carrier, including occupation labels with zero amplitude.

**Definition 1.1 (Occupation labels).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.Occupation`

*Formalization.* `D5/S3/Quantum/Fermionic/OrderedSlaterCut.Occupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occupation label is a finite subset of the indicated side.

**Definition 1.2 (Retained one-particle rows).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.retainedRows`

*Formalization.* `D5/S3/Quantum/Fermionic/OrderedSlaterCut.retainedRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the orbital matrix to the retained site rows and keep the original particle columns.

**Definition 1.3 (Amplitudes in the original site order).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.orderedCut`

*Formalization.* `D5/S3/Quantum/Fermionic/OrderedSlaterCut.orderedCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Join the two occupied subsets and use their increasing enumeration for the rows of the determinant. The entry is zero when the joined subset has a different size from the particle number.

**Definition 1.4 (Amplitudes in the order grouped by side).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.groupedCut`

*Formalization.* `D5/S3/Quantum/Fermionic/OrderedSlaterCut.groupedCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List the occupied rows on the retained side before the occupied rows on the traced side. The order within each side is increasing. The same particle number condition determines the zero entries.

**Theorem 1.5 (The two occupied sets are disjoint).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.cut_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.cut_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An occupation of the retained side and an occupation of the discarded side share no site.

**Theorem 1.6 (The shuffle sign of a grouped determinant).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.groupedCut_eq_signed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.groupedCut_eq_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The grouped amplitude is the ordered amplitude times minus one raised to the number of pairs in which an occupied discarded site precedes an occupied retained site.

**Theorem 1.7 (Support at the prescribed particle number).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.orderedCut_eq_zero_of_card_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.orderedCut_eq_zero_of_card_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered amplitude vanishes if the retained and discarded occupations have a combined size different from the number of orbital columns.

**Theorem 1.8 (The two-particle witness at an alternating cut).**

$$\begin{aligned}\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)] [\operatorname{Fintype}(\iota)], I: \operatorname{Set}(\iota),\\\operatorname{Alternates}(I) \longrightarrow \exists V: \operatorname{Matrix}(\iota, \operatorname{Fin}(2), \mathbb{C}), V^{*}V=1 \land\\\operatorname{charpoly}(\operatorname{retainedRows}(I, V)\operatorname{retainedRows}(I, V)^{*}) = X^{\operatorname{card}(I)-1}(X-1) \land\\\operatorname{charpoly}(\operatorname{groupedCut}(I, V)\operatorname{groupedCut}(I, V)^{*}) = X^{\operatorname{card}(\operatorname{Occupation}(I))-1}(X-1) \land\\\operatorname{charpoly}(\operatorname{orderedCut}(I, V)\operatorname{orderedCut}(I, V)^{*}) = X^{\operatorname{card}(\operatorname{Occupation}(I))-2}(X-\operatorname{C}(\frac{1}{2}))^{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.alternating_cut_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either orientation of a four-site alternation, take one normalized two-site orbital on each side and leave every other site empty. The orbitals are orthogonal. The compression has a single nonzero eigenvalue of one. The grouped marginal has a single nonzero eigenvalue of one. The original-order marginal has two nonzero eigenvalues of one half, and the two remaining polynomial factors are powers of X with the exponents specified by the full carriers.

**Theorem 1.9 (The four-site support of the alternating witness).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.alternating_cut_supported_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.alternating_cut_supported_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same two-column matrix realizes the three characteristic polynomials and vanishes outside a set of four sites. Its first column is supported on the retained side, its second column on the discarded side, and the four-site set contains a discarded site that can be used for coordinate replacement.

**Definition 1.10 (Weight of an occupation in the product spectrum).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.bernoulliWeight`

*Formalization.* `D5/S3/Quantum/Fermionic/OrderedSlaterCut.bernoulliWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each retained site label, use the supplied mode value when that label is occupied and one minus that value otherwise. Multiply over all labels.

**Definition 1.11 (The complete product-spectrum property).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.HasProductSpectrum`

*Formalization.* `D5/S3/Quantum/Fermionic/OrderedSlaterCut.HasProductSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every labeling that factors the characteristic polynomial of the retained one-particle compression, the original-order determinant marginal has the characteristic polynomial with one factor for every occupation weight. This preserves repeated and zero eigenvalues.

**Theorem 1.12 (Transport of the prefix product spectrum to grouped amplitudes).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.grouped_product_from_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.grouped_product_from_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the product-spectrum property for every ordered prefix. For an orthonormal orbital matrix at any cut, stably order the two sides as consecutive blocks. The grouped marginal then has the occupation product characteristic polynomial for each labeling of the compression spectrum.

**Theorem 1.13 (Reduction of the cut classification to the ordered-prefix formula).**

$$\begin{aligned}(\forall m,n,k \in \mathbb{N}, W: \operatorname{Matrix}(\operatorname{Fin}(m+n), \operatorname{Fin}(k), \mathbb{C}),\\W^{*}W=1 \longrightarrow \operatorname{HasProductSpectrum}(\{i \in \operatorname{Fin}(m+n) \mid \operatorname{val}(i)<m\}, W)) \longrightarrow\\\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)] [\operatorname{Fintype}(\iota)], I: \operatorname{Set}(\iota),\\\neg\operatorname{Alternates}(I) \iff \forall k \in \mathbb{N}, V: \operatorname{Matrix}(\iota, \operatorname{Fin}(k), \mathbb{C}),\\V^{*}V=1 \longrightarrow \operatorname{HasProductSpectrum}(I, V)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterCut.universal_cut_product_iff_of_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the product-spectrum property for every prefix and every column-orthonormal orbital matrix on the consecutive order. At an arbitrary cut with no four alternating sites, the occupied permutation contributes the cross-inversion sign. The fixed-occupation shuffle theorem preserves the marginal characteristic polynomial. The stable ordering of the two sides then transports the grouped marginal, the retained compression and each occupation weight to the prefix formula. If four sites alternate, the two-particle witness has a rank-one compression with a single nonzero eigenvalue of one. Its occupation product spectrum is concentrated at one weight of one, so the original-order marginal violates the formula.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.HasProductSpectrum`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.Occupation`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.alternating_cut_obstruction`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.alternating_cut_supported_obstruction`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.bernoulliWeight`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.cut_disjoint`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.groupedCut`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.groupedCut_eq_signed`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.grouped_product_from_prefix`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.orderedCut`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.orderedCut_eq_zero_of_card_ne`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.retainedRows`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterCut.universal_cut_product_iff_of_prefix`
- Dependency: [D5/S3/Quantum/Fermionic/SlaterCutPhase](SlaterCutPhase.md)
