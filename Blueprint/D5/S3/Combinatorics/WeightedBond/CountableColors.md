# Finite specialization of the countable-color sum

## Abstract

Finite specialization of the countable-color sum.

**Definition 1.1 (CountableBond).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.CountableBond`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.CountableBond` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The connected-block model with natural-number colors. Each block has finite support and total weight its size minus one. Weights off blocks are zero.

**Definition 1.2 (childSum).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.childSum`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.childSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For a given vertex set and color, sum the weights of the partition blocks contained in that set.

**Definition 1.3 (Refines).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.Refines`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.Refines` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The partition refines the upper partition and each upper weight dominates the sum of the finer weights in that color.

**Definition 1.4 (pad).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.pad`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.pad` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Embed a finite color vector into the countable color model by filling the remaining coordinates with zeros.

**Theorem 1.5 (pad_le_iff).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.pad_le_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.pad_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Zero-padding preserves and reflects the componentwise refinement order.

**Theorem 1.6 (lower_supported).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.lower_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.lower_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Every element below a padded element is supported on the same initial color segment.

**Theorem 1.7 (sum_range_cutoff).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.sum_range_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.sum_range_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Sums taken to two bounds agree when the summand vanishes from each bound onward.

**Definition 1.8 (truncate).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.truncate`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.truncate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For a countable weighting supported in the initial segment, restrict coordinates to that segment.

**Theorem 1.9 (pad_truncate).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.pad_truncate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.pad_truncate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Zero-padding the truncation recovers the original supported weighting.

**Definition 1.10 (padLowerIso).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.padLowerIso`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.padLowerIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Padding identifies the entire literal lower interval of a finite-color element with the entire countable-color lower interval below its image.

**Definition 1.11 (colorExponent).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.colorExponent`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.colorExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The exponent of a color is the sum of that coordinate over the actual partition blocks.

**Theorem 1.12 (colorExponent_finite).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.colorExponent_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.colorExponent_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

There is a common cutoff from which every color exponent is zero.

**Theorem 1.13 (supported_iff_exponents).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.supported_iff_exponents`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.supported_iff_exponents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The weights are supported below r if and only if every color exponent from r onward is zero.

**Definition 1.14 (supportedColorsEquiv).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.supportedColorsEquiv`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.supportedColorsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Finite-color elements are equivalent to the countable-color elements whose exponents vanish from r onward.

**Theorem 1.15 (monomial_specializes).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.monomial_specializes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.monomial_specializes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For any support cutoff, substituting X below r and zero from r onward gives X to the rank on supported elements and zero on the others.

**Definition 1.16 (sourceMu).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMu`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Take the incidence Möbius value from bottom to top in the element's literal countable-color lower interval. That interval is finite by the top's finite color support.

**Theorem 1.17 (sourceMu_pad).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMu_pad`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMu_pad` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The Möbius value of a padded element in the countable-color lower interval equals its original Möbius value in the finite-color poset.

**Definition 1.18 (sourceMonomial).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMonomial`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Specialize the color monomial at X on the initial segment of r colors and at zero on the remaining colors, using a finite product up to an exponent cutoff.

**Definition 1.19 (sourceSpecialization).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Sum the specialized monomials over the countable-color poset of the complete graph, with the integer coefficients from its actual lower intervals.

**Theorem 1.20 (sourceSpecialization_eq).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The specialized countable-color sum in equation (7.1) is the finite-color rank polynomial, for every vertex count and color count.

## References

- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.CountableBond`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.Refines`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.childSum`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.colorExponent`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.colorExponent_finite`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.lower_supported`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.monomial_specializes`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.pad`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.padLowerIso`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.pad_le_iff`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.pad_truncate`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMonomial`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMu`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceMu_pad`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization_eq`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.sum_range_cutoff`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.supportedColorsEquiv`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.supported_iff_exponents`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CountableColors.truncate`
- Dependency: [D5/S3/Combinatorics/WeightedBond/FiniteOrder](FiniteOrder.md)
