# Matching Translations of a Steiner Triple System

## Abstract

Pair completion in a complete Steiner triple system gives perfect matchings on the enlarged point set.

**Definition 1.1 (Translation through a pivot).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate` (`✓ std3`).

*Citation.* Robert W. Quackenbush (1976). *Varieties of Steiner Loops and Steiner Quasigroups*. DOI: [10.4153/CJM-1976-118-1](https://doi.org/10.4153/CJM-1976-118-1). URL: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00020873>.

*Commentary.*

Adjoin one point to the finite complete Steiner triple system. Pair it with the pivot. For an original point distinct from the pivot, take the third point of its block with the pivot.

**Theorem 1.2 (Translation at the adjoined point).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_none`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_none` (`✓ std3`). ∎

*Citation.* Robert W. Quackenbush (1976). *Varieties of Steiner Loops and Steiner Quasigroups*. DOI: [10.4153/CJM-1976-118-1](https://doi.org/10.4153/CJM-1976-118-1). URL: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00020873>.

*Commentary.*

The translation sends the adjoined point to the pivot.

**Theorem 1.3 (Translation at the pivot).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_self`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_self` (`✓ std3`). ∎

*Citation.* Robert W. Quackenbush (1976). *Varieties of Steiner Loops and Steiner Quasigroups*. DOI: [10.4153/CJM-1976-118-1](https://doi.org/10.4153/CJM-1976-118-1). URL: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00020873>.

*Commentary.*

The translation sends the pivot to the adjoined point.

**Theorem 1.4 (Involution law).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_involutive` (`✓ std3`). ∎

*Citation.* Robert W. Quackenbush (1976). *Varieties of Steiner Loops and Steiner Quasigroups*. DOI: [10.4153/CJM-1976-118-1](https://doi.org/10.4153/CJM-1976-118-1). URL: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00020873>.

*Commentary.*

The translation applied twice is the identity. The second step uses the same block by uniqueness of pair completion.

**Theorem 1.5 (No fixed points).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_ne_self`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_ne_self` (`✓ std3`). ∎

*Citation.* Robert W. Quackenbush (1976). *Varieties of Steiner Loops and Steiner Quasigroups*. DOI: [10.4153/CJM-1976-118-1](https://doi.org/10.4153/CJM-1976-118-1). URL: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00020873>.

*Commentary.*

Every point moves under the translation. A pivot exchanges with the adjoined point and the other pairs consist of distinct points in a block.

**Theorem 1.6 (Distinct partners).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_ne_translate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_ne_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translations through distinct pivots give different partners at every point. At a point away from both pivots, a common partner would force two distinct blocks to share a pair.

**Theorem 1.7 (The square containing the adjoined point).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_special_square`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_special_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct pivots the two translations send the other pivot to a common third point distinct from both pivots. The adjoined point, the two pivots, and their common third point therefore form a square.

**Theorem 1.8 (Restriction to the leave matching).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_deleted_match`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_deleted_match` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the uncovered pairs of the point-deleted packing agree exactly with the partners of a map on retained labels, the translation through the deleted pivot sends each retained point to the corresponding partner. The original block through the deleted pivot excludes its other pair from every retained block by pair uniqueness.

**Theorem 1.9 (Commutation detects the closing pair).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.switch_commutes_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.switch_commutes_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the leave partners of the retained packing are given by the map m. For a start a and a retained pivot v distinct from a and m(a), suppose the blocks through the pairs av and m(a)v have respective third labels b and d. The two translations through the deleted point and v commute at the embedded start exactly when d equals m(b). One order reaches d and the other reaches m(b).

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.switch_commutes_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_deleted_match`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_involutive`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_ne_self`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_ne_translate`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_none`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_self`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations.translate_special_square`
- Dependency: [D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch](PointDeletedSteinerSwitch.md)
