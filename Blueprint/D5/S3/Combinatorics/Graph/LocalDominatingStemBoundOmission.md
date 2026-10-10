# Dominating sets omitting a stem

## Abstract

Omitting a stem forces every one of its leaves and full internal domination of the residual graph.

**Theorem 1.1 (Internal residual domination).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_stem_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_stem_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Selected leaves can dominate only themselves and the omitted stem, so residual vertices must be dominated internally.

**Theorem 1.2 (Omitted-family size).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_family_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_family_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjoining all leaf neighbours gives a bijection from residual dominating sets to dominating sets omitting the stem.

**Theorem 1.3 (Omitted-family cardinality sum).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_card_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_card_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every omitted-stem set has all leaf neighbours and a disjoint residual dominating set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_card_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_family_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.omitted_stem_residual`
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual](LocalDominatingStemBoundResidual.md)
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit](LocalDominatingStemBoundSplit.md)
