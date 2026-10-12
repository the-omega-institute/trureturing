# Transporting residual domination

## Abstract

Embedding finite sets of induced-graph vertices into the original labels preserves cardinalities and averages.

**Definition 1.1 (Full residual domination).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualDomSets`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualDomSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dominating sets of the induced residual graph written on the original vertex labels.

**Theorem 1.2 (Preservation of the mean).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualPartial_average`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualPartial_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the partially dominating residual family preserves its mean size.

**Theorem 1.3 (Full domination implies partial domination).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualDomSets_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualDomSets_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Internal domination of every residual vertex includes domination of all vertices outside the neighbourhood of the removed stem.

**Theorem 1.4 (Equal family sizes).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residual_equal_of_card_equal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residual_equal_of_card_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A subfamily of equal finite cardinality equals its containing family.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualDomSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualDomSets_subset`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residualPartial_average`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.residual_equal_of_card_equal`
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication](LocalDominatingStemBoundReplication.md)
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure](LocalDominatingStemBoundStructure.md)
