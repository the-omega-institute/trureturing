# Reversible classification of all labelled subsets

## Abstract

Reversible classification of all labelled subsets

**Definition 1.1 (An actual graph automorphism).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.turn`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.turn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exchange alpha and beta, send a(i) to b(i), and send b(i) to a(i+1). The inverse sends a(i) to b(i-1) and b(i) to a(i). Both maps preserve exactly the original edge relation.

**Definition 1.2 (Labelled cut covers).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.CoverData`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.CoverData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A removed edge label j together with a minimal cover C of the remaining cyclic edges containing an endpoint. The tag and every label remain part of the data.

**Definition 1.3 (The complete apex encoding).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.actualTaggedEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.actualTaggedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n>=3, the type of original admissible labelled subsets is equivalent to Bool times the dependent cut-cover family. The inverse reads the unique apex, unique opposite label, and selected same-type labels. Every tag decodes to an original minimal connected dominating subset. This theorem does not yet identify cut covers with ordered path covers or give the literal generating series.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.CoverData`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.actualTaggedEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.turn`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification](TrapezohedralApexClassification.md)
