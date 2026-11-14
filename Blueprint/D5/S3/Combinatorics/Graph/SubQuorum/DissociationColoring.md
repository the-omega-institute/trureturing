# Dissociation and injective partial colorings

## Abstract

Dissociation and injective partial colorings

For any finite simple graph and any partial coloring injective on its actual support, the sub-quorum majority condition is equivalent to that support inducing maximum degree at most one. Each actual dissociation set therefore yields a coloring with exactly its cardinality many distinct represented natural colors; attainment gives beta two at most psi square. Empty graphs and empty supports are included. This does not provide the opposite representative-packing bound or identify SF with the coloring parameter.

**Theorem 1.1 (injective support iff).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.injective_support_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.injective_support_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem injective_support_iff (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Option C) (hi : Set.InjOn c (coloredSupport c Finset.univ)) : IsSubQuorum G c ↔ IsKIndependent G 2 (coloredSupport c Finset.univ).

**Theorem 1.2 (distinct support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem distinct_support (S : Finset V) : coloredSupport (distinctColoring S) Finset.univ = S.

**Theorem 1.3 (distinct injective).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem distinct_injective (S : Finset V) : Set.InjOn (distinctColoring S) (coloredSupport (distinctColoring S) Finset.univ).

**Theorem 1.4 (distinct palette).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_palette`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_palette` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem distinct_palette (S : Finset V) : (palette (distinctColoring S) Finset.univ).card = S.card.

**Theorem 1.5 (palette le psiSq).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.palette_le_psiSq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.palette_le_psiSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem palette_le_psiSq (G : SimpleGraph V) (c : V → Option ℕ) (h : IsSubQuorum G c) : (palette c Finset.univ).card ≤ psiSq G.

**Theorem 1.6 (beta le psiSq).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.beta_le_psiSq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.beta_le_psiSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_le_psiSq (G : SimpleGraph V) [DecidableRel G.Adj] : beta G 2 ≤ psiSq G.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.beta_le_psiSq`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_palette`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.distinct_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.injective_support_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.palette_le_psiSq`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DisjointUnion](../StarForming/DisjointUnion.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting](DoubleStarGrafting.md)
