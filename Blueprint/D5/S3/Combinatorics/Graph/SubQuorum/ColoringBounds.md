# A degree obstruction to a full injective palette

## Abstract

A degree obstruction to a full injective palette

For every finite simple graph with a vertex of degree at least three, every admissible partial sub-quorum coloring has fewer represented colors than vertices. Equality of these cardinalities would force full support and injective coloring, contradicting the weak majority at that vertex. Actual represented colors are counted; unused labels and none are excluded.

**Theorem 1.1 (palette lt card of degree).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/ColoringBounds.palette_lt_card_of_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/ColoringBounds.palette_lt_card_of_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem palette_lt_card_of_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (hd : 3 ≤ (Finset.univ.filter (G.Adj v)).card) (c : V → Option C) (hc : IsSubQuorum G c) : (palette c Finset.univ).card < Fintype.card V.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/ColoringBounds.palette_lt_card_of_degree`
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting](DoubleStarGrafting.md)
