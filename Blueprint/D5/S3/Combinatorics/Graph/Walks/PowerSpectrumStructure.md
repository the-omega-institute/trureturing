# Native spectrum and metric transport

## Abstract

Graph isomorphisms preserve distances and spectra, and complete powers have exact singleton spectra.

All spectra use actual maximal independent vertex Finsets. Isomorphisms act on vertices, not merely on cardinality lists. Extended distance is used for arbitrary graphs; natural distance and diameter are obtained by conversion. A connected graph whose exponent reaches its diameter has a complete native power.

**Theorem 1.1 (Length-preserving metric transport).**

$$\forall u \in V,\; \forall v \in V,\; \operatorname{edist}\left(H, \operatorname{apply}\left(e, u\right), \operatorname{apply}\left(e, v\right)\right) = \operatorname{edist}\left(G, u, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.edist_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every graph isomorphism e:G to H, map native finite walks through e and through its inverse. The two length bounds give equality even when vertices are unreachable. Natural distance and diameter are transported from the same equality.

**Theorem 1.2 (The attained spectrum of a nonempty complete graph).**

$$\operatorname{spectrum}\left(\operatorname{completeGraph}\left(V\right)\right) = \operatorname{singleton}\left(1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.spectrum_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the existing-owner theorem CayleySquare.wellCovered_complete. A singleton vertex set is independent and dominates all omitted vertices; comparing any maximal independent set with this singleton gives cardinality one. The same singleton also proves attainment.

**Theorem 1.3 (Every sufficiently large connected power is complete).**

$$\left(\operatorname{Connected}\left(G\right) \land \operatorname{diam}\left(G\right) \le d\right) \Rightarrow \operatorname{power}\left(G, d\right) = \operatorname{completeGraph}\left(V\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.power_eq_top_of_diam_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native diameter bounds every pairwise distance in a finite connected graph. Consequently every two distinct vertices are adjacent in the stated power.

**Theorem 1.4 (Uniformity is a subsingleton attained spectrum).**

$$\operatorname{WellCovered}\left(G\right) \Leftrightarrow \operatorname{Subsingleton}\left(\operatorname{spectrum}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.wellCovered_iff_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectrum is defined by actual maximal independent Finsets. Equality of all their cardinalities is therefore equivalent to any two attained spectrum values being equal.

**Theorem 1.5 (Triangle-free complements have exact spectrum two).**

$$\left(\operatorname{TriangleFree}\left(G\right) \land \left(\forall u \in V,\; \exists v \in V,\; \operatorname{Adj}\left(G, u, v\right)\right)\right) \Rightarrow \operatorname{spectrum}\left(\operatorname{complement}\left(G\right)\right) = \operatorname{singleton}\left(2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.spectrum_complement_triangleFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here V is nonempty and finite. A maximal independent set in the complement is a maximal clique in G. It cannot be a singleton because G has no isolated vertex, and it cannot have three distinct vertices because G is triangle-free. An existing finite maximum-independent-set supplier gives attainment.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.edist_iso`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.power_eq_top_of_diam_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.spectrum_complement_triangleFree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.spectrum_top`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure.wellCovered_iff_spectrum`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower](FiniteDistancePower.md)
