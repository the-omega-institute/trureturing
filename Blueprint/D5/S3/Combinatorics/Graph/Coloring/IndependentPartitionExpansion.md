# Proper colourings and all unlabelled independent partitions

## Abstract

Every finite graph and every natural palette admit the full independent-partition expansion.

**Definition 1.1 (Injective block names give a proper colouring).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.decode`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.decode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The input is an actual Mathlib SimpleGraph.Partition P and an injection from P.parts to the palette. Compose that injection with P.toColoring. Every part is nonempty, the parts cover every vertex exactly once, and independence gives the proper-colouring condition. No palette size or block-count cap appears.

**Definition 1.2 (The full palette and partition correspondence).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.coloringEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.coloringEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every vertex type V, graph G and palette type α, G.Coloring α is equivalent to Σ P : G.Partition, (P.parts ↪ α). Reconstructing the colour classes of an injectively named partition gives exactly P. For a colouring, label each nonempty class by the colour of a representative vertex; equality of labels is exactly membership in the same class. The inverse proofs recover the complete original colouring and all block names. This also covers empty vertex sets, empty palettes and unused palette names.

**Definition 1.3 (All independent partitions with exactly j blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.stirling`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.stirling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

stirling G j is Nat.card {P : G.Partition // Nat.card P.parts = j}. This counts actual unlabelled partitions into j nonempty independent vertex sets, without reference to a target expression or a palette. There is no three-block restriction. A finite N-vertex graph has no such partition for j>N; a nonempty graph has none for j=0.

**Theorem 1.4 (The unrestricted falling-factorial expansion).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.chromatic_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.chromatic_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every finite vertex type V with a Fintype instance, every simple graph G on V and every q:Nat, P_G(q)=Σ(j=0..N) q.descFactorial(j)·stirling(G,j), where N=Fintype.card V and P_G(q)=Nat.card (G.Coloring (Fin q)). The colouring equivalence gives a sum of actual injection cardinalities. Mathlib Fintype.card_embedding_eq identifies each cardinality with the falling factorial. Surjectivity of P.toColoring proves that every block count is at most N, and finite fibrewise summation groups the terms by exactly that count. This is a uniform kernel proof, with q=4 and partitions into four singleton blocks inside its domain.

For nonempty V the zero-block term is zero, so the source formula is exactly P_G(q)=Σ(j=1..N)(q)_j s_j. Equivalently the source sum over all j≥1 has finite support: s_j=0 for j>N. Mathlib Nat.descFactorial_eq_prod_range identifies (q)_j with ∏(i=0..j-1)(q-i); when j>q this is zero. The palette q=0 gives zero colourings on every nonempty graph. A singleton has P_G(q)=q. On the empty vertex set there is one empty partition with zero blocks and one empty colouring for every q, including q=0; the finite expansion therefore has the single term (q)_0 s_0=1. This is separate from the strip series convention at index zero, and does not extend the six-colour 48L identity to the empty graph.

This supplies the unrestricted chromatic clause in the proof of Hardin revision 2, Proposition prop:graph. The separate three-pair StablePartition construction still has at most three blocks and proves the literal six-colour weights and the 48L identity in HardinGraphNormalization. General palettes here do not enlarge the six-colour normalization domain or assert arbitrary-palette equality between the distinct square and diagonal strip graphs. The graphical Stirling expansion is established prior work: Duncan and Peele, Bell and Stirling Numbers for Graphs, JIS 12 (2009), Article 09.7.1, section 5 equation (2), with their attribution to Biggs Proposition 9.2. No mathematical priority claim is made.

The source-specific registration remains separate from this mathematical proof. The attempted source-owner Reg mirror's complete universe-polymorphic family, variation and dependence compile, but the report reader rejects its audit with contract.discovery:rigid_universes. The attempted source and exact failure are preserved outside the project; the failed audit addition is not retained in the build. Source-occurrence selection and current binding evidence remain missing. This does not assert validated registration, freezing, independent acceptance, required CI or delivery.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.chromatic_expansion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.coloringEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.decode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.stirling`
