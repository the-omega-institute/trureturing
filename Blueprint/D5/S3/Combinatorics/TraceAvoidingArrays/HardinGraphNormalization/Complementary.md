# Arbitrary palettes on finite ordered graphs

## Abstract

Literal complementary-colour normalization by partition and free signs.

**Definition 1.1 (The literal complementary colour).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.complement`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.complement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c in Fin (2p), the complementary colour is 2p−1−c.

**Definition 1.2 (The lower colour labels the pair).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.pair`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label is min(c,2p−1−c) in Fin p.

**Definition 1.3 (The sign of the actual colour).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.sign`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.sign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign is true exactly when p≤c.

**Definition 1.4 (The literal lifting map).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.lift`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower sign gives t and the upper sign gives 2p−1−t.

**Definition 1.5 (The pair label and sign recover every literal colour).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.colourEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.colourEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two palette halves give inverse maps Fin (2p) and Fin p × Bool.

**Theorem 1.6 (Unequal pair labels characterize legal bonds).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.bond_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.bond_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural p and c,d in Fin (2p), pair c differs from pair d exactly when c differs from d and their natural values do not sum to 2p−1.

**Definition 1.7 (The first vertex of a label class).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.First`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.First` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every strictly earlier vertex has a different label.

**Definition 1.8 (The vertices with a free sign).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Free`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Free` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A free vertex has an earlier vertex with the same pair label.

**Definition 1.9 (The arbitrary-p first-appearance convention).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Normal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair word is canonical and every first vertex has the lower sign. Canonicality gives each smaller label an earlier occurrence, so the used labels form an initial segment and the least vertex has literal colour zero.

**Definition 1.10 (Normalized literal graph assignments).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Legal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assignments have colours in Fin (2p) and obey the actual literal bond at every graph edge.

**Definition 1.11 (Independent partitions with at most p blocks).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.AtMost`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.AtMost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks are the actual nonempty subsets in a Mathlib graph partition.

**Definition 1.12 (Canonical proper pair words).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.OrderedColoring`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.OrderedColoring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restricted-growth labels name the occupied classes in the order of their first vertices.

**Definition 1.13 (Canonical proper words and their independent partitions).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.partitionEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.partitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IndependentPartitionExpansion.coloringEquiv gives the actual blocks and their injected names. The canonical permutation representative of HardinA233177Canonical.canonical_exists_unique is unique because two injections on the same blocks differ by a palette permutation. The inverse names all blocks of any partition with at most p blocks.

**Definition 1.14 (Read the actual pair word).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.toOrderedColoring`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.toOrderedColoring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the lower-member label to each literal colour. The bond equivalence makes the resulting word proper.

**Definition 1.15 (Inverse signs over the same canonical proper word).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.fiberEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.fiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the sign to non-first vertices. The inverse lifts the given word with false at every first vertex and the supplied sign elsewhere. The palette inverse laws recover each endpoint of this equivalence.

**Definition 1.16 (Literal assignments by partition and free signs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.literalPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.literalPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical pair word and its partition determine one another. Together with the sign inverse this decomposes the entire literal assignment type, including partitions that omit some palette labels.

**Theorem 1.17 (Exactly N−k free signs over a k-block partition).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.free_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.free_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite linearly ordered vertex type and each independent partition with k≤p blocks, the free-vertex type of the canonical word reconstructed from the partition has cardinality N−k. Each block has a unique least vertex. Removing these k vertices leaves N−k independent Boolean choices and therefore 2^(N−k) assignments over the partition.

**Theorem 1.18 (The weighted graphical Stirling sum for the actual palette).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.card_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.card_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty finite linearly ordered simple graph and every natural p, the cardinality of Legal G p is the sum of 2^(N−k) S_G(k) over 1≤k≤min(p,N). Here S_G(k) counts the actual unlabelled independent partitions into k blocks. The graphical Stirling expansion is due to Biggs and is presented by Duncan and Peele in Bell and Stirling Numbers for Graphs. The weights here count the normalized complementary-colour lifts. The cardinality is invariant under changing the vertex order, since N and the independent partitions use only the underlying graph.

**Definition 1.19 (The original six-colour scanner at p=3).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.scannerEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.scannerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence is the identity on the literal word. The fixed scanner characterization normal_iff supplies both directions. The original three-pair count and chromatic reduction apply under this identification.

A singleton has literal colour zero and count one for every positive p. For p=1 the unique pair word is constant. Its count is 2^(N−1) on an edgeless nonempty graph and zero on a graph with an edge. The empty carrier has one empty assignment. The sum beginning at k=1 applies to nonempty carriers, and the strip series retain their zero constant-term convention.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.AtMost`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.First`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Free`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.Normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.OrderedColoring`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.bond_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.card_eq_sum`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.colourEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.complement`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.fiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.free_card`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.lift`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.literalPartitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.pair`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.partitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.scannerEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.sign`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.toOrderedColoring`
- Dependency: [D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion](../../Graph/Coloring/IndependentPartitionExpansion.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization](../HardinGraphNormalization.md)
