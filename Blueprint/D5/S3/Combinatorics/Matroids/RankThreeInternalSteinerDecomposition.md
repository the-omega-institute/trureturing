# Latin Squares and Partial Steiner Systems

## Abstract

Internal extensions with the extra ternary potential dimension are organized by rows and residue classes.

For extraction and realization, let $d$ and $r$ be positive integers. A row is a vector of $d$ ternary coordinates. A point consists of a row and a cyclic coordinate modulo $3 \cdot r$. Label the points in each row by a fixed bijection with pairs of a ternary residue and one of the $r$ labels. The first coordinate of each bijection is reduction of the cyclic coordinate modulo three.

Fix an existing indexed family of lifted triples on three distinct rows. Each triple sums to zero in the product group, and every pair on distinct rows occurs with its zero-sum completion. Each pair of distinct points is covered by at most one index. For an extended family, a ternary potential vanishes at the zero point, sums to zero over all points and on each triple, and takes equal values at the two points of any uncovered pair.

**Definition 1.1 (Partial Steiner triple systems).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.IsPartialSteiner`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.IsPartialSteiner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A system is an unordered family of three-element sets. Two distinct labels occur together in at most one member.

**Definition 1.2 (The unordered extension from the square and packing data).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.extendedFamily`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.extendedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each cell, lift its two indices as labels in residues zero and one and its square entry in residue two. For each block of a partial Steiner system, lift its three labels within its specified row and residue class. The unordered internal family is the union of these two sets of triples.

**Theorem 1.3 (An extension with the extra dimension splits into squares and partial systems).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.forward_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.forward_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume each added triple consists of three distinct points in a single row, each pair of distinct points is covered by at most one index of the combined family, and the combined normalized potential space has dimension $d + 1$. Then the unordered added triples equal the family built from one Latin square per row and one partial Steiner system per row and residue.

The residue condition forbids a triple with exactly two residues. The different-residue triples cover each pair from different residues in the same row and give the Latin square there. The remaining triples project to pair-unique blocks in their own residue classes.

**Theorem 1.4 (Independent square and packing data give an extension).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.realize_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.realize_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the fixed pair-unique lifted family and the residue-preserving labellings above, choose a Latin square in each row and a partial Steiner system of labels in each row and residue. These data give a finitely indexed internal extension with exactly the prescribed unordered triples. All triples in the combined family have distinct points, each distinct pair is covered by at most one index, and the normalized potential space has dimension $d + 1$.

Enumerate each packing block and lift its labels back into the residue class. Mixed triples use pairs on different rows, Latin triples use pairs on one row in different residues, and the packing triples use pairs inside a single residue class. The same-residue triples preserve the potential dimension of the Latin extension.

**Theorem 1.5 (The unordered extension determines all of its data).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.decomposition_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.decomposition_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed rowwise labelling bijection, take two assignments of tables and two assignments of partial Steiner systems, one system per row and residue. If their unordered internal families are equal, the tables agree entry by entry and the systems agree in every row and residue.

A triple meeting three residues gives its cell indices and entry. A same-residue triple gives its row, residue, and three labels through the fixed bijection.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.IsPartialSteiner`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.decomposition_unique`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.extendedFamily`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.forward_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.realize_decomposition`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin](RankThreeOptimalInternalLatin.md)
