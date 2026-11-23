# Latin Squares and Partial Steiner Systems

## Abstract

Internal extensions with the extra ternary potential dimension are organized by rows and residue classes.

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

Each square gives the different-residue triples in its row. Each partial Steiner system adds triples inside one actual residue class.

**Theorem 1.3 (An extension with the extra dimension splits into squares and partial systems).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.forward_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.forward_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue condition forbids a triple with exactly two residues. The different-residue triples cover every required pair and give the Latin square in each row. The remaining triples project to pair-unique triples in their own residue classes.

**Theorem 1.4 (Independent square and packing data give an extension).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.realize_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.realize_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an enumeration for each three-element block in a partial system and transport its labels back into the residue class. The fixed mixed family, the Latin squares, and the partial Steiner systems each give pair uniqueness within their own component. Their three kinds of pairs are disjoint, so pair uniqueness also holds across components. Adding the latter triples preserves the dimension criterion.

**Theorem 1.5 (The unordered extension determines all of its data).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.decomposition_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.decomposition_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three distinct residues of a Latin triple distinguish it from every same-residue triple. A same-residue triple identifies its row and residue class, and its labels are recovered using the given bijection. Thus the unordered family recovers every square entry and every block.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.IsPartialSteiner`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.decomposition_unique`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.extendedFamily`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.forward_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition.realize_decomposition`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin](RankThreeOptimalInternalLatin.md)
