# Latin Squares of Optimal Internal Extensions

## Abstract

An optimal internal extension of lifted ternary lines determines one Latin square on each row.

**Definition 1.1 (The triple attached to a Latin-square cell).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.latinPoint`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.latinPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In a fixed row, use the two cell indices as labels in residue classes zero and one. The entry at that cell supplies the label in residue class two.

**Theorem 1.2 (Every optimal family comes from Latin squares).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.exists_latin_of_optimal_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.exists_latin_of_optimal_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The internal family has exactly as many ordered slots as there are different-residue ordered pairs within rows. Saturation makes every added triple meet all three residues. The unique completions of pairs in each row give the row and column permutation laws.

**Theorem 1.3 (The unordered family determines the squares).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.latin_assignment_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.latin_assignment_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue of each point determines its slot even after forgetting the order of the triple. The row and the two cell indices determine the third label, so equality of the families gives equality of the entries.

**Theorem 1.4 (Every assignment gives an optimal extension).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.optimal_family_of_latin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.optimal_family_of_latin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permutation laws give unique completion for any two residue classes within a row. The construction retains the mixed triples and satisfies the residue criterion for dimension d plus one. There is one new triple for each cell in each row.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.exists_latin_of_optimal_family`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.latinPoint`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.latin_assignment_injective`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin.optimal_family_of_latin`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](../LatinEulerianDefs.md)
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials](RankThreeInternalTriplePotentials.md)
