# Canonical row enumeration

## Abstract

Canonical width-six boundary rows.

The equality-pattern index selects a row-table entry for each boundary. For every canonical boundary, the selected entry equals that boundary.

**Remark 1.1 (Canonical rows).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.rows`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.rows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The type is Fin 187 -> Data.Row. Each entry is a six-position word over Fin 4 in first-appearance order. The reconstruction theorem pins this table's coverage.

**Remark 1.2 (Equality-pattern index).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.rowIndex`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.rowIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The type is Data.Row -> Fin 187. The index depends only on equalities between row positions. Reconstruction identifies its representative for every canonical row.

**Theorem 1.3 (Canonical reconstruction).**

$$\forall (p: \operatorname{Data}.\operatorname{Row}), ((\operatorname{Canonical}\left(p\right)) \Rightarrow (\operatorname{rows}\left(\operatorname{rowIndex}\left(p\right)\right) = p))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

Canonicality forces the first coordinate to be zero. The remaining five coordinates determine the row, and finite checks partitioned by the next two coordinates identify its equality-pattern representative. This reconstructs every canonical boundary before colour-permutation transport.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.reconstruction`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.rowIndex`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](Data.md)
