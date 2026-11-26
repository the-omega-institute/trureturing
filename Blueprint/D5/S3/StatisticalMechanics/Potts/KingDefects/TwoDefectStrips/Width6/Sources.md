# Width-six source index

## Abstract

Canonical source rows with valid residual budgets.

**Remark 1.1 (Valid sources).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.sources`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.sources` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The type is Fin 313 -> Data.Row x Fin 3. The entries are exactly the canonical six-position rows paired with residual budgets d for which the horizontal defect count is at most 2-d. Certificate.canonical_successors proves reconstruction from the row index and budget.

**Remark 1.2 (Source lookup).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.sourceIndex`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.sourceIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The type is Fin 187 -> Fin 3 -> Fin 313. At every valid row and residual budget, this lookup selects their pair in sources; values at invalid pairs are immaterial. Certificate.canonical_successors pins the lookup on the valid domain.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.sourceIndex`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.sources`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](Data.md)
