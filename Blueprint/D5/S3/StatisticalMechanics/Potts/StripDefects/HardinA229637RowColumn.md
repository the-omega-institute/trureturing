# A229637: the first column and the first row

## Abstract

The first column of A229637 vanishes, and its first row is C(k−1,2)2^(k−4) with a sharp order-three recurrence.

**Definition 1.1 (Horizontal bonds of a row).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.horiz`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.horiz` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229637: exact-defect canonical three-colour arrays, table by width*. URL: <https://oeis.org/A229637>.

*Commentary.*

horiz k is the set of column pairs (j, j+1) of a row of width k; a pair whose two cells carry the same colour is a horizontal mistake.

**Definition 1.2 (Diagonal and antidiagonal bonds between rows).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.betw`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.betw` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229637: exact-defect canonical three-colour arrays, table by width*. URL: <https://oeis.org/A229637>.

*Commentary.*

betw k is the set of column pairs (j, j+1) and (j+1, j) joining a cell of a row to the diagonal and antidiagonal cells of the next row.

**Definition 1.3 (The table T(n,k)).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.T` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229637: exact-defect canonical three-colour arrays, table by width*. URL: <https://oeis.org/A229637>.

*Commentary.*

T(n,k) counts the n × k arrays over {0,1,2} whose defect count, with the horizontal bonds inside rows and the diagonal and antidiagonal bonds between consecutive rows, is exactly 2, and whose colours are introduced in row-major order. It uses the same defect and canonical predicates as the width-5 column A229634.

**Definition 1.4 (The first column and the first row).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.claim`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.claim` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229637: exact-defect canonical three-colour arrays, table by width*. URL: <https://oeis.org/A229637>.

*Commentary.*

The claim collects: T(n,1) = 0 for every n; T(1,1) = T(1,2) = 0 and T(1,3) = 1; T(1,k) = C(k−1,2)·2^(k−4) for k ≥ 4; the recurrence T(1,k) = 6T(1,k−1) − 12T(1,k−2) + 8T(1,k−3) for k ≥ 7, with residual −4 at k = 6; and no recurrence of order at most two with rational coefficients holds for all large k. OEIS records the column and row recurrences as empirical and identifies the row with A052482(k−2); the residual at k = 6 and the exclusion of order-two recurrences are added here.

**Theorem 1.5 (Proof of the first column and row).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.result`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229637: exact-defect canonical three-colour arrays, table by width*. URL: <https://oeis.org/A229637>.

*Commentary.*

A single column has no horizontal, diagonal or antidiagonal neighbours, so no array has a mistake and T(n,1) = 0. A single row is a word starting with 0 in which each colour first appears after the previous one, and its mistakes are its equal adjacent letters. Appending a letter to such a word w gives one extension repeating the last letter and, among the other colours, two admissible ones unless w is constant, when only the colour 1 is admissible. So the number c(L,m) of such words of length L with m equal adjacencies obeys c(L+2,m) + [L = m] = c(L+1,m−1) + 2c(L+1,m), giving c(L,0) = 2^(L−2), c(L,1) = (L−1)2^(L−3) and c(L,2) = C(L−1,2)·2^(L−4). The recurrence and the residual follow from the closed form. An order-two recurrence would make 4(k−1)(k−2) − 2c₁(k−2)(k−3) − c₂(k−3)(k−4) vanish at three consecutive k, and the combination of these equations whose quadratic and linear parts cancel gives 8 = 0.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.betw`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.horiz`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
