# Partition-indexed polytabloid Specht modules

## Abstract

Construct the Specht representation from the literal partition and its polytabloids.

The rational permutation module acts on left cosets of the consecutive-block Young subgroup. A tableau identifies one coset; column antisymmetrization produces its polytabloid. The row and column groups intersect trivially, making column permutations of that coset distinct and its own coefficient equal to one. Relabeling transports the antisymmetrizer and the tabloid together, so the polytabloid span is a nonzero subrepresentation.

The partition-indexed module uses the actual Young diagram of the partition and transports the symmetric-group action along its cardinality equality. Complexification extends scalars from the rational numbers to the complex numbers. These constructions do not depend on a cycle list, a coefficient formula or a chosen bijection of irreducible characters.

The signed column-group sum is the sum of sign(q) times the group-algebra basis vector q over the column subgroup. Applying it to a tabloid basis vector gives the displayed polytabloid sum. The rational Specht space is the span of all these vectors. The partition-indexed action transports this span along the diagram-cardinality equality, and its complex form extends scalars from the rational numbers. Auxiliary entries link to their exact declarations without duplicating their signatures.

**Theorem 1.1 (sort coe rowLens).**

$$\forall mu \in \operatorname{YoungDiagram},\; \operatorname{descendingSort}\left(\operatorname{rowLengthMultiset}\left(mu\right)\right) = \operatorname{rowLens}\left(mu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.sort_coe_rowLens` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.2 (shapePartition).**

$$\forall mu \in \operatorname{YoungDiagram},\; \operatorname{shapePartition}\left(mu\right) = \operatorname{partitionOfRowLengthMultiset}\left(mu\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.3 (shapePartition parts).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition_parts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition_parts` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.4 (shapePartition parts sort).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition_parts_sort`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition_parts_sort` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.5 (YoungTableau).**

$$\forall mu \in \operatorname{YoungDiagram},\; \operatorname{YoungTableau}\left(mu\right) = \operatorname{Equivalence}\left(\operatorname{cells}\left(mu\right), \operatorname{Fin}\left(\operatorname{card}\left(mu\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.YoungTableau` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.6 (rowIndex).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.7 (colIndex).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.8 (rowIndex def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.9 (colIndex def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.10 (rowIndex apply).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.11 (rowIndex colIndex injective).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_colIndex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_colIndex_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.12 (relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.13 (relabel apply).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.14 (relabel symm apply).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel_symm_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel_symm_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.15 (colIndex relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.16 (nonempty).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.nonempty` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.17 (fiberSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.18 (mem fiberSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_fiberSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_fiberSubgroup` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.19 (fiberSubgroup map conj).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_map_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_map_conj` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.20 (fiberSubgroup inf).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_inf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_inf` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.21 (fiberSubgroup eq bot of injective).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_eq_bot_of_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_eq_bot_of_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.22 (youngBlocksEquiv).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlocksEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlocksEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.23 (youngBlock).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlock`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlock` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.24 (youngBlock youngBlocksEquiv).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlock_youngBlocksEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlock_youngBlocksEquiv` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.25 (youngSubgroup).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{youngSubgroup}\left(mu\right) = \operatorname{fiberSubgroup}\left(\operatorname{youngBlock}\left(mu\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.26 (mem youngSubgroup iff).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_youngSubgroup_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_youngSubgroup_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.27 (youngSubgroup eq fiberSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup_eq_fiberSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup_eq_fiberSubgroup` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.28 (rowSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.29 (colSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.30 (mem rowSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_rowSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_rowSubgroup` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.31 (mem colSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_colSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_colSubgroup` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.32 (rowSubgroup def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.33 (colSubgroup def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.34 (rowSubgroup inf colSubgroup eq bot).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup_inf_colSubgroup_eq_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup_inf_colSubgroup_eq_bot` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.35 (rowYoungConjugator).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowYoungConjugator`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowYoungConjugator` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.36 (rowIndex rowYoungConjugator).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_rowYoungConjugator`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_rowYoungConjugator` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.37 (rowYoungConjugator relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowYoungConjugator_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowYoungConjugator_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.38 (youngSubgroup map conj eq rowSubgroup).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup_map_conj_eq_rowSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup_map_conj_eq_rowSubgroup` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.39 (stabilizer quotientGroup mk).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.stabilizer_quotientGroup_mk`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.stabilizer_quotientGroup_mk` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.40 (permutationModule).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.permutationModule`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.permutationModule` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.41 (subgroupCharSum).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.42 (subgroupCharSum def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.43 (subgroupCharSum coeff).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum_coeff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.44 (signLinearCharacter).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.signLinearCharacter`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.signLinearCharacter` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.45 (coe signLinearCharacter apply).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.coe_signLinearCharacter_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.coe_signLinearCharacter_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.46 (columnAntisymmetrizer).**

$$\forall mu \in \operatorname{YoungDiagram},\; \forall t \in \operatorname{YoungTableau}\left(mu\right),\; \operatorname{columnAntisymmetrizer}\left(t\right) = \operatorname{signedColumnGroupSum}\left(t\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.47 (columnAntisymmetrizer def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.48 (columnAntisymmetrizer eq subgroupCharSum).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_eq_subgroupCharSum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_eq_subgroupCharSum` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.49 (columnAntisymmetrizer coeff).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_coeff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.50 (colSubgroup relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.51 (mem colSubgroup relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_colSubgroup_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_colSubgroup_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.52 (columnAntisymmetrizer relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.53 (tabloid).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.54 (tabloid def).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid_def`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.55 (tabloid relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.56 (smul tabloid eq self iff).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_eq_self_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_eq_self_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.57 (smul tabloid eq iff).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_eq_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.58 (smul tabloid injective).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.59 (polytabloid).**

$$\forall mu \in \operatorname{YoungDiagram},\; \forall t \in \operatorname{YoungTableau}\left(mu\right),\; \operatorname{polytabloid}\left(t\right) = \operatorname{columnAntisymmetrizerAction}\left(t, \operatorname{tabloidBasisVector}\left(t\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.60 (polytabloid eq sum).**

$$\forall mu \in \operatorname{YoungDiagram},\; \forall t \in \operatorname{YoungTableau}\left(mu\right),\; \operatorname{polytabloid}\left(t\right) = \operatorname{sumSignedColumnOrbitBasisVectors}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_eq_sum` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.61 (polytabloid relabel).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.62 (polytabloid coeff smul tabloid).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_coeff_smul_tabloid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_coeff_smul_tabloid` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.63 (polytabloid coeff tabloid).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_coeff_tabloid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_coeff_tabloid` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.64 (polytabloid ne zero).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_ne_zero` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.65 (spechtSubrepresentation).**

$$\forall mu \in \operatorname{YoungDiagram},\; \operatorname{underlyingSubspace}\left(\operatorname{spechtSubrepresentation}\left(mu\right)\right) = \operatorname{rationalSpanOfAllPolytabloids}\left(mu\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtSubrepresentation` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.66 (polytabloid mem spechtSubrepresentation).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_mem_spechtSubrepresentation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_mem_spechtSubrepresentation` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Theorem 1.67 (spechtSubrepresentation ne bot).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtSubrepresentation_ne_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtSubrepresentation_ne_bot` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.68 (spechtModule).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{spechtModule}\left(mu\right) = \operatorname{transportedPolytabloidSpanRepresentation}\left(\operatorname{ofPartition}\left(mu\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtModule` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.69 (baseChange).**

Lean statement: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.baseChange`

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.baseChange` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

**Definition 1.70 (spechtModuleℂ).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{spechtModuleComplex}\left(mu\right) = \operatorname{FDRepOf}\left(\operatorname{baseChange}\left(\operatorname{Complex}, \operatorname{rationalSpechtAction}\left(mu\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtModuleℂ` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Rows, columns, cosets and signs refer to the literal Young diagram and its permutation action.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.YoungTableau`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.baseChange`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.coe_signLinearCharacter_apply`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colIndex_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.colSubgroup_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_coeff`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_eq_subgroupCharSum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.columnAntisymmetrizer_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_eq_bot_of_injective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_inf`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.fiberSubgroup_map_conj`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_colSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_colSubgroup_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_fiberSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_rowSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.mem_youngSubgroup_iff`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.nonempty`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.permutationModule`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_coeff_smul_tabloid`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_coeff_tabloid`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_eq_sum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_mem_spechtSubrepresentation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.polytabloid_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel_apply`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.relabel_symm_apply`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_apply`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_colIndex_injective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowIndex_rowYoungConjugator`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowSubgroup_inf_colSubgroup_eq_bot`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowYoungConjugator`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.rowYoungConjugator_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition_parts`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.shapePartition_parts_sort`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.signLinearCharacter`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_eq_self_iff`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.smul_tabloid_injective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.sort_coe_rowLens`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtModule`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtModuleℂ`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtSubrepresentation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.spechtSubrepresentation_ne_bot`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.stabilizer_quotientGroup_mk`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum_coeff`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.subgroupCharSum_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid_def`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.tabloid_relabel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlock`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlock_youngBlocksEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngBlocksEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup_eq_fiberSubgroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtPolytabloid.youngSubgroup_map_conj_eq_rowSubgroup`
