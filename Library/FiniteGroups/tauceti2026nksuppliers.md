---
bibkey: tauceti2026nksuppliers
authors: The Tau Ceti contributors; Kevin Gomez
year: 2026
title: Finite-group and Young-tableau suppliers for Schur moments
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278
claim: "Character sums, algebra centers, partition dominance, Young-diagram counting, and tableau constructions."
strata_touched:
  - D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01
  - D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01
  - D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02
license: Apache-2.0
triage: anchor
---

## Verified locator

DOI: null

Source: https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278

The PartitionYoungDiagram compatibility declarations are by Kevin Gomez,
Mathlib revision `3b531c35df33d6bbe64b4e87dec056211d3a5676`, blob
`ac23c7777b7fe62455d359a79c1cab5d0e7b8fe0`.

Copyright (c) 2026 Tau Ceti. All rights reserved.
Authors: The Tau Ceti contributors.
Copyright (c) 2026 Kevin Gomez. All rights reserved.

The `YoungTableau` carrier is written directly as `↥μ.cells ≃ Fin μ.card`; the `sortedParts` forwarding name is inlined as `μ.parts.sort (· ≥ ·)`.

The `unitaryTorus` range and `StrictlyDominates` relation are also written directly in their consumers.

## Source and declaration mapping

The local port uses the repository's pinned Mathlib APIs. It relocates declarations
into file namespaces, prunes declarations without consumers, writes tableau
carriers directly, and uses the existing normal-matrix diagonalization theorem
`Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`. The product-center and
diagonal maps are assembled from `AlgHom.pi`, `AlgHom.codRestrict`,
`AlgEquiv.ofBijective`, `Matrix.diagonalRingHom` and `Circle.coeHom`; the list-range
sum applies `List.sum_toFinset` directly. The row-length total applies the frozen
`D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts.rowLens_sum`.

### AlgebraGroups01

Source: `TauCeti/Algebra/Group/Conj.lean`.

- `TauCeti.isConj_inv_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.isConj_inv_iff`.
- `ConjClasses.ncard_carrier_mk_eq_card_filter` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.ConjClasses.ncard_carrier_mk_eq_card_filter`.

Source: `TauCeti/Algebra/Group/ConjFinite.lean`.

- `TauCeti.ConjClasses.card_carrier_pos` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.ConjClasses.card_carrier_pos`.

Source: `TauCeti/Algebra/MonoidAlgebra/SubgroupCharSum.lean`.

- `TauCeti.subgroupCharSum` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.subgroupCharSum`.
- `TauCeti.subgroupCharSum_def` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.subgroupCharSum_def`.
- `TauCeti.subgroupCharSum_coeff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.subgroupCharSum_coeff`.
- `TauCeti.single_mul_subgroupCharSum` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.single_mul_subgroupCharSum`.
- `TauCeti.subgroupCharSum_mul_single` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.subgroupCharSum_mul_single`.

Source: `TauCeti/Algebra/MonoidAlgebra/Trace.lean`.

- `TauCeti.MonoidAlgebra.trace_mulRight` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.MonoidAlgebra.trace_mulRight`.
- `MonoidAlgebra.trace_mulLeft_single_mul_mulRight` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.MonoidAlgebra.trace_mulLeft_single_mul_mulRight`.

Source: `TauCeti/Algebra/MvPolynomial/Monomial.lean`.

- `TauCeti.prod_map_X_eq_monomial` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.prod_map_X_eq_monomial`.

Source: `TauCeti/Algebra/Subalgebra/Center.lean`.

- `Subalgebra.map_center_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Subalgebra.map_center_eq`.
- `TauCeti.centerCongr` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.centerCongr`.
- `TauCeti.centerPiAlgEquiv` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.centerPiAlgEquiv`.
- `TauCeti.centerAlgEquivOfIsCentral` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.centerAlgEquivOfIsCentral`.

Source: `TauCeti/Algebra/Matrix/Pi.lean`.

- `TauCeti.finrank_pi_matrix` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.finrank_pi_matrix`.
- `TauCeti.centerPiMatrixAlgEquiv` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.centerPiMatrixAlgEquiv`.

Source: `TauCeti/Analysis/Matrix/UnitaryGroup/Basic.lean`.

- `Matrix.diagonal_mem_unitaryGroup_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Matrix.diagonal_mem_unitaryGroup_iff`.
- `Circle.coe_mem_unitary` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Circle.coe_mem_unitary`.

Source: `TauCeti/Analysis/Matrix/UnitaryGroup/Torus.lean`.

- `TauCeti.unitaryTorusHom` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.unitaryTorusHom`.
- `TauCeti.coe_unitaryTorusHom` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.coe_unitaryTorusHom`.
- `TauCeti.mem_unitaryTorus_iff_exists_unitaryTorusHom` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.mem_unitaryTorus_iff_exists_unitaryTorusHom`.
- `TauCeti.mem_unitaryTorus_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.mem_unitaryTorus_iff`.
- `TauCeti.exists_conj_mem_unitaryTorus` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.exists_conj_mem_unitaryTorus`.
- `TauCeti.exists_isConj_unitaryTorusHom` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.exists_isConj_unitaryTorusHom`.

Source: `TauCeti/Combinatorics/Enumerative/Partition/Basic.lean`.

- `TauCeti.parts_equivCast` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.parts_equivCast`.

Source: `TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean`.

- `_private.TauCeti.Combinatorics.Enumerative.Partition.Dominance.0.TauCeti.sortedParts_sum` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.sortedParts_sum`.
- `_private.TauCeti.Combinatorics.Enumerative.Partition.Dominance.0.TauCeti.sortedParts_length_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.sortedParts_length_le`.
- `TauCeti.PartitionLex.partitionLinearOrder` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.PartitionLex.partitionLinearOrder`.
- `TauCeti.PartitionLex.partition_lt_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.PartitionLex.partition_lt_iff`.
- `TauCeti.Dominates` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Dominates`.
- `TauCeti.dominates_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.dominates_iff`.
- `TauCeti.dominates_iff_forall_fin` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.dominates_iff_forall_fin`.
- `TauCeti.instDecidableDominates` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.instDecidableDominates`.
- `TauCeti.dominates_refl` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.dominates_refl`.
- `TauCeti.Dominates.trans` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Dominates.trans`.
- `_private.TauCeti.Combinatorics.Enumerative.Partition.Dominance.0.TauCeti.lex_lt_of_prefix_sum_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.lex_lt_of_prefix_sum_le`.
- `_private.TauCeti.Combinatorics.Enumerative.Partition.Dominance.0.TauCeti.lex_lt_of_dominates_of_ne` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.lex_lt_of_dominates_of_ne`.
- `TauCeti.Dominates.antisymm` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Dominates.antisymm`.
- `TauCeti.DominanceOrder.partitionPartialOrder` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.DominanceOrder.partitionPartialOrder`.
- `TauCeti.DominanceOrder.partition_le_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.DominanceOrder.partition_le_iff`.
- `TauCeti.DominanceOrder.partition_lt_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.DominanceOrder.partition_lt_iff`.
- `TauCeti.strictlyDominates_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.strictlyDominates_iff`.
- `TauCeti.lex_lt_of_strictlyDominates` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.lex_lt_of_strictlyDominates`.
- `TauCeti.lex_le_of_dominates` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.lex_le_of_dominates`.

Source: `TauCeti/Combinatorics/Young/Diagram.lean`.

- `YoungDiagram.sum_list_range` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.YoungDiagram.sum_list_range`.
- `YoungDiagram.rowLen_eq_zero_of_colLen_le` → `D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero μ i hi`.
- `YoungDiagram.lt_colLen_zero_of_mem` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.YoungDiagram.lt_colLen_zero_of_mem`.
- `YoungDiagram.rowLen_bot` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.YoungDiagram.rowLen_bot`.
- `YoungDiagram.rowLen_injective` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.YoungDiagram.rowLen_injective`.

### YoungTableaux01

Source: `TauCeti/Combinatorics/Young/Diagram.lean`.

- `YoungDiagram.getD_rowLens` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.getD_rowLens`.
- `_private.TauCeti.Combinatorics.Young.Diagram.0.YoungDiagram.mergeSort_rowLens` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.mergeSort_rowLens`.
- `YoungDiagram.sort_coe_rowLens` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.sort_coe_rowLens`.
- `YoungDiagram.sum_range_rowLen_eq_card_filter_fst` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.sum_range_rowLen_eq_card_filter_fst`.
- `YoungDiagram.card_eq_sum_range_rowLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_eq_sum_range_rowLen`.
- `YoungDiagram.card_filter_cells` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_filter_cells`.
- `YoungDiagram.sum_take_rowLens_eq_card_filter_fst` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.sum_take_rowLens_eq_card_filter_fst`.
- `YoungDiagram.card_filter_fst_lt_filter_snd_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_filter_fst_lt_filter_snd_eq`.
- `YoungDiagram.card_filter_le_sum_take_rowLens` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_filter_le_sum_take_rowLens`.
- `YoungDiagram.rowLen_le_of_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.rowLen_le_of_le`.
- `YoungDiagram.le_of_forall_rowLen_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.le_of_forall_rowLen_le`.
- `YoungDiagram.le_rowLen_of_forall_mem` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.le_rowLen_of_forall_mem`.
- `YoungDiagram.finite_Iic` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.finite_Iic`.
- `YoungDiagram.mem_iff_of_colLen_le_one` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.mem_iff_of_colLen_le_one`.
- `YoungDiagram.cells_eq_of_colLen_le_one` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.cells_eq_of_colLen_le_one`.
- `YoungDiagram.card_eq_rowLen_of_colLen_le_one` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_eq_rowLen_of_colLen_le_one`.

Source: `TauCeti/Combinatorics/Young/OfRowLens.lean`.

- `YoungDiagram.ofRowLensFin` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.ofRowLensFin`.
- `YoungDiagram.rowLen_ofRowLensFin` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.rowLen_ofRowLensFin`.
- `YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le`.
- `YoungDiagram.colLen_zero_ofRowLensFin_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.colLen_zero_ofRowLensFin_le`.
- `YoungDiagram.ofRowLensFin_rowLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.ofRowLensFin_rowLen`.

Source: `TauCeti/Combinatorics/Young/SemistandardTableau.lean`.

- `SemistandardYoungTableau.entry_le_of_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.SemistandardYoungTableau.entry_le_of_le`.

Source: `TauCeti/Combinatorics/Young/Tableau.lean`.

- `TauCeti.YoungTableau.rowIndex` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowIndex`.
- `TauCeti.YoungTableau.colIndex` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.colIndex`.
- `TauCeti.YoungTableau.rowIndex_def` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowIndex_def`.
- `TauCeti.YoungTableau.colIndex_def` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.colIndex_def`.
- `TauCeti.YoungTableau.rowIndex_apply` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowIndex_apply`.
- `TauCeti.YoungTableau.colIndex_apply` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.colIndex_apply`.
- `TauCeti.YoungTableau.rowIndex_colIndex_injective` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowIndex_colIndex_injective`.
- `TauCeti.YoungTableau.rowFiberEquiv` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowFiberEquiv`.
- `TauCeti.YoungTableau.colFiberEquiv` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.colFiberEquiv`.
- `TauCeti.YoungTableau.rowIndex_colIndex_mem` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowIndex_colIndex_mem`.
- `TauCeti.YoungTableau.colIndex_lt_rowLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.colIndex_lt_rowLen`.
- `TauCeti.YoungTableau.rowIndex_lt_colLen_zero` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.rowIndex_lt_colLen_zero`.
- `TauCeti.YoungTableau.exists_rowIndex_colIndex` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.exists_rowIndex_colIndex`.
- `TauCeti.YoungTableau.card_filter_rowIndex_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.card_filter_rowIndex_eq`.
- `TauCeti.YoungTableau.card_filter_colIndex_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.card_filter_colIndex_eq`.
- `TauCeti.YoungTableau.exists_ne_and_apply_eq_of_lt_colLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.exists_ne_and_apply_eq_of_lt_colLen`.
- `TauCeti.YoungTableau.card_filter_rowIndex_lt` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.card_filter_rowIndex_lt`.
- `_private.TauCeti.Combinatorics.Young.Tableau.0.TauCeti.YoungTableau.card_filter_colIndex_lt_and_rowIndex_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.card_filter_colIndex_lt_and_rowIndex_eq`.
- `_private.TauCeti.Combinatorics.Young.Tableau.0.TauCeti.YoungTableau.card_filter_colIndex_comp_lt_and_rowIndex_eq_le` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.card_filter_colIndex_comp_lt_and_rowIndex_eq_le`.
- `_private.TauCeti.Combinatorics.Young.Tableau.0.TauCeti.YoungTableau.sum_card_filter_colIndex_comp_lt_and_rowIndex_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau.sum_card_filter_colIndex_comp_lt_and_rowIndex_eq`.

### YoungTableaux02

Source: `TauCeti/Combinatorics/Young/Tableau.lean`.

- `TauCeti.YoungTableau.colIndex_lt_rowLen_of_injective` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.colIndex_lt_rowLen_of_injective`.
- `TauCeti.YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt`.
- `TauCeti.YoungTableau.rowFilling` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.rowFilling`.
- `TauCeti.YoungTableau.val_rowFilling` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.val_rowFilling`.
- `TauCeti.YoungTableau.relabel` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.relabel`.
- `TauCeti.YoungTableau.relabel_apply` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.relabel_apply`.
- `TauCeti.YoungTableau.relabel_symm_apply` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.relabel_symm_apply`.
- `TauCeti.YoungTableau.rowIndex_relabel` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.rowIndex_relabel`.
- `TauCeti.YoungTableau.colIndex_relabel` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.colIndex_relabel`.
- `TauCeti.YoungTableau.relabelPerm` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.relabelPerm`.
- `TauCeti.YoungTableau.relabel_relabelPerm` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.relabel_relabelPerm`.
- `TauCeti.YoungTableau.exists_relabel_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.exists_relabel_eq`.
- `TauCeti.YoungTableau.nonempty` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.nonempty`.

Source: `TauCeti/Combinatorics/Young/Dominance.lean`.

- `TauCeti.YoungTableau.sum_take_rowLens_le_of_injective` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungTableau.sum_take_rowLens_le_of_injective`.

Source: `TauCeti/Combinatorics/Young/StandardTableau/Basic.lean`.

- `TauCeti.StandardYoungTableau` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.StandardYoungTableau`.

Source: `TauCeti/Combinatorics/Young/StandardTableau/Reading.lean`.

- `YoungDiagram.readingIndex` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex`.
- `YoungDiagram.readingIndex_lt_card` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex_lt_card`.
- `YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt`.
- `YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt`.
- `YoungDiagram.eq_of_readingIndex_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.eq_of_readingIndex_eq`.
- `TauCeti.StandardYoungTableau.rowSuperstandard` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.StandardYoungTableau.rowSuperstandard`.

Source: `TauCeti/Compat/PartitionYoungDiagram.lean`.

- `YoungDiagram.sum_rowLens_eq_card` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.sum_rowLens_eq_card`.
- `YoungDiagram.card_transpose` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.card_transpose`.
- `YoungDiagram.toPartition` → `D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n ⟨μ, h⟩`.
- `YoungDiagram.ofPartition` → `((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm p).1`.
- `YoungDiagram.rowLens_ofPartition_eq_sort_parts` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.rowLens_ofPartition_eq_sort_parts`.
- `YoungDiagram.card_ofPartition` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.card_ofPartition`.
- `YoungDiagram.ofPartition_toPartition` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.ofPartition_toPartition`.
- `YoungDiagram.toPartition_ofPartition` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.toPartition_ofPartition`.
- `YoungDiagram.equivPartition` → `D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n`.

Source: `TauCeti/Combinatorics/Young/Kostka.lean`.

- `SemistandardYoungTableau.content` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content`.
- `SemistandardYoungTableau.content_apply` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content_apply`.
- `SemistandardYoungTableau.support_content` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.support_content`.
- `SemistandardYoungTableau.le_entry` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.le_entry`.
- `SemistandardYoungTableau.filter_entry_lt_subset_filter_fst_lt` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.filter_entry_lt_subset_filter_fst_lt`.
- `SemistandardYoungTableau.sum_content_eq_card_filter` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.sum_content_eq_card_filter`.
- `SemistandardYoungTableau.sum_content_eq_card` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.sum_content_eq_card`.
- `SemistandardYoungTableau.sum_content_le_sum_take_rowLens` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.sum_content_le_sum_take_rowLens`.
- `SemistandardYoungTableau.content_highestWeight` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content_highestWeight`.
- `SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`.
- `SemistandardYoungTableau.finite_content_eq` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.finite_content_eq`.
- `TauCeti.BoundedSSYT` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.BoundedSSYT`.
- `TauCeti.BoundedSSYT.entry_lt` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.BoundedSSYT.entry_lt`.
- `TauCeti.BoundedSSYT.isEmpty_of_lt_colLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.BoundedSSYT.isEmpty_of_lt_colLen`.
- `TauCeti.BoundedSSYT.instUniqueBotYoungDiagram` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.BoundedSSYT.instUniqueBotYoungDiagram`.
- `TauCeti.finite_boundedSSYT` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.finite_boundedSSYT`.
- `TauCeti.instFintypeBoundedSSYT` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.instFintypeBoundedSSYT`.
- `TauCeti.diagramKostkaNumber` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.diagramKostkaNumber`.
- `TauCeti.diagramKostkaNumber_def` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.diagramKostkaNumber_def`.
- `TauCeti.diagramKostkaNumber_ne_zero_iff` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.diagramKostkaNumber_ne_zero_iff`.
- `TauCeti.diagramKostkaNumber_rowLen` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.diagramKostkaNumber_rowLen`.
- `TauCeti.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero` → `D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero`.

The name map applies to every integration layer. Later layers use the published row-length theorem and the forward and inverse maps of the published diagram/partition equivalence directly.

## Apache License, Version 2.0

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

```
