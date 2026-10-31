---
bibkey: tauceti2026spechtpolytabloids
authors: The Tau Ceti contributors
year: 2026
title: TauCeti partition-indexed polytabloid Specht construction
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156
claim: The literal Young diagram determines a rational polytabloid Specht representation and its complex scalar extension.
strata_touched:
  - D5/S3/Combinatorics/Partitions/SpechtPolytabloid
license: Apache-2.0
triage: anchor
---

# Source, selection and mathematical boundary

The immutable supplier is TauCetiProject/TauCeti at
`5a01f5fe3621126cccf9ba22e700493cbc7b7156`, under Apache-2.0.
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.
The immutable supplier tree contains no NOTICE-prefixed file.

Both projects use Lean 4.35.0. The supplier Mathlib pin is
`ccbef15ebdb41c2addfac682131f83c75904c3c1`; our unchanged Mathlib pin is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This is an A17.2 source port.
Retire each selection only when OUR pinned Mathlib supplies an equivalent
statement with the same hypotheses and conclusions and its use is verified.
Acceptance at a different upstream revision does not satisfy retirement.

The literal partition determines the rational polytabloid module and its complex
scalar extension. The selected chain supplies nonvanishing, complex simplicity,
integer ordinary characters, actual character orthogonality and completeness,
Young permutation-character Hom dimensions, their complete homogeneous Gram
matrix, tableau Kostka numbers, Schur expansions and unrestricted Frobenius.
Generic finite-character algebra, induced-character and Mackey formulas are
reused from existing D5 suppliers rather than copied.

All source in this continuation is UNCOMPILED. Axiom closure, elaborated
proof-term dependence and independent per-declaration admission are UNKNOWN.
Source consumer tables describe textual proof dependencies and candidate
implicit instance/simp uses; they are not native liveness evidence. Known ports
and bind-only organization have no independent novelty or firstfreeze claim.
The unfinished four-slot audit is tracked by
[issue 24542](https://github.com/the-omega-institute/trureturing/issues/24542).
No compiled Reg mirror or declared_validated status is asserted.

## Preserved construction and representation selections

The locators and tables below concern the same immutable supplier revision.
Their historical source endpoints are now consumed by the Young-rule,
Frobenius and trace comparison chain described after the tables.

- `TauCeti/Combinatorics/Young/Diagram.lean:108`: `mergeSort_rowLens`.
- `TauCeti/Combinatorics/Young/Diagram.lean:115`: `sort_coe_rowLens`.
- `TauCeti/Combinatorics/Young/Partitions.lean:103`: `shapePartition`.
- `TauCeti/Combinatorics/Young/Partitions.lean:119`: `shapePartition_parts`.
- `TauCeti/Combinatorics/Young/Partitions.lean:127`: `shapePartition_parts_sort`.
- `TauCeti/Combinatorics/Young/Tableau.lean:60`: `YoungTableau`.
- `TauCeti/Combinatorics/Young/Tableau.lean:67`: `rowIndex`.
- `TauCeti/Combinatorics/Young/Tableau.lean:70`: `colIndex`.
- `TauCeti/Combinatorics/Young/Tableau.lean:75`: `rowIndex_def`.
- `TauCeti/Combinatorics/Young/Tableau.lean:81`: `colIndex_def`.
- `TauCeti/Combinatorics/Young/Tableau.lean:85`: `rowIndex_apply`.
- `TauCeti/Combinatorics/Young/Tableau.lean:97`: `rowIndex_colIndex_injective`.
- `TauCeti/Combinatorics/Young/Tableau.lean:407`: `relabel`.
- `TauCeti/Combinatorics/Young/Tableau.lean:410`: `relabel_apply`.
- `TauCeti/Combinatorics/Young/Tableau.lean:415`: `relabel_symm_apply`.
- `TauCeti/Combinatorics/Young/Tableau.lean:427`: `colIndex_relabel`.
- `TauCeti/Combinatorics/Young/Tableau.lean:465`: `nonempty`.
- `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:62`: `fiberSubgroup`.
- `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:70`: `mem_fiberSubgroup`.
- `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:89`: `fiberSubgroup_map_conj`.
- `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:115`: `fiberSubgroup_inf`.
- `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:140`: `fiberSubgroup_eq_bot_of_injective`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:47`: `youngBlocksEquiv`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:66`: `youngBlock`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:71`: `youngBlock_youngBlocksEquiv`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:159`: `youngSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:172`: `mem_youngSubgroup_stabilizer_iff`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:250`: `mem_youngSubgroup_iff`.
- `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:257`: `youngSubgroup_eq_fiberSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:46`: `rowSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:51`: `colSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:54`: `mem_rowSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:59`: `mem_colSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:65`: `rowSubgroup_def`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:71`: `colSubgroup_def`.
- `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:91`: `rowSubgroup_inf_colSubgroup_eq_bot`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:33`: `rowBlocks`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:36`: `rowCellsEquiv`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:53`: `sortedBlocksEquivRows`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:57`: `cast_rowBlocks_fst`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:69`: `sortedBlocksEquivRows_fst`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:81`: `rowYoungConjugator`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:87`: `rowIndex_rowYoungConjugator`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:128`: `rowYoungConjugator_relabel`.
- `TauCeti/RepresentationTheory/Symmetric/TableauSubgroupConjugacy.lean:137`: `youngSubgroup_map_conj_eq_rowSubgroup`.
- `TauCeti/GroupTheory/QuotientGroup/Basic.lean:81`: `stabilizer_quotientGroup_mk`.
- `TauCeti/RepresentationTheory/Symmetric/PermutationModule/Basic.lean:53`: `permutationModule`.
- `TauCeti/Algebra/MonoidAlgebra/SubgroupCharSum.lean:49`: `subgroupCharSum`.
- `TauCeti/Algebra/MonoidAlgebra/SubgroupCharSum.lean:53`: `subgroupCharSum_def`.
- `TauCeti/Algebra/MonoidAlgebra/SubgroupCharSum.lean:58`: `subgroupCharSum_coeff`.
- `TauCeti/RepresentationTheory/Symmetric/SignCharacter.lean:43`: `signLinearCharacter`.
- `TauCeti/RepresentationTheory/Symmetric/SignCharacter.lean:52`: `coe_signLinearCharacter_apply`.
- `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:87`: `decidablePredMemColSubgroup`.
- `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:98`: `columnAntisymmetrizer`.
- `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:118`: `columnAntisymmetrizer_def`.
- `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:138`: `columnAntisymmetrizer_eq_subgroupCharSum`.
- `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:154`: `columnAntisymmetrizer_coeff`.
- `TauCeti/RepresentationTheory/Symmetric/Relabel.lean:78`: `coeff_conj`.
- `TauCeti/RepresentationTheory/Symmetric/Relabel.lean:96`: `colSubgroup_relabel`.
- `TauCeti/RepresentationTheory/Symmetric/Relabel.lean:115`: `mem_colSubgroup_relabel`.
- `TauCeti/RepresentationTheory/Symmetric/Relabel.lean:134`: `columnAntisymmetrizer_relabel`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:93`: `tabloid`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:97`: `tabloid_def`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:102`: `tabloid_relabel`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:118`: `smul_tabloid_eq_self_iff`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:129`: `smul_tabloid_eq_iff`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:151`: `smul_tabloid_injective`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:168`: `polytabloid`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:190`: `polytabloid_eq_sum`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:199`: `polytabloid_relabel`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:226`: `polytabloid_coeff_smul_tabloid`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:244`: `polytabloid_coeff_tabloid`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:262`: `polytabloid_ne_zero`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:302`: `spechtSubrepresentation`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:323`: `polytabloid_mem_spechtSubrepresentation`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:344`: `spechtSubrepresentation_ne_bot`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:354`: `<finite-dimensional-instance>`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:368`: `spechtModule`.
- `TauCeti/RepresentationTheory/BaseChange.lean:119`: `_root_.Representation.baseChange`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean:92`: `spechtModuleℂ`.


| Declaration | Shape | Current consumers |
| --- | --- | --- |
| `mergeSort_rowLens` | bind-only | `sort_coe_rowLens` |
| `sort_coe_rowLens` | bind-only | `shapePartition_parts_sort` |
| `shapePartition` | bind-only | `shapePartition_parts`; `shapePartition_parts_sort`; `sortedBlocksEquivRows`; `sortedBlocksEquivRows_fst`; `rowYoungConjugator`; `rowIndex_rowYoungConjugator`; `youngSubgroup_map_conj_eq_rowSubgroup`; `tabloid`; `polytabloid`; `polytabloid_relabel`; `spechtSubrepresentation`; `spechtSubrepresentation_ne_bot` |
| `shapePartition_parts` | bind-only | `shapePartition_parts_sort` |
| `shapePartition_parts_sort` | bind-only | `sortedBlocksEquivRows`; `sortedBlocksEquivRows_fst` |
| `YoungTableau` | bind-only | `rowIndex`; `colIndex`; `rowIndex_def`; `colIndex_def`; `rowIndex_apply`; `rowIndex_colIndex_injective`; `relabel`; `relabel_apply`; `relabel_symm_apply`; `colIndex_relabel`; `nonempty`; `youngSubgroup_eq_fiberSubgroup`; `rowSubgroup`; `colSubgroup`; `mem_rowSubgroup`; `mem_colSubgroup`; `rowSubgroup_def`; `colSubgroup_def`; `rowSubgroup_inf_colSubgroup_eq_bot`; `rowYoungConjugator`; `rowIndex_rowYoungConjugator`; `rowYoungConjugator_relabel`; `youngSubgroup_map_conj_eq_rowSubgroup`; `coe_signLinearCharacter_apply`; `columnAntisymmetrizer`; `columnAntisymmetrizer_def`; `columnAntisymmetrizer_eq_subgroupCharSum`; `columnAntisymmetrizer_coeff`; `coeff_conj`; `columnAntisymmetrizer_relabel`; `tabloid`; `tabloid_def`; `tabloid_relabel`; `smul_tabloid_eq_self_iff`; `smul_tabloid_eq_iff`; `smul_tabloid_injective`; `polytabloid`; `polytabloid_eq_sum`; `polytabloid_relabel`; `polytabloid_coeff_smul_tabloid`; `polytabloid_coeff_tabloid`; `polytabloid_ne_zero`; `polytabloid_mem_spechtSubrepresentation`; `spechtSubrepresentation_ne_bot` |
| `rowIndex` | bind-only | `rowIndex_def`; `rowIndex_apply`; `rowIndex_colIndex_injective`; `rowSubgroup`; `mem_rowSubgroup`; `rowSubgroup_def`; `rowIndex_rowYoungConjugator` |
| `colIndex` | bind-only | `colIndex_def`; `rowIndex_colIndex_injective`; `colIndex_relabel`; `colSubgroup`; `mem_colSubgroup`; `colSubgroup_def` |
| `rowIndex_def` | bind-only | `rowIndex_apply`; `rowIndex_colIndex_injective` |
| `colIndex_def` | bind-only | `rowIndex_colIndex_injective`; `colIndex_relabel` |
| `rowIndex_apply` | bind-only | `rowIndex_rowYoungConjugator` |
| `rowIndex_colIndex_injective` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot` |
| `relabel` | bind-only | `relabel_apply`; `relabel_symm_apply`; `colIndex_relabel`; `rowYoungConjugator_relabel`; `colSubgroup_relabel`; `mem_colSubgroup_relabel`; `columnAntisymmetrizer_relabel`; `tabloid_relabel`; `polytabloid_relabel`; `spechtSubrepresentation` |
| `relabel_apply` | bind-only | `rowYoungConjugator_relabel` |
| `relabel_symm_apply` | bind-only | `colIndex_relabel` |
| `colIndex_relabel` | bind-only | `colSubgroup_relabel (simp in conjugacy premise)` |
| `nonempty` | bind-only | `spechtSubrepresentation_ne_bot` |
| `fiberSubgroup` | content (ported construction; source assessment) | `mem_fiberSubgroup`; `fiberSubgroup_map_conj`; `fiberSubgroup_inf`; `fiberSubgroup_eq_bot_of_injective`; `youngSubgroup_eq_fiberSubgroup`; `rowSubgroup`; `colSubgroup`; `rowSubgroup_def`; `colSubgroup_def` |
| `mem_fiberSubgroup` | bind-only | `fiberSubgroup_map_conj`; `youngSubgroup_eq_fiberSubgroup`; `mem_rowSubgroup`; `mem_colSubgroup`; `rowSubgroup_def`; `colSubgroup_def` |
| `fiberSubgroup_map_conj` | bind-only | `youngSubgroup_map_conj_eq_rowSubgroup`; `colSubgroup_relabel` |
| `fiberSubgroup_inf` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot` |
| `fiberSubgroup_eq_bot_of_injective` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot` |
| `youngBlocksEquiv` | content (ported construction; source assessment) | `youngBlock`; `youngBlock_youngBlocksEquiv`; `rowYoungConjugator`; `rowIndex_rowYoungConjugator` |
| `youngBlock` | bind-only | `youngBlock_youngBlocksEquiv`; `youngSubgroup`; `mem_youngSubgroup_stabilizer_iff`; `mem_youngSubgroup_iff`; `youngSubgroup_eq_fiberSubgroup`; `rowIndex_rowYoungConjugator` |
| `youngBlock_youngBlocksEquiv` | bind-only | `rowIndex_rowYoungConjugator` |
| `youngSubgroup` | bind-only | `mem_youngSubgroup_stabilizer_iff`; `mem_youngSubgroup_iff`; `youngSubgroup_eq_fiberSubgroup`; `youngSubgroup_map_conj_eq_rowSubgroup`; `permutationModule`; `tabloid` |
| `mem_youngSubgroup_stabilizer_iff` | bind-only | `mem_youngSubgroup_iff` |
| `mem_youngSubgroup_iff` | bind-only | `youngSubgroup_eq_fiberSubgroup` |
| `youngSubgroup_eq_fiberSubgroup` | bind-only | `youngSubgroup_map_conj_eq_rowSubgroup` |
| `rowSubgroup` | bind-only | `mem_rowSubgroup`; `rowSubgroup_def`; `rowSubgroup_inf_colSubgroup_eq_bot`; `youngSubgroup_map_conj_eq_rowSubgroup`; `smul_tabloid_eq_self_iff`; `smul_tabloid_eq_iff`; `smul_tabloid_injective` |
| `colSubgroup` | bind-only | `mem_colSubgroup`; `colSubgroup_def`; `rowSubgroup_inf_colSubgroup_eq_bot`; `coe_signLinearCharacter_apply`; `columnAntisymmetrizer`; `columnAntisymmetrizer_def`; `columnAntisymmetrizer_eq_subgroupCharSum`; `columnAntisymmetrizer_coeff`; `colSubgroup_relabel`; `mem_colSubgroup_relabel`; `columnAntisymmetrizer_relabel`; `smul_tabloid_injective`; `polytabloid_eq_sum`; `polytabloid_coeff_smul_tabloid` |
| `mem_rowSubgroup` | bind-only | `rowSubgroup_def` |
| `mem_colSubgroup` | bind-only | `colSubgroup_def` |
| `rowSubgroup_def` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot`; `youngSubgroup_map_conj_eq_rowSubgroup` |
| `colSubgroup_def` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot`; `colSubgroup_relabel` |
| `rowSubgroup_inf_colSubgroup_eq_bot` | bind-only | `smul_tabloid_injective` |
| `rowBlocks` | bind-only | `rowCellsEquiv`; `sortedBlocksEquivRows`; `cast_rowBlocks_fst`; `sortedBlocksEquivRows_fst` |
| `rowCellsEquiv` | content (ported construction; source assessment) | `rowYoungConjugator`; `rowIndex_rowYoungConjugator` |
| `sortedBlocksEquivRows` | bind-only | `sortedBlocksEquivRows_fst`; `rowYoungConjugator` |
| `cast_rowBlocks_fst` | bind-only | `sortedBlocksEquivRows_fst` |
| `sortedBlocksEquivRows_fst` | bind-only | `rowIndex_rowYoungConjugator` |
| `rowYoungConjugator` | content (ported construction; source assessment) | `rowIndex_rowYoungConjugator`; `rowYoungConjugator_relabel`; `youngSubgroup_map_conj_eq_rowSubgroup`; `tabloid`; `tabloid_def` |
| `rowIndex_rowYoungConjugator` | bind-only | `youngSubgroup_map_conj_eq_rowSubgroup` |
| `rowYoungConjugator_relabel` | bind-only | `tabloid_relabel` |
| `youngSubgroup_map_conj_eq_rowSubgroup` | bind-only | `smul_tabloid_eq_self_iff` |
| `stabilizer_quotientGroup_mk` | bind-only | `smul_tabloid_eq_self_iff` |
| `permutationModule` | bind-only | `polytabloid`; `polytabloid_relabel`; `spechtSubrepresentation`; `spechtSubrepresentation_ne_bot` |
| `subgroupCharSum` | bind-only | `subgroupCharSum_def`; `subgroupCharSum_coeff`; `columnAntisymmetrizer_eq_subgroupCharSum` |
| `subgroupCharSum_def` | bind-only | `subgroupCharSum_coeff`; `columnAntisymmetrizer_eq_subgroupCharSum` |
| `subgroupCharSum_coeff` | bind-only | `columnAntisymmetrizer_coeff` |
| `signLinearCharacter` | bind-only | `coe_signLinearCharacter_apply`; `columnAntisymmetrizer_eq_subgroupCharSum` |
| `coe_signLinearCharacter_apply` | bind-only | `columnAntisymmetrizer_eq_subgroupCharSum (simp)`; `columnAntisymmetrizer_coeff (simp)` |
| `columnAntisymmetrizer` | content (ported construction; source assessment) | `columnAntisymmetrizer_def`; `columnAntisymmetrizer_eq_subgroupCharSum`; `columnAntisymmetrizer_coeff`; `columnAntisymmetrizer_relabel`; `polytabloid` |
| `columnAntisymmetrizer_def` | bind-only | `columnAntisymmetrizer_eq_subgroupCharSum`; `polytabloid_eq_sum` |
| `columnAntisymmetrizer_eq_subgroupCharSum` | bind-only | `columnAntisymmetrizer_coeff` |
| `columnAntisymmetrizer_coeff` | bind-only | `columnAntisymmetrizer_relabel` |
| `coeff_conj` | bind-only | `columnAntisymmetrizer_relabel` |
| `colSubgroup_relabel` | bind-only | `mem_colSubgroup_relabel` |
| `mem_colSubgroup_relabel` | bind-only | `columnAntisymmetrizer_relabel` |
| `columnAntisymmetrizer_relabel` | bind-only | `polytabloid_relabel` |
| `tabloid` | bind-only | `tabloid_def`; `tabloid_relabel`; `smul_tabloid_eq_self_iff`; `smul_tabloid_eq_iff`; `smul_tabloid_injective`; `polytabloid`; `polytabloid_eq_sum`; `polytabloid_coeff_smul_tabloid`; `polytabloid_coeff_tabloid` |
| `tabloid_def` | bind-only | `tabloid_relabel`; `smul_tabloid_eq_self_iff` |
| `tabloid_relabel` | bind-only | `polytabloid_relabel` |
| `smul_tabloid_eq_self_iff` | bind-only | `smul_tabloid_eq_iff` |
| `smul_tabloid_eq_iff` | bind-only | `smul_tabloid_injective` |
| `smul_tabloid_injective` | bind-only | `polytabloid_coeff_smul_tabloid` |
| `polytabloid` | content (ported construction; source assessment) | `polytabloid_eq_sum`; `polytabloid_relabel`; `polytabloid_coeff_smul_tabloid`; `polytabloid_coeff_tabloid`; `polytabloid_ne_zero`; `spechtSubrepresentation`; `polytabloid_mem_spechtSubrepresentation`; `spechtSubrepresentation_ne_bot` |
| `polytabloid_eq_sum` | bind-only | `polytabloid_coeff_smul_tabloid` |
| `polytabloid_relabel` | bind-only | `spechtSubrepresentation` |
| `polytabloid_coeff_smul_tabloid` | content | `polytabloid_coeff_tabloid` |
| `polytabloid_coeff_tabloid` | content | `polytabloid_ne_zero` |
| `polytabloid_ne_zero` | content | `spechtSubrepresentation_ne_bot` |
| `spechtSubrepresentation` | content (ported construction; source assessment) | `polytabloid_mem_spechtSubrepresentation`; `spechtSubrepresentation_ne_bot`; `spechtModule` |
| `polytabloid_mem_spechtSubrepresentation` | bind-only | `spechtSubrepresentation_ne_bot` |
| `spechtSubrepresentation_ne_bot` | content | Substantive construction/nonvanishing endpoint; no independent theorem closure claimed |
| `spechtModule` | content (ported construction; source assessment) | `spechtModuleℂ` |
| `baseChange` | content (ported construction; source assessment) | `spechtModuleℂ` |
| `spechtModuleℂ` | content (ported construction; source assessment) | Substantive construction/nonvanishing endpoint; no independent theorem closure claimed |
| `decidablePredMemColSubgroup` | bind-only instance | `columnAntisymmetrizer`, `polytabloid_eq_sum` finite sums |
| finite-dimensional submodule instance | bind-only instance | `spechtModule`, hence `spechtModuleℂ` |


| Immutable source locator | Declaration | Candidate proof shape / admission | Source-level current consumer |
| --- | --- | --- | --- |
| `TauCeti/RepresentationTheory/PermutationForm.lean:101` | `permutationForm` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `permutationForm_apply`, `permutationForm_comm`, `permutationForm_isSymm`, `permutationForm_isRefl`, `permutationForm_self_pos`, `permutationForm_self_eq_zero_iff`, `permutationForm_restrict_nondegenerate`, `permutationForm_ofMulAction_invariant`, `permutationForm_ofMulAction_left`, `ofMulAction_mem_orthogonal`, `orthogonalSubrepresentation`, `toSubmodule_orthogonalSubrepresentation`, `isCompl_orthogonalSubrepresentation`, `tabloidForm` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:110` | `permutationForm_apply` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `permutationForm_comm`, `permutationForm_self_pos`, `permutationForm_ofMulAction_invariant` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:122` | `permutationForm_comm` | content candidate (ported); A17.2PORT supplier only, native review pending | `permutationForm_isSymm`, `ofMulAction_mem_orthogonal` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:135` | `permutationForm_isSymm` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `permutationForm_isRefl` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:139` | `permutationForm_isRefl` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `isCompl_orthogonalSubrepresentation` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:183` | `permutationForm_self_pos` | content candidate (ported); A17.2PORT supplier only, native review pending | `permutationForm_self_eq_zero_iff` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:192` | `permutationForm_self_eq_zero_iff` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `permutationForm_restrict_nondegenerate` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:199` | `permutationForm_restrict_nondegenerate` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `isCompl_orthogonalSubrepresentation` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:216` | `permutationForm_ofMulAction_invariant` | content candidate (ported); A17.2PORT supplier only, native review pending | `permutationForm_ofMulAction_left` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:230` | `permutationForm_ofMulAction_left` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `ofMulAction_mem_orthogonal`, `tabloidForm_asAlgebraHom_columnAntisymmetrizer` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:237` | `ofMulAction_mem_orthogonal` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `orthogonalSubrepresentation` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:255` | `orthogonalSubrepresentation` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `toSubmodule_orthogonalSubrepresentation`, `isCompl_orthogonalSubrepresentation`, `isCompl_orthogonalSubrepresentation_permutationModule`, `spechtSubrepresentation_le_or_le_orthogonal`, `exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:264` | `toSubmodule_orthogonalSubrepresentation` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtSubrepresentation_le_or_le_orthogonal` |
| `TauCeti/RepresentationTheory/PermutationForm.lean:285` | `isCompl_orthogonalSubrepresentation` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `isCompl_orthogonalSubrepresentation_permutationModule` |
| `TauCeti/RepresentationTheory/Symmetric/PermutationModule/Form.lean:60` | `tabloidForm` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `tabloidForm_asAlgebraHom_columnAntisymmetrizer` |
| `TauCeti/RepresentationTheory/Symmetric/PermutationModule/Form.lean:99` | `isCompl_orthogonalSubrepresentation_permutationModule` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `isAtom_spechtSubrepresentation`, `exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid` |
| `TauCeti/Combinatorics/Young/Tableau.lean:91` | `colIndex_apply` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_rowIndex_colIndex (simp)` |
| `TauCeti/Combinatorics/Young/Tableau.lean:104` | `rowFiberEquiv` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `card_filter_rowIndex_eq` |
| `TauCeti/Combinatorics/Young/Tableau.lean:164` | `rowIndex_colIndex_mem` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `colIndex_lt_rowLen` |
| `TauCeti/Combinatorics/Young/Tableau.lean:170` | `colIndex_lt_rowLen` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `card_filter_colIndex_lt_and_rowIndex_eq` |
| `TauCeti/Combinatorics/Young/Tableau.lean:182` | `exists_rowIndex_colIndex` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `card_filter_colIndex_lt_and_rowIndex_eq` |
| `TauCeti/Combinatorics/Young/Tableau.lean:187` | `card_filter_rowIndex_eq` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `card_filter_colIndex_comp_lt_and_rowIndex_eq_le`, `colIndex_lt_rowLen_of_injective` |
| `TauCeti/Combinatorics/Young/Tableau.lean:230` | `card_filter_colIndex_lt_and_rowIndex_eq` | content candidate (ported); A17.2PORT supplier only, native review pending | `sum_card_filter_colIndex_comp_lt_and_rowIndex_eq` |
| `TauCeti/Combinatorics/Young/Tableau.lean:258` | `card_filter_colIndex_comp_lt_and_rowIndex_eq_le` | content candidate (ported); A17.2PORT supplier only, native review pending | `colIndex_lt_rowLen_of_injective` |
| `TauCeti/Combinatorics/Young/Tableau.lean:285` | `sum_card_filter_colIndex_comp_lt_and_rowIndex_eq` | content candidate (ported); A17.2PORT supplier only, native review pending | `colIndex_lt_rowLen_of_injective` |
| `TauCeti/Combinatorics/Young/Tableau.lean:318` | `colIndex_lt_rowLen_of_injective` | content candidate (ported); A17.2PORT supplier only, native review pending | `mem_mul_of_not_rowMeetsColumnTwice` |
| `TauCeti/Combinatorics/Young/Tableau.lean:422` | `rowIndex_relabel` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `rowMeetsColumnTwice_relabel_left_iff` |
| `TauCeti/Combinatorics/Young/Tableau.lean:443` | `relabelPerm` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `relabel_relabelPerm`, `exists_relabel_eq` |
| `TauCeti/Combinatorics/Young/Tableau.lean:454` | `relabel_relabelPerm` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_relabel_eq` |
| `TauCeti/Combinatorics/Young/Tableau.lean:458` | `exists_relabel_eq` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtSubrepresentation_eq_span_orbit`, `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul` |
| `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:77` | `swap_mem_fiberSubgroup` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `swap_mem_rowSubgroup`, `swap_mem_colSubgroup` |
| `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:77` | `swap_mem_rowSubgroup` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/RowColumnSubgroup.lean:84` | `swap_mem_colSubgroup` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/Vanishing.lean:80` | `RowMeetsColumnTwice` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `rowMeetsColumnTwice_def`, `rowMeetsColumnTwice_relabel_iff`, `rowMeetsColumnTwice_relabel_left_iff`, `mem_mul_of_not_rowMeetsColumnTwice`, `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul`, `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/Vanishing.lean:86` | `rowMeetsColumnTwice_def` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `rowMeetsColumnTwice_relabel_iff`, `rowMeetsColumnTwice_relabel_left_iff`, `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/Vanishing.lean:94` | `rowMeetsColumnTwice_relabel_iff` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `mem_mul_of_not_rowMeetsColumnTwice` |
| `TauCeti/RepresentationTheory/Symmetric/Vanishing.lean:107` | `rowMeetsColumnTwice_relabel_left_iff` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul` |
| `TauCeti/RepresentationTheory/Symmetric/Factorization.lean:68` | `mem_mul_of_not_rowMeetsColumnTwice` | content candidate (ported); A17.2PORT supplier only, native review pending | `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul` |
| `TauCeti/Algebra/MonoidAlgebra/SubgroupCharSum.lean:88` | `subgroupCharSum_mul_single` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `asAlgebraHom_subgroupCharSum_apply_eq_zero`, `mul_columnAntisymmetrizer_right` |
| `TauCeti/RepresentationTheory/AsAlgebraHom.lean:181` | `asAlgebraHom_eq_zero_of_mul_single_eq_neg` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `asAlgebraHom_subgroupCharSum_apply_eq_zero` |
| `TauCeti/RepresentationTheory/SubgroupCharSum.lean:45` | `asAlgebraHom_subgroupCharSum_apply` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `asAlgebraHom_columnAntisymmetrizer_apply` |
| `TauCeti/RepresentationTheory/SubgroupCharSum.lean:62` | `asAlgebraHom_subgroupCharSum_apply_eq_zero` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `asAlgebraHom_columnAntisymmetrizer_single_eq_zero` |
| `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:191` | `mul_columnAntisymmetrizer_right` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul` |
| `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean:321` | `asAlgebraHom_columnAntisymmetrizer_apply` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `tabloidForm_asAlgebraHom_columnAntisymmetrizer` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:109` | `tabloid_surjective` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:174` | `polytabloid_def` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul`, `spechtSubrepresentation_le_or_le_orthogonal`, `exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid` |
| `TauCeti/RepresentationTheory/Symmetric/PermutationModule/Basic.lean:59` | `permutationModuleBasis` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:317` | `spechtSubrepresentation_toSubmodule` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtSubrepresentation_eq_span_orbit`, `spechtSubrepresentation_le_or_le_orthogonal` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean:329` | `spechtSubrepresentation_eq_span_orbit` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtSubrepresentation_le_or_le_orthogonal`, `intertwiningMap_eq_smul_one_of_apply_polytabloid_eq` |
| `TauCeti/RepresentationTheory/Symmetric/Dominance.lean:114` | `asAlgebraHom_columnAntisymmetrizer_single_eq_zero` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean:91` | `exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid_single` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean:122` | `exists_eq_smul_polytabloid_single` | content candidate (ported); A17.2PORT supplier only, native review pending | `exists_eq_smul_polytabloid` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean:144` | `exists_eq_smul_polytabloid` | content candidate (ported); A17.2PORT supplier only, native review pending | `spechtSubrepresentation_le_or_le_orthogonal`, `algebraMap_intertwiningMap_spechtSubrepresentation_bijective` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean:171` | `tabloidForm_asAlgebraHom_columnAntisymmetrizer` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtSubrepresentation_le_or_le_orthogonal` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean:198` | `spechtSubrepresentation_le_or_le_orthogonal` | content candidate (ported); A17.2PORT supplier only, native review pending | `isAtom_spechtSubrepresentation` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Dominance.lean:79` | `exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `algebraMap_intertwiningMap_spechtSubrepresentation_bijective` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:49` | `intertwiningMap_eq_smul_one_of_apply_polytabloid_eq` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `algebraMap_intertwiningMap_spechtSubrepresentation_bijective` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:92` | `algebraMap_intertwiningMap_injective` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `algebraMap_intertwiningMap_spechtSubrepresentation_injective`, `algebraMap_intertwiningMap_spechtModule_bijective` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:103` | `algebraMap_intertwiningMap_spechtSubrepresentation_injective` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `algebraMap_intertwiningMap_spechtSubrepresentation_bijective` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:118` | `algebraMap_intertwiningMap_spechtSubrepresentation_bijective` | content candidate (ported); A17.2PORT supplier only, native review pending | `algebraMap_intertwiningMap_spechtModule_bijective` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:157` | `algebraMap_intertwiningMap_spechtModule_bijective` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtModuleScalarAlgEquiv` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:195` | `spechtModuleScalarAlgEquiv` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `spechtModuleIntertwiningEndAlgEquiv` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean:209` | `spechtModuleIntertwiningEndAlgEquiv` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `instSimpleSpechtModuleℂ` |
| `TauCeti/LinearAlgebra/TensorProduct/Hom.lean:24` | `isBaseChange_baseChangeHom` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `intertwiningDefect_homBaseChangeEquiv`, `comap_ker_intertwiningDefect_baseChange`, `_root_.Representation.intertwiningMapBaseChangeEquiv` |
| `TauCeti/RepresentationTheory/BaseChange.lean:127` | `_root_.Representation.baseChange_apply` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `intertwiningDefect_baseChange` |
| `TauCeti/RepresentationTheory/BaseChange.lean:492` | `intertwiningDefect` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `intertwiningDefect_apply`, `mem_ker_intertwiningDefect`, `intertwiningMapEquivKerDefect`, `intertwiningDefect_baseChange`, `intertwiningDefect_homBaseChangeEquiv`, `comap_ker_intertwiningDefect_baseChange`, `_root_.Representation.intertwiningMapBaseChangeEquiv` |
| `TauCeti/RepresentationTheory/BaseChange.lean:496` | `intertwiningDefect_apply` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `mem_ker_intertwiningDefect`, `intertwiningDefect_baseChange` |
| `TauCeti/RepresentationTheory/BaseChange.lean:501` | `mem_ker_intertwiningDefect` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `intertwiningMapEquivKerDefect` |
| `TauCeti/RepresentationTheory/BaseChange.lean:509` | `intertwiningMapEquivKerDefect` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `_root_.Representation.intertwiningMapBaseChangeEquiv` |
| `TauCeti/RepresentationTheory/BaseChange.lean:522` | `intertwiningDefect_baseChange` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `intertwiningDefect_homBaseChangeEquiv` |
| `TauCeti/RepresentationTheory/BaseChange.lean:534` | `intertwiningDefect_homBaseChangeEquiv` | content candidate (ported); A17.2PORT supplier only, native review pending | `comap_ker_intertwiningDefect_baseChange` |
| `TauCeti/RepresentationTheory/BaseChange.lean:557` | `comap_ker_intertwiningDefect_baseChange` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `_root_.Representation.intertwiningMapBaseChangeEquiv` |
| `TauCeti/RepresentationTheory/BaseChange.lean:577` | `_root_.Representation.intertwiningMapBaseChangeEquiv` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `_root_.Representation.finrank_intertwiningMap_baseChange` |
| `TauCeti/RepresentationTheory/BaseChange.lean:626` | `_root_.Representation.finrank_intertwiningMap_baseChange` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `finrank_intertwiningMap_spechtModuleℂ` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean:97` | `spechtModuleℂ_def` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `finrank_intertwiningMap_spechtModuleℂ` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean:124` | `finrank_intertwiningMap_spechtModuleℂ` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean:154` | `sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card` | bind-only organization (ported); A17.2PORT supplier only, native review pending | `instSimpleSpechtModuleℂ` |
| `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean:173` | `instSimpleSpechtModuleℂ` | content candidate (ported); A17.2PORT supplier only, native review pending | `sum_spechtTrace_mul_spechtTrace_inv`; actual trace completeness and same-partition HSW comparison |
- `TauCeti/Combinatorics/Enumerative/Partition/Basic.lean`, `parts_equivCast`.
- `TauCeti/RepresentationTheory/Symmetric/Partitions.lean`, from
- `TauCeti/RepresentationTheory/CharacterTable/Values.lean`,
- `TauCeti/RepresentationTheory/BaseChange.lean`,
- `TauCeti/RepresentationTheory/Symmetric/Specht/Character.lean`,
- `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean`,


| Declaration in SpechtPolytabloid namespace | Source consumer |
| --- | --- |
| `TauCeti.parts_equivCast` | `parts_partitionEquivConjClasses_symm_mk` |
| `TauCeti.exists_perm_partition_eq` (ported representative construction) | `permConjClassPartition_surjective` |
| `TauCeti.permConjClassPartition` | `permConjClassPartition_mk`, injectivity, surjectivity and equivalence construction |
| `TauCeti.permConjClassPartition_mk` | injectivity, surjectivity, `partitionEquivPermConjClasses_symm_mk` |
| `TauCeti.permConjClassPartition_injective` | `partitionEquivPermConjClasses` |
| `TauCeti.permConjClassPartition_surjective` | `partitionEquivPermConjClasses` |
| `TauCeti.partitionEquivPermConjClasses` | `partitionEquivConjClasses`, its inverse lemma |
| `TauCeti.partitionEquivConjClasses` | `spechtCharValue`, inverse/parts lemmas, final certification |
| `TauCeti.partitionEquivPermConjClasses_symm_mk` | `partitionEquivConjClasses_symm_mk` via its simp attribute |
| `TauCeti.partitionEquivConjClasses_symm_mk` | `parts_partitionEquivConjClasses_symm_mk` |
| `TauCeti.parts_partitionEquivConjClasses_symm_mk` | `spechtCharValue_ordinaryTrace` (existence and every-representative comparison) |
| `FDRep.exists_char_eq_intCast` | `FDRep.intCharacter_cast` |
| `FDRep.intCharacter` | integer cast/conjugacy, `intClassFunction`, `spechtChar` |
| `FDRep.intCharacter_cast` | `FDRep.intCharacter_conj`, `spechtChar_cast` |
| `FDRep.intCharacter_conj` | `FDRep.intClassFunction` |
| `FDRep.intClassFunction` | `spechtCharConjClasses`, `intClassFunction_apply` |
| `FDRep.intClassFunction_apply` | `spechtCharConjClasses_mk` |
| `Representation.character_baseChange` | `character_spechtModuleℂ` |
| `TauCeti.spechtChar` | rational/complex cast comparison and conjugacy-value comparison |
| `TauCeti.spechtChar_cast` | `character_spechtModuleℂ_intCast` |
| `TauCeti.spechtCharConjClasses` | `spechtCharValue`, `spechtCharConjClasses_mk` |
| `TauCeti.spechtCharConjClasses_mk` | `spechtCharValue_eq_spechtChar` |
| `TauCeti.spechtCharValue` | `spechtCharValue_eq_spechtChar`, final certification |
| `TauCeti.spechtCharValue_eq_spechtChar` | `spechtCharValue_ordinaryTrace` |
| `TauCeti.character_spechtModuleℂ` | `character_spechtModuleℂ_intCast` |
| `TauCeti.character_spechtModuleℂ_intCast` | `spechtCharValue_ordinaryTrace` |
| `TauCeti.spechtCharValue_ordinaryTrace` | `spechtTrace_eq_hsw_frobChar`; actual orthogonality and character completeness; no standalone admission |


| Module / declaration | Immutable supplier or local proof shape | Actual source consumer |
| --- | --- | --- |
| `SpechtMonomialCoordinates.rowLen_eq_zero_of_colLen_le` | `TauCeti/Combinatorics/Young/Diagram.lean:64`; selected port | `SpechtMonomialCoordinates.getD_rowLens` |
| `SpechtMonomialCoordinates.getD_rowLens` | `TauCeti/Combinatorics/Young/Diagram.lean:96`; selected port | `SpechtMonomialCoordinates.rowLen_ofPartition` |
| `SpechtMonomialCoordinates.rowLen_ofPartition` | `TauCeti/Combinatorics/Young/Partitions.lean:48`; selected port | `SpechtMonomialCoordinates.map_univ_val_partWeight`, `SpechtFixedTabloidPowerSum.card_filter_youngColouring` |
| `SpechtMonomialCoordinates.prod_map_X_eq_monomial` | `TauCeti/Algebra/MvPolynomial/Monomial.lean:39`; selected port | `SpechtMonomialCoordinates.coeff_msymm_eq_zero_of_degree_ne`, `SpechtMonomialCoordinates.coeff_msymm`, `SpechtFixedTabloidPowerSum.coeff_psumPart_partition` |
| `SpechtMonomialCoordinates.rowLenWeight` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:254`; selected port | `SpechtMonomialCoordinates.rowLenWeight_apply`, `SpechtMonomialCoordinates.partWeight` |
| `SpechtMonomialCoordinates.rowLenWeight_apply` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:258`; selected port | `SpechtMonomialCoordinates.partWeight_apply` |
| `SpechtMonomialCoordinates.partWeight` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:392`; selected port | `SpechtMonomialCoordinates.partWeight_apply`, `SpechtMonomialCoordinates.map_univ_val_partWeight`, `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight`, `SpechtMonomialCoordinates.coeff_eq_coeff_partWeight`, `SpechtFixedTabloidPowerSum.card_filter_youngColouring`, `SpechtFixedTabloidPowerSum.coeff_partWeight_psumPart_partition` |
| `SpechtMonomialCoordinates.partWeight_apply` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:396`; selected port | `SpechtMonomialCoordinates.map_univ_val_partWeight`, `SpechtFixedTabloidPowerSum.card_filter_youngColouring` |
| `SpechtMonomialCoordinates.exists_perm_comp_eq` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:98`; selected port | `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight` |
| `SpechtMonomialCoordinates.card_toMultiset_eq_degree` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:117`; selected port | `SpechtMonomialCoordinates.weightSym`, `SpechtMonomialCoordinates.coeff_msymm_eq_zero_of_degree_ne` |
| `SpechtMonomialCoordinates.weightSym` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:123`; selected port | `SpechtMonomialCoordinates.coe_weightSym`, `SpechtMonomialCoordinates.weightPartition`, `SpechtMonomialCoordinates.coeff_msymm` |
| `SpechtMonomialCoordinates.coe_weightSym` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:128`; selected port | `SpechtMonomialCoordinates.coeff_msymm` |
| `SpechtMonomialCoordinates.weightPartition` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:134`; selected port | `SpechtMonomialCoordinates.weightPartition_parts`, `SpechtMonomialCoordinates.card_parts_weightPartition_le`, `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight`, `SpechtMonomialCoordinates.coeff_msymm`, `SpechtMonomialCoordinates.coeff_eq_coeff_partWeight`, `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints`, `SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` |
| `SpechtMonomialCoordinates.weightPartition_parts` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:141`; selected port | `SpechtMonomialCoordinates.card_parts_weightPartition_le`, `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight` |
| `SpechtMonomialCoordinates.card_parts_weightPartition_le` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:153`; selected port | `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight`, `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints` |
| `SpechtMonomialCoordinates.map_univ_val` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:163`; selected port | `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight` |
| `SpechtMonomialCoordinates.map_univ_val_partWeight` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:182`; selected port | `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight` |
| `SpechtMonomialCoordinates.exists_perm_mapDomain_eq_partWeight` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:219`; selected port | `SpechtMonomialCoordinates.coeff_eq_coeff_partWeight` |
| `SpechtMonomialCoordinates.coeff_msymm_eq_zero_of_degree_ne` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:237`; selected port | `SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` |
| `SpechtMonomialCoordinates.coeff_msymm` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:249`; selected port | `SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` |
| `SpechtMonomialCoordinates.coeff_eq_coeff_partWeight` | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basis.lean:143`; selected port | `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints` |
| `SpechtFixedTabloidPowerSum.perm_zpow_right` | `TauCeti/GroupTheory/Perm/Basic.lean:55`; selected port | `SpechtFixedTabloidPowerSum.apply_eq_of_apply_eq` |
| `SpechtFixedTabloidPowerSum.apply_eq_of_apply_eq` | `TauCeti/GroupTheory/Perm/Basic.lean:78`; selected port | `SpechtFixedTabloidPowerSum.invariantColouringEquiv` |
| `SpechtFixedTabloidPowerSum.fullCycleType` | `TauCeti/GroupTheory/Perm/Partition.lean:103`; selected port | `SpechtFixedTabloidPowerSum.fullCycleType_def`, `SpechtFixedTabloidPowerSum.fullCycleType_eq_map_card_filter` |
| `SpechtFixedTabloidPowerSum.fullCycleType_def` | `TauCeti/GroupTheory/Perm/Partition.lean:317`; selected port | `SpechtFixedTabloidPowerSum.psumPart_partition_eq_sum_prod_X` |
| `SpechtFixedTabloidPowerSum.fullCycleType_eq_map_card_filter` | `TauCeti/GroupTheory/Perm/Partition.lean:429`; selected port | `SpechtFixedTabloidPowerSum.psumPart_partition_eq_sum_prod_X` |
| `SpechtFixedTabloidPowerSum.invariantColouringEquiv` | `TauCeti/GroupTheory/Perm/Basic.lean:260`; selected port | `SpechtFixedTabloidPowerSum.invariantColouringEquiv_apply_coe`, `SpechtFixedTabloidPowerSum.psumPart_partition_eq_sum_prod_X` |
| `SpechtFixedTabloidPowerSum.invariantColouringEquiv_apply_coe` | `TauCeti/GroupTheory/Perm/Basic.lean:271`; selected port | `SpechtFixedTabloidPowerSum.psumPart_partition_eq_sum_prod_X` |
| `SpechtFixedTabloidPowerSum.card_filter_comp_perm` | `TauCeti/GroupTheory/Perm/Basic.lean:285`; selected port | `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv` |
| `SpechtFixedTabloidPowerSum.fiberSubgroup_comp_of_injective` | `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:109`; selected port | `SpechtFixedTabloidPowerSum.fiberSubgroup_youngColouring` |
| `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv` | `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:267`; selected port | `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv_mk`, `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv_smul`, `SpechtFixedTabloidPowerSum.smul_eq_self_iff_quotientFiberSubgroupEquiv`, `SpechtFixedTabloidPowerSum.card_fixedPoints_quotient_fiberSubgroup` |
| `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv_mk` | `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:290`; selected port | `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv_smul` |
| `SpechtFixedTabloidPowerSum.quotientFiberSubgroupEquiv_smul` | `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:297`; selected port | `SpechtFixedTabloidPowerSum.smul_eq_self_iff_quotientFiberSubgroupEquiv` |
| `SpechtFixedTabloidPowerSum.smul_eq_self_iff_quotientFiberSubgroupEquiv` | `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:307`; selected port | `SpechtFixedTabloidPowerSum.card_fixedPoints_quotient_fiberSubgroup` |
| `SpechtFixedTabloidPowerSum.card_fixedPoints_quotient_fiberSubgroup` | `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:324`; selected port | `SpechtFixedTabloidPowerSum.coeff_partWeight_psumPart_partition` |
| `SpechtFixedTabloidPowerSum.psumPart_isSymmetric` | `TauCeti/RingTheory/MvPolynomial/Symmetric/PowerSum.lean:60`; selected port | `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints` |
| `SpechtFixedTabloidPowerSum.isHomogeneous_psum` | `TauCeti/RingTheory/MvPolynomial/Symmetric/PowerSum.lean:68`; selected port | `SpechtFixedTabloidPowerSum.isHomogeneous_psumPart` |
| `SpechtFixedTabloidPowerSum.isHomogeneous_psumPart` | `TauCeti/RingTheory/MvPolynomial/Symmetric/PowerSum.lean:72`; selected port | `SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` |
| `SpechtFixedTabloidPowerSum.psumPart_partition_eq_sum_prod_X` | `TauCeti/RingTheory/MvPolynomial/Symmetric/PowerSum.lean:96`; selected port | `SpechtFixedTabloidPowerSum.coeff_psumPart_partition` |
| `SpechtFixedTabloidPowerSum.coeff_psumPart_partition` | `TauCeti/RingTheory/MvPolynomial/Symmetric/PowerSum.lean:125`; selected port | `SpechtFixedTabloidPowerSum.coeff_partWeight_psumPart_partition` |
| `SpechtFixedTabloidPowerSum.youngBlockEquiv` | `TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:79`; selected port | `SpechtFixedTabloidPowerSum.card_filter_youngColouring` |
| `SpechtFixedTabloidPowerSum.length_sort_parts_le` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:78`; selected port | `SpechtFixedTabloidPowerSum.youngColouring` |
| `SpechtFixedTabloidPowerSum.psumPart_eq_psumPart_partition` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:84`; selected port | `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints`, `SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities` |
| `SpechtFixedTabloidPowerSum.youngColouring` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:92`; selected port | `SpechtFixedTabloidPowerSum.fiberSubgroup_youngColouring`, `SpechtFixedTabloidPowerSum.card_filter_youngColouring` |
| `SpechtFixedTabloidPowerSum.fiberSubgroup_youngColouring` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:97`; selected port | `SpechtFixedTabloidPowerSum.coeff_partWeight_psumPart_partition` |
| `SpechtFixedTabloidPowerSum.card_filter_youngColouring` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:107`; selected port | `SpechtFixedTabloidPowerSum.coeff_partWeight_psumPart_partition` |
| `SpechtFixedTabloidPowerSum.coeff_partWeight_psumPart_partition` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:133`; selected port | `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints` |
| `SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:176`; selected port | `SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` |
| `SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` | `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:190`; selected port | `SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities`, `SpechtFrobeniusPairing.hsw_frobChar_eq_fixedTabloid_coefficients` |
| `SpechtFrobeniusPairing.char_ofMulAction` | `TauCeti/RepresentationTheory/Induction/Permutation.lean:365`; selected port | `SpechtFrobeniusPairing.char_permutationModuleℂ` |
| `SpechtFrobeniusPairing.permutationModuleℂ` | Local composition; no independent escape witness | `SpechtFrobeniusPairing.char_permutationModuleℂ`, `SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints`, `SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities` |
| `SpechtFrobeniusPairing.char_permutationModuleℂ` | Local composition; no independent escape witness | `SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints` |
| `SpechtFrobeniusPairing.spechtTrace_inv` | Local composition; no independent escape witness | `SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints` |
| `SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints` | Local composition; no independent escape witness | `SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities` |
| `SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities` | Local composition; no independent escape witness | Necessary comparison source; no independent admission; full weighted HSW consumers remain missing |
| `SpechtFrobeniusPairing.hsw_powerSumProd_eq_psumPart` | Local composition; no independent escape witness | `SpechtFrobeniusPairing.hsw_frobChar_eq_fixedTabloid_coefficients` |
| `SpechtFrobeniusPairing.hsw_frobChar_eq_fixedTabloid_coefficients` | Local composition; no independent escape witness | Necessary comparison source; no independent admission; full weighted HSW consumers remain missing |


| Module / declaration | Immutable source or adaptation | Actual source consumer |
| --- | --- | --- |
| `SpechtYoungDominance.lean:sum_list_range` | TauCeti/Combinatorics/Young/Diagram.lean:55; selected body unchanged | `SpechtYoungDominance.lean:sum_take_rowLens_eq_card_filter_fst` |
| `SpechtYoungDominance.lean:sum_range_rowLen_eq_card_filter_fst` | TauCeti/Combinatorics/Young/Diagram.lean:121; selected body unchanged | `SpechtYoungDominance.lean:sum_take_rowLens_eq_card_filter_fst` |
| `SpechtYoungDominance.lean:sum_take_rowLens_eq_card_filter_fst` | TauCeti/Combinatorics/Young/Diagram.lean:202; selected body unchanged | `SpechtYoungDominance.lean:card_filter_le_sum_take_rowLens` |
| `SpechtYoungDominance.lean:card_filter_fst_lt_filter_snd_eq` | TauCeti/Combinatorics/Young/Diagram.lean:214; selected body unchanged | `SpechtYoungDominance.lean:card_filter_le_sum_take_rowLens` |
| `SpechtYoungDominance.lean:card_filter_le_sum_take_rowLens` | TauCeti/Combinatorics/Young/Diagram.lean:239; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_youngBlock_colIndex_injective` |
| `SpechtYoungDominance.lean:Dominates` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:89; selected body unchanged | `SpechtYoungDominance.lean:dominates_iff`, `SpechtYoungDominance.lean:lex_lt_of_dominates_of_ne`, `SpechtYoungDominance.lean:Dominates.antisymm`, `SpechtYoungDominance.lean:dominates_of_youngBlock_colIndex_injective`, `SpechtYoungDominance.lean:dominates_of_forall_swap_smul_ne`, `SpechtYoungDominance.lean:dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero`, `SpechtYoungDominance.lean:asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates`, `SpechtYoungDominance.lean:dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero`, `SpechtYoungDominance.lean:dominates_of_intertwiningMap_ne_zero`, `SpechtYoungDominance.lean:intertwiningMap_eq_zero_of_not_dominates`, `SpechtYoungMultiplicity.lean:spechtMultiplicity_eq_zero_of_not_dominates`, `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_eq_zero`, `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero`, `SpechtYoungTrace.lean:spechtModuleℂ_iso_iff` |
| `SpechtYoungDominance.lean:dominates_iff` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:94; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_youngBlock_colIndex_injective` |
| `SpechtYoungDominance.lean:sortedParts` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:34; selected body unchanged | `SpechtYoungDominance.lean:sortedParts_sum`, `SpechtYoungDominance.lean:lex_lt_of_dominates_of_ne` |
| `SpechtYoungDominance.lean:sortedParts_sum` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:37; selected body unchanged | `SpechtYoungDominance.lean:lex_lt_of_dominates_of_ne` |
| `SpechtYoungDominance.lean:lex_lt_of_prefix_sum_le` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:130; selected body unchanged | `SpechtYoungDominance.lean:lex_lt_of_dominates_of_ne` |
| `SpechtYoungDominance.lean:lex_lt_of_dominates_of_ne` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:167; selected body unchanged | `SpechtYoungDominance.lean:Dominates.antisymm` |
| `SpechtYoungDominance.lean:Dominates.antisymm` | TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean:185; selected body unchanged | `SpechtYoungTrace.lean:spechtModuleℂ_iso_iff` |
| `SpechtYoungDominance.lean:card_filter_youngBlock_lt` | TauCeti/RepresentationTheory/Symmetric/YoungSubgroup.lean:116; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_youngBlock_colIndex_injective` |
| `SpechtYoungDominance.lean:stabilizer_quotientGroup_mk_youngSubgroup` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungDominance.lean:dominates_of_forall_swap_smul_ne` |
| `SpechtYoungDominance.lean:dominates_of_youngBlock_colIndex_injective` | TauCeti/RepresentationTheory/Symmetric/Dominance.lean:65; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_forall_swap_smul_ne` |
| `SpechtYoungDominance.lean:dominates_of_forall_swap_smul_ne` | TauCeti/RepresentationTheory/Symmetric/Dominance.lean:91; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero` |
| `SpechtYoungDominance.lean:dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero` | TauCeti/RepresentationTheory/Symmetric/Dominance.lean:135; selected body unchanged | `SpechtYoungDominance.lean:asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates` |
| `SpechtYoungDominance.lean:asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates` | TauCeti/RepresentationTheory/Symmetric/Dominance.lean:155; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero` |
| `SpechtYoungDominance.lean:dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero` | TauCeti/RepresentationTheory/Symmetric/Dominance.lean:174; selected body unchanged | `SpechtYoungDominance.lean:dominates_of_intertwiningMap_ne_zero` |
| `SpechtYoungDominance.lean:isIrreducible_spechtSubrepresentation` | TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean:257; explicit D5/pinned interface adaptation | `SpechtYoungDominance.lean:dominates_of_intertwiningMap_ne_zero` |
| `SpechtYoungDominance.lean:dominates_of_intertwiningMap_ne_zero` | TauCeti/RepresentationTheory/Symmetric/Specht/Dominance.lean:143; selected body unchanged | `SpechtYoungDominance.lean:intertwiningMap_eq_zero_of_not_dominates` |
| `SpechtYoungDominance.lean:intertwiningMap_eq_zero_of_not_dominates` | TauCeti/RepresentationTheory/Symmetric/Specht/Dominance.lean:182; selected body unchanged | `SpechtYoungMultiplicity.lean:spechtMultiplicity_eq_zero_of_not_dominates` |
| `SpechtYoungMultiplicity.lean:spechtMultiplicity` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:61; selected body unchanged | `SpechtYoungMultiplicity.lean:spechtMultiplicity_eq_zero_of_not_dominates`, `SpechtYoungMultiplicity.lean:spechtMultiplicity_self`, `SpechtYoungTrace.lean:sum_spechtChar_shapePartition_mul_char_permutationModule` |
| `SpechtYoungMultiplicity.lean:spechtMultiplicity_eq_zero_of_not_dominates` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:75; selected body unchanged | `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_eq_zero` |
| `SpechtYoungMultiplicity.lean:exists_intertwiningMap_eq_smul_subtype` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:94; selected body unchanged | `SpechtYoungMultiplicity.lean:spechtSelfMultiplicityEquiv` |
| `SpechtYoungMultiplicity.lean:scalarToSpechtIntertwiningMap` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:155; selected body unchanged | `SpechtYoungMultiplicity.lean:scalarToSpechtIntertwiningMap_injective`, `SpechtYoungMultiplicity.lean:spechtSelfMultiplicityEquiv` |
| `SpechtYoungMultiplicity.lean:scalarToSpechtIntertwiningMap_injective` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:162; selected body unchanged | `SpechtYoungMultiplicity.lean:spechtSelfMultiplicityEquiv` |
| `SpechtYoungMultiplicity.lean:spechtSelfMultiplicityEquiv` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:183; selected body unchanged | `SpechtYoungMultiplicity.lean:spechtMultiplicity_self` |
| `SpechtYoungMultiplicity.lean:spechtMultiplicity_self` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Multiplicity.lean:200; selected body unchanged | `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_self` |
| `SpechtYoungTrace.lean:toPartition_eq_shapePartition` | TauCeti/Combinatorics/Young/Partitions.lean:109; selected body unchanged | `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_eq_zero`, `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_self` |
| `SpechtYoungTrace.lean:ofPartition_shapePartition` | TauCeti/Combinatorics/Young/Partitions.lean:114; selected body unchanged | `SpechtYoungTrace.lean:spechtChar_shapePartition` |
| `SpechtYoungTrace.lean:char_permutationModule` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/Basic.lean:100; selected body unchanged | `SpechtYoungTrace.lean:ratCast_sum_spechtChar_mul_char_permutationModule` |
| `SpechtYoungTrace.lean:spechtChar_eq_of_isConj` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungTrace.lean:sum_spechtChar_shapePartition_mul_char_permutationModule` |
| `SpechtYoungTrace.lean:spechtChar_shapePartition` | TauCeti/RepresentationTheory/Symmetric/Specht/Character.lean:140; explicit D5/pinned interface adaptation | `SpechtYoungTrace.lean:sum_spechtChar_shapePartition_mul_char_permutationModule` |
| `SpechtYoungTrace.lean:sum_spechtChar_shapePartition_mul_char_permutationModule` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/YoungRule.lean:95; explicit D5/pinned interface adaptation | `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_eq_zero`, `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_self` |
| `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_eq_zero` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/YoungRule.lean:111; selected body unchanged | `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero` |
| `SpechtYoungTrace.lean:sum_spechtChar_mul_char_permutationModule_self` | TauCeti/RepresentationTheory/Symmetric/PermutationModule/YoungRule.lean:123; selected body unchanged | `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_self` |
| `SpechtYoungTrace.lean:ratCast_sum_spechtChar_mul_char_permutationModule` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero`, `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_self` |
| `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungTrace.lean:spechtModuleℂ_iso_iff` |
| `SpechtYoungTrace.lean:finrank_hom_spechtModuleℂ_permutationModuleℂ_self` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungTrace.lean:spechtModuleℂ_iso_iff` |
| `SpechtYoungTrace.lean:spechtModuleℂ_iso_iff` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungTrace.lean:sum_spechtTrace_mul_spechtTrace_inv` |
| `SpechtYoungTrace.lean:sum_spechtTrace_mul_spechtTrace_inv` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtYoungCompleteness.lean:spechtClassFunction_pairing` |


| Supplier locator | Selected declaration | Actual source consumer |
| --- | --- | --- |
| `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:347` | `natCard_fiberSubgroup` | `sum_natCard_fiberSubgroup_smul` |
| `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:359` | `exists_forall_card_filter_eq` | `sum_natCard_fiberSubgroup_smul` |
| `TauCeti/GroupTheory/Perm/FiberSubgroup.lean:373` | `sum_natCard_fiberSubgroup_smul` | `sum_card_smul_psumPart_partition` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Complete.lean:76` | `hsymm_eq_sum_piAntidiag` | `sum_card_smul_psumPart_partition` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/PowerSum.lean:160` | `sum_card_smul_psumPart_partition` | `sum_card_fixedPoints_smul_psumPart_partition` |
| `TauCeti/RepresentationTheory/Symmetric/PermutationModule/PowerSum.lean:150` | `sum_card_fixedPoints_smul_psumPart_partition` | `coeff_hsymmPart_partWeight_eq_sum_multiplicity_mul` |


| Declaration in SpechtYoungCompleteness | Source classification | Source consumers |
| --- | --- | --- |
| `classFunctionEquivConjClasses` | adapted supplier, bind-only organization | `spechtCharacterBasis` |
| `spechtClassFunction_pairing` | local binding/normalization of actual orthogonality | `linearIndependent_spechtClassFunction`; `spechtCharacterBasis_repr` |
| `linearIndependent_spechtClassFunction` | direct pinned supplier application | `spechtCharacterBasis` |
| `spechtCharacterBasis` | adapted supplier construction | `spechtCharacterBasis_apply`; `spechtCharacterBasis_repr`; `eq_sum_spechtTrace` |
| `spechtCharacterBasis_apply` | definitional basis equation | `spechtCharacterBasis_repr`; `eq_sum_spechtTrace` |
| `spechtCharacterBasis_repr` | adapted supplier coordinate calculation | `eq_sum_spechtTrace` |
| `eq_sum_spechtTrace` | local basis expansion | `char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace` |
| `youngClassFunction` | existing character organization | `youngClassFunction_coordinate`; `char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace` |
| `youngClassFunction_coordinate` | exact existing D5 Hom pairing application | `char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace` |
| `char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace` | local character decomposition | `sum_char_permutationModuleℂ_mul_char_permutationModuleℂ` |
| `sum_char_permutationModuleℂ_mul_char_permutationModuleℂ` | local finite-sum Gram calculation | `SpechtYoungPolynomialGram.coeff_hsymmPart_partWeight_eq_sum_multiplicity_mul` |


## Tableau and Schur selections

Only the selected declarations below are ported. Existing diagram coordinates and
dominance suppliers are reused. Namespace and root qualifications are adapted;
proof bodies retain the supplier argument. Each row gives an immutable locator,
its local declaration and source consumers. Implicit instance/simp candidates
remain subject to native dependency review.

| Immutable supplier locator | Local declaration | Source consumers |
| --- | --- | --- |
| `TauCeti/Combinatorics/Young/Diagram.lean:87` | `SpechtTableauGeometry.lean:YoungDiagram.rowLen_injective` | `TauCeti.diagramSchurPoly_mul_alternant`; `YoungDiagram.eq_of_betaNumber_eq`; `YoungDiagram.sum_interlacingShapes_eq_sum_piFinset` |
| `TauCeti/Combinatorics/Young/Diagram.lean:145` | `SpechtTableauGeometry.lean:YoungDiagram.card_eq_sum_range_rowLen` | `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`; `YoungDiagram.card_ofRowLensFin`; `YoungDiagram.sum_betaNumber` |
| `TauCeti/Combinatorics/Young/Diagram.lean:156` | `SpechtTableauGeometry.lean:YoungDiagram.card_filter_cells` | `SemistandardYoungTableau.content_recut`; `SemistandardYoungTableau.content_recut_succ` |
| `TauCeti/Combinatorics/Young/Diagram.lean:273` | `SpechtTableauGeometry.lean:YoungDiagram.rowLen_le_of_le` | `TauCeti.BoundedSSYT.interlacedBy_restrictShape`; `YoungDiagram.colLen_le_of_le` |
| `TauCeti/Combinatorics/Young/Diagram.lean:282` | `SpechtTableauGeometry.lean:YoungDiagram.le_of_forall_rowLen_le` | `YoungDiagram.InterlacedBy.le`; `YoungDiagram.IsVerticalStrip.le` |
| `TauCeti/Combinatorics/Young/Diagram.lean:292` | `SpechtTableauGeometry.lean:YoungDiagram.colLen_le_of_le` | `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/Diagram.lean:297` | `SpechtTableauGeometry.lean:YoungDiagram.le_rowLen_of_forall_mem` | `TauCeti.BoundedSSYT.interlacedBy_restrictShape` |
| `TauCeti/Combinatorics/Young/Diagram.lean:305` | `SpechtTableauGeometry.lean:YoungDiagram.finite_Iic` | `YoungDiagram.interlacingShapes` |
| `TauCeti/Combinatorics/Young/Partitions.lean:55` | `SpechtTableauGeometry.lean:YoungDiagram.colLen_zero_ofPartition` | `TauCeti.coeff_schurPoly_eq_kostkaNumber` |
| `TauCeti/Combinatorics/Young/Partitions.lean:60` | `SpechtTableauGeometry.lean:YoungDiagram.ofPartition_injective` | `TauCeti..hsymm_mul_alternant_betaNumber`; `TauCeti.card_weight_eq_sum_partition` |
| `TauCeti/Combinatorics/Young/SemistandardTableau.lean:34` | `SpechtTableauGeometry.lean:SemistandardYoungTableau.entry_le_of_le` | `TauCeti.BoundedSSYT.restrictShape` |
| `TauCeti/Combinatorics/Young/OfRowLens.lean:53` | `SpechtTableauGeometry.lean:YoungDiagram.ofRowLensFin` | `YoungDiagram.card_ofRowLensFin`; `YoungDiagram.colLen_zero_ofRowLensFin_le`; `YoungDiagram.exists_eq_betaNumber_of_strictAnti`; `YoungDiagram.rowLen_ofRowLensFin`; `YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le` |
| `TauCeti/Combinatorics/Young/OfRowLens.lean:58` | `SpechtTableauGeometry.lean:YoungDiagram.rowLen_ofRowLensFin` | `YoungDiagram.card_ofRowLensFin`; `YoungDiagram.exists_eq_betaNumber_of_strictAnti`; `YoungDiagram.sum_interlacingShapes_eq_sum_piFinset` |
| `TauCeti/Combinatorics/Young/OfRowLens.lean:66` | `SpechtTableauGeometry.lean:YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le` | `YoungDiagram.colLen_zero_ofRowLensFin_le`; `YoungDiagram.sum_interlacingShapes_eq_sum_piFinset` |
| `TauCeti/Combinatorics/Young/OfRowLens.lean:74` | `SpechtTableauGeometry.lean:YoungDiagram.colLen_zero_ofRowLensFin_le` | `YoungDiagram.card_ofRowLensFin`; `YoungDiagram.exists_eq_betaNumber_of_strictAnti`; `YoungDiagram.sum_interlacingShapes_eq_sum_piFinset` |
| `TauCeti/Combinatorics/Young/OfRowLens.lean:91` | `SpechtTableauGeometry.lean:YoungDiagram.card_ofRowLensFin` | `YoungDiagram.card_ofRowLensFin [typeclass/simp]`; `YoungDiagram.colLen_zero_ofRowLensFin_le [typeclass/simp]` |
| `TauCeti/Data/Fin/StrictAnti.lean:45` | `SpechtTableauGeometry.lean:StrictAnti.add_sub_le_nat` | `YoungDiagram.exists_eq_betaNumber_of_strictAnti` |
| `TauCeti/Data/Fin/StrictAnti.lean:57` | `SpechtTableauGeometry.lean:Function.Injective.exists_strictAnti_comp` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Data/Fin/StrictAnti.lean:66` | `SpechtTableauGeometry.lean:StrictAnti.perm_eq` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:67` | `SpechtTableauGeometry.lean:YoungDiagram.betaNumber` | `TauCeti..hsymm_mul_alternant_betaNumber`; `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber`; `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`; `TauCeti.diagramSchurPoly_mul_alternant`; `TauCeti.forall_betaNumber_le_iff_interlacedBy` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:69` | `SpechtTableauGeometry.lean:YoungDiagram.betaNumber_def` | `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`; `TauCeti.diagramSchurPoly_mul_alternant`; `TauCeti.forall_betaNumber_le_iff_interlacedBy`; `YoungDiagram.betaNumber_lt_betaNumber`; `YoungDiagram.eq_of_betaNumber_eq` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:74` | `SpechtTableauGeometry.lean:YoungDiagram.betaNumber_lt_betaNumber` | `YoungDiagram.strictAnti_betaNumber` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:99` | `SpechtTableauGeometry.lean:YoungDiagram.eq_of_betaNumber_eq` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:110` | `SpechtTableauGeometry.lean:YoungDiagram.strictAnti_betaNumber` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:118` | `SpechtTableauGeometry.lean:YoungDiagram.exists_eq_betaNumber_of_strictAnti` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/BetaNumbers.lean:148` | `SpechtTableauGeometry.lean:YoungDiagram.sum_betaNumber` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/Kostka.lean:76` | `SpechtKostka.lean:SemistandardYoungTableau.content` | `SemistandardYoungTableau.content_apply`; `SemistandardYoungTableau.content_benderKnuth`; `SemistandardYoungTableau.content_benderKnuth_of_ne`; `SemistandardYoungTableau.content_benderKnuth_self`; `SemistandardYoungTableau.content_benderKnuth_succ` |
| `TauCeti/Combinatorics/Young/Kostka.lean:80` | `SpechtKostka.lean:SemistandardYoungTableau.content_apply` | `SemistandardYoungTableau.content_highestWeight`; `SemistandardYoungTableau.content_recut`; `SemistandardYoungTableau.content_recut_of_ne`; `SemistandardYoungTableau.content_recut_succ`; `SemistandardYoungTableau.sum_content_eq_card_filter` |
| `TauCeti/Combinatorics/Young/Kostka.lean:87` | `SpechtKostka.lean:SemistandardYoungTableau.support_content` | `SemistandardYoungTableau.finite_content_eq`; `TauCeti.BoundedSSYT.lt_of_content_eq`; `TauCeti.BoundedSSYT.support_content_subset_range` |
| `TauCeti/Combinatorics/Young/Kostka.lean:93` | `SpechtKostka.lean:SemistandardYoungTableau.le_entry` | `SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`; `SemistandardYoungTableau.filter_entry_lt_subset_filter_fst_lt`; `TauCeti.BoundedSSYT.colLen_zero_restrictShape_le`; `TauCeti.BoundedSSYT.isEmpty_of_lt_colLen` |
| `TauCeti/Combinatorics/Young/Kostka.lean:102` | `SpechtKostka.lean:SemistandardYoungTableau.filter_entry_lt_subset_filter_fst_lt` | `SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`; `SemistandardYoungTableau.sum_content_le_sum_take_rowLens` |
| `TauCeti/Combinatorics/Young/Kostka.lean:110` | `SpechtKostka.lean:SemistandardYoungTableau.sum_content_eq_card_filter` | `SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`; `SemistandardYoungTableau.sum_content_eq_card`; `SemistandardYoungTableau.sum_content_le_sum_take_rowLens` |
| `TauCeti/Combinatorics/Young/Kostka.lean:130` | `SpechtKostka.lean:SemistandardYoungTableau.sum_content_eq_card` | `TauCeti.BoundedSSYT.sum_weight` |
| `TauCeti/Combinatorics/Young/Kostka.lean:137` | `SpechtKostka.lean:SemistandardYoungTableau.sum_content_le_sum_take_rowLens` | `TauCeti.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero` |
| `TauCeti/Combinatorics/Young/Kostka.lean:145` | `SpechtKostka.lean:SemistandardYoungTableau.content_highestWeight` | `TauCeti.diagramKostkaNumber_rowLen` |
| `TauCeti/Combinatorics/Young/Kostka.lean:157` | `SpechtKostka.lean:SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen` | `TauCeti.diagramKostkaNumber_rowLen` |
| `TauCeti/Combinatorics/Young/Kostka.lean:177` | `SpechtKostka.lean:SemistandardYoungTableau.finite_content_eq` | `SemistandardYoungTableau.content [typeclass/simp]`; `SemistandardYoungTableau.content_apply [typeclass/simp]` |
| `TauCeti/Combinatorics/Young/Kostka.lean:208` | `SpechtKostka.lean:TauCeti.BoundedSSYT` | `TauCeti.BoundedSSYT.__instance_11522`; `TauCeti.BoundedSSYT.benderKnuth`; `TauCeti.BoundedSSYT.benderKnuth_benderKnuth`; `TauCeti.BoundedSSYT.benderKnuth_involutive`; `TauCeti.BoundedSSYT.card_add_weight_last` |
| `TauCeti/Combinatorics/Young/Kostka.lean:217` | `SpechtKostka.lean:TauCeti.BoundedSSYT.entry_lt` | `TauCeti.BoundedSSYT.extend`; `TauCeti.BoundedSSYT.extendTableau`; `TauCeti.BoundedSSYT.fiberEquiv`; `TauCeti.BoundedSSYT.interlacedBy_restrictShape`; `TauCeti.BoundedSSYT.isEmpty_of_lt_colLen` |
| `TauCeti/Combinatorics/Young/Kostka.lean:222` | `SpechtKostka.lean:TauCeti.BoundedSSYT.isEmpty_of_lt_colLen` | `TauCeti.card_weight_eq_sum_partition`; `TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen` |
| `TauCeti/Combinatorics/Young/Kostka.lean:227` | `SpechtKostka.lean:TauCeti.BoundedSSYT.__instance_11522` | `TauCeti.BoundedSSYT [typeclass/simp]`; `TauCeti.BoundedSSYT.__instance_11522 [typeclass/simp]` |
| `TauCeti/Combinatorics/Young/Kostka.lean:240` | `SpechtKostka.lean:TauCeti.finite_boundedSSYT` | `TauCeti.BoundedSSYT [typeclass/simp]`; `TauCeti.BoundedSSYT.__instance_11522 [typeclass/simp]` |
| `TauCeti/Combinatorics/Young/Kostka.lean:249` | `SpechtKostka.lean:TauCeti.__instance_12840` | `TauCeti.BoundedSSYT [typeclass/simp]`; `TauCeti.BoundedSSYT.__instance_11522 [typeclass/simp]` |
| `TauCeti/Combinatorics/Young/Kostka.lean:253` | `SpechtKostka.lean:TauCeti.diagramKostkaNumber` | `TauCeti..coeff_schurPoly`; `TauCeti..coeff_schurPoly_mapDomain`; `TauCeti.BoundedSSYT.card_weight_eq`; `TauCeti.coeff_diagramSchurPoly`; `TauCeti.coeff_hsymmPart` |
| `TauCeti/Combinatorics/Young/Kostka.lean:258` | `SpechtKostka.lean:TauCeti.diagramKostkaNumber_def` | `TauCeti.BoundedSSYT.card_weight_eq`; `TauCeti.diagramKostkaNumber_ne_zero_iff`; `TauCeti.diagramKostkaNumber_rowLen` |
| `TauCeti/Combinatorics/Young/Kostka.lean:266` | `SpechtKostka.lean:TauCeti.diagramKostkaNumber_ne_zero_iff` | `TauCeti.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero` |
| `TauCeti/Combinatorics/Young/Kostka.lean:275` | `SpechtKostka.lean:TauCeti.diagramKostkaNumber_rowLen` | `TauCeti.coeff_diagramSchurPoly_rowLenWeight`; `TauCeti.kostkaNumber_self` |
| `TauCeti/Combinatorics/Young/Kostka.lean:286` | `SpechtKostka.lean:TauCeti.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero` | `TauCeti.dominates_of_kostkaNumber_ne_zero` |
| `TauCeti/Combinatorics/Young/Kostka.lean:299` | `SpechtKostka.lean:TauCeti.kostkaNumber` | `TauCeti..coeff_schurPoly_partWeight`; `TauCeti.coeff_hsymmPart`; `TauCeti.coeff_hsymmPart_partWeight`; `TauCeti.coeff_schurPoly_eq_kostkaNumber`; `TauCeti.dominates_of_kostkaNumber_ne_zero` |
| `TauCeti/Combinatorics/Young/Kostka.lean:304` | `SpechtKostka.lean:TauCeti.kostkaNumber_def` | `TauCeti..coeff_schurPoly_partWeight`; `TauCeti.dominates_of_kostkaNumber_ne_zero`; `TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly`; `TauCeti.kostkaNumber_self` |
| `TauCeti/Combinatorics/Young/Kostka.lean:316` | `SpechtKostka.lean:TauCeti.kostkaNumber_self` | `TauCeti..coeff_schurPoly_partWeight [typeclass/simp]`; `TauCeti.coeff_hsymmPart [typeclass/simp]`; `finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber` |
| `TauCeti/Combinatorics/Young/Kostka.lean:321` | `SpechtKostka.lean:TauCeti.dominates_of_kostkaNumber_ne_zero` | `TauCeti.kostkaNumber_eq_zero_of_not_dominates` |
| `TauCeti/Combinatorics/Young/Kostka.lean:333` | `SpechtKostka.lean:TauCeti.kostkaNumber_eq_zero_of_not_dominates` | `finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:75` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt` | `SemistandardYoungTableau.IsCut`; `SemistandardYoungTableau.bkCut`; `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.bkCut_key`; `SemistandardYoungTableau.content_benderKnuth_self` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:80` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.filter_lt_eq_range` | `SemistandardYoungTableau.lt_rowCountLt_iff` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:100` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.lt_rowCountLt_iff` | `SemistandardYoungTableau.benderKnuth_benderKnuth`; `SemistandardYoungTableau.inBlock_iff`; `SemistandardYoungTableau.recut_rowCountLt`; `SemistandardYoungTableau.rowCountLt_recut_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:106` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_le_rowLen` | `SemistandardYoungTableau.filter_recut_eq`; `SemistandardYoungTableau.filter_recut_eq_succ`; `SemistandardYoungTableau.rowCountLt_eq_zero_of_colLen_le`; `SemistandardYoungTableau.rowCountLt_recut_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:112` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_mono` | `SemistandardYoungTableau.content_recut_add`; `SemistandardYoungTableau.cutLower_le`; `SemistandardYoungTableau.isCut_rowCountLt`; `SemistandardYoungTableau.le_cutUpper` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:121` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_succ_le` | `SemistandardYoungTableau.cutLower_le`; `SemistandardYoungTableau.isCut_rowCountLt`; `SemistandardYoungTableau.le_cutUpper` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:130` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_eq_zero_of_colLen_le` | `SemistandardYoungTableau.sum_prevBlockStart` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:138` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.InBlock` | `SemistandardYoungTableau.__instance_7336`; `SemistandardYoungTableau.benderKnuth_apply_of_inBlock`; `SemistandardYoungTableau.benderKnuth_apply_of_not_inBlock`; `SemistandardYoungTableau.benderKnuth_benderKnuth`; `SemistandardYoungTableau.content_recut_of_ne` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:141` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.__instance_7336` | `SemistandardYoungTableau.InBlock [typeclass/simp]`; `SemistandardYoungTableau.__instance_7336 [typeclass/simp]` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:146` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.inBlock_iff` | `SemistandardYoungTableau.filter_recut_eq`; `SemistandardYoungTableau.filter_recut_eq_succ`; `SemistandardYoungTableau.recutEntry_lt_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:156` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.not_inBlock_of_notMem` | `SemistandardYoungTableau.recut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:173` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.IsCut` | `SemistandardYoungTableau.IsCut.recut`; `SemistandardYoungTableau.content_recut`; `SemistandardYoungTableau.content_recut_add`; `SemistandardYoungTableau.content_recut_of_ne`; `SemistandardYoungTableau.content_recut_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:185` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry` | `SemistandardYoungTableau.inBlock_recutEntry_iff`; `SemistandardYoungTableau.recut`; `SemistandardYoungTableau.recutEntry_col_strict`; `SemistandardYoungTableau.recutEntry_col_strict_aux`; `SemistandardYoungTableau.recutEntry_eq_or` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:189` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_of_not_inBlock` | `SemistandardYoungTableau.inBlock_recutEntry_iff`; `SemistandardYoungTableau.recut`; `SemistandardYoungTableau.recutEntry_eq_or`; `SemistandardYoungTableau.recutEntry_lt_succ`; `SemistandardYoungTableau.recutEntry_row_weak` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:194` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_of_inBlock` | `SemistandardYoungTableau.inBlock_recutEntry_iff`; `SemistandardYoungTableau.recutEntry_eq_or`; `SemistandardYoungTableau.recutEntry_lt_succ`; `SemistandardYoungTableau.recutEntry_row_weak` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:200` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_eq_or` | `SemistandardYoungTableau.benderKnuth_apply_eq_or` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:212` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.inBlock_recutEntry_iff` | `SemistandardYoungTableau.inBlock_recut_iff` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:223` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_lt_succ` | `SemistandardYoungTableau.recutEntry_col_strict_aux` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:247` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_col_strict_aux` | `SemistandardYoungTableau.recutEntry_col_strict` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:259` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_col_strict` | `SemistandardYoungTableau.recut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:267` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recutEntry_row_weak` | `SemistandardYoungTableau.recut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:289` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recut` | `SemistandardYoungTableau.IsCut.recut`; `SemistandardYoungTableau.benderKnuth`; `SemistandardYoungTableau.content_recut`; `SemistandardYoungTableau.content_recut_add`; `SemistandardYoungTableau.content_recut_of_ne` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:300` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recut_apply` | `SemistandardYoungTableau.recut_apply_of_inBlock`; `SemistandardYoungTableau.recut_apply_of_not_inBlock` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:306` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recut_apply_of_inBlock` | `SemistandardYoungTableau.benderKnuth_apply_of_inBlock`; `SemistandardYoungTableau.content_recut_of_ne`; `SemistandardYoungTableau.filter_recut_eq`; `SemistandardYoungTableau.filter_recut_eq_succ`; `SemistandardYoungTableau.recut_rowCountLt` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:311` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recut_apply_of_not_inBlock` | `SemistandardYoungTableau.benderKnuth_apply_of_not_inBlock`; `SemistandardYoungTableau.content_recut_of_ne`; `SemistandardYoungTableau.filter_recut_eq`; `SemistandardYoungTableau.filter_recut_eq_succ`; `SemistandardYoungTableau.recut_rowCountLt` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:316` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.inBlock_recut_iff` | `SemistandardYoungTableau.inBlock_benderKnuth_iff` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:323` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_recut_of_le` | `SemistandardYoungTableau.IsCut.recut`; `SemistandardYoungTableau.rowCountLt_benderKnuth_of_le` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:334` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_recut_of_ge` | `SemistandardYoungTableau.IsCut.recut`; `SemistandardYoungTableau.rowCountLt_benderKnuth_of_ge` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:346` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_recut_succ` | `SemistandardYoungTableau.rowCountLt_benderKnuth_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:381` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.isCut_rowCountLt` | `SemistandardYoungTableau.content_eq_sum`; `SemistandardYoungTableau.content_succ_eq_sum`; `SemistandardYoungTableau.recut_rowCountLt` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:389` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.recut_rowCountLt` | `SemistandardYoungTableau.content_eq_sum`; `SemistandardYoungTableau.content_succ_eq_sum` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:427` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.filter_recut_eq` | `SemistandardYoungTableau.content_recut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:453` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.filter_recut_eq_succ` | `SemistandardYoungTableau.content_recut_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:479` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_recut_of_ne` | `SemistandardYoungTableau.content_benderKnuth_of_ne` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:493` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_recut` | `SemistandardYoungTableau.content_benderKnuth_self`; `SemistandardYoungTableau.content_eq_sum`; `SemistandardYoungTableau.content_recut_add` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:500` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_recut_succ` | `SemistandardYoungTableau.content_recut_add`; `SemistandardYoungTableau.content_succ_eq_sum` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:508` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_eq_sum` | `SemistandardYoungTableau.content_recut_add` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:515` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_succ_eq_sum` | `SemistandardYoungTableau.content_benderKnuth_self`; `SemistandardYoungTableau.content_recut_add` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:523` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_recut_add` | `SemistandardYoungTableau.content_benderKnuth_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:540` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.prevBlockStart` | `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.bkCut_key`; `SemistandardYoungTableau.content_benderKnuth_self`; `SemistandardYoungTableau.cutUpper`; `SemistandardYoungTableau.sum_prevBlockStart` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:545` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.cutLower` | `SemistandardYoungTableau.bkCut`; `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.bkCut_key`; `SemistandardYoungTableau.cutLower_le`; `SemistandardYoungTableau.isCut_bkCut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:549` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.cutUpper` | `SemistandardYoungTableau.bkCut`; `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.bkCut_key`; `SemistandardYoungTableau.isCut_bkCut`; `SemistandardYoungTableau.le_cutUpper` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:554` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.cutLower_le` | `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.isCut_bkCut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:560` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.le_cutUpper` | `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.bkCut_key`; `SemistandardYoungTableau.isCut_bkCut` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:569` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.bkCut` | `SemistandardYoungTableau.benderKnuth`; `SemistandardYoungTableau.benderKnuth_apply_eq_or`; `SemistandardYoungTableau.benderKnuth_apply_of_inBlock`; `SemistandardYoungTableau.bkCut_benderKnuth`; `SemistandardYoungTableau.bkCut_key` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:573` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.isCut_bkCut` | `SemistandardYoungTableau.benderKnuth`; `SemistandardYoungTableau.benderKnuth_apply_of_inBlock`; `SemistandardYoungTableau.benderKnuth_apply_of_not_inBlock`; `SemistandardYoungTableau.content_benderKnuth_of_ne`; `SemistandardYoungTableau.content_benderKnuth_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:596` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.benderKnuth` | `SemistandardYoungTableau.benderKnuth_apply_eq_or`; `SemistandardYoungTableau.benderKnuth_apply_of_inBlock`; `SemistandardYoungTableau.benderKnuth_apply_of_not_inBlock`; `SemistandardYoungTableau.benderKnuth_benderKnuth`; `SemistandardYoungTableau.benderKnuth_involutive` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:600` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.benderKnuth_apply_of_inBlock` | `SemistandardYoungTableau.benderKnuth_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:605` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.benderKnuth_apply_of_not_inBlock` | `SemistandardYoungTableau.benderKnuth_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:610` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.benderKnuth_apply_eq_or` | `TauCeti.BoundedSSYT.benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:615` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.inBlock_benderKnuth_iff` | `SemistandardYoungTableau.benderKnuth_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:619` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_benderKnuth_of_le` | `SemistandardYoungTableau.bkCut_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:623` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_benderKnuth_of_ge` | `SemistandardYoungTableau.bkCut_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:627` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.rowCountLt_benderKnuth_succ` | `SemistandardYoungTableau.bkCut_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:633` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.bkCut_benderKnuth` | `SemistandardYoungTableau.benderKnuth_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:654` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.benderKnuth_benderKnuth` | `SemistandardYoungTableau.benderKnuth_involutive`; `TauCeti.BoundedSSYT.benderKnuth_benderKnuth`; `TauCeti.BoundedSSYT.benderKnuth_involutive` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:668` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.benderKnuth_involutive` | `TauCeti.BoundedSSYT.benderKnuth_involutive`; `TauCeti.rename_swap_diagramSchurPoly` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:674` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.bkCut_key` | `SemistandardYoungTableau.content_benderKnuth_self` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:682` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.sum_prevBlockStart` | `SemistandardYoungTableau.content_benderKnuth_self` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:697` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_benderKnuth_self` | `SemistandardYoungTableau.content_benderKnuth`; `SemistandardYoungTableau.content_benderKnuth_succ` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:711` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_benderKnuth_succ` | `SemistandardYoungTableau.content_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:718` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_benderKnuth_of_ne` | `SemistandardYoungTableau.content_benderKnuth` |
| `TauCeti/Combinatorics/Young/BenderKnuth.lean:725` | `SpechtTableauInvolution.lean:SemistandardYoungTableau.content_benderKnuth` | `TauCeti.BoundedSSYT.weight_benderKnuth` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:97` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.support_content_subset_range` | `TauCeti.BoundedSSYT.mapDomain_weight` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:107` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.weight` | `TauCeti.BoundedSSYT.card_add_weight_last`; `TauCeti.BoundedSSYT.card_weight_eq`; `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.BoundedSSYT.mapDomain_weight`; `TauCeti.BoundedSSYT.mapDomain_weight_swap` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:111` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.weight_apply` | `TauCeti.BoundedSSYT.sum_weight`; `TauCeti.BoundedSSYT.weight_benderKnuth`; `TauCeti.BoundedSSYT.weight_eq_of_content_eq`; `TauCeti.BoundedSSYT.weight_restrict`; `TauCeti.diagramSchurPoly_bot` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:117` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.mapDomain_weight` | `TauCeti.BoundedSSYT.weightFiberEquivContentFiber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:123` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.sum_weight` | `TauCeti.BoundedSSYT.card_add_weight_last`; `TauCeti.isHomogeneous_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:131` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.lt_of_content_eq` | `TauCeti.BoundedSSYT.weightFiberEquivContentFiber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:144` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.weight_eq_of_content_eq` | `TauCeti.BoundedSSYT.weightFiberEquivContentFiber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:153` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.weightFiberEquivContentFiber` | `TauCeti.BoundedSSYT.card_weight_eq` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:164` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.card_weight_eq` | `TauCeti.coeff_diagramSchurPoly`; `TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:176` | `SpechtSchurTableaux.lean:TauCeti.diagramSchurPoly` | `TauCeti..hsymm_mul_diagramSchurPoly`; `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber`; `TauCeti..schurPoly`; `TauCeti..schurPoly_eq_rename`; `TauCeti.coeff_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:183` | `SpechtSchurTableaux.lean:TauCeti.diagramSchurPoly_eq_sum` | `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`; `TauCeti.rename_swap_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:192` | `SpechtSchurTableaux.lean:TauCeti.coeff_diagramSchurPoly` | `TauCeti..coeff_schurPoly_mapDomain`; `TauCeti.coeff_diagramSchurPoly_rowLenWeight`; `TauCeti.map_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:205` | `SpechtSchurTableaux.lean:TauCeti.eval_diagramSchurPoly` | `TauCeti.map_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:225` | `SpechtSchurTableaux.lean:TauCeti.map_diagramSchurPoly` | `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:232` | `SpechtSchurTableaux.lean:TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen` | `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber`; `TauCeti.diagramSchurPoly_eq_zero_iff` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:240` | `SpechtSchurTableaux.lean:TauCeti.diagramSchurPoly_bot` | `TauCeti..schurPoly_partition_zero`; `TauCeti.diagramSchurPoly_mul_alternant`; `TauCeti.prod_hsymm_eq_sum_card_smul` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:264` | `SpechtSchurTableaux.lean:TauCeti.mapDomain_rowLenWeight` | `TauCeti..coeff_schurPoly_partWeight`; `TauCeti.coeff_diagramSchurPoly_rowLenWeight`; `TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:293` | `SpechtSchurTableaux.lean:TauCeti.coeff_diagramSchurPoly_rowLenWeight` | `TauCeti.diagramSchurPoly_ne_zero` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:298` | `SpechtSchurTableaux.lean:TauCeti.diagramSchurPoly_ne_zero` | `TauCeti.diagramSchurPoly_eq_zero_iff` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:306` | `SpechtSchurTableaux.lean:TauCeti.diagramSchurPoly_eq_zero_iff` | `TauCeti..schurPoly_eq_zero_iff` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:324` | `SpechtSchurTableaux.lean:TauCeti.isHomogeneous_diagramSchurPoly` | `TauCeti..isHomogeneous_schurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:369` | `SpechtSchurTableaux.lean:TauCeti..schurPoly` | `TauCeti..coeff_schurPoly`; `TauCeti..coeff_schurPoly_mapDomain`; `TauCeti..coeff_schurPoly_partWeight`; `TauCeti..isHomogeneous_schurPoly`; `TauCeti..schurPoly_eq_rename` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:377` | `SpechtSchurTableaux.lean:TauCeti..schurPoly_eq_rename` | `TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly`; `TauCeti.schurPoly_fin_shapePartition`; `TauCeti.schurPoly_isSymmetric` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:406` | `SpechtSchurTableaux.lean:TauCeti..coeff_schurPoly_mapDomain` | `TauCeti..coeff_schurPoly`; `TauCeti..coeff_schurPoly_partWeight` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:415` | `SpechtSchurTableaux.lean:TauCeti..coeff_schurPoly` | `TauCeti.coeff_hsymmPart`; `TauCeti.coeff_hsymmPart_partWeight` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:431` | `SpechtSchurTableaux.lean:TauCeti..coeff_schurPoly_partWeight` | `TauCeti.coeff_hsymmPart_partWeight`; `TauCeti.coeff_schurPoly_eq_kostkaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:461` | `SpechtSchurTableaux.lean:TauCeti..schurPoly_eq_zero_iff` | `coeff_hsw_vandermonde_mul_schurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean:468` | `SpechtSchurTableaux.lean:TauCeti..isHomogeneous_schurPoly` | `TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:76` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.benderKnuth` | `SemistandardYoungTableau.benderKnuth`; `SemistandardYoungTableau.benderKnuth_apply_eq_or`; `SemistandardYoungTableau.benderKnuth_apply_of_inBlock`; `SemistandardYoungTableau.benderKnuth_apply_of_not_inBlock`; `SemistandardYoungTableau.benderKnuth_benderKnuth` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:85` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.benderKnuth_benderKnuth` | `SemistandardYoungTableau.benderKnuth_benderKnuth`; `SemistandardYoungTableau.benderKnuth_involutive`; `TauCeti.BoundedSSYT.benderKnuth_involutive` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:89` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.benderKnuth_involutive` | `SemistandardYoungTableau.benderKnuth_involutive`; `TauCeti.rename_swap_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:95` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.val_swap` | `TauCeti.BoundedSSYT.weight_benderKnuth` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:106` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.weight_benderKnuth` | `TauCeti.BoundedSSYT.mapDomain_weight_swap` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:112` | `SpechtSchurTableaux.lean:TauCeti.BoundedSSYT.mapDomain_weight_swap` | `TauCeti.rename_swap_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:125` | `SpechtSchurTableaux.lean:TauCeti.rename_swap_diagramSchurPoly` | `TauCeti.isSymmetric_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:141` | `SpechtSchurTableaux.lean:TauCeti.isSymmetric_diagramSchurPoly` | `TauCeti.rename_diagramSchurPoly`; `TauCeti.schurPoly_isSymmetric` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:163` | `SpechtSchurTableaux.lean:TauCeti.rename_diagramSchurPoly` | `TauCeti.schurPoly_fin_shapePartition` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:177` | `SpechtSchurTableaux.lean:TauCeti.isSymmetric_rename` | `TauCeti.schurPoly_isSymmetric` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean:185` | `SpechtSchurTableaux.lean:TauCeti.schurPoly_isSymmetric` | `TauCeti.coeff_schurPoly_eq_kostkaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:338` | `SpechtSchurTableaux.lean:TauCeti.coeff_schurPoly_eq_kostkaNumber` | `TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean:352` | `SpechtSchurTableaux.lean:TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm` | `psumPart_eq_sum_spechtCharValue_smul_schurPoly` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:88` | `SpechtSchurBranching.lean:YoungDiagram.InterlacedBy` | `TauCeti..hsymm_mul_alternant_betaNumber`; `TauCeti..hsymm_mul_diagramSchurPoly`; `TauCeti.BoundedSSYT.extend`; `TauCeti.BoundedSSYT.extendTableau`; `TauCeti.BoundedSSYT.extendTableau_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:94` | `SpechtSchurBranching.lean:YoungDiagram.interlacedBy_iff` | `TauCeti.diagramSchurPoly_mul_alternant`; `TauCeti.forall_betaNumber_le_iff_interlacedBy`; `YoungDiagram.sum_interlacingShapes_eq_sum_piFinset` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:99` | `SpechtSchurBranching.lean:YoungDiagram.InterlacedBy.rowLen_succ_le` | `YoungDiagram.InterlacedBy.mem_of_lt` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:104` | `SpechtSchurBranching.lean:YoungDiagram.InterlacedBy.rowLen_le` | `YoungDiagram.InterlacedBy.le`; `YoungDiagram.IsVerticalStrip.le`; `YoungDiagram.IsVerticalStrip.rowLen_le` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:108` | `SpechtSchurBranching.lean:YoungDiagram.InterlacedBy.le` | `SemistandardYoungTableau.filter_recut_eq`; `SemistandardYoungTableau.recutEntry_row_weak`; `TauCeti..hsymm_mul_diagramSchurPoly`; `TauCeti.BoundedSSYT.extendTableau`; `TauCeti.BoundedSSYT.restrictShape_extend` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:114` | `SpechtSchurBranching.lean:YoungDiagram.InterlacedBy.mem_of_lt` | `TauCeti.BoundedSSYT.extendTableau` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:123` | `SpechtSchurBranching.lean:YoungDiagram.interlacingShapes` | `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes`; `TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes`; `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`; `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:129` | `SpechtSchurBranching.lean:YoungDiagram.mem_interlacingShapes` | `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes`; `TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes`; `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`; `TauCeti.card_weight_eq_sum_partition`; `TauCeti.diagramSchurPoly_mul_alternant` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:138` | `SpechtSchurBranching.lean:YoungDiagram.sum_interlacingShapes_eq_sum_piFinset` | `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:177` | `SpechtSchurBranching.lean:TauCeti.forall_betaNumber_le_iff_interlacedBy` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:218` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrictShape` | `TauCeti.BoundedSSYT.card_add_weight_last`; `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.BoundedSSYT.colLen_zero_restrictShape_le`; `TauCeti.BoundedSSYT.content_restrict`; `TauCeti.BoundedSSYT.fiberEquiv` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:227` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.mem_restrictShape` | `TauCeti.BoundedSSYT.colLen_zero_restrictShape_le`; `TauCeti.BoundedSSYT.interlacedBy_restrictShape`; `TauCeti.BoundedSSYT.mem_iff_of_restrictShape_eq`; `TauCeti.BoundedSSYT.restrictShape_extend`; `TauCeti.BoundedSSYT.restrictShape_le` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:233` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.mem_iff_of_restrictShape_eq` | `TauCeti.BoundedSSYT.content_restrict`; `TauCeti.BoundedSSYT.fiberEquiv`; `TauCeti.BoundedSSYT.restrict`; `TauCeti.BoundedSSYT.restrictTableau` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:238` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrictShape_le` | `TauCeti.BoundedSSYT.interlacedBy_restrictShape` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:245` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.interlacedBy_restrictShape` | `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:256` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.colLen_zero_restrictShape_le` | `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:265` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes` | `TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:274` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrictTableau` | `TauCeti.BoundedSSYT.restrict`; `TauCeti.BoundedSSYT.restrictTableau_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:288` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrictTableau_apply` | `TauCeti.BoundedSSYT.restrict`; `TauCeti.BoundedSSYT.restrict_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:297` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrict` | `TauCeti.BoundedSSYT.card_add_weight_last`; `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.BoundedSSYT.content_restrict`; `TauCeti.BoundedSSYT.fiberEquiv`; `TauCeti.BoundedSSYT.fiberEquiv_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:305` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrict_apply` | `TauCeti.BoundedSSYT.content_restrict`; `TauCeti.BoundedSSYT.fiberEquiv` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:314` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.content_restrict` | `TauCeti.BoundedSSYT.weight_restrict` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:331` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.extendTableau` | `TauCeti.BoundedSSYT.extend`; `TauCeti.BoundedSSYT.extendTableau_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:357` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.extendTableau_apply` | `TauCeti.BoundedSSYT.extend`; `TauCeti.BoundedSSYT.extend_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:365` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.extend` | `TauCeti.BoundedSSYT.extend_apply`; `TauCeti.BoundedSSYT.fiberEquiv`; `TauCeti.BoundedSSYT.fiberEquiv_symm_apply`; `TauCeti.BoundedSSYT.restrictShape_extend` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:376` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.extend_apply` | `TauCeti.BoundedSSYT.fiberEquiv`; `TauCeti.BoundedSSYT.restrictShape_extend` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:384` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.restrictShape_extend` | `TauCeti.BoundedSSYT.fiberEquiv`; `TauCeti.BoundedSSYT.fiberEquiv_symm_apply` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:394` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.fiberEquiv` | `TauCeti.BoundedSSYT.fiberEquiv_apply`; `TauCeti.BoundedSSYT.fiberEquiv_symm_apply`; `TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes` |
| `TauCeti/Combinatorics/Young/Interlacing.lean:438` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes` | `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Branching.lean:100` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.weight_restrict` | `TauCeti.BoundedSSYT.card_add_weight_last`; `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.BoundedSSYT.weight_eq_mapDomain_add_single` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Branching.lean:108` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.card_add_weight_last` | `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`; `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Branching.lean:120` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.weight_eq_mapDomain_add_single` | `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Branching.lean:140` | `SpechtSchurBranching.lean:TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes` | `TauCeti.card_weight_eq_sum_partition` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Branching.lean:180` | `SpechtSchurBranching.lean:TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` | `TauCeti.diagramSchurPoly_mul_alternant` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:92` | `SpechtSchurAlternant.lean:TauCeti.alternant` | `TauCeti..hsymm_mul_alternant_betaNumber`; `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber`; `TauCeti.alternant_comp_perm`; `TauCeti.alternant_def`; `TauCeti.alternant_eq_X_last_pow_mul_det` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:98` | `SpechtSchurAlternant.lean:TauCeti.alternant_def` | `TauCeti.alternant_comp_perm`; `TauCeti.alternant_eq_X_last_pow_mul_det`; `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`; `TauCeti.alternant_eq_sum`; `TauCeti.diagramSchurPoly_mul_alternant` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:104` | `SpechtSchurAlternant.lean:TauCeti.alternant_eq_sum` | `TauCeti.coeff_alternant`; `TauCeti.hsymm_mul_alternant` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:110` | `SpechtSchurAlternant.lean:TauCeti.coeff_alternant` | `TauCeti.coeff_alternant_of_injective` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:133` | `SpechtSchurAlternant.lean:TauCeti.coeff_alternant_of_injective` | `TauCeti.alternant_ne_zero_of_injective` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:151` | `SpechtSchurAlternant.lean:TauCeti.alternant_ne_zero_of_injective` | `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:178` | `SpechtSchurAlternant.lean:TauCeti.alternant_comp_perm` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:184` | `SpechtSchurAlternant.lean:TauCeti.alternant_eq_zero_of_not_injective` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:233` | `SpechtSchurAlternant.lean:TauCeti.hsymm_mul_alternant` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Bialternant.lean:86` | `SpechtSchurBialternant.lean:TauCeti.alternant_eq_X_last_pow_mul_det` | `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Bialternant.lean:139` | `SpechtSchurBialternant.lean:TauCeti.alternant_eq_prod_mul_sum_interlacingShapes` | `TauCeti.diagramSchurPoly_mul_alternant` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Bialternant.lean:241` | `SpechtSchurBialternant.lean:TauCeti.injective_staircase` | `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Bialternant.lean:254` | `SpechtSchurBialternant.lean:TauCeti.diagramSchurPoly_mul_alternant` | `TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber` |
| `TauCeti/GroupTheory/Perm/SignedDomination.lean:47` | `SpechtSchurPieri.lean:TauCeti.sum_sign_filter_forall_le_of_antitone` | `TauCeti..hsymm_mul_alternant_betaNumber` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Pieri.lean:103` | `SpechtSchurPieri.lean:TauCeti..hsymm_mul_alternant_betaNumber` | `TauCeti..hsymm_mul_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Pieri.lean:337` | `SpechtSchurPieri.lean:TauCeti..mul_diagramSchurPoly_of_mul_alternant_betaNumber` | `TauCeti..hsymm_mul_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Pieri.lean:380` | `SpechtSchurPieri.lean:TauCeti..hsymm_mul_diagramSchurPoly` | `TauCeti.prod_hsymm_eq_sum_card_smul` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:77` | `SpechtSchurKostka.lean:TauCeti.card_weight_eq_sum_partition` | `TauCeti.prod_hsymm_eq_sum_card_smul` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:106` | `SpechtSchurKostka.lean:TauCeti.prod_hsymm_eq_sum_card_smul` | `TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:148` | `SpechtSchurKostka.lean:TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly` | `TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:162` | `SpechtSchurKostka.lean:TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly` | `TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:179` | `SpechtSchurKostka.lean:TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly` | `TauCeti.coeff_hsymmPart` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:204` | `SpechtSchurKostka.lean:TauCeti.coeff_hsymmPart` | `TauCeti.coeff_hsymmPart_partWeight` |
| `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean:215` | `SpechtSchurKostka.lean:TauCeti.coeff_hsymmPart_partWeight` | `finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber` |

The unitriangular Gram uniqueness argument is selected and adapted from
`TauCeti/LinearAlgebra/Matrix/Cholesky/Unitriangular.lean:42`, declaration
`eq_of_transpose_mul_self_eq`. Its consumer is the actual Hom–Kostka equality.
The unrestricted Frobenius proof is selected and adapted from
`TauCeti/RepresentationTheory/Symmetric/FrobeniusCharacteristic.lean:164`, declaration
`psumPart_eq_sum_spechtCharValue_smul_schurPoly`. It consumes actual Young rule,
not a coefficient-defined character.

## Actual comparison consumers

| Declaration | Source role and actual source consumer |
| --- | --- |
| `hsymm_eq_sum_piAntidiag` | Existing proof exposed for `hsymm_mul_alternant`; no duplicate proof |
| `coeff_hsymmPart_partWeight_eq_sum_multiplicity_mul` | Existing actual Hom Gram coefficient consumed by `finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber` |
| `eq_of_transpose_mul_self_eq` | Finite partial-order descending induction; consumed by the actual Hom–Kostka equality |
| `finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber` | Actual complex Hom dimensions; consumed by `char_permutationModuleℂ_eq_sum_kostkaNumber_mul_spechtTrace` |
| `char_permutationModuleℂ_eq_sum_kostkaNumber_mul_spechtTrace` | Actual Young-character equality; consumed by `card_fixedPoints_eq_sum_kostkaNumber_mul_spechtChar` |
| `card_fixedPoints_eq_sum_kostkaNumber_mul_spechtChar` | Exact integer descent of the actual characters; consumed by unrestricted Frobenius |
| `psumPart_eq_sum_spechtCharValue_smul_schurPoly` | Every degree and finite alphabet over every commutative ring; consumed by `spechtCharValue_eq_hsw_frobChar` |
| `hsw_vandermonde3_eq_alternant` | Exact staircase (2,1,0); consumed by coefficient isolation |
| `schurPoly_fin` | Exact finite alphabet coordinate transport; consumed by coefficient isolation |
| `coeff_hsw_vandermonde_mul_schurPoly` | Height vanishing and literal same-partition delta; consumed by integer HSW comparison |
| `spechtCharValue_eq_hsw_frobChar` | Integer ordinary character equals the existing coefficient; consumed by actual trace comparison |
| `spechtTrace_eq_hsw_frobChar` | Consumes `spechtCharValue_ordinaryTrace` for the SAME independently constructed complex module; consumed by the triple theorem |
| `triplePartition` | Literal positive row partition; consumed by shape and triple trace theorems |
| `triplePartition_shape` | Original first three rows and all later rows zero; consumed by the triple trace theorem |
| `spechtTrace_triplePartition_eq_hsw_frobChar` | Consumed by `HemmerStraubWestremOrdinary.ordinaryCharacter_triple_eq_coefficient`, then by BOTH `leftTerm_eq_frobenius` and `rightTerm_eq_frobenius`; no standalone admission |

The local same-shape comparison is candidate coefficient-isolation content;
the padded trace statement is exact application organization. Neither supplies
independent admission evidence. Literal labels, full cycle partitions including
ones, and integer-to-complex character casts are retained. No degree bound by
the alphabet is introduced. The tableau height bound is used only to isolate
the requested three-row coefficient.

## Full remaining theorem and evidence boundary

`HemmerStraubWestremOrdinary` defines the actual complex trace at an
independently selected full-cycle representative. `ordinaryCharacter_eq_trace`
compares it with any representative of the same complete partition; that
comparison is used at the representation supplier's own representative in the
triple coefficient bridge. `evTypes_spec` supplies positive parts and doubled
size to `evPartition`. This partition is formed separately for each occurrence
of the original Ev list, without conversion to a finite set. Its parts are the
literal multiset of the occurrence, including ones. The R3 membership proofs
supply decreasing triples of size 2n; `triplePartition` retains their exact
positive rows and zero padding. The rectangle is (n,n,0) for every n.

| Ordinary declaration | Textual source consumer |
| --- | --- |
| `ordinaryCharacter_eq_trace` | `ordinaryCharacter_triple_eq_coefficient` |
| `evTypes_spec` | `evPartition`, used in both ordinary terms |
| `leftTerm_eq_frobenius` | `pointwise_identity`, `averages_eq_frobenius` |
| `rightTerm_eq_frobenius` | `pointwise_identity`, `averages_eq_frobenius` |
| `pointwise_identity` | `weighted_identity` |
| `averages_eq_frobenius` | `HemmerStraubWestremOrdinaryClosedForm.result` |
| `weighted_identity` | `HemmerStraubWestremOrdinaryClosedForm.result` |
| `HemmerStraubWestremOrdinaryClosedForm.result` | Exact external full-problem endpoint, without a standalone known-port claim |

The coefficient API is the canonical
`HemmerStraubWestremWeightedAverage.result` published at
https://github.com/the-omega-institute/trureturing/blob/69f68474a0566d6f465a14259b74f28b58e293f3/D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.lean.
The closed-form composition references that API through its original module
path, rather than copying its implementation. Its supplier import must be
available before native validation of this composition. The coefficient owner
must reuse the strongest
`LatticeHalfFockChargedCoefficients.solution_unique`; neither its implementation
nor its formal ODE proof is reproduced in these ordinary-character consumers.

The full endpoint retains every n >= 1 and every input partition, independent
per-occurrence Ev choices with duplicate outcomes, full positive cycle lists
including ones, the existing exact reciprocal centralizer
`z = product_k k^multiplicity(k) * multiplicity(k)!`, length sign,
integer-to-rational-to-complex casts, and all even-part shapes of size 2n with
at most three rows and zero padding. Both weighted averages are compared with
choose(n/2+2,2) in even degree and zero in odd degree. These are source-level
consumers; native proof-term dependence and the complete ordinary result remain
unverified.

All new sources require native reconstruction, accepted axiom closure and
proof-term dependence checks. The faithful Reg audit still requires exact
whole-family source reconstruction, lawful enrolled-template readout,
variation/sensitivity and actual observational dependence, with compiled binding
evidence. Finite roles do not replace these unbounded families. Original
preregistration 21960 and the coefficient-only scope of 22528 are unchanged.
Ordinary PR required CI, review and merge remain due for a finished delivery.

## Apache License 2.0 (complete upstream LICENSE)

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
