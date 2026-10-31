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

# Source and license

The immutable TauCeti revision is 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
It and this repository use Lean 4.35.0. Its Mathlib pin is
ccbef15ebdb41c2addfac682131f83c75904c3c1; ours is
56a005855ea17e0b0958f73ec801ae140b0a1679. A17.2 therefore requires a
source port. No dependency or pin change is made. The complete selected consumer has been elaborated at our pins. Selected
statements and proof strategies are ported with namespace, universe, pinned-API
and coercion adaptations; the native correction commits preserve the original
mathematical objects and hypotheses.
The root license is reproduced below. Every selected source bears an Apache-2.0
header. The downloaded immutable tree contains no NOTICE-prefixed file.

Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.

Retire each port only when OUR lake-manifest.json-pinned Mathlib contains an
equivalent declaration with the same hypotheses and conclusions and its use is
verified at that pin. Acceptance at some other upstream revision is insufficient.

The full-file import closure of Specht/Module contains 47 TauCeti files. The port
selects only the construction and nonvanishing dependencies below; induction,
generic character theory, the tabloid bilinear form and the symmetrizer ideal are
not copied. Existing frozen FiniteCharacterAlgebra, InducedCharacterFormula and
MackeyCharacterFormula remain the suppliers for the later generic character steps.
This selection is a source dependency assessment, not a native constant closure.

## Selected declarations and source-level admission

The following locators refer to the immutable revision above. Each helper is
retained for a current use in the polytabloid construction or nonvanishing proof.
Definitions implement the actual objects. Structural construction and coefficient
isolation are candidate content; bind-only helpers organize their live proofs.
The full ordinary-character consumer is SpechtThreeRowCauchy.
Per-declaration source classifications below distinguish organizational helpers
from the constructions they support; current native dependency and admission
readings accompany the full delivery.

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

## Per-declaration source assessment

These are source classifications, not accepted native dependency evidence. Every
bind-only entry names a current proof or construction consumer. The two implicit
simp uses must be confirmed by native proof terms. No classification grants firstfreeze.

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

The nonzero coefficient proof is the nominated source content: distinct column
permutations yield distinct tabloids because the row and column groups intersect
trivially; the finite signed sum then has coefficient one at its own tabloid.
The new construction proof closes stability under relabeling on the spanning
generators. The native dependency and independent semantic audit must confirm
that these are admissible content at the unchanged pins.

## Mathematical boundary

The Specht module uses precisely YoungDiagram.ofPartition of the supplied partition,
the rational span of its column-antisymmetrized tabloids and explicit cardinality
transport. Complexification is the scalar extension of that same representation.
The definitions are independent of a desired Frobenius coefficient.
No irreducibility or equality with an ordinary character is asserted by this port.
The rejected PartitionAlternantCoefficients standalone module and its Scribe are
removed. Its source derivation remains recoverable at c77e08fff8fb94bc8a77133f38ca3a3768bd08df
and is reusable only in a full comparison that actually consumes it.

Still required are native verification of the simplicity continuation below,
the rational/integer trace character and trace cast, literal full-cycle class indexing (including
fixed points), Young's rule, arbitrary-degree finite-alphabet Schur expansion,
bialternant and height vanishing, the coefficient comparison at the padded
three-row label, and substitution into the existing full weighted HSW argument.
No degree bound, changed character model, dropped Ev multiplicity or restricted
shape family is an acceptable replacement. Preregistration #21960 already records the full original ordinary-character
assertion and its weighted conventions. Issue #22528 concerns the earlier
coefficient result. Current Reg reconstruction and validation of the new
ordinary trace comparison remain unfinished; no duplicate preregistration is needed.

## James submodule continuation

`SpechtTabloidForm` and `SpechtSubmoduleTheorem` select the invariant pairing,
its orthogonal complement, the row-column counting/factorization argument,
James's rank-one antisymmetrizer calculation, the submodule dichotomy and
rational irreducibility for the **same** literal partition. They do not copy
the symmetrizer ideal, dominance order, character classification, standard basis,
Young's rule or symmetric-polynomial modules. The original 80 declarations
remain in `SpechtPolytabloid`; this continuation selects 79 named declarations plus one local invertibility instance
from 20 immutable source files (some already represented in the original port).
This is an A17.2PORT supplier chain, not standalone new-content qualification.

Exact D5 reuse: `FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot`
in the polytabloid-preimage proof, from module statement identity
`sha256:5ea5be4246f85df1a6a5a34be414eaa3174509f06a0bb1c923f3d8e8cfff6a55`.
The existing atom-to-irreducibility and surjective-restriction results were
examined; no standalone rational irreducibility specialization is retained,
since the complex proof below uses scalar endomorphisms and the character norm
criterion. `InducedCharacterFormula` and `MackeyCharacterFormula` were examined:
their induction character, Frobenius reciprocity and double-coset formulas do not
prove James's same-shape antisymmetrizer lemma. They remain candidates for the
later Young-rule/character comparison; no duplicates of them are added.
The two uses of the private `toSubmodule_le_toSubmodule` normalization in the
supplier proof are replaced inline by `change`, leaving the existing frozen D5
module and all pins untouched.

Every entry below is a source-level selection, with an actual current proof
consumer where present. Bind-only organization supplies no admission witness.
The scalar pairing/orthogonal invariant subrepresentation, row-column counting,
factorization, antisymmetrizer collapse and James dichotomy are the substantive
ported proof chain; their exact proof shapes and liveness require native terms.
Atomicity of the rational polytabloid span is a substantive source endpoint,
not the full original theorem. Its use in the final comparison must be checked
before first freeze. No new standalone ordinary-character/coefficient wrapper is added.

The original full ordinary assertion was already preregistered in #21960, with
clarification at https://github.com/the-omega-institute/trureturing/issues/21960#issuecomment-6537494498.
No new preregistration, priority claim, forecast or deadline is created here.
#22528 concerns only the earlier coefficient result. The literature screen is
still partial; an existing settlement of the exact assertion defeats open-problem
eligibility. This checkpoint claims neither that eligibility nor a settlement.

The continuation also selects the rational scalar-endomorphism proof and the flat
intertwining-kernel comparison, ending in `instSimpleSpechtModuleℂ` for the already
constructed module. The scalarity proof normalizes the restricted algebra action
locally, without a duplicate public/private normalization declaration. Simplicity
uses the Mathlib complex character norm criterion, not rational irreducibility alone.
No arbitrary assignment of labels or classification bijection is used.

Still missing: native elaboration and standard-axiom closure of the whole selected
chain; integral trace and its
same-partition labeling; a representative using the **full** permutation partition
and independence of that representative; arbitrary-degree finite-alphabet
power-sum/Schur expansion; height vanishing and division-free bialternant
coefficient comparison to the existing three-variable `frobChar`; and consumption
of that comparison in **both** full weighted sums. Nothing here imposes a degree
bound, removes fixed points, changes Ev multiplicity, restricts the odd rectangle,
or replaces the Z-to-Q-to-C casts. Existing coefficient work is not rederived.

Public four-slot reconstruction, full-family sensitivity and observational
dependence remain uncompiled. No Reg mirror or declared_validated status exists.
Audit issue: https://github.com/the-omega-institute/trureturing/issues/24542.

### Continuation declaration selections

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
| `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean:173` | `instSimpleSpechtModuleℂ` | content candidate (ported); A17.2PORT supplier only, native review pending | complex same-partition construction output; comparison consumer not yet delivered |

The local complex invertibility instance is selected from `Specht/Complex.lean:82-83` and consumed by the character norm/trace pairing. The two construction endpoints, rational atomicity and complex simplicity, are useful source outputs; their eventual ordinary-comparison consumers are not delivered or claimed. No firstfreeze is authorized by this checkpoint.

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

## Integral ordinary trace continuation (source only)

`SpechtOrdinaryTrace.lean` continues the same constructed Specht module; it does
not introduce another representation or an isomorphism with a surrogate. The
selected `Complex.character_spechtModuleℂ` fact concerns exactly
`FDRep.of (Representation.baseChange ℂ (spechtModule μ).ρ)`, the existing definition.
The final `spechtCharValue_ordinaryTrace` source statement certifies simplicity
of that actual module, existence of a permutation with the full specified
partition, and equality of its complex trace with the integer value at **every**
such permutation. Its first conjunct is the original semantic obligation that the
ordinary character belongs to an irreducible module; it is not a dummy proof-term
argument inserted into the trace computation. Its second conjunct includes all
fixed points, through `Equiv.Perm.partition`, and imposes no degree/alphabet bound.
This is necessary ordinary-character certification, not the HSW result, and has
no independent firstfreeze/admission claim. All proof-term liveness is unverified.

### Exact reuse and adaptations

The main checkout's Mathlib source was read at the actual pinned revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its
`Mathlib/RepresentationTheory/Character.lean:207` already supplies
`FDRep.isIntegral_character`. This directly discharges integrality over ℤ;
`IsIntegrallyClosed.isIntegral_iff` gives the integer in ℚ. Consequently this
continuation does **not** select the TauCeti finite-order endomorphism/root-of-unity
integrality closure. The selected integer-character definition uses the numerator
of the already constructed rational trace, and proves the cast back to that trace.
`LinearMap.trace_baseChange` is reused from pinned Mathlib. The exact casts are
ℤ → ℚ → ℂ, with `Rat.cast_intCast` in the final complex comparison.

The existing D5 `FiniteCharacterAlgebra.TauCeti.ClassFunction.mem_iff`,
`toConjClasses` and `toConjClasses_mk` are directly reused, through the current
Specht dependency chain. `InducedCharacterFormula` and `MackeyCharacterFormula`
were inspected: their induction and double-coset formulas do not establish this
same-shape trace or the finite-alphabet Frobenius expansion, so no extra copies or
unused imports of those formulas are introduced. They remain exact available
suppliers for any later selected Young-rule proof that actually needs them.

Selected immutable source locators (all at the TauCeti revision above):

- `TauCeti/Combinatorics/Enumerative/Partition/Basic.lean`, `parts_equivCast`.
- `TauCeti/RepresentationTheory/Symmetric/Partitions.lean`, from
  `exists_perm_partition_eq` through `partitionEquivConjClasses`, and the three
  inverse/parts lemmas ending at `parts_partitionEquivConjClasses_symm_mk`.
  Forward inverse companions and cardinality formulas are omitted.
- `TauCeti/RepresentationTheory/CharacterTable/Values.lean`,
  `FDRep.exists_char_eq_intCast`, `intCharacter`, `intCharacter_cast`,
  `intCharacter_conj`, `intClassFunction`, `intClassFunction_apply`.
  Integrality is adapted to the pinned Mathlib supplier. The unused equality-iff
  companion and the trivial private definition wrapper are inlined.
- `TauCeti/RepresentationTheory/BaseChange.lean`,
  `Representation.character_baseChange` only; the existing local base-change
  definition and application lemma are reused.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Character.lean`,
  `spechtChar`, `spechtChar_cast`, `spechtCharConjClasses`,
  `spechtCharConjClasses_mk`, `spechtCharValue`,
  `spechtCharValue_eq_spechtChar`. Trivial definition wrappers are inlined.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Complex.lean`,
  `character_spechtModuleℂ`, `character_spechtModuleℂ_intCast` only.
  No classification of all complex representations is required for this step.

### Per-declaration consumers and admission boundary

Every row below is a **source** dependency assessment. Except for the explicit
representative construction, these are bind-only constructions or organization of
exact suppliers; no row is an independent escape witness. Ported mathematical
content is attributed to its supplier and supplies no independent novelty. The
new local endpoint is bind-only composition and the necessary semantic
certification of this source continuation; it is not standalone admissible new
content and cannot be first-frozen on a promised Frobenius/HSW consumer.
Native dependency closure, liveness and admission remain open for every row.

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
| `TauCeti.spechtCharValue_ordinaryTrace` | current necessary ordinary-trace certification endpoint; Frobenius and full weighted-sum consumption still absent; no standalone admission |

The existing `instSimpleSpechtModuleℂ` is now directly consumed by the first
conclusion of the ordinary-trace certification. This proves no new simplicity
construction and does not imply that the trace equality depends on irreducibility:
trace integrality holds for arbitrary rational finite-group representations.
Both obligations belong to the original ordinary-character interpretation.

### Concrete remaining comparison

The public arbitrary-degree supplier
`FrobeniusCharacteristic.psumPart_eq_sum_spechtCharValue_smul_schurPoly` was read
at the immutable revision. It expands a power-sum product in any finite alphabet,
with `spechtCharValue` coefficients. Its proof uses the fixed-tabloid power-sum
expansion, Young's rule and the Kostka/monomial Schur expansion. Those necessary
suppliers have not been ported in this pass. The separate characteristic linear
equivalence with `degree ≤ alphabet` is insufficient and is not substituted.

After that actual supplier closure is selected and validated, one must connect
positive full cycle lists to its partition power sums, construct the literal
positive-parts partition of each decreasing padded triple and prove its row lengths,
vanish shapes of height greater than three, multiply by the division-free Schur
bialternant, identify the descending staircase (2,1,0) with
`(X₀-X₁)(X₀-X₂)(X₁-X₂)`, and isolate the exact `HSW.frobChar` coefficient.
No such bridge is assumed or claimed here. Both original weighted equalities remain
unfinished, with all n ≥ 1, every λ ⊢ n, exact reciprocal z, duplicate Ev outcomes,
positive cycles including 1s, all even three-row shapes, rectangle (n,n,0) even for
odd n, the sign, and the parity-dependent binomial value still required. Reuse the
strongest existing D5 coefficient owner and `solution_unique`; do not reprove them
or modify the separate live coefficient branch.

The source-linked escape audit remains unfinished at
https://github.com/the-omega-institute/trureturing/issues/24542; the additional
module and all its new public theorems require faithful source reconstruction,
readout, whole-family intervention/sensitivity and native binding evidence. The
DependentFamily and PointwiseEquality registration supports were inspected; no
uncompiled Reg mirror is represented as validated. Issue 21960 remains the sole
existing preregistration of the full original assertion. No literature settlement,
new forecast, open-problem eligibility or full ordinary theorem is asserted.


## Fixed-tabloid and actual-trace Frobenius precursor (source continuation)

This continuation is source only at the same unchanged pins. It adds
`SpechtMonomialCoordinates`, `SpechtFixedTabloidPowerSum`, and
`SpechtFrobeniusPairing`, with their matching Blueprint Scribes. The exact supplier
`FrobeniusCharacteristic.psumPart_eq_sum_spechtCharValue_smul_schurPoly` was
inspected at TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156. Its proof requires
the fixed-tabloid power-sum expansion, Young's rule and the Kostka/monomial Schur
expansion. Only the first of these and its actual-trace character-pairing
precursor are supplied in this finite batch. The degree-at-most-alphabet linear
equivalence is neither imported nor substituted for the unrestricted formula.

The implemented source chain is:

1. Sort arbitrary finite-alphabet exponent weights into their literal nonzero
   partition. `rowLen_ofPartition` supplies actual decreasing row lengths, with
   zeros beyond the last row. No Schur polynomial is defined by these weights.
2. Expand a full-permutation-partition power-sum product through invariant
   colourings. The cycle-orbit fibres include fixed points, so one-cycles remain
   present. An equivariant coset/colouring equivalence identifies the coefficients
   with fixed points of actual Young tabloids.
3. Use OUR existing D5 `FiniteCharacterAlgebra` character pairing to convert the
   sum of the product of the actual complex Specht trace and the tabloid count
   into factorial times the dimension of the actual Hom space from that Specht
   module to the complex Young permutation module. The orientation of the Hom
   matches the existing pairing supplier. The existing
   `spechtCharValue_ordinaryTrace` is consumed by `spechtTrace_inv`, comparing
   inverse permutations through their full partitions. No representation
   equivalence, simplicity hypothesis or Frobenius equality is assumed.
4. Combine these into
   `sum_spechtTrace_smul_psumPart_eq_multiplicities`: for every degree and finite
   alphabet, the sum of actual Specht traces times full-cycle power sums equals
   factorial times the monomial expansion with genuine Hom dimensions.
   These dimensions are **not** identified with Kostka numbers, and the result
   is **not** claimed to be the same-shape Schur polynomial.
5. `hsw_frobChar_eq_fixedTabloid_coefficients` transports the existing exact HSW
   list power-sum product through the fixed-tabloid expansion, retaining repeated
   occurrences and ones by equality of full multisets. It expresses the existing
   integer coefficient owner in tabloid coordinates, **not** as an ordinary
   character. The original coefficient owner is reused without edits or reproof.

The current D5 `FiniteCharacterAlgebra` supplies
`ClassFunction.characterPairing_ofFDRep_eq_finrank`, `characterPairing_apply`,
and `ofCharacter_apply`. `InducedCharacterFormula` and `MackeyCharacterFormula`
were examined; their formulas do not identify these multiplicities with Kostka
numbers, so no unused import or copied induction closure is added. OUR pinned
Mathlib supplies `MvPolynomial.psumPart`, `msymm`, finite-dimensional
representation traces, and permutation/coset infrastructure. The source search
found no matching same-shape Schur/Specht comparison there; that bounded search
is not a complete literature or worldwide minimality claim.

### Selected source and per-declaration consumers

All following locators are immutable paths in the same TauCeti revision, under
the existing Apache license reproduced above. No new license or NOTICE exception
is introduced. Fifty selected declaration bodies were compared directly to the
immutable source: 49 are byte-identical, and `invariantColouringEquiv` changes
only the qualification of the selected local SameCycle helper. Surrounding
sections supply the explicit/implicit parameters required at OUR pin; no
supplier theorem is accepted as an elaborated proof by this comparison.

Every row records an actual **source** consumer, not native proof-term liveness.
Port rows credit the supplier and claim no independent novelty or escape witness.
Local rows compose existing suppliers and are bind-only necessary comparison
helpers. The two terminal comparison endpoints have no subsequent ordinary-HSW
consumer yet. This entire source checkpoint has **no independent admission or
firstfreeze claim**, and those endpoints must not be first-frozen as standalone
content. The earlier complex simplicity proof is part of the ordinary-character
certification; this composition does not establish that its proof term is live
inside a final ordinary-character theorem. Native closure and admission remain
unknown for every declaration, including the earlier representation chain.

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
| `SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities` | Local composition; no independent escape witness | **Retired from the delivered source: this comparison has no full-consumer use** |
| `SpechtFrobeniusPairing.hsw_powerSumProd_eq_psumPart` | Local composition; no independent escape witness | `SpechtFrobeniusPairing.hsw_frobChar_eq_fixedTabloid_coefficients` |
| `SpechtFrobeniusPairing.hsw_frobChar_eq_fixedTabloid_coefficients` | Local composition; no independent escape witness | **Retired from the delivered source: this comparison has no full-consumer use** |

### Exact residual and retirement

For the general Young-rule route, the missing equality is the identification
`finrank Complex (spechtModuleComplex mu --> permutationModuleComplex nu) =
kostkaNumber mu nu`, with its dominance/diagonal and genuine Kostka suppliers.
It must be connected to the semistandard-tableau Schur expansion and the
arbitrary-degree `psumPart_eq_sum_spechtCharValue_smul_schurPoly`; these are not
assumptions or claims here. The alternative three-row construction below avoids
those unused general closure results. It addresses the literal positive-parts
shape, zero padding and descending-staircase coefficient isolation directly.
Its source character bridge is consumed by both ordinary Ev sums; their common
weighted value still needs the existing strongest D5 coefficient owner and
`solution_unique`. No coefficient-only result closes either original ordinary
weighted theorem.

The original target remains all n >= 1 and every partition of n; the exact
reciprocal centralizer product, independent per-occurrence Ev replacements with
duplicate outcomes, positive full cycle lists of sum 2n including ones, every
even-part shape of at most three rows with zero padding, rectangle (n,n,0) for
odd n as well, sign by list length, and even-binomial/odd-zero values are all
still required. No clause is removed or restricted by these precursor lemmas.

Retirement is evaluated against OUR Mathlib pin
56a005855ea17e0b0958f73ec801ae140b0a1679, not TauCeti's different pin. Replace
selected port declarations only when an exact compatible published supplier
covers their actual use. There is no dependency upgrade and no entire-file
TauCeti import. No new complete prior-art claim or open-problem eligibility is
established. Issue 21960 remains the full preregistration unchanged; 22528 remains
coefficient-only.

The linked unfinished escape audit is issue 24542. Existing PointwiseEquality
and DependentFamily registration supports were read. The all-degree dependent
partition/group/module domains, the full reconstruction/readout bridge and
whole-family intervention, sensitivity and actual observational-dependence
proofs have not been constructed and compiled. No Reg mirror or
`declared_validated` status is claimed. No local Lean/Lake, native elaboration,
accepted axiom closure, proof-term liveness, canonical emission, freeze, deposit,
PR, CI or merge result is asserted. Native validation remains with the caller's
existing Mac task; this pass neither accesses nor starts another Mac job/tree.

## Young dominance, diagonal multiplicity and actual-trace orthogonality continuation

This continuation selects the necessary dominance/diagonal part of Young rule,
not the full Young/Kostka identity. The rational Specht space remains the same
polytabloid subrepresentation. Nonzero maps into a Young permutation module force
dominance; the diagonal intertwiner space is identified with the rationals by
scalar multiples of the actual inclusion. These facts are transported to the
existing complex Hom dimensions by the actual trace pairing and exact rational
to complex casts. Those dimensions distinguish the literal complex Specht shape
labels. The existing complex simplicity instance is then used by OUR pinned
Mathlib FDRep.char_orthonormal in a genuine ordinary-trace orthogonality proof.
No separate representation model or assumed equivalence is introduced.

The existing sum_spechtTrace_mul_card_fixedPoints declaration is exposed from
private so the new source comparison can directly reuse its unchanged proof.
The previously removed isIrreducible_spechtSubrepresentation application is
selected only now that dominates_of_intertwiningMap_ne_zero actually uses it.
The unused partition-indexed rational irreducibility wrapper remains omitted.

Our pinned character orthogonality theorem has the normalized factor
(Nat.card G : Complex) inverse. The source comparison explicitly multiplies it
back by n factorial; it does not use an unnormalized supplier signature guessed
from another pin. The shape-character proof explicitly unfolds the existing
composition instead of relying on the convenience name
character_spechtModule_apply. The stabilizer of a Young coset is obtained from
the existing pinned stabilizer map-conjugation fact and the already selected
fiberSubgroup_map_conj. These surrounding adaptations require native checking.

All new modules use utility none: arbitrary partitions, finite representations
and full spaces of intertwiners, with no certified finite instance or enumeration.
Every helper has the source consumer below. Source references do not establish
elaborated proof-term liveness. Every retained declaration remains an uncompiled
necessary supplier or comparison with admission NOT ESTABLISHED; the selected
ports provide no independent novelty or escape witness. The terminal orthogonality
statement has no full Young/Frobenius/HSW consumer yet and is WIP, not standalone
admissible firstfreeze content. No native Lean/Lake, accepted axiom closure,
validated Reg, canonical emission, freeze, deposit, PR, CI or merge is asserted.

### Selected declarations and actual source consumers

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
| `SpechtYoungTrace.lean:sum_spechtTrace_mul_spechtTrace_inv` | Local composition of the existing representation and pinned interfaces; no independent admission | `SpechtThreeRowVirtual.lean`: actual self-norm criterion; general Young-rule consumer remains absent |

### Exact remaining target and retirement

The actual Hom dimensions still need identification with Kostka numbers. The
selected public YoungRule proof requires the permutation-character Gram identity
from the complete-homogeneous/Schur/Kostka expansion, plus completeness of the
Specht characters. Row orthogonality alone supplies neither completeness nor
Young rule. The selected endpoints do not assume either fact. The arbitrary-degree
finite-alphabet psumPart_eq_sum_spechtCharValue_smul_schurPoly remains unported
and unproved here; the degree-at-most-alphabet equivalence is not substituted.

The alternative finite Cauchy route below supplies source constructions for the
literal triple shape, zero padding and actual ordinary-trace equality without
the general Schur-height or bialternant route. Both evaluated original weighted
sums must still consume the existing coefficient owner and solution_unique.
All n at least one, every partition, fixed-point cycles, per-occurrence Ev
duplicates, exact reciprocal z and sign, every even-part three-row shape,
rectangle (n,n,0) also for odd n, and the even-binomial/odd-zero values are
unchanged. No coefficient-only conclusion is presented as the original theorem.

The complete Apache license and attributions above apply to this selection.
Retirement is evaluated against OUR unchanged Mathlib pin
56a005855ea17e0b0958f73ec801ae140b0a1679, not the supplier's different pin.
No dependency/pin upgrade or whole-file library import is introduced. No complete
prior-art or open-problem eligibility claim is made. Issue 21960 remains the
original preregistration, unchanged; 22528 remains coefficient-only.

The unfinished audit remains issue 24542. Actual PointwiseEqualityRegistrations
and DependentFamily support sources were inspected. Full dependent-domain source
reconstruction and lawful readout, whole-family intervention/sensitivity, actual
observational dependence, native elaboration and binding evidence remain absent.
No Reg mirror or declared_validated claim is supplied.


## Ordered three-colouring Gram and virtual-character criterion

The three-row route uses ordered colourings with integer margins. Negative
margins have no colourings; equal and empty rows stay labelled, with no extra
row factorial. A pair of colourings is grouped by its nine joint fibre sizes
under one common permutation action. This gives the unnormalised character
pairing n! times the number of nonnegative 3 by 3 tables with those margins.
The signed six-by-six table sum is consequently the Gram matrix of the signed
permutation character in arbitrary degree. The argument does not impose n <= 3.

Three necessary private suppliers are selected from
`TauCeti/GroupTheory/Perm/FiberSubgroup.lean` at immutable revision
`5a01f5fe3621126cccf9ba22e700493cbc7b7156`:
`natCard_fiberSubgroup`, `exists_forall_card_filter_eq`, and
`sum_natCard_fiberSubgroup_smul`. Their proof bodies are unchanged; only private
visibility and surrounding local context differ. The complete Apache 2.0 text,
contributor attribution and no-NOTICE assessment above apply. These are selected
proofs, not a whole-file/library import. Retirement remains against OUR unchanged
Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`; an exact compatible
published supplier should replace them when available.

The actual source consumer chain is:

| Source endpoint | Consumer |
| --- | --- |
| private fibre-count suppliers | `ThreeRowGram.sum_fixedColourings_mul` |
| `ThreeRowGram.character_colouringRepresentation` | `ThreeRowGram.sum_colouringTrace_mul`, also its cast in the signed Gram proof |
| `ThreeRowGram.sum_fixedColourings_mul` | `ThreeRowGram.sum_colouringTrace_mul` |
| `ThreeRowGram.sum_colouringTrace_mul` | `ThreeRowGram.sum_virtualCharacter_mul` |
| `ThreeRowGram.sum_virtualCharacter_mul` | private `ThreeRowGram.spechtChar_eq_virtualCharacter_of_gram` |
| `ThreeRowGram.virtualCharacter_eq_frobChar` | `ThreeRowGram.ordinaryTrace_eq_frobChar_of_gram` |
| exposed `TauCeti.spechtTrace_inv` | private `ThreeRowGram.spechtChar_inv`, then the actual integral self-norm |
| exposed `TauCeti.hsw_powerSumProd_eq_psumPart` | `ThreeRowGram.virtualCharacter_eq_frobChar` |
| `ThreeRowGram.ordinaryTrace_eq_frobChar_of_gram` | `ThreeRowMixed.ordinaryTrace_eq_frobChar_of_selfGram`, then `ThreeRowCauchy.ordinaryTrace_eq_frobChar` |

The two exposed declarations only lose `private`; their bodies are unchanged.
The virtual character is identified with the existing HSW alternant coefficient
using the full cycle partition, including all fixed points. The norm criterion
uses the unchanged actual complex polytabloid module, its integral trace,
actual self-orthogonality and positivity of integer squares. It retains two
explicit hypotheses: signed contingency self-Gram equal to one, and actual
Specht/virtual mixed sum equal to n!. Neither hypothesis is asserted as proved,
and neither defines the Specht module by the desired coefficient.

The owning Scribes give the mathematical Cauchy, strict-dominance and final
weighted-substitution arguments. The source constructions below address the finite Cauchy
coefficient identity, the literal Young-subgroup comparison, strict shifted
dominance, mixed pairing and same-shape discharge. Native checking of those
constructions and the evaluated weighted consumer through the existing
coefficient owner and `solution_unique` remain required. This alternative
does not require full Young rule, Kostka completeness or general Schur expansion.
It has not established that its total formalization cost is smaller.

The full original quantifiers are preserved: every n >= 1 and partition of n,
independent per-occurrence Ev with duplicate outcomes, exact reciprocal z,
length sign, all positive cycles including ones, every padded nonincreasing
even-part shape of at most three rows and total 2n, rectangle (n,n,0) also for
odd n, and the even-binomial/odd-zero value in each average. The criterion alone
does not prove either evaluated ordinary weighted theorem.

Classical provenance is verified against Etingof et al., *Introduction to
Representation Theory*, author arXiv version
<https://arxiv.org/pdf/0901.0827>, sections 4.14--4.15: Proposition 4.44,
Theorem 4.46, Theorem 4.47, Lemma 4.48 and Corollary 4.49. The proposed
5.14/5.15 numbering was not verified in this version and is not cited as such.
Krattenthaler, *Advanced Determinant Calculus*, equation (2.7), is verified in
the primary source <https://www.mat.univie.ac.at/~slc/wpapers/s42kratt.tex>
(and its PDF), linked from
<https://www.mat.univie.ac.at/~kratt/artikel/detsurv.html>.
No originality or complete prior-art eligibility claim is made.

All new declarations have utility none: finite colour alphabet and nine table
entries do not bound degree or dependent domains. The unfinished section 3.9
exception is linked to issue 24542; issue 21960 is unchanged and 22528 remains
coefficient-only. Required audit evidence remains the full original dependent
telescope, scoped observations, lawful enrolled-template readout, exact source
reconstruction/equivalence, actual-positive law, whole-family interventions and
sensitivity, observational dependence and native binding. No Reg mirror or
`declared_validated` claim is supplied. Source consumer references do not prove
compiled proof-term liveness or independent escape. This is uncompiled WIP,
not standalone admissible firstfreeze content. No native Lean/Lake, accepted
axiom closure, emission, freeze, deposit, ordinary PR, CI or merge is asserted.


## Finite Cauchy isolation and literal three-row mixed pairing

`SpechtThreeRowMixed` compares the natural ordered-colouring character with the
actual Young-subgroup fixed-coset character by applying the two existing
power-sum coefficient calculations to the same monomial. Its literal partition
is `tripleShape`, the existing `weightPartition` of the natural triple. Positive
entries retain their multiplicities, zeros disappear, and weakly decreasing
triples have those exact padded row lengths. There is no equal-row or empty-row
factorial. Sorting increases each proper prefix; every nonidentity integer shift
has a strict proper-prefix increase. Actual Hom dominance kills these terms,
while the same-partition diagonal Hom dimension supplies one at the identity.
Negative margins have no colourings. This gives the actual mixed scalar n!.

`SpechtThreeRowCauchy` uses formal power series in six variables, with an edge
series for each of the nine labelled pairs. A finite exponent-decomposition/table
bijection identifies its kernel coefficients with the existing contingency
counts. The cleared three-by-three numerator is a commutative-ring polynomial
identity, and its nine specified inverse factors give the Cauchy determinant.
Strict decreasing exponent triples have only the identity matching in the
three-edge determinant product. Transporting the existing signed Vandermonde
expansion therefore gives the signed contingency delta in arbitrary degree.
Together with the mixed scalar and the existing integer sum-of-squares criterion,
this supplies an unconditional source formula for the actual independently
defined polytabloid trace of the same literal partition.

The exact unchanged pinned source APIs used for the new construction are
`Matrix.det_fin_three`, `Matrix.det_apply`, `Matrix.det_mul_column`,
`MvPowerSeries.coeff_prod`, `MvPowerSeries.coeff_monomial_mul`,
`MvPowerSeries.monomial_mul_monomial`, `MvPolynomial.coeToMvPowerSeries.ringHom`,
`Finset.mem_finsuppAntidiag`, `Finset.mem_piAntidiag`, and the existing D5
`coeff_psumPart_partition`, `coeff_psumPart_eq_card_fixedPoints`,
`exists_perm_mapDomain_eq_partWeight`, `partWeight_apply`,
`finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero` and its `_self` companion.
Only `private` is removed from the existing `staircase`, `permutedStaircase`,
and `vandermonde_eq_signed_monomials`; their definitions and proof bodies are
unchanged and are used by the two-variable-set Vandermonde transport.

| New source declaration | Actual source consumer |
| --- | --- |
| `Mixed.tripleShape` | literal row comparison, mixed pairing, actual trace formula, both ordinary Ev sums |
| `Mixed.shifted_nat_sum` | strict-dominance partition and Cauchy shifted-exponent comparison |
| `Mixed.sum_spechtChar_mul_virtualCharacter` | `Mixed.ordinaryTrace_eq_frobChar_of_selfGram` |
| `Mixed.ordinaryTrace_eq_frobChar_of_selfGram` | `Cauchy.ordinaryTrace_eq_frobChar` |
| `Cauchy.doubleWeight`, `cauchyKernel`, `doubleVandermonde` | finite table coefficient, determinant isolation and signed Gram comparison |
| `Cauchy.cauchy_coefficient_delta` | `Cauchy.signedContingencyGram_eq_delta` |
| `Cauchy.signedContingencyGram_eq_delta` | `Cauchy.ordinaryTrace_eq_frobChar` |
| `Cauchy.ordinaryTrace_eq_frobChar` | `Cauchy.spechtCharValue_eq_frobChar` |
| `Cauchy.spechtCharValue_eq_frobChar` | `Cauchy.evSpechtSums_eq_coefficients` |
| `Cauchy.evPartition`, `signedEvSpechtSum`, `rectangleEvSpechtSum` | `Cauchy.evSpechtSums_eq_coefficients`, `ordinaryEv_identity`, `ordinaryWeightedEv_identity` |
| `Cauchy.evSpechtSums_eq_coefficients` | `Cauchy.ordinaryEv_identity`, using existing `HemmerStraubWestrem.result` |
| `Cauchy.ordinaryEv_identity` | `Cauchy.ordinaryWeightedEv_identity` |
| `Cauchy.ordinaryWeightedEv_identity` | `Cauchy.ordinaryWeightedSignedEv_evaluated` |
| `Cauchy.ordinaryWeightedRectangleEv_evaluated` | `Cauchy.ordinaryWeightedSignedEv_evaluated`; rectangular final evaluated consumer |
| `Cauchy.ordinaryWeightedSignedEv_evaluated` | signed final evaluated consumer |

In this table `Mixed` and `Cauchy` abbreviate module names; declarations share
namespace `SpechtPolytabloid.TauCeti.ThreeRowGram`. The weighted identity uses
the existing `DeformedJucysMurphyC2.zPartition` literally. Both evaluated
consumers quantify over every `n : ℕ` with the sole premise `1 ≤ n`, and conclude
the literal rational weighted sum equals
`if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0`.

The rectangular final consumer retains the owning weighted derivation from
[the merged HSW Scribe](https://github.com/the-omega-institute/trureturing/blob/165fcda2eb263add60bba2842909811e26a35683/Blueprint/D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.scribe.cs).
Its partition sum and Laurent coefficient maps are local proof bindings, not a
new global coefficient system. The partition-deletion equivalence is Mathlib's
`Nat.Partition.partitionWithPartEquiv`; insertion at positive part `k` consumes
`zExponent_add_single` at index `k-1`. The exact ODE application uses existing
private `LatticeHalfFockChargedCoefficients.solution_unique`, with
`Ring = LaurentPolynomial ℚ`, first series the local literal partition sum,
second series the product of the three rescaled `invOneSubPow` factors of order
two, and the common driver at index `k` equal to
`2 * (T (k+1) + 1 + T (-(k+1)))`. `HasUniqueDiv.of_module_rat` provides the
stronger unique-divisibility instance and hence additive torsion freeness.
`Batteries.Tactic.OpenPrivate` accesses that existing proof and the owning HSW
`ev_right`, `right_coefficient` and `triProd`; none of their bodies changes.
The earlier immutable coefficient source at
[69f68474](https://github.com/the-omega-institute/trureturing/blob/69f68474a0566d6f465a14259b74f28b58e293f3/D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.lean)
is the source for the local finite-sum and Laurent normalization calculations.
Its alternate ODE proof and global weighted/coefficient declarations are not
retained. The retired module is absent.

The adjacent Laurent coefficients reduce the constant-term generating series
to `(1-t²)⁻³`; `PowerSeries.coeff_expand` gives the even binomial and odd zero.
The same-literal-shape actual trace enters through
`evSpechtSums_eq_coefficients`; no coefficient defines an ordinary character.
The signed final consumer applies `ordinaryWeightedEv_identity` and the
rectangular evaluation. All original partitions, occurrence-wise choices,
duplicate Ev lists, positive cycles including ones, zero-padded/equal even rows
and odd rectangles remain included. The module's generality tag is `I` because
its reused coefficient-uniqueness supplier lies in an `I` module; the endpoint
quantifiers remain all `n ≥ 1`.

The mirrored Reg source uses the existing dependent-family template for both
new evaluated endpoints. Parameters range over every natural degree, states are
all partitions of that degree, and its two readouts are the literal reciprocal
zPartition and the actual ordinary character sum. The law is the entire original
weighted equality for every n at least one. Zeroing either readout only in degree
two provides a whole-family intervention that violates the law while fixing the
other readout. In degree three, the partitions [3] and [2,1] have distinct weights
1/3 and 1/2 and actual rectangle sums 2 and -4. The signed sums agree with these by
the proved per-partition ordinary identity. Lean checks the actual positive law,
source equivalence, variation, sensitivity and observational dependence. The
family proof axiom closures are propext, Classical.choice and Quot.sound. Report
binding and the remaining public-helper audit are tracked in
[#24542](https://github.com/the-omega-institute/trureturing/issues/24542); successful
kernel compilation by itself does not assert declared_validated. Preregistration
#21960 and the coefficient-only audit #22528 keep their respective scopes.

The native full selected target and scoped report succeed at Lean 4.35.0 and
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Both evaluated endpoint proof
values have exactly the standard axioms propext, Classical.choice and Quot.sound.
The endpoint telescopes have only n : Nat and the premise 1 <= n. The direct
representation-theory construction and finite Cauchy calculation are consumed
inside this complete ordinary weighted application. The canonical publication
and admission records belong to the full consumer delivery. The Apache
attribution, complete license, no-NOTICE assessment and retirement obligations
above remain applicable.

The current compiled dependency readout identified no consumer for the former
`sum_spechtTrace_smul_psumPart_eq_multiplicities` and
`hsw_frobChar_eq_fixedTabloid_coefficients` composition theorems. Both are removed,
together with their theorem descriptions. The retained
`sum_spechtTrace_mul_card_fixedPoints` is consumed in `SpechtYoungTrace` and
`SpechtThreeRowMixed`; `hsw_powerSumProd_eq_psumPart` is consumed in
`SpechtThreeRowVirtual`. These are proof-organization helpers, with no independent
new-content claim. The generated `weightPartition.congr_simp` is a compiler
congruence artifact, not an authored retained theorem.

The current source-bound Reg report records both evaluated endpoint registrations
as `declared_unresolved`, with `IE-C050 ClosedTruthReadout`,
`reason=unclassified_form`, and `rule=source.residual_requires_open`. The typed
family proofs compile; this report does not certify `declared_validated`. The
section 3.9 linked-issue exception #24542 applies without changing the inspector.
