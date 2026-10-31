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
source port. No dependency or pin change is made. This source has not been
elaborated at our pins. All selected proof bodies are copied with only
namespace qualification and surrounding context adapted; comments are selected.
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
Native proof-term liveness and independent per-declaration admission remain pending.
No public ordinary-character comparison or open-problem-resolution basis is claimed.

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
| `fiberSubgroup` | construction | `mem_fiberSubgroup`; `fiberSubgroup_map_conj`; `fiberSubgroup_inf`; `fiberSubgroup_eq_bot_of_injective`; `youngSubgroup_eq_fiberSubgroup`; `rowSubgroup`; `colSubgroup`; `rowSubgroup_def`; `colSubgroup_def` |
| `mem_fiberSubgroup` | bind-only | `fiberSubgroup_map_conj`; `youngSubgroup_eq_fiberSubgroup`; `mem_rowSubgroup`; `mem_colSubgroup`; `rowSubgroup_def`; `colSubgroup_def` |
| `fiberSubgroup_map_conj` | bind-only | `youngSubgroup_map_conj_eq_rowSubgroup`; `colSubgroup_relabel` |
| `fiberSubgroup_inf` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot` |
| `fiberSubgroup_eq_bot_of_injective` | bind-only | `rowSubgroup_inf_colSubgroup_eq_bot` |
| `youngBlocksEquiv` | construction | `youngBlock`; `youngBlock_youngBlocksEquiv`; `rowYoungConjugator`; `rowIndex_rowYoungConjugator` |
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
| `rowCellsEquiv` | construction | `rowYoungConjugator`; `rowIndex_rowYoungConjugator` |
| `sortedBlocksEquivRows` | bind-only | `sortedBlocksEquivRows_fst`; `rowYoungConjugator` |
| `cast_rowBlocks_fst` | bind-only | `sortedBlocksEquivRows_fst` |
| `sortedBlocksEquivRows_fst` | bind-only | `rowIndex_rowYoungConjugator` |
| `rowYoungConjugator` | construction | `rowIndex_rowYoungConjugator`; `rowYoungConjugator_relabel`; `youngSubgroup_map_conj_eq_rowSubgroup`; `tabloid`; `tabloid_def` |
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
| `columnAntisymmetrizer` | construction | `columnAntisymmetrizer_def`; `columnAntisymmetrizer_eq_subgroupCharSum`; `columnAntisymmetrizer_coeff`; `columnAntisymmetrizer_relabel`; `polytabloid` |
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
| `polytabloid` | construction | `polytabloid_eq_sum`; `polytabloid_relabel`; `polytabloid_coeff_smul_tabloid`; `polytabloid_coeff_tabloid`; `polytabloid_ne_zero`; `spechtSubrepresentation`; `polytabloid_mem_spechtSubrepresentation`; `spechtSubrepresentation_ne_bot` |
| `polytabloid_eq_sum` | bind-only | `polytabloid_coeff_smul_tabloid` |
| `polytabloid_relabel` | bind-only | `spechtSubrepresentation` |
| `polytabloid_coeff_smul_tabloid` | content | `polytabloid_coeff_tabloid` |
| `polytabloid_coeff_tabloid` | content | `polytabloid_ne_zero` |
| `polytabloid_ne_zero` | content | `spechtSubrepresentation_ne_bot` |
| `spechtSubrepresentation` | construction | `polytabloid_mem_spechtSubrepresentation`; `spechtSubrepresentation_ne_bot`; `spechtModule` |
| `polytabloid_mem_spechtSubrepresentation` | bind-only | `spechtSubrepresentation_ne_bot` |
| `spechtSubrepresentation_ne_bot` | content | Substantive construction/nonvanishing endpoint; no independent theorem closure claimed |
| `spechtModule` | construction | `spechtModuleℂ` |
| `baseChange` | construction | `spechtModuleℂ` |
| `spechtModuleℂ` | construction | Substantive construction/nonvanishing endpoint; no independent theorem closure claimed |
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

Still required are the source proofs of the rational/integer trace character,
complex simplicity and trace cast, literal full-cycle class indexing (including
fixed points), Young's rule, arbitrary-degree finite-alphabet Schur expansion,
bialternant and height vanishing, the coefficient comparison at the padded
three-row label, and substitution into the existing full weighted HSW argument.
No degree bound, changed character model, dropped Ev multiplicity or restricted
shape family is an acceptable replacement. Preregistration #21960 explicitly
binds the weighted coefficient conventions; issue #22528 names that weighted
result's audit. They do not supply current registration/echo for a new ordinary
trace comparison. Caller owns that precise missing preregistration and Reg work.

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
