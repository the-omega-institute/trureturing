/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover036
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03555 : selected 8 ⟨111159, by decide⟩
    (prefixPartial 13 27981) = some ⟨13, 2, 0, 111159, 27981, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_27981_111159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27981 ⟨111159, by decide⟩ :=
  accepted_of_selected 13 27981 ⟨111159, by decide⟩ ⟨13, 2, 0, 111159, 27981, 2205, 16384⟩
    (by decide) selected_cut_03555

theorem selected_cut_03556 : selected 8 ⟨111185, by decide⟩
    (prefixPartial 13 27982) = some ⟨13, 2, 0, 111185, 27982, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_27982_111185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27982 ⟨111185, by decide⟩ :=
  accepted_of_selected 13 27982 ⟨111185, by decide⟩ ⟨13, 2, 0, 111185, 27982, 2217, 16384⟩
    (by decide) selected_cut_03556

theorem selected_cut_03557 : selected 8 ⟨111193, by decide⟩
    (prefixPartial 13 27983) = some ⟨13, 2, 0, 111193, 27983, 865, 16384⟩ := by
  decide +kernel

theorem context_13_27983_111193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27983 ⟨111193, by decide⟩ :=
  accepted_of_selected 13 27983 ⟨111193, by decide⟩ ⟨13, 2, 0, 111193, 27983, 865, 16384⟩
    (by decide) selected_cut_03557

theorem unmarked_context_12_6995_111194 : frontier 9 ⟨111194, by decide⟩
    (prefixCache 12 6995) (prefixPartial 12 6995) = false := by
  decide +kernel

theorem node_context_12_6995_111194 : EJMOriginalGlobalDAGData.nodes 9 ⟨111194, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111159, by decide⟩,⟨111185, by decide⟩,⟨111193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6995_111194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6995 ⟨111194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6995
    ⟨111194, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111159, by decide⟩,⟨111185, by decide⟩,⟨111193, by decide⟩]) unmarked_context_12_6995_111194 node_context_12_6995_111194
  intro a
  fin_cases a
  · exact context_13_27980_3444
  · exact context_13_27981_111159
  · exact context_13_27982_111185
  · exact context_13_27983_111193

theorem unmarked_context_11_1748_111195 : frontier 10 ⟨111195, by decide⟩
    (prefixCache 11 1748) (prefixPartial 11 1748) = false := by
  decide +kernel

theorem node_context_11_1748_111195 : EJMOriginalGlobalDAGData.nodes 10 ⟨111195, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨110998, by decide⟩,⟨111109, by decide⟩,⟨111194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1748_111195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1748 ⟨111195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1748
    ⟨111195, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨110998, by decide⟩,⟨111109, by decide⟩,⟨111194, by decide⟩]) unmarked_context_11_1748_111195 node_context_11_1748_111195
  intro a
  fin_cases a
  · exact context_12_6992_106538
  · exact context_12_6993_110998
  · exact context_12_6994_111109
  · exact context_12_6995_111194

theorem selected_cut_03558 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6996) = some ⟨12, 1, 0, 106538, 6996, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6996_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6996 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6996 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6996, 1, 65536⟩
    (by decide) selected_cut_03558

theorem selected_cut_03559 : selected 9 ⟨111258, by decide⟩
    (prefixPartial 12 6997) = some ⟨12, 2, 0, 111258, 6997, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_6997_111258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6997 ⟨111258, by decide⟩ :=
  accepted_of_selected 12 6997 ⟨111258, by decide⟩ ⟨12, 2, 0, 111258, 6997, 3641, 65536⟩
    (by decide) selected_cut_03559

theorem selected_cut_03560 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27992) = some ⟨13, 1, 0, 3444, 27992, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27992_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27992 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27992 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27992, 1, 16384⟩
    (by decide) selected_cut_03560

theorem selected_cut_03561 : selected 8 ⟨111310, by decide⟩
    (prefixPartial 13 27993) = some ⟨13, 2, 0, 111310, 27993, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_27993_111310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27993 ⟨111310, by decide⟩ :=
  accepted_of_selected 13 27993 ⟨111310, by decide⟩ ⟨13, 2, 0, 111310, 27993, 2473, 16384⟩
    (by decide) selected_cut_03561

theorem selected_cut_03562 : selected 8 ⟨111362, by decide⟩
    (prefixPartial 13 27994) = some ⟨13, 2, 0, 111362, 27994, 2985, 16384⟩ := by
  decide +kernel

theorem context_13_27994_111362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27994 ⟨111362, by decide⟩ :=
  accepted_of_selected 13 27994 ⟨111362, by decide⟩ ⟨13, 2, 0, 111362, 27994, 2985, 16384⟩
    (by decide) selected_cut_03562

theorem selected_cut_03563 : selected 8 ⟨111381, by decide⟩
    (prefixPartial 13 27995) = some ⟨13, 2, 0, 111381, 27995, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_27995_111381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27995 ⟨111381, by decide⟩ :=
  accepted_of_selected 13 27995 ⟨111381, by decide⟩ ⟨13, 2, 0, 111381, 27995, 1181, 16384⟩
    (by decide) selected_cut_03563

theorem unmarked_context_12_6998_111382 : frontier 9 ⟨111382, by decide⟩
    (prefixCache 12 6998) (prefixPartial 12 6998) = false := by
  decide +kernel

theorem node_context_12_6998_111382 : EJMOriginalGlobalDAGData.nodes 9 ⟨111382, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111310, by decide⟩,⟨111362, by decide⟩,⟨111381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6998_111382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6998 ⟨111382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6998
    ⟨111382, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111310, by decide⟩,⟨111362, by decide⟩,⟨111381, by decide⟩]) unmarked_context_12_6998_111382 node_context_12_6998_111382
  intro a
  fin_cases a
  · exact context_13_27992_3444
  · exact context_13_27993_111310
  · exact context_13_27994_111362
  · exact context_13_27995_111381

theorem selected_cut_03564 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27996) = some ⟨13, 1, 0, 3444, 27996, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27996_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27996 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27996 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27996, 1, 16384⟩
    (by decide) selected_cut_03564

theorem selected_cut_03565 : selected 8 ⟨111425, by decide⟩
    (prefixPartial 13 27997) = some ⟨13, 2, 0, 111425, 27997, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_27997_111425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27997 ⟨111425, by decide⟩ :=
  accepted_of_selected 13 27997 ⟨111425, by decide⟩ ⟨13, 2, 0, 111425, 27997, 1821, 16384⟩
    (by decide) selected_cut_03565

theorem selected_cut_03566 : selected 8 ⟨111468, by decide⟩
    (prefixPartial 13 27998) = some ⟨13, 2, 0, 111468, 27998, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_27998_111468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27998 ⟨111468, by decide⟩ :=
  accepted_of_selected 13 27998 ⟨111468, by decide⟩ ⟨13, 2, 0, 111468, 27998, 2825, 16384⟩
    (by decide) selected_cut_03566

theorem selected_cut_03567 : selected 8 ⟨111478, by decide⟩
    (prefixPartial 13 27999) = some ⟨13, 2, 0, 111478, 27999, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_27999_111478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27999 ⟨111478, by decide⟩ :=
  accepted_of_selected 13 27999 ⟨111478, by decide⟩ ⟨13, 2, 0, 111478, 27999, 1057, 16384⟩
    (by decide) selected_cut_03567

theorem unmarked_context_12_6999_111479 : frontier 9 ⟨111479, by decide⟩
    (prefixCache 12 6999) (prefixPartial 12 6999) = false := by
  decide +kernel

theorem node_context_12_6999_111479 : EJMOriginalGlobalDAGData.nodes 9 ⟨111479, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111425, by decide⟩,⟨111468, by decide⟩,⟨111478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6999_111479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6999 ⟨111479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6999
    ⟨111479, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111425, by decide⟩,⟨111468, by decide⟩,⟨111478, by decide⟩]) unmarked_context_12_6999_111479 node_context_12_6999_111479
  intro a
  fin_cases a
  · exact context_13_27996_3444
  · exact context_13_27997_111425
  · exact context_13_27998_111468
  · exact context_13_27999_111478

theorem unmarked_context_11_1749_111480 : frontier 10 ⟨111480, by decide⟩
    (prefixCache 11 1749) (prefixPartial 11 1749) = false := by
  decide +kernel

theorem node_context_11_1749_111480 : EJMOriginalGlobalDAGData.nodes 10 ⟨111480, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨111258, by decide⟩,⟨111382, by decide⟩,⟨111479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1749_111480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1749 ⟨111480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1749
    ⟨111480, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨111258, by decide⟩,⟨111382, by decide⟩,⟨111479, by decide⟩]) unmarked_context_11_1749_111480 node_context_11_1749_111480
  intro a
  fin_cases a
  · exact context_12_6996_106538
  · exact context_12_6997_111258
  · exact context_12_6998_111382
  · exact context_12_6999_111479

theorem selected_cut_03568 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7000) = some ⟨12, 1, 0, 106538, 7000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7000_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7000 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7000 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7000, 1, 65536⟩
    (by decide) selected_cut_03568

theorem selected_cut_03569 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28004) = some ⟨13, 1, 0, 3444, 28004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28004, 1, 16384⟩
    (by decide) selected_cut_03569

theorem selected_cut_03570 : selected 8 ⟨111505, by decide⟩
    (prefixPartial 13 28005) = some ⟨13, 2, 0, 111505, 28005, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_28005_111505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28005 ⟨111505, by decide⟩ :=
  accepted_of_selected 13 28005 ⟨111505, by decide⟩ ⟨13, 2, 0, 111505, 28005, 1549, 16384⟩
    (by decide) selected_cut_03570

theorem selected_cut_03571 : selected 8 ⟨111541, by decide⟩
    (prefixPartial 13 28006) = some ⟨13, 2, 0, 111541, 28006, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_28006_111541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28006 ⟨111541, by decide⟩ :=
  accepted_of_selected 13 28006 ⟨111541, by decide⟩ ⟨13, 2, 0, 111541, 28006, 2561, 16384⟩
    (by decide) selected_cut_03571

theorem selected_cut_03572 : selected 8 ⟨111559, by decide⟩
    (prefixPartial 13 28007) = some ⟨13, 2, 0, 111559, 28007, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_28007_111559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28007 ⟨111559, by decide⟩ :=
  accepted_of_selected 13 28007 ⟨111559, by decide⟩ ⟨13, 2, 0, 111559, 28007, 1265, 16384⟩
    (by decide) selected_cut_03572

theorem unmarked_context_12_7001_111560 : frontier 9 ⟨111560, by decide⟩
    (prefixCache 12 7001) (prefixPartial 12 7001) = false := by
  decide +kernel

theorem node_context_12_7001_111560 : EJMOriginalGlobalDAGData.nodes 9 ⟨111560, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111505, by decide⟩,⟨111541, by decide⟩,⟨111559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7001_111560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7001 ⟨111560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7001
    ⟨111560, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111505, by decide⟩,⟨111541, by decide⟩,⟨111559, by decide⟩]) unmarked_context_12_7001_111560 node_context_12_7001_111560
  intro a
  fin_cases a
  · exact context_13_28004_3444
  · exact context_13_28005_111505
  · exact context_13_28006_111541
  · exact context_13_28007_111559

theorem selected_cut_03573 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28008) = some ⟨13, 1, 0, 3444, 28008, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28008_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28008 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28008 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28008, 1, 16384⟩
    (by decide) selected_cut_03573

theorem selected_cut_03574 : selected 8 ⟨111591, by decide⟩
    (prefixPartial 13 28009) = some ⟨13, 2, 0, 111591, 28009, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_28009_111591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28009 ⟨111591, by decide⟩ :=
  accepted_of_selected 13 28009 ⟨111591, by decide⟩ ⟨13, 2, 0, 111591, 28009, 1517, 16384⟩
    (by decide) selected_cut_03574

theorem selected_cut_03575 : selected 8 ⟨111628, by decide⟩
    (prefixPartial 13 28010) = some ⟨13, 2, 0, 111628, 28010, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_28010_111628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28010 ⟨111628, by decide⟩ :=
  accepted_of_selected 13 28010 ⟨111628, by decide⟩ ⟨13, 2, 0, 111628, 28010, 2665, 16384⟩
    (by decide) selected_cut_03575

theorem selected_cut_03576 : selected 8 ⟨111637, by decide⟩
    (prefixPartial 13 28011) = some ⟨13, 2, 0, 111637, 28011, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_28011_111637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28011 ⟨111637, by decide⟩ :=
  accepted_of_selected 13 28011 ⟨111637, by decide⟩ ⟨13, 2, 0, 111637, 28011, 1061, 16384⟩
    (by decide) selected_cut_03576

theorem unmarked_context_12_7002_111638 : frontier 9 ⟨111638, by decide⟩
    (prefixCache 12 7002) (prefixPartial 12 7002) = false := by
  decide +kernel

theorem node_context_12_7002_111638 : EJMOriginalGlobalDAGData.nodes 9 ⟨111638, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111591, by decide⟩,⟨111628, by decide⟩,⟨111637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7002_111638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7002 ⟨111638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7002
    ⟨111638, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111591, by decide⟩,⟨111628, by decide⟩,⟨111637, by decide⟩]) unmarked_context_12_7002_111638 node_context_12_7002_111638
  intro a
  fin_cases a
  · exact context_13_28008_3444
  · exact context_13_28009_111591
  · exact context_13_28010_111628
  · exact context_13_28011_111637

theorem selected_cut_03577 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28012) = some ⟨13, 1, 0, 3444, 28012, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28012_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28012 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28012 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28012, 1, 16384⟩
    (by decide) selected_cut_03577

theorem selected_cut_03578 : selected 8 ⟨111663, by decide⟩
    (prefixPartial 13 28013) = some ⟨13, 2, 0, 111663, 28013, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_28013_111663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28013 ⟨111663, by decide⟩ :=
  accepted_of_selected 13 28013 ⟨111663, by decide⟩ ⟨13, 2, 0, 111663, 28013, 1325, 16384⟩
    (by decide) selected_cut_03578

theorem selected_cut_03579 : selected 8 ⟨111697, by decide⟩
    (prefixPartial 13 28014) = some ⟨13, 2, 0, 111697, 28014, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_28014_111697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28014 ⟨111697, by decide⟩ :=
  accepted_of_selected 13 28014 ⟨111697, by decide⟩ ⟨13, 2, 0, 111697, 28014, 2525, 16384⟩
    (by decide) selected_cut_03579

theorem selected_cut_03580 : selected 8 ⟨111704, by decide⟩
    (prefixPartial 13 28015) = some ⟨13, 2, 0, 111704, 28015, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_28015_111704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28015 ⟨111704, by decide⟩ :=
  accepted_of_selected 13 28015 ⟨111704, by decide⟩ ⟨13, 2, 0, 111704, 28015, 1073, 16384⟩
    (by decide) selected_cut_03580

theorem unmarked_context_12_7003_111705 : frontier 9 ⟨111705, by decide⟩
    (prefixCache 12 7003) (prefixPartial 12 7003) = false := by
  decide +kernel

theorem node_context_12_7003_111705 : EJMOriginalGlobalDAGData.nodes 9 ⟨111705, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111663, by decide⟩,⟨111697, by decide⟩,⟨111704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7003_111705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7003 ⟨111705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7003
    ⟨111705, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111663, by decide⟩,⟨111697, by decide⟩,⟨111704, by decide⟩]) unmarked_context_12_7003_111705 node_context_12_7003_111705
  intro a
  fin_cases a
  · exact context_13_28012_3444
  · exact context_13_28013_111663
  · exact context_13_28014_111697
  · exact context_13_28015_111704

theorem unmarked_context_11_1750_111706 : frontier 10 ⟨111706, by decide⟩
    (prefixCache 11 1750) (prefixPartial 11 1750) = false := by
  decide +kernel

theorem node_context_11_1750_111706 : EJMOriginalGlobalDAGData.nodes 10 ⟨111706, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨111560, by decide⟩,⟨111638, by decide⟩,⟨111705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1750_111706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1750 ⟨111706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1750
    ⟨111706, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨111560, by decide⟩,⟨111638, by decide⟩,⟨111705, by decide⟩]) unmarked_context_11_1750_111706 node_context_11_1750_111706
  intro a
  fin_cases a
  · exact context_12_7000_106538
  · exact context_12_7001_111560
  · exact context_12_7002_111638
  · exact context_12_7003_111705

theorem selected_cut_03581 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7004) = some ⟨12, 1, 0, 106538, 7004, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7004_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7004 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7004 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7004, 1, 65536⟩
    (by decide) selected_cut_03581

theorem selected_cut_03582 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 7005) = some ⟨12, 1, 0, 4596, 7005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7005_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7005 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 7005 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 7005, 1, 65536⟩
    (by decide) selected_cut_03582

theorem selected_cut_03583 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28024) = some ⟨13, 1, 0, 3444, 28024, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28024_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28024 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28024 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28024, 1, 16384⟩
    (by decide) selected_cut_03583

theorem selected_cut_03584 : selected 8 ⟨111753, by decide⟩
    (prefixPartial 13 28025) = some ⟨13, 2, 0, 111753, 28025, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_28025_111753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28025 ⟨111753, by decide⟩ :=
  accepted_of_selected 13 28025 ⟨111753, by decide⟩ ⟨13, 2, 0, 111753, 28025, 1705, 16384⟩
    (by decide) selected_cut_03584

theorem selected_cut_03585 : selected 8 ⟨111798, by decide⟩
    (prefixPartial 13 28026) = some ⟨13, 2, 0, 111798, 28026, 2797, 16384⟩ := by
  decide +kernel

theorem context_13_28026_111798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28026 ⟨111798, by decide⟩ :=
  accepted_of_selected 13 28026 ⟨111798, by decide⟩ ⟨13, 2, 0, 111798, 28026, 2797, 16384⟩
    (by decide) selected_cut_03585

theorem selected_cut_03586 : selected 8 ⟨111807, by decide⟩
    (prefixPartial 13 28027) = some ⟨13, 2, 0, 111807, 28027, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_28027_111807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28027 ⟨111807, by decide⟩ :=
  accepted_of_selected 13 28027 ⟨111807, by decide⟩ ⟨13, 2, 0, 111807, 28027, 1117, 16384⟩
    (by decide) selected_cut_03586

theorem unmarked_context_12_7006_111808 : frontier 9 ⟨111808, by decide⟩
    (prefixCache 12 7006) (prefixPartial 12 7006) = false := by
  decide +kernel

theorem node_context_12_7006_111808 : EJMOriginalGlobalDAGData.nodes 9 ⟨111808, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111753, by decide⟩,⟨111798, by decide⟩,⟨111807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7006_111808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7006 ⟨111808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7006
    ⟨111808, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111753, by decide⟩,⟨111798, by decide⟩,⟨111807, by decide⟩]) unmarked_context_12_7006_111808 node_context_12_7006_111808
  intro a
  fin_cases a
  · exact context_13_28024_3444
  · exact context_13_28025_111753
  · exact context_13_28026_111798
  · exact context_13_28027_111807

theorem selected_cut_03587 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28028) = some ⟨13, 1, 0, 3444, 28028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28028, 1, 16384⟩
    (by decide) selected_cut_03587

theorem selected_cut_03588 : selected 8 ⟨111863, by decide⟩
    (prefixPartial 13 28029) = some ⟨13, 2, 0, 111863, 28029, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_28029_111863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28029 ⟨111863, by decide⟩ :=
  accepted_of_selected 13 28029 ⟨111863, by decide⟩ ⟨13, 2, 0, 111863, 28029, 2269, 16384⟩
    (by decide) selected_cut_03588

theorem selected_cut_03589 : selected 7 ⟨111893, by decide⟩
    (prefixPartial 14 112120) = some ⟨14, 2, 0, 111893, 112120, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_112120_111893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112120 ⟨111893, by decide⟩ :=
  accepted_of_selected 14 112120 ⟨111893, by decide⟩ ⟨14, 2, 0, 111893, 112120, 1265, 4096⟩
    (by decide) selected_cut_03589

theorem selected_cut_03590 : selected 7 ⟨111932, by decide⟩
    (prefixPartial 14 112121) = some ⟨14, 2, 0, 111932, 112121, 1461, 4096⟩ := by
  decide +kernel

theorem context_14_112121_111932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112121 ⟨111932, by decide⟩ :=
  accepted_of_selected 14 112121 ⟨111932, by decide⟩ ⟨14, 2, 0, 111932, 112121, 1461, 4096⟩
    (by decide) selected_cut_03590

theorem selected_cut_03591 : selected 7 ⟨111951, by decide⟩
    (prefixPartial 14 112122) = some ⟨14, 2, 0, 111951, 112122, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_112122_111951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112122 ⟨111951, by decide⟩ :=
  accepted_of_selected 14 112122 ⟨111951, by decide⟩ ⟨14, 2, 0, 111951, 112122, 1145, 4096⟩
    (by decide) selected_cut_03591

theorem selected_cut_03592 : selected 7 ⟨111977, by decide⟩
    (prefixPartial 14 112123) = some ⟨14, 2, 0, 111977, 112123, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_112123_111977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112123 ⟨111977, by decide⟩ :=
  accepted_of_selected 14 112123 ⟨111977, by decide⟩ ⟨14, 2, 0, 111977, 112123, 1105, 4096⟩
    (by decide) selected_cut_03592

theorem unmarked_context_13_28030_111978 : frontier 8 ⟨111978, by decide⟩
    (prefixCache 13 28030) (prefixPartial 13 28030) = false := by
  decide +kernel

theorem node_context_13_28030_111978 : EJMOriginalGlobalDAGData.nodes 8 ⟨111978, by decide⟩ =
    .split (coordinate 13) (![⟨111893, by decide⟩,⟨111932, by decide⟩,⟨111951, by decide⟩,⟨111977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_28030_111978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28030 ⟨111978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 28030
    ⟨111978, by decide⟩ (by decide) (![⟨111893, by decide⟩,⟨111932, by decide⟩,⟨111951, by decide⟩,⟨111977, by decide⟩]) unmarked_context_13_28030_111978 node_context_13_28030_111978
  intro a
  fin_cases a
  · exact context_14_112120_111893
  · exact context_14_112121_111932
  · exact context_14_112122_111951
  · exact context_14_112123_111977

theorem selected_cut_03593 : selected 8 ⟨112020, by decide⟩
    (prefixPartial 13 28031) = some ⟨13, 2, 0, 112020, 28031, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_28031_112020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28031 ⟨112020, by decide⟩ :=
  accepted_of_selected 13 28031 ⟨112020, by decide⟩ ⟨13, 2, 0, 112020, 28031, 1825, 16384⟩
    (by decide) selected_cut_03593

theorem unmarked_context_12_7007_112021 : frontier 9 ⟨112021, by decide⟩
    (prefixCache 12 7007) (prefixPartial 12 7007) = false := by
  decide +kernel

theorem node_context_12_7007_112021 : EJMOriginalGlobalDAGData.nodes 9 ⟨112021, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111863, by decide⟩,⟨111978, by decide⟩,⟨112020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7007_112021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7007 ⟨112021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7007
    ⟨112021, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111863, by decide⟩,⟨111978, by decide⟩,⟨112020, by decide⟩]) unmarked_context_12_7007_112021 node_context_12_7007_112021
  intro a
  fin_cases a
  · exact context_13_28028_3444
  · exact context_13_28029_111863
  · exact context_13_28030_111978
  · exact context_13_28031_112020

theorem unmarked_context_11_1751_112022 : frontier 10 ⟨112022, by decide⟩
    (prefixCache 11 1751) (prefixPartial 11 1751) = false := by
  decide +kernel

theorem node_context_11_1751_112022 : EJMOriginalGlobalDAGData.nodes 10 ⟨112022, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨4596, by decide⟩,⟨111808, by decide⟩,⟨112021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1751_112022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1751 ⟨112022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1751
    ⟨112022, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨4596, by decide⟩,⟨111808, by decide⟩,⟨112021, by decide⟩]) unmarked_context_11_1751_112022 node_context_11_1751_112022
  intro a
  fin_cases a
  · exact context_12_7004_106538
  · exact context_12_7005_4596
  · exact context_12_7006_111808
  · exact context_12_7007_112021

theorem unmarked_context_10_437_112023 : frontier 11 ⟨112023, by decide⟩
    (prefixCache 10 437) (prefixPartial 10 437) = false := by
  decide +kernel

theorem node_context_10_437_112023 : EJMOriginalGlobalDAGData.nodes 11 ⟨112023, by decide⟩ =
    .split (coordinate 10) (![⟨111195, by decide⟩,⟨111480, by decide⟩,⟨111706, by decide⟩,⟨112022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_437_112023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 437 ⟨112023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 437
    ⟨112023, by decide⟩ (by decide) (![⟨111195, by decide⟩,⟨111480, by decide⟩,⟨111706, by decide⟩,⟨112022, by decide⟩]) unmarked_context_10_437_112023 node_context_10_437_112023
  intro a
  fin_cases a
  · exact context_11_1748_111195
  · exact context_11_1749_111480
  · exact context_11_1750_111706
  · exact context_11_1751_112022

theorem selected_cut_03594 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7008) = some ⟨12, 1, 0, 106538, 7008, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7008_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7008 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7008 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7008, 1, 65536⟩
    (by decide) selected_cut_03594

theorem selected_cut_03595 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7009) = some ⟨12, 1, 0, 106538, 7009, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7009_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7009 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7009 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7009, 1, 65536⟩
    (by decide) selected_cut_03595

theorem selected_cut_03596 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28040) = some ⟨13, 1, 0, 3444, 28040, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28040_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28040 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28040 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28040, 1, 16384⟩
    (by decide) selected_cut_03596

theorem selected_cut_03597 : selected 8 ⟨112063, by decide⟩
    (prefixPartial 13 28041) = some ⟨13, 2, 0, 112063, 28041, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_28041_112063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28041 ⟨112063, by decide⟩ :=
  accepted_of_selected 13 28041 ⟨112063, by decide⟩ ⟨13, 2, 0, 112063, 28041, 1565, 16384⟩
    (by decide) selected_cut_03597

theorem selected_cut_03598 : selected 8 ⟨112094, by decide⟩
    (prefixPartial 13 28042) = some ⟨13, 2, 0, 112094, 28042, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_28042_112094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28042 ⟨112094, by decide⟩ :=
  accepted_of_selected 13 28042 ⟨112094, by decide⟩ ⟨13, 2, 0, 112094, 28042, 2269, 16384⟩
    (by decide) selected_cut_03598

theorem selected_cut_03599 : selected 8 ⟨112102, by decide⟩
    (prefixPartial 13 28043) = some ⟨13, 2, 0, 112102, 28043, 933, 16384⟩ := by
  decide +kernel

theorem context_13_28043_112102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28043 ⟨112102, by decide⟩ :=
  accepted_of_selected 13 28043 ⟨112102, by decide⟩ ⟨13, 2, 0, 112102, 28043, 933, 16384⟩
    (by decide) selected_cut_03599

theorem unmarked_context_12_7010_112103 : frontier 9 ⟨112103, by decide⟩
    (prefixCache 12 7010) (prefixPartial 12 7010) = false := by
  decide +kernel

theorem node_context_12_7010_112103 : EJMOriginalGlobalDAGData.nodes 9 ⟨112103, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨112063, by decide⟩,⟨112094, by decide⟩,⟨112102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7010_112103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7010 ⟨112103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7010
    ⟨112103, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨112063, by decide⟩,⟨112094, by decide⟩,⟨112102, by decide⟩]) unmarked_context_12_7010_112103 node_context_12_7010_112103
  intro a
  fin_cases a
  · exact context_13_28040_3444
  · exact context_13_28041_112063
  · exact context_13_28042_112094
  · exact context_13_28043_112102

theorem selected_cut_03600 : selected 9 ⟨112178, by decide⟩
    (prefixPartial 12 7011) = some ⟨12, 2, 0, 112178, 7011, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_7011_112178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7011 ⟨112178, by decide⟩ :=
  accepted_of_selected 12 7011 ⟨112178, by decide⟩ ⟨12, 2, 0, 112178, 7011, 2997, 65536⟩
    (by decide) selected_cut_03600

theorem unmarked_context_11_1752_112179 : frontier 10 ⟨112179, by decide⟩
    (prefixCache 11 1752) (prefixPartial 11 1752) = false := by
  decide +kernel

theorem node_context_11_1752_112179 : EJMOriginalGlobalDAGData.nodes 10 ⟨112179, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112103, by decide⟩,⟨112178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1752_112179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1752 ⟨112179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1752
    ⟨112179, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112103, by decide⟩,⟨112178, by decide⟩]) unmarked_context_11_1752_112179 node_context_11_1752_112179
  intro a
  fin_cases a
  · exact context_12_7008_106538
  · exact context_12_7009_106538
  · exact context_12_7010_112103
  · exact context_12_7011_112178

theorem selected_cut_03601 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7012) = some ⟨12, 1, 0, 106538, 7012, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7012_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7012 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7012 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7012, 1, 65536⟩
    (by decide) selected_cut_03601

theorem selected_cut_03602 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7013) = some ⟨12, 1, 0, 106538, 7013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7013_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7013 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7013 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7013, 1, 65536⟩
    (by decide) selected_cut_03602

theorem selected_cut_03603 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28056) = some ⟨13, 1, 0, 3444, 28056, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28056_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28056 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28056 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28056, 1, 16384⟩
    (by decide) selected_cut_03603

theorem selected_cut_03604 : selected 8 ⟨112213, by decide⟩
    (prefixPartial 13 28057) = some ⟨13, 2, 0, 112213, 28057, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_28057_112213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28057 ⟨112213, by decide⟩ :=
  accepted_of_selected 13 28057 ⟨112213, by decide⟩ ⟨13, 2, 0, 112213, 28057, 1349, 16384⟩
    (by decide) selected_cut_03604

theorem selected_cut_03605 : selected 8 ⟨112267, by decide⟩
    (prefixPartial 13 28058) = some ⟨13, 2, 0, 112267, 28058, 2897, 16384⟩ := by
  decide +kernel

theorem context_13_28058_112267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28058 ⟨112267, by decide⟩ :=
  accepted_of_selected 13 28058 ⟨112267, by decide⟩ ⟨13, 2, 0, 112267, 28058, 2897, 16384⟩
    (by decide) selected_cut_03605

theorem selected_cut_03606 : selected 8 ⟨112291, by decide⟩
    (prefixPartial 13 28059) = some ⟨13, 2, 0, 112291, 28059, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_28059_112291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28059 ⟨112291, by decide⟩ :=
  accepted_of_selected 13 28059 ⟨112291, by decide⟩ ⟨13, 2, 0, 112291, 28059, 1369, 16384⟩
    (by decide) selected_cut_03606

theorem unmarked_context_12_7014_112292 : frontier 9 ⟨112292, by decide⟩
    (prefixCache 12 7014) (prefixPartial 12 7014) = false := by
  decide +kernel

theorem node_context_12_7014_112292 : EJMOriginalGlobalDAGData.nodes 9 ⟨112292, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨112213, by decide⟩,⟨112267, by decide⟩,⟨112291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7014_112292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7014 ⟨112292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7014
    ⟨112292, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨112213, by decide⟩,⟨112267, by decide⟩,⟨112291, by decide⟩]) unmarked_context_12_7014_112292 node_context_12_7014_112292
  intro a
  fin_cases a
  · exact context_13_28056_3444
  · exact context_13_28057_112213
  · exact context_13_28058_112267
  · exact context_13_28059_112291

theorem selected_cut_03607 : selected 9 ⟨112396, by decide⟩
    (prefixPartial 12 7015) = some ⟨12, 2, 0, 112396, 7015, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_7015_112396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7015 ⟨112396, by decide⟩ :=
  accepted_of_selected 12 7015 ⟨112396, by decide⟩ ⟨12, 2, 0, 112396, 7015, 3681, 65536⟩
    (by decide) selected_cut_03607

theorem unmarked_context_11_1753_112397 : frontier 10 ⟨112397, by decide⟩
    (prefixCache 11 1753) (prefixPartial 11 1753) = false := by
  decide +kernel

theorem node_context_11_1753_112397 : EJMOriginalGlobalDAGData.nodes 10 ⟨112397, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112292, by decide⟩,⟨112396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1753_112397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1753 ⟨112397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1753
    ⟨112397, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112292, by decide⟩,⟨112396, by decide⟩]) unmarked_context_11_1753_112397 node_context_11_1753_112397
  intro a
  fin_cases a
  · exact context_12_7012_106538
  · exact context_12_7013_106538
  · exact context_12_7014_112292
  · exact context_12_7015_112396

theorem selected_cut_03608 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7016) = some ⟨12, 1, 0, 106538, 7016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7016_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7016 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7016 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7016, 1, 65536⟩
    (by decide) selected_cut_03608

theorem selected_cut_03609 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7017) = some ⟨12, 1, 0, 106538, 7017, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7017_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7017 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7017 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7017, 1, 65536⟩
    (by decide) selected_cut_03609

theorem selected_cut_03610 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28072) = some ⟨13, 1, 0, 3444, 28072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28072, 1, 16384⟩
    (by decide) selected_cut_03610

theorem selected_cut_03611 : selected 8 ⟨112431, by decide⟩
    (prefixPartial 13 28073) = some ⟨13, 2, 0, 112431, 28073, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_28073_112431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28073 ⟨112431, by decide⟩ :=
  accepted_of_selected 13 28073 ⟨112431, by decide⟩ ⟨13, 2, 0, 112431, 28073, 1265, 16384⟩
    (by decide) selected_cut_03611

theorem selected_cut_03612 : selected 7 ⟨112452, by decide⟩
    (prefixPartial 14 112296) = some ⟨14, 2, 0, 112452, 112296, 989, 4096⟩ := by
  decide +kernel

theorem context_14_112296_112452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112296 ⟨112452, by decide⟩ :=
  accepted_of_selected 14 112296 ⟨112452, by decide⟩ ⟨14, 2, 0, 112452, 112296, 989, 4096⟩
    (by decide) selected_cut_03612

theorem selected_cut_03613 : selected 7 ⟨112485, by decide⟩
    (prefixPartial 14 112297) = some ⟨14, 2, 0, 112485, 112297, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_112297_112485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112297 ⟨112485, by decide⟩ :=
  accepted_of_selected 14 112297 ⟨112485, by decide⟩ ⟨14, 2, 0, 112485, 112297, 1341, 4096⟩
    (by decide) selected_cut_03613

theorem selected_cut_03614 : selected 7 ⟨112513, by decide⟩
    (prefixPartial 14 112298) = some ⟨14, 2, 0, 112513, 112298, 1413, 4096⟩ := by
  decide +kernel

theorem context_14_112298_112513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112298 ⟨112513, by decide⟩ :=
  accepted_of_selected 14 112298 ⟨112513, by decide⟩ ⟨14, 2, 0, 112513, 112298, 1413, 4096⟩
    (by decide) selected_cut_03614

theorem selected_cut_03615 : selected 7 ⟨112529, by decide⟩
    (prefixPartial 14 112299) = some ⟨14, 2, 0, 112529, 112299, 933, 4096⟩ := by
  decide +kernel

theorem context_14_112299_112529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112299 ⟨112529, by decide⟩ :=
  accepted_of_selected 14 112299 ⟨112529, by decide⟩ ⟨14, 2, 0, 112529, 112299, 933, 4096⟩
    (by decide) selected_cut_03615

theorem unmarked_context_13_28074_112530 : frontier 8 ⟨112530, by decide⟩
    (prefixCache 13 28074) (prefixPartial 13 28074) = false := by
  decide +kernel

theorem node_context_13_28074_112530 : EJMOriginalGlobalDAGData.nodes 8 ⟨112530, by decide⟩ =
    .split (coordinate 13) (![⟨112452, by decide⟩,⟨112485, by decide⟩,⟨112513, by decide⟩,⟨112529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_28074_112530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28074 ⟨112530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 28074
    ⟨112530, by decide⟩ (by decide) (![⟨112452, by decide⟩,⟨112485, by decide⟩,⟨112513, by decide⟩,⟨112529, by decide⟩]) unmarked_context_13_28074_112530 node_context_13_28074_112530
  intro a
  fin_cases a
  · exact context_14_112296_112452
  · exact context_14_112297_112485
  · exact context_14_112298_112513
  · exact context_14_112299_112529

theorem selected_cut_03616 : selected 8 ⟨112573, by decide⟩
    (prefixPartial 13 28075) = some ⟨13, 2, 0, 112573, 28075, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_28075_112573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28075 ⟨112573, by decide⟩ :=
  accepted_of_selected 13 28075 ⟨112573, by decide⟩ ⟨13, 2, 0, 112573, 28075, 1585, 16384⟩
    (by decide) selected_cut_03616

theorem unmarked_context_12_7018_112574 : frontier 9 ⟨112574, by decide⟩
    (prefixCache 12 7018) (prefixPartial 12 7018) = false := by
  decide +kernel

theorem node_context_12_7018_112574 : EJMOriginalGlobalDAGData.nodes 9 ⟨112574, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨112431, by decide⟩,⟨112530, by decide⟩,⟨112573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7018_112574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7018 ⟨112574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7018
    ⟨112574, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨112431, by decide⟩,⟨112530, by decide⟩,⟨112573, by decide⟩]) unmarked_context_12_7018_112574 node_context_12_7018_112574
  intro a
  fin_cases a
  · exact context_13_28072_3444
  · exact context_13_28073_112431
  · exact context_13_28074_112530
  · exact context_13_28075_112573

theorem selected_cut_03617 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28076) = some ⟨13, 1, 0, 3444, 28076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28076, 1, 16384⟩
    (by decide) selected_cut_03617

theorem selected_cut_03618 : selected 8 ⟨112612, by decide⟩
    (prefixPartial 13 28077) = some ⟨13, 2, 0, 112612, 28077, 897, 16384⟩ := by
  decide +kernel

theorem context_13_28077_112612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28077 ⟨112612, by decide⟩ :=
  accepted_of_selected 13 28077 ⟨112612, by decide⟩ ⟨13, 2, 0, 112612, 28077, 897, 16384⟩
    (by decide) selected_cut_03618

theorem selected_cut_03619 : selected 7 ⟨112644, by decide⟩
    (prefixPartial 14 112312) = some ⟨14, 2, 0, 112644, 112312, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_112312_112644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112312 ⟨112644, by decide⟩ :=
  accepted_of_selected 14 112312 ⟨112644, by decide⟩ ⟨14, 2, 0, 112644, 112312, 1285, 4096⟩
    (by decide) selected_cut_03619

theorem selected_cut_03620 : selected 7 ⟨112677, by decide⟩
    (prefixPartial 14 112313) = some ⟨14, 2, 0, 112677, 112313, 1469, 4096⟩ := by
  decide +kernel

theorem context_14_112313_112677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112313 ⟨112677, by decide⟩ :=
  accepted_of_selected 14 112313 ⟨112677, by decide⟩ ⟨14, 2, 0, 112677, 112313, 1469, 4096⟩
    (by decide) selected_cut_03620

theorem selected_cut_03621 : selected 7 ⟨112702, by decide⟩
    (prefixPartial 14 112314) = some ⟨14, 2, 0, 112702, 112314, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_112314_112702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112314 ⟨112702, by decide⟩ :=
  accepted_of_selected 14 112314 ⟨112702, by decide⟩ ⟨14, 2, 0, 112702, 112314, 1153, 4096⟩
    (by decide) selected_cut_03621

theorem selected_cut_03622 : selected 7 ⟨112728, by decide⟩
    (prefixPartial 14 112315) = some ⟨14, 2, 0, 112728, 112315, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_112315_112728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 112315 ⟨112728, by decide⟩ :=
  accepted_of_selected 14 112315 ⟨112728, by decide⟩ ⟨14, 2, 0, 112728, 112315, 1113, 4096⟩
    (by decide) selected_cut_03622

theorem unmarked_context_13_28078_112729 : frontier 8 ⟨112729, by decide⟩
    (prefixCache 13 28078) (prefixPartial 13 28078) = false := by
  decide +kernel

theorem node_context_13_28078_112729 : EJMOriginalGlobalDAGData.nodes 8 ⟨112729, by decide⟩ =
    .split (coordinate 13) (![⟨112644, by decide⟩,⟨112677, by decide⟩,⟨112702, by decide⟩,⟨112728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_28078_112729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28078 ⟨112729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 28078
    ⟨112729, by decide⟩ (by decide) (![⟨112644, by decide⟩,⟨112677, by decide⟩,⟨112702, by decide⟩,⟨112728, by decide⟩]) unmarked_context_13_28078_112729 node_context_13_28078_112729
  intro a
  fin_cases a
  · exact context_14_112312_112644
  · exact context_14_112313_112677
  · exact context_14_112314_112702
  · exact context_14_112315_112728

theorem selected_cut_03623 : selected 8 ⟨112771, by decide⟩
    (prefixPartial 13 28079) = some ⟨13, 2, 0, 112771, 28079, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_28079_112771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28079 ⟨112771, by decide⟩ :=
  accepted_of_selected 13 28079 ⟨112771, by decide⟩ ⟨13, 2, 0, 112771, 28079, 1629, 16384⟩
    (by decide) selected_cut_03623

theorem unmarked_context_12_7019_112772 : frontier 9 ⟨112772, by decide⟩
    (prefixCache 12 7019) (prefixPartial 12 7019) = false := by
  decide +kernel

theorem node_context_12_7019_112772 : EJMOriginalGlobalDAGData.nodes 9 ⟨112772, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨112612, by decide⟩,⟨112729, by decide⟩,⟨112771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7019_112772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7019 ⟨112772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7019
    ⟨112772, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨112612, by decide⟩,⟨112729, by decide⟩,⟨112771, by decide⟩]) unmarked_context_12_7019_112772 node_context_12_7019_112772
  intro a
  fin_cases a
  · exact context_13_28076_3444
  · exact context_13_28077_112612
  · exact context_13_28078_112729
  · exact context_13_28079_112771

theorem unmarked_context_11_1754_112773 : frontier 10 ⟨112773, by decide⟩
    (prefixCache 11 1754) (prefixPartial 11 1754) = false := by
  decide +kernel

theorem node_context_11_1754_112773 : EJMOriginalGlobalDAGData.nodes 10 ⟨112773, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112574, by decide⟩,⟨112772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1754_112773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1754 ⟨112773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1754
    ⟨112773, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112574, by decide⟩,⟨112772, by decide⟩]) unmarked_context_11_1754_112773 node_context_11_1754_112773
  intro a
  fin_cases a
  · exact context_12_7016_106538
  · exact context_12_7017_106538
  · exact context_12_7018_112574
  · exact context_12_7019_112772

theorem selected_cut_03624 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7020) = some ⟨12, 1, 0, 106538, 7020, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7020_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7020 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7020 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7020, 1, 65536⟩
    (by decide) selected_cut_03624

theorem selected_cut_03625 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7021) = some ⟨12, 1, 0, 106538, 7021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7021_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7021 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7021 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7021, 1, 65536⟩
    (by decide) selected_cut_03625

theorem selected_cut_03626 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28088) = some ⟨13, 1, 0, 3444, 28088, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28088_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28088 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28088 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28088, 1, 16384⟩
    (by decide) selected_cut_03626

theorem selected_cut_03627 : selected 8 ⟨112788, by decide⟩
    (prefixPartial 13 28089) = some ⟨13, 2, 0, 112788, 28089, 461, 16384⟩ := by
  decide +kernel

theorem context_13_28089_112788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28089 ⟨112788, by decide⟩ :=
  accepted_of_selected 13 28089 ⟨112788, by decide⟩ ⟨13, 2, 0, 112788, 28089, 461, 16384⟩
    (by decide) selected_cut_03627

theorem selected_cut_03628 : selected 8 ⟨112826, by decide⟩
    (prefixPartial 13 28090) = some ⟨13, 2, 0, 112826, 28090, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_28090_112826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28090 ⟨112826, by decide⟩ :=
  accepted_of_selected 13 28090 ⟨112826, by decide⟩ ⟨13, 2, 0, 112826, 28090, 2533, 16384⟩
    (by decide) selected_cut_03628

theorem selected_cut_03629 : selected 8 ⟨112840, by decide⟩
    (prefixPartial 13 28091) = some ⟨13, 2, 0, 112840, 28091, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_28091_112840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28091 ⟨112840, by decide⟩ :=
  accepted_of_selected 13 28091 ⟨112840, by decide⟩ ⟨13, 2, 0, 112840, 28091, 1129, 16384⟩
    (by decide) selected_cut_03629

theorem unmarked_context_12_7022_112841 : frontier 9 ⟨112841, by decide⟩
    (prefixCache 12 7022) (prefixPartial 12 7022) = false := by
  decide +kernel

theorem node_context_12_7022_112841 : EJMOriginalGlobalDAGData.nodes 9 ⟨112841, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨112788, by decide⟩,⟨112826, by decide⟩,⟨112840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7022_112841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7022 ⟨112841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7022
    ⟨112841, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨112788, by decide⟩,⟨112826, by decide⟩,⟨112840, by decide⟩]) unmarked_context_12_7022_112841 node_context_12_7022_112841
  intro a
  fin_cases a
  · exact context_13_28088_3444
  · exact context_13_28089_112788
  · exact context_13_28090_112826
  · exact context_13_28091_112840

theorem selected_cut_03630 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 7023) = some ⟨12, 1, 0, 4596, 7023, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7023_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7023 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 7023 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 7023, 1, 65536⟩
    (by decide) selected_cut_03630

theorem unmarked_context_11_1755_112842 : frontier 10 ⟨112842, by decide⟩
    (prefixCache 11 1755) (prefixPartial 11 1755) = false := by
  decide +kernel

theorem node_context_11_1755_112842 : EJMOriginalGlobalDAGData.nodes 10 ⟨112842, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112841, by decide⟩,⟨4596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1755_112842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1755 ⟨112842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1755
    ⟨112842, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨112841, by decide⟩,⟨4596, by decide⟩]) unmarked_context_11_1755_112842 node_context_11_1755_112842
  intro a
  fin_cases a
  · exact context_12_7020_106538
  · exact context_12_7021_106538
  · exact context_12_7022_112841
  · exact context_12_7023_4596

theorem unmarked_context_10_438_112843 : frontier 11 ⟨112843, by decide⟩
    (prefixCache 10 438) (prefixPartial 10 438) = false := by
  decide +kernel

theorem node_context_10_438_112843 : EJMOriginalGlobalDAGData.nodes 11 ⟨112843, by decide⟩ =
    .split (coordinate 10) (![⟨112179, by decide⟩,⟨112397, by decide⟩,⟨112773, by decide⟩,⟨112842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_438_112843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 438 ⟨112843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 438
    ⟨112843, by decide⟩ (by decide) (![⟨112179, by decide⟩,⟨112397, by decide⟩,⟨112773, by decide⟩,⟨112842, by decide⟩]) unmarked_context_10_438_112843 node_context_10_438_112843
  intro a
  fin_cases a
  · exact context_11_1752_112179
  · exact context_11_1753_112397
  · exact context_11_1754_112773
  · exact context_11_1755_112842

theorem selected_cut_03631 : selected 10 ⟨112913, by decide⟩
    (prefixPartial 11 1756) = some ⟨11, 2, 0, 112913, 1756, 2797, 262144⟩ := by
  decide +kernel

theorem context_11_1756_112913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1756 ⟨112913, by decide⟩ :=
  accepted_of_selected 11 1756 ⟨112913, by decide⟩ ⟨11, 2, 0, 112913, 1756, 2797, 262144⟩
    (by decide) selected_cut_03631

theorem selected_cut_03632 : selected 10 ⟨113025, by decide⟩
    (prefixPartial 11 1757) = some ⟨11, 2, 0, 113025, 1757, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_1757_113025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1757 ⟨113025, by decide⟩ :=
  accepted_of_selected 11 1757 ⟨113025, by decide⟩ ⟨11, 2, 0, 113025, 1757, 3565, 262144⟩
    (by decide) selected_cut_03632

theorem selected_cut_03633 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7032) = some ⟨12, 1, 0, 106538, 7032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7032_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7032 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7032 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7032, 1, 65536⟩
    (by decide) selected_cut_03633

theorem selected_cut_03634 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7033) = some ⟨12, 1, 0, 106538, 7033, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7033_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7033 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7033 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7033, 1, 65536⟩
    (by decide) selected_cut_03634

theorem selected_cut_03635 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28136) = some ⟨13, 1, 0, 3444, 28136, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28136_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28136 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28136 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28136, 1, 16384⟩
    (by decide) selected_cut_03635

theorem selected_cut_03636 : selected 8 ⟨113031, by decide⟩
    (prefixPartial 13 28137) = some ⟨13, 2, 0, 113031, 28137, 113, 16384⟩ := by
  decide +kernel

theorem context_13_28137_113031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28137 ⟨113031, by decide⟩ :=
  accepted_of_selected 13 28137 ⟨113031, by decide⟩ ⟨13, 2, 0, 113031, 28137, 113, 16384⟩
    (by decide) selected_cut_03636

theorem selected_cut_03637 : selected 8 ⟨113072, by decide⟩
    (prefixPartial 13 28138) = some ⟨13, 2, 0, 113072, 28138, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_28138_113072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28138 ⟨113072, by decide⟩ :=
  accepted_of_selected 13 28138 ⟨113072, by decide⟩ ⟨13, 2, 0, 113072, 28138, 2821, 16384⟩
    (by decide) selected_cut_03637

theorem selected_cut_03638 : selected 8 ⟨113094, by decide⟩
    (prefixPartial 13 28139) = some ⟨13, 2, 0, 113094, 28139, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_28139_113094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28139 ⟨113094, by decide⟩ :=
  accepted_of_selected 13 28139 ⟨113094, by decide⟩ ⟨13, 2, 0, 113094, 28139, 1221, 16384⟩
    (by decide) selected_cut_03638

theorem unmarked_context_12_7034_113095 : frontier 9 ⟨113095, by decide⟩
    (prefixCache 12 7034) (prefixPartial 12 7034) = false := by
  decide +kernel

theorem node_context_12_7034_113095 : EJMOriginalGlobalDAGData.nodes 9 ⟨113095, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨113031, by decide⟩,⟨113072, by decide⟩,⟨113094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7034_113095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7034 ⟨113095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7034
    ⟨113095, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨113031, by decide⟩,⟨113072, by decide⟩,⟨113094, by decide⟩]) unmarked_context_12_7034_113095 node_context_12_7034_113095
  intro a
  fin_cases a
  · exact context_13_28136_3444
  · exact context_13_28137_113031
  · exact context_13_28138_113072
  · exact context_13_28139_113094

theorem selected_cut_03639 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 7035) = some ⟨12, 1, 0, 106538, 7035, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7035_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7035 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 7035 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 7035, 1, 65536⟩
    (by decide) selected_cut_03639

theorem unmarked_context_11_1758_113096 : frontier 10 ⟨113096, by decide⟩
    (prefixCache 11 1758) (prefixPartial 11 1758) = false := by
  decide +kernel

theorem node_context_11_1758_113096 : EJMOriginalGlobalDAGData.nodes 10 ⟨113096, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨113095, by decide⟩,⟨106538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1758_113096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1758 ⟨113096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1758
    ⟨113096, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨113095, by decide⟩,⟨106538, by decide⟩]) unmarked_context_11_1758_113096 node_context_11_1758_113096
  intro a
  fin_cases a
  · exact context_12_7032_106538
  · exact context_12_7033_106538
  · exact context_12_7034_113095
  · exact context_12_7035_106538

theorem selected_cut_03640 : selected 10 ⟨109216, by decide⟩
    (prefixPartial 11 1759) = some ⟨11, 2, 0, 109216, 1759, 5, 262144⟩ := by
  decide +kernel

theorem context_11_1759_109216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1759 ⟨109216, by decide⟩ :=
  accepted_of_selected 11 1759 ⟨109216, by decide⟩ ⟨11, 2, 0, 109216, 1759, 5, 262144⟩
    (by decide) selected_cut_03640

theorem unmarked_context_10_439_113097 : frontier 11 ⟨113097, by decide⟩
    (prefixCache 10 439) (prefixPartial 10 439) = false := by
  decide +kernel

theorem node_context_10_439_113097 : EJMOriginalGlobalDAGData.nodes 11 ⟨113097, by decide⟩ =
    .split (coordinate 10) (![⟨112913, by decide⟩,⟨113025, by decide⟩,⟨113096, by decide⟩,⟨109216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_439_113097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 439 ⟨113097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 439
    ⟨113097, by decide⟩ (by decide) (![⟨112913, by decide⟩,⟨113025, by decide⟩,⟨113096, by decide⟩,⟨109216, by decide⟩]) unmarked_context_10_439_113097 node_context_10_439_113097
  intro a
  fin_cases a
  · exact context_11_1756_112913
  · exact context_11_1757_113025
  · exact context_11_1758_113096
  · exact context_11_1759_109216

theorem unmarked_context_9_109_113098 : frontier 12 ⟨113098, by decide⟩
    (prefixCache 9 109) (prefixPartial 9 109) = false := by
  decide +kernel

theorem node_context_9_109_113098 : EJMOriginalGlobalDAGData.nodes 12 ⟨113098, by decide⟩ =
    .split (coordinate 9) (![⟨110902, by decide⟩,⟨112023, by decide⟩,⟨112843, by decide⟩,⟨113097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_109_113098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 109 ⟨113098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 109
    ⟨113098, by decide⟩ (by decide) (![⟨110902, by decide⟩,⟨112023, by decide⟩,⟨112843, by decide⟩,⟨113097, by decide⟩]) unmarked_context_9_109_113098 node_context_9_109_113098
  intro a
  fin_cases a
  · exact context_10_436_110902
  · exact context_10_437_112023
  · exact context_10_438_112843
  · exact context_10_439_113097

theorem selected_cut_03641 : selected 9 ⟨113133, by decide⟩
    (prefixPartial 12 7040) = some ⟨12, 2, 0, 113133, 7040, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_7040_113133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7040 ⟨113133, by decide⟩ :=
  accepted_of_selected 12 7040 ⟨113133, by decide⟩ ⟨12, 2, 0, 113133, 7040, 2941, 65536⟩
    (by decide) selected_cut_03641

theorem selected_cut_03642 : selected 9 ⟨113186, by decide⟩
    (prefixPartial 12 7041) = some ⟨12, 2, 0, 113186, 7041, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_7041_113186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7041 ⟨113186, by decide⟩ :=
  accepted_of_selected 12 7041 ⟨113186, by decide⟩ ⟨12, 2, 0, 113186, 7041, 3525, 65536⟩
    (by decide) selected_cut_03642

theorem selected_cut_03643 : selected 9 ⟨113230, by decide⟩
    (prefixPartial 12 7042) = some ⟨12, 2, 0, 113230, 7042, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_7042_113230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7042 ⟨113230, by decide⟩ :=
  accepted_of_selected 12 7042 ⟨113230, by decide⟩ ⟨12, 2, 0, 113230, 7042, 3125, 65536⟩
    (by decide) selected_cut_03643

theorem selected_cut_03644 : selected 9 ⟨113276, by decide⟩
    (prefixPartial 12 7043) = some ⟨12, 2, 0, 113276, 7043, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_7043_113276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7043 ⟨113276, by decide⟩ :=
  accepted_of_selected 12 7043 ⟨113276, by decide⟩ ⟨12, 2, 0, 113276, 7043, 3133, 65536⟩
    (by decide) selected_cut_03644

theorem unmarked_context_11_1760_113277 : frontier 10 ⟨113277, by decide⟩
    (prefixCache 11 1760) (prefixPartial 11 1760) = false := by
  decide +kernel

theorem node_context_11_1760_113277 : EJMOriginalGlobalDAGData.nodes 10 ⟨113277, by decide⟩ =
    .split (coordinate 11) (![⟨113133, by decide⟩,⟨113186, by decide⟩,⟨113230, by decide⟩,⟨113276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1760_113277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1760 ⟨113277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1760
    ⟨113277, by decide⟩ (by decide) (![⟨113133, by decide⟩,⟨113186, by decide⟩,⟨113230, by decide⟩,⟨113276, by decide⟩]) unmarked_context_11_1760_113277 node_context_11_1760_113277
  intro a
  fin_cases a
  · exact context_12_7040_113133
  · exact context_12_7041_113186
  · exact context_12_7042_113230
  · exact context_12_7043_113276

theorem selected_cut_03645 : selected 9 ⟨113325, by decide⟩
    (prefixPartial 12 7044) = some ⟨12, 2, 0, 113325, 7044, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_7044_113325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7044 ⟨113325, by decide⟩ :=
  accepted_of_selected 12 7044 ⟨113325, by decide⟩ ⟨12, 2, 0, 113325, 7044, 3161, 65536⟩
    (by decide) selected_cut_03645

theorem selected_cut_03646 : selected 9 ⟨113390, by decide⟩
    (prefixPartial 12 7045) = some ⟨12, 2, 0, 113390, 7045, 3793, 65536⟩ := by
  decide +kernel

theorem context_12_7045_113390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7045 ⟨113390, by decide⟩ :=
  accepted_of_selected 12 7045 ⟨113390, by decide⟩ ⟨12, 2, 0, 113390, 7045, 3793, 65536⟩
    (by decide) selected_cut_03646

theorem selected_cut_03647 : selected 9 ⟨113445, by decide⟩
    (prefixPartial 12 7046) = some ⟨12, 2, 0, 113445, 7046, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_7046_113445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7046 ⟨113445, by decide⟩ :=
  accepted_of_selected 12 7046 ⟨113445, by decide⟩ ⟨12, 2, 0, 113445, 7046, 3457, 65536⟩
    (by decide) selected_cut_03647

theorem selected_cut_03648 : selected 9 ⟨113503, by decide⟩
    (prefixPartial 12 7047) = some ⟨12, 2, 0, 113503, 7047, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_7047_113503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7047 ⟨113503, by decide⟩ :=
  accepted_of_selected 12 7047 ⟨113503, by decide⟩ ⟨12, 2, 0, 113503, 7047, 3481, 65536⟩
    (by decide) selected_cut_03648

theorem unmarked_context_11_1761_113504 : frontier 10 ⟨113504, by decide⟩
    (prefixCache 11 1761) (prefixPartial 11 1761) = false := by
  decide +kernel

theorem node_context_11_1761_113504 : EJMOriginalGlobalDAGData.nodes 10 ⟨113504, by decide⟩ =
    .split (coordinate 11) (![⟨113325, by decide⟩,⟨113390, by decide⟩,⟨113445, by decide⟩,⟨113503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1761_113504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1761 ⟨113504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1761
    ⟨113504, by decide⟩ (by decide) (![⟨113325, by decide⟩,⟨113390, by decide⟩,⟨113445, by decide⟩,⟨113503, by decide⟩]) unmarked_context_11_1761_113504 node_context_11_1761_113504
  intro a
  fin_cases a
  · exact context_12_7044_113325
  · exact context_12_7045_113390
  · exact context_12_7046_113445
  · exact context_12_7047_113503

theorem selected_cut_03649 : selected 9 ⟨113535, by decide⟩
    (prefixPartial 12 7048) = some ⟨12, 2, 0, 113535, 7048, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_7048_113535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7048 ⟨113535, by decide⟩ :=
  accepted_of_selected 12 7048 ⟨113535, by decide⟩ ⟨12, 2, 0, 113535, 7048, 2621, 65536⟩
    (by decide) selected_cut_03649

theorem selected_cut_03650 : selected 9 ⟨113590, by decide⟩
    (prefixPartial 12 7049) = some ⟨12, 2, 0, 113590, 7049, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_7049_113590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7049 ⟨113590, by decide⟩ :=
  accepted_of_selected 12 7049 ⟨113590, by decide⟩ ⟨12, 2, 0, 113590, 7049, 3189, 65536⟩
    (by decide) selected_cut_03650

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
