/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover006
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00674 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1580) = some ⟨12, 1, 0, 26677, 1580, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1580_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1580 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1580 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1580, 1, 65536⟩
    (by decide) selected_cut_00674

theorem selected_cut_00675 : selected 8 ⟨28667, by decide⟩
    (prefixPartial 13 6324) = some ⟨13, 2, 0, 28667, 6324, 297, 16384⟩ := by
  decide +kernel

theorem context_13_6324_28667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6324 ⟨28667, by decide⟩ :=
  accepted_of_selected 13 6324 ⟨28667, by decide⟩ ⟨13, 2, 0, 28667, 6324, 297, 16384⟩
    (by decide) selected_cut_00675

theorem selected_cut_00676 : selected 8 ⟨28726, by decide⟩
    (prefixPartial 13 6325) = some ⟨13, 2, 0, 28726, 6325, 3261, 16384⟩ := by
  decide +kernel

theorem context_13_6325_28726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6325 ⟨28726, by decide⟩ :=
  accepted_of_selected 13 6325 ⟨28726, by decide⟩ ⟨13, 2, 0, 28726, 6325, 3261, 16384⟩
    (by decide) selected_cut_00676

theorem selected_cut_00677 : selected 8 ⟨1982, by decide⟩
    (prefixPartial 13 6326) = some ⟨13, 1, 0, 1982, 6326, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6326_1982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6326 ⟨1982, by decide⟩ :=
  accepted_of_selected 13 6326 ⟨1982, by decide⟩ ⟨13, 1, 0, 1982, 6326, 1, 16384⟩
    (by decide) selected_cut_00677

theorem selected_cut_00678 : selected 8 ⟨28739, by decide⟩
    (prefixPartial 13 6327) = some ⟨13, 2, 0, 28739, 6327, 745, 16384⟩ := by
  decide +kernel

theorem context_13_6327_28739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6327 ⟨28739, by decide⟩ :=
  accepted_of_selected 13 6327 ⟨28739, by decide⟩ ⟨13, 2, 0, 28739, 6327, 745, 16384⟩
    (by decide) selected_cut_00678

theorem unmarked_context_12_1581_28740 : frontier 9 ⟨28740, by decide⟩
    (prefixCache 12 1581) (prefixPartial 12 1581) = false := by
  decide +kernel

theorem node_context_12_1581_28740 : EJMOriginalGlobalDAGData.nodes 9 ⟨28740, by decide⟩ =
    .split (coordinate 12) (![⟨28667, by decide⟩,⟨28726, by decide⟩,⟨1982, by decide⟩,⟨28739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1581_28740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1581 ⟨28740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1581
    ⟨28740, by decide⟩ (by decide) (![⟨28667, by decide⟩,⟨28726, by decide⟩,⟨1982, by decide⟩,⟨28739, by decide⟩]) unmarked_context_12_1581_28740 node_context_12_1581_28740
  intro a
  fin_cases a
  · exact context_13_6324_28667
  · exact context_13_6325_28726
  · exact context_13_6326_1982
  · exact context_13_6327_28739

theorem selected_cut_00679 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1582) = some ⟨12, 1, 0, 26677, 1582, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1582_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1582 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1582 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1582, 1, 65536⟩
    (by decide) selected_cut_00679

theorem selected_cut_00680 : selected 8 ⟨28750, by decide⟩
    (prefixPartial 13 6332) = some ⟨13, 2, 0, 28750, 6332, 357, 16384⟩ := by
  decide +kernel

theorem context_13_6332_28750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6332 ⟨28750, by decide⟩ :=
  accepted_of_selected 13 6332 ⟨28750, by decide⟩ ⟨13, 2, 0, 28750, 6332, 357, 16384⟩
    (by decide) selected_cut_00680

theorem selected_cut_00681 : selected 8 ⟨28793, by decide⟩
    (prefixPartial 13 6333) = some ⟨13, 2, 0, 28793, 6333, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_6333_28793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6333 ⟨28793, by decide⟩ :=
  accepted_of_selected 13 6333 ⟨28793, by decide⟩ ⟨13, 2, 0, 28793, 6333, 2889, 16384⟩
    (by decide) selected_cut_00681

theorem selected_cut_00682 : selected 8 ⟨28821, by decide⟩
    (prefixPartial 13 6334) = some ⟨13, 2, 0, 28821, 6334, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_6334_28821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6334 ⟨28821, by decide⟩ :=
  accepted_of_selected 13 6334 ⟨28821, by decide⟩ ⟨13, 2, 0, 28821, 6334, 1929, 16384⟩
    (by decide) selected_cut_00682

theorem selected_cut_00683 : selected 8 ⟨28832, by decide⟩
    (prefixPartial 13 6335) = some ⟨13, 2, 0, 28832, 6335, 901, 16384⟩ := by
  decide +kernel

theorem context_13_6335_28832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6335 ⟨28832, by decide⟩ :=
  accepted_of_selected 13 6335 ⟨28832, by decide⟩ ⟨13, 2, 0, 28832, 6335, 901, 16384⟩
    (by decide) selected_cut_00683

theorem unmarked_context_12_1583_28833 : frontier 9 ⟨28833, by decide⟩
    (prefixCache 12 1583) (prefixPartial 12 1583) = false := by
  decide +kernel

theorem node_context_12_1583_28833 : EJMOriginalGlobalDAGData.nodes 9 ⟨28833, by decide⟩ =
    .split (coordinate 12) (![⟨28750, by decide⟩,⟨28793, by decide⟩,⟨28821, by decide⟩,⟨28832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1583_28833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1583 ⟨28833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1583
    ⟨28833, by decide⟩ (by decide) (![⟨28750, by decide⟩,⟨28793, by decide⟩,⟨28821, by decide⟩,⟨28832, by decide⟩]) unmarked_context_12_1583_28833 node_context_12_1583_28833
  intro a
  fin_cases a
  · exact context_13_6332_28750
  · exact context_13_6333_28793
  · exact context_13_6334_28821
  · exact context_13_6335_28832

theorem unmarked_context_11_395_28834 : frontier 10 ⟨28834, by decide⟩
    (prefixCache 11 395) (prefixPartial 11 395) = false := by
  decide +kernel

theorem node_context_11_395_28834 : EJMOriginalGlobalDAGData.nodes 10 ⟨28834, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨28740, by decide⟩,⟨26677, by decide⟩,⟨28833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_395_28834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 395 ⟨28834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 395
    ⟨28834, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨28740, by decide⟩,⟨26677, by decide⟩,⟨28833, by decide⟩]) unmarked_context_11_395_28834 node_context_11_395_28834
  intro a
  fin_cases a
  · exact context_12_1580_26677
  · exact context_12_1581_28740
  · exact context_12_1582_26677
  · exact context_12_1583_28833

theorem unmarked_context_10_98_28835 : frontier 11 ⟨28835, by decide⟩
    (prefixCache 10 98) (prefixPartial 10 98) = false := by
  decide +kernel

theorem node_context_10_98_28835 : EJMOriginalGlobalDAGData.nodes 11 ⟨28835, by decide⟩ =
    .split (coordinate 10) (![⟨28340, by decide⟩,⟨28555, by decide⟩,⟨28655, by decide⟩,⟨28834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_98_28835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 98 ⟨28835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 98
    ⟨28835, by decide⟩ (by decide) (![⟨28340, by decide⟩,⟨28555, by decide⟩,⟨28655, by decide⟩,⟨28834, by decide⟩]) unmarked_context_10_98_28835 node_context_10_98_28835
  intro a
  fin_cases a
  · exact context_11_392_28340
  · exact context_11_393_28555
  · exact context_11_394_28655
  · exact context_11_395_28834

theorem selected_cut_00684 : selected 10 ⟨28904, by decide⟩
    (prefixPartial 11 396) = some ⟨11, 2, 0, 28904, 396, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_396_28904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 396 ⟨28904, by decide⟩ :=
  accepted_of_selected 11 396 ⟨28904, by decide⟩ ⟨11, 2, 0, 28904, 396, 3205, 262144⟩
    (by decide) selected_cut_00684

theorem selected_cut_00685 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1588) = some ⟨12, 1, 0, 26677, 1588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1588_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1588 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1588 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1588, 1, 65536⟩
    (by decide) selected_cut_00685

theorem selected_cut_00686 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1589) = some ⟨12, 1, 0, 26677, 1589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1589_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1589 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1589 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1589, 1, 65536⟩
    (by decide) selected_cut_00686

theorem selected_cut_00687 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1590) = some ⟨12, 1, 0, 26677, 1590, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1590_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1590 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1590 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1590, 1, 65536⟩
    (by decide) selected_cut_00687

theorem selected_cut_00688 : selected 8 ⟨28918, by decide⟩
    (prefixPartial 13 6364) = some ⟨13, 2, 0, 28918, 6364, 257, 16384⟩ := by
  decide +kernel

theorem context_13_6364_28918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6364 ⟨28918, by decide⟩ :=
  accepted_of_selected 13 6364 ⟨28918, by decide⟩ ⟨13, 2, 0, 28918, 6364, 257, 16384⟩
    (by decide) selected_cut_00688

theorem selected_cut_00689 : selected 8 ⟨28976, by decide⟩
    (prefixPartial 13 6365) = some ⟨13, 2, 0, 28976, 6365, 3413, 16384⟩ := by
  decide +kernel

theorem context_13_6365_28976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6365 ⟨28976, by decide⟩ :=
  accepted_of_selected 13 6365 ⟨28976, by decide⟩ ⟨13, 2, 0, 28976, 6365, 3413, 16384⟩
    (by decide) selected_cut_00689

theorem selected_cut_00690 : selected 8 ⟨29013, by decide⟩
    (prefixPartial 13 6366) = some ⟨13, 2, 0, 29013, 6366, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_6366_29013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6366 ⟨29013, by decide⟩ :=
  accepted_of_selected 13 6366 ⟨29013, by decide⟩ ⟨13, 2, 0, 29013, 6366, 2185, 16384⟩
    (by decide) selected_cut_00690

theorem selected_cut_00691 : selected 8 ⟨29029, by decide⟩
    (prefixPartial 13 6367) = some ⟨13, 2, 0, 29029, 6367, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_6367_29029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6367 ⟨29029, by decide⟩ :=
  accepted_of_selected 13 6367 ⟨29029, by decide⟩ ⟨13, 2, 0, 29029, 6367, 1021, 16384⟩
    (by decide) selected_cut_00691

theorem unmarked_context_12_1591_29030 : frontier 9 ⟨29030, by decide⟩
    (prefixCache 12 1591) (prefixPartial 12 1591) = false := by
  decide +kernel

theorem node_context_12_1591_29030 : EJMOriginalGlobalDAGData.nodes 9 ⟨29030, by decide⟩ =
    .split (coordinate 12) (![⟨28918, by decide⟩,⟨28976, by decide⟩,⟨29013, by decide⟩,⟨29029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1591_29030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1591 ⟨29030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1591
    ⟨29030, by decide⟩ (by decide) (![⟨28918, by decide⟩,⟨28976, by decide⟩,⟨29013, by decide⟩,⟨29029, by decide⟩]) unmarked_context_12_1591_29030 node_context_12_1591_29030
  intro a
  fin_cases a
  · exact context_13_6364_28918
  · exact context_13_6365_28976
  · exact context_13_6366_29013
  · exact context_13_6367_29029

theorem unmarked_context_11_397_29031 : frontier 10 ⟨29031, by decide⟩
    (prefixCache 11 397) (prefixPartial 11 397) = false := by
  decide +kernel

theorem node_context_11_397_29031 : EJMOriginalGlobalDAGData.nodes 10 ⟨29031, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨26677, by decide⟩,⟨26677, by decide⟩,⟨29030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_397_29031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 397 ⟨29031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 397
    ⟨29031, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨26677, by decide⟩,⟨26677, by decide⟩,⟨29030, by decide⟩]) unmarked_context_11_397_29031 node_context_11_397_29031
  intro a
  fin_cases a
  · exact context_12_1588_26677
  · exact context_12_1589_26677
  · exact context_12_1590_26677
  · exact context_12_1591_29030

theorem selected_cut_00692 : selected 10 ⟨29032, by decide⟩
    (prefixPartial 11 398) = some ⟨11, 2, 0, 29032, 398, 5, 262144⟩ := by
  decide +kernel

theorem context_11_398_29032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 398 ⟨29032, by decide⟩ :=
  accepted_of_selected 11 398 ⟨29032, by decide⟩ ⟨11, 2, 0, 29032, 398, 5, 262144⟩
    (by decide) selected_cut_00692

theorem selected_cut_00693 : selected 10 ⟨29101, by decide⟩
    (prefixPartial 11 399) = some ⟨11, 2, 0, 29101, 399, 3493, 262144⟩ := by
  decide +kernel

theorem context_11_399_29101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 399 ⟨29101, by decide⟩ :=
  accepted_of_selected 11 399 ⟨29101, by decide⟩ ⟨11, 2, 0, 29101, 399, 3493, 262144⟩
    (by decide) selected_cut_00693

theorem unmarked_context_10_99_29102 : frontier 11 ⟨29102, by decide⟩
    (prefixCache 10 99) (prefixPartial 10 99) = false := by
  decide +kernel

theorem node_context_10_99_29102 : EJMOriginalGlobalDAGData.nodes 11 ⟨29102, by decide⟩ =
    .split (coordinate 10) (![⟨28904, by decide⟩,⟨29031, by decide⟩,⟨29032, by decide⟩,⟨29101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_99_29102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 99 ⟨29102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 99
    ⟨29102, by decide⟩ (by decide) (![⟨28904, by decide⟩,⟨29031, by decide⟩,⟨29032, by decide⟩,⟨29101, by decide⟩]) unmarked_context_10_99_29102 node_context_10_99_29102
  intro a
  fin_cases a
  · exact context_11_396_28904
  · exact context_11_397_29031
  · exact context_11_398_29032
  · exact context_11_399_29101

theorem unmarked_context_9_24_29103 : frontier 12 ⟨29103, by decide⟩
    (prefixCache 9 24) (prefixPartial 9 24) = false := by
  decide +kernel

theorem node_context_9_24_29103 : EJMOriginalGlobalDAGData.nodes 12 ⟨29103, by decide⟩ =
    .split (coordinate 9) (![⟨26676, by decide⟩,⟨28172, by decide⟩,⟨28835, by decide⟩,⟨29102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_24_29103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 24 ⟨29103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 24
    ⟨29103, by decide⟩ (by decide) (![⟨26676, by decide⟩,⟨28172, by decide⟩,⟨28835, by decide⟩,⟨29102, by decide⟩]) unmarked_context_9_24_29103 node_context_9_24_29103
  intro a
  fin_cases a
  · exact context_10_96_26676
  · exact context_10_97_28172
  · exact context_10_98_28835
  · exact context_10_99_29102

theorem selected_cut_00694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6400) = some ⟨13, 1, 0, 3444, 6400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6400, 1, 16384⟩
    (by decide) selected_cut_00694

theorem selected_cut_00695 : selected 8 ⟨29141, by decide⟩
    (prefixPartial 13 6401) = some ⟨13, 2, 0, 29141, 6401, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_6401_29141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6401 ⟨29141, by decide⟩ :=
  accepted_of_selected 13 6401 ⟨29141, by decide⟩ ⟨13, 2, 0, 29141, 6401, 2269, 16384⟩
    (by decide) selected_cut_00695

theorem selected_cut_00696 : selected 8 ⟨29174, by decide⟩
    (prefixPartial 13 6402) = some ⟨13, 2, 0, 29174, 6402, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_6402_29174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6402 ⟨29174, by decide⟩ :=
  accepted_of_selected 13 6402 ⟨29174, by decide⟩ ⟨13, 2, 0, 29174, 6402, 2021, 16384⟩
    (by decide) selected_cut_00696

theorem selected_cut_00697 : selected 8 ⟨29187, by decide⟩
    (prefixPartial 13 6403) = some ⟨13, 2, 0, 29187, 6403, 921, 16384⟩ := by
  decide +kernel

theorem context_13_6403_29187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6403 ⟨29187, by decide⟩ :=
  accepted_of_selected 13 6403 ⟨29187, by decide⟩ ⟨13, 2, 0, 29187, 6403, 921, 16384⟩
    (by decide) selected_cut_00697

theorem unmarked_context_12_1600_29188 : frontier 9 ⟨29188, by decide⟩
    (prefixCache 12 1600) (prefixPartial 12 1600) = false := by
  decide +kernel

theorem node_context_12_1600_29188 : EJMOriginalGlobalDAGData.nodes 9 ⟨29188, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29141, by decide⟩,⟨29174, by decide⟩,⟨29187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1600_29188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1600 ⟨29188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1600
    ⟨29188, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29141, by decide⟩,⟨29174, by decide⟩,⟨29187, by decide⟩]) unmarked_context_12_1600_29188 node_context_12_1600_29188
  intro a
  fin_cases a
  · exact context_13_6400_3444
  · exact context_13_6401_29141
  · exact context_13_6402_29174
  · exact context_13_6403_29187

theorem selected_cut_00698 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6404) = some ⟨13, 1, 0, 3444, 6404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6404, 1, 16384⟩
    (by decide) selected_cut_00698

theorem selected_cut_00699 : selected 8 ⟨29221, by decide⟩
    (prefixPartial 13 6405) = some ⟨13, 2, 0, 29221, 6405, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_6405_29221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6405 ⟨29221, by decide⟩ :=
  accepted_of_selected 13 6405 ⟨29221, by decide⟩ ⟨13, 2, 0, 29221, 6405, 2149, 16384⟩
    (by decide) selected_cut_00699

theorem selected_cut_00700 : selected 8 ⟨29245, by decide⟩
    (prefixPartial 13 6406) = some ⟨13, 2, 0, 29245, 6406, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_6406_29245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6406 ⟨29245, by decide⟩ :=
  accepted_of_selected 13 6406 ⟨29245, by decide⟩ ⟨13, 2, 0, 29245, 6406, 1629, 16384⟩
    (by decide) selected_cut_00700

theorem selected_cut_00701 : selected 8 ⟨29262, by decide⟩
    (prefixPartial 13 6407) = some ⟨13, 2, 0, 29262, 6407, 961, 16384⟩ := by
  decide +kernel

theorem context_13_6407_29262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6407 ⟨29262, by decide⟩ :=
  accepted_of_selected 13 6407 ⟨29262, by decide⟩ ⟨13, 2, 0, 29262, 6407, 961, 16384⟩
    (by decide) selected_cut_00701

theorem unmarked_context_12_1601_29263 : frontier 9 ⟨29263, by decide⟩
    (prefixCache 12 1601) (prefixPartial 12 1601) = false := by
  decide +kernel

theorem node_context_12_1601_29263 : EJMOriginalGlobalDAGData.nodes 9 ⟨29263, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29221, by decide⟩,⟨29245, by decide⟩,⟨29262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1601_29263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1601 ⟨29263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1601
    ⟨29263, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29221, by decide⟩,⟨29245, by decide⟩,⟨29262, by decide⟩]) unmarked_context_12_1601_29263 node_context_12_1601_29263
  intro a
  fin_cases a
  · exact context_13_6404_3444
  · exact context_13_6405_29221
  · exact context_13_6406_29245
  · exact context_13_6407_29262

theorem selected_cut_00702 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6408) = some ⟨13, 1, 0, 3444, 6408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6408, 1, 16384⟩
    (by decide) selected_cut_00702

theorem selected_cut_00703 : selected 8 ⟨29298, by decide⟩
    (prefixPartial 13 6409) = some ⟨13, 2, 0, 29298, 6409, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_6409_29298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6409 ⟨29298, by decide⟩ :=
  accepted_of_selected 13 6409 ⟨29298, by decide⟩ ⟨13, 2, 0, 29298, 6409, 2241, 16384⟩
    (by decide) selected_cut_00703

theorem selected_cut_00704 : selected 8 ⟨29323, by decide⟩
    (prefixPartial 13 6410) = some ⟨13, 2, 0, 29323, 6410, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_6410_29323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6410 ⟨29323, by decide⟩ :=
  accepted_of_selected 13 6410 ⟨29323, by decide⟩ ⟨13, 2, 0, 29323, 6410, 1637, 16384⟩
    (by decide) selected_cut_00704

theorem selected_cut_00705 : selected 8 ⟨29336, by decide⟩
    (prefixPartial 13 6411) = some ⟨13, 2, 0, 29336, 6411, 949, 16384⟩ := by
  decide +kernel

theorem context_13_6411_29336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6411 ⟨29336, by decide⟩ :=
  accepted_of_selected 13 6411 ⟨29336, by decide⟩ ⟨13, 2, 0, 29336, 6411, 949, 16384⟩
    (by decide) selected_cut_00705

theorem unmarked_context_12_1602_29337 : frontier 9 ⟨29337, by decide⟩
    (prefixCache 12 1602) (prefixPartial 12 1602) = false := by
  decide +kernel

theorem node_context_12_1602_29337 : EJMOriginalGlobalDAGData.nodes 9 ⟨29337, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29298, by decide⟩,⟨29323, by decide⟩,⟨29336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1602_29337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1602 ⟨29337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1602
    ⟨29337, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29298, by decide⟩,⟨29323, by decide⟩,⟨29336, by decide⟩]) unmarked_context_12_1602_29337 node_context_12_1602_29337
  intro a
  fin_cases a
  · exact context_13_6408_3444
  · exact context_13_6409_29298
  · exact context_13_6410_29323
  · exact context_13_6411_29336

theorem selected_cut_00706 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6412) = some ⟨13, 1, 0, 3444, 6412, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6412_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6412 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6412 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6412, 1, 16384⟩
    (by decide) selected_cut_00706

theorem selected_cut_00707 : selected 8 ⟨29374, by decide⟩
    (prefixPartial 13 6413) = some ⟨13, 2, 0, 29374, 6413, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_6413_29374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6413 ⟨29374, by decide⟩ :=
  accepted_of_selected 13 6413 ⟨29374, by decide⟩ ⟨13, 2, 0, 29374, 6413, 2413, 16384⟩
    (by decide) selected_cut_00707

theorem selected_cut_00708 : selected 8 ⟨29401, by decide⟩
    (prefixPartial 13 6414) = some ⟨13, 2, 0, 29401, 6414, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_6414_29401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6414 ⟨29401, by decide⟩ :=
  accepted_of_selected 13 6414 ⟨29401, by decide⟩ ⟨13, 2, 0, 29401, 6414, 1801, 16384⟩
    (by decide) selected_cut_00708

theorem selected_cut_00709 : selected 8 ⟨29414, by decide⟩
    (prefixPartial 13 6415) = some ⟨13, 2, 0, 29414, 6415, 929, 16384⟩ := by
  decide +kernel

theorem context_13_6415_29414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6415 ⟨29414, by decide⟩ :=
  accepted_of_selected 13 6415 ⟨29414, by decide⟩ ⟨13, 2, 0, 29414, 6415, 929, 16384⟩
    (by decide) selected_cut_00709

theorem unmarked_context_12_1603_29415 : frontier 9 ⟨29415, by decide⟩
    (prefixCache 12 1603) (prefixPartial 12 1603) = false := by
  decide +kernel

theorem node_context_12_1603_29415 : EJMOriginalGlobalDAGData.nodes 9 ⟨29415, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29374, by decide⟩,⟨29401, by decide⟩,⟨29414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1603_29415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1603 ⟨29415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1603
    ⟨29415, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29374, by decide⟩,⟨29401, by decide⟩,⟨29414, by decide⟩]) unmarked_context_12_1603_29415 node_context_12_1603_29415
  intro a
  fin_cases a
  · exact context_13_6412_3444
  · exact context_13_6413_29374
  · exact context_13_6414_29401
  · exact context_13_6415_29414

theorem unmarked_context_11_400_29416 : frontier 10 ⟨29416, by decide⟩
    (prefixCache 11 400) (prefixPartial 11 400) = false := by
  decide +kernel

theorem node_context_11_400_29416 : EJMOriginalGlobalDAGData.nodes 10 ⟨29416, by decide⟩ =
    .split (coordinate 11) (![⟨29188, by decide⟩,⟨29263, by decide⟩,⟨29337, by decide⟩,⟨29415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_400_29416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 400 ⟨29416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 400
    ⟨29416, by decide⟩ (by decide) (![⟨29188, by decide⟩,⟨29263, by decide⟩,⟨29337, by decide⟩,⟨29415, by decide⟩]) unmarked_context_11_400_29416 node_context_11_400_29416
  intro a
  fin_cases a
  · exact context_12_1600_29188
  · exact context_12_1601_29263
  · exact context_12_1602_29337
  · exact context_12_1603_29415

theorem selected_cut_00710 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6416) = some ⟨13, 1, 0, 3444, 6416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6416, 1, 16384⟩
    (by decide) selected_cut_00710

theorem selected_cut_00711 : selected 8 ⟨29442, by decide⟩
    (prefixPartial 13 6417) = some ⟨13, 2, 0, 29442, 6417, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_6417_29442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6417 ⟨29442, by decide⟩ :=
  accepted_of_selected 13 6417 ⟨29442, by decide⟩ ⟨13, 2, 0, 29442, 6417, 1949, 16384⟩
    (by decide) selected_cut_00711

theorem selected_cut_00712 : selected 8 ⟨29471, by decide⟩
    (prefixPartial 13 6418) = some ⟨13, 2, 0, 29471, 6418, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_6418_29471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6418 ⟨29471, by decide⟩ :=
  accepted_of_selected 13 6418 ⟨29471, by decide⟩ ⟨13, 2, 0, 29471, 6418, 1829, 16384⟩
    (by decide) selected_cut_00712

theorem selected_cut_00713 : selected 8 ⟨29487, by decide⟩
    (prefixPartial 13 6419) = some ⟨13, 2, 0, 29487, 6419, 909, 16384⟩ := by
  decide +kernel

theorem context_13_6419_29487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6419 ⟨29487, by decide⟩ :=
  accepted_of_selected 13 6419 ⟨29487, by decide⟩ ⟨13, 2, 0, 29487, 6419, 909, 16384⟩
    (by decide) selected_cut_00713

theorem unmarked_context_12_1604_29488 : frontier 9 ⟨29488, by decide⟩
    (prefixCache 12 1604) (prefixPartial 12 1604) = false := by
  decide +kernel

theorem node_context_12_1604_29488 : EJMOriginalGlobalDAGData.nodes 9 ⟨29488, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29442, by decide⟩,⟨29471, by decide⟩,⟨29487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1604_29488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1604 ⟨29488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1604
    ⟨29488, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29442, by decide⟩,⟨29471, by decide⟩,⟨29487, by decide⟩]) unmarked_context_12_1604_29488 node_context_12_1604_29488
  intro a
  fin_cases a
  · exact context_13_6416_3444
  · exact context_13_6417_29442
  · exact context_13_6418_29471
  · exact context_13_6419_29487

theorem selected_cut_00714 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6420) = some ⟨13, 1, 0, 3444, 6420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6420, 1, 16384⟩
    (by decide) selected_cut_00714

theorem selected_cut_00715 : selected 8 ⟨29517, by decide⟩
    (prefixPartial 13 6421) = some ⟨13, 2, 0, 29517, 6421, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_6421_29517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6421 ⟨29517, by decide⟩ :=
  accepted_of_selected 13 6421 ⟨29517, by decide⟩ ⟨13, 2, 0, 29517, 6421, 1913, 16384⟩
    (by decide) selected_cut_00715

theorem selected_cut_00716 : selected 8 ⟨29545, by decide⟩
    (prefixPartial 13 6422) = some ⟨13, 2, 0, 29545, 6422, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_6422_29545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6422 ⟨29545, by decide⟩ :=
  accepted_of_selected 13 6422 ⟨29545, by decide⟩ ⟨13, 2, 0, 29545, 6422, 1581, 16384⟩
    (by decide) selected_cut_00716

theorem selected_cut_00717 : selected 8 ⟨29558, by decide⟩
    (prefixPartial 13 6423) = some ⟨13, 2, 0, 29558, 6423, 949, 16384⟩ := by
  decide +kernel

theorem context_13_6423_29558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6423 ⟨29558, by decide⟩ :=
  accepted_of_selected 13 6423 ⟨29558, by decide⟩ ⟨13, 2, 0, 29558, 6423, 949, 16384⟩
    (by decide) selected_cut_00717

theorem unmarked_context_12_1605_29559 : frontier 9 ⟨29559, by decide⟩
    (prefixCache 12 1605) (prefixPartial 12 1605) = false := by
  decide +kernel

theorem node_context_12_1605_29559 : EJMOriginalGlobalDAGData.nodes 9 ⟨29559, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29517, by decide⟩,⟨29545, by decide⟩,⟨29558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1605_29559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1605 ⟨29559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1605
    ⟨29559, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29517, by decide⟩,⟨29545, by decide⟩,⟨29558, by decide⟩]) unmarked_context_12_1605_29559 node_context_12_1605_29559
  intro a
  fin_cases a
  · exact context_13_6420_3444
  · exact context_13_6421_29517
  · exact context_13_6422_29545
  · exact context_13_6423_29558

theorem selected_cut_00718 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6424) = some ⟨13, 1, 0, 3444, 6424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6424, 1, 16384⟩
    (by decide) selected_cut_00718

theorem selected_cut_00719 : selected 8 ⟨29595, by decide⟩
    (prefixPartial 13 6425) = some ⟨13, 2, 0, 29595, 6425, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_6425_29595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6425 ⟨29595, by decide⟩ :=
  accepted_of_selected 13 6425 ⟨29595, by decide⟩ ⟨13, 2, 0, 29595, 6425, 2185, 16384⟩
    (by decide) selected_cut_00719

theorem selected_cut_00720 : selected 8 ⟨29621, by decide⟩
    (prefixPartial 13 6426) = some ⟨13, 2, 0, 29621, 6426, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_6426_29621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6426 ⟨29621, by decide⟩ :=
  accepted_of_selected 13 6426 ⟨29621, by decide⟩ ⟨13, 2, 0, 29621, 6426, 1853, 16384⟩
    (by decide) selected_cut_00720

theorem selected_cut_00721 : selected 8 ⟨29636, by decide⟩
    (prefixPartial 13 6427) = some ⟨13, 2, 0, 29636, 6427, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_6427_29636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6427 ⟨29636, by decide⟩ :=
  accepted_of_selected 13 6427 ⟨29636, by decide⟩ ⟨13, 2, 0, 29636, 6427, 1069, 16384⟩
    (by decide) selected_cut_00721

theorem unmarked_context_12_1606_29637 : frontier 9 ⟨29637, by decide⟩
    (prefixCache 12 1606) (prefixPartial 12 1606) = false := by
  decide +kernel

theorem node_context_12_1606_29637 : EJMOriginalGlobalDAGData.nodes 9 ⟨29637, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29595, by decide⟩,⟨29621, by decide⟩,⟨29636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1606_29637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1606 ⟨29637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1606
    ⟨29637, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29595, by decide⟩,⟨29621, by decide⟩,⟨29636, by decide⟩]) unmarked_context_12_1606_29637 node_context_12_1606_29637
  intro a
  fin_cases a
  · exact context_13_6424_3444
  · exact context_13_6425_29595
  · exact context_13_6426_29621
  · exact context_13_6427_29636

theorem selected_cut_00722 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6428) = some ⟨13, 1, 0, 3444, 6428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6428, 1, 16384⟩
    (by decide) selected_cut_00722

theorem selected_cut_00723 : selected 8 ⟨29675, by decide⟩
    (prefixPartial 13 6429) = some ⟨13, 2, 0, 29675, 6429, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_6429_29675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6429 ⟨29675, by decide⟩ :=
  accepted_of_selected 13 6429 ⟨29675, by decide⟩ ⟨13, 2, 0, 29675, 6429, 2313, 16384⟩
    (by decide) selected_cut_00723

theorem selected_cut_00724 : selected 8 ⟨29713, by decide⟩
    (prefixPartial 13 6430) = some ⟨13, 2, 0, 29713, 6430, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_6430_29713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6430 ⟨29713, by decide⟩ :=
  accepted_of_selected 13 6430 ⟨29713, by decide⟩ ⟨13, 2, 0, 29713, 6430, 2073, 16384⟩
    (by decide) selected_cut_00724

theorem selected_cut_00725 : selected 8 ⟨29729, by decide⟩
    (prefixPartial 13 6431) = some ⟨13, 2, 0, 29729, 6431, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_6431_29729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6431 ⟨29729, by decide⟩ :=
  accepted_of_selected 13 6431 ⟨29729, by decide⟩ ⟨13, 2, 0, 29729, 6431, 1145, 16384⟩
    (by decide) selected_cut_00725

theorem unmarked_context_12_1607_29730 : frontier 9 ⟨29730, by decide⟩
    (prefixCache 12 1607) (prefixPartial 12 1607) = false := by
  decide +kernel

theorem node_context_12_1607_29730 : EJMOriginalGlobalDAGData.nodes 9 ⟨29730, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29675, by decide⟩,⟨29713, by decide⟩,⟨29729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1607_29730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1607 ⟨29730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1607
    ⟨29730, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29675, by decide⟩,⟨29713, by decide⟩,⟨29729, by decide⟩]) unmarked_context_12_1607_29730 node_context_12_1607_29730
  intro a
  fin_cases a
  · exact context_13_6428_3444
  · exact context_13_6429_29675
  · exact context_13_6430_29713
  · exact context_13_6431_29729

theorem unmarked_context_11_401_29731 : frontier 10 ⟨29731, by decide⟩
    (prefixCache 11 401) (prefixPartial 11 401) = false := by
  decide +kernel

theorem node_context_11_401_29731 : EJMOriginalGlobalDAGData.nodes 10 ⟨29731, by decide⟩ =
    .split (coordinate 11) (![⟨29488, by decide⟩,⟨29559, by decide⟩,⟨29637, by decide⟩,⟨29730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_401_29731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 401 ⟨29731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 401
    ⟨29731, by decide⟩ (by decide) (![⟨29488, by decide⟩,⟨29559, by decide⟩,⟨29637, by decide⟩,⟨29730, by decide⟩]) unmarked_context_11_401_29731 node_context_11_401_29731
  intro a
  fin_cases a
  · exact context_12_1604_29488
  · exact context_12_1605_29559
  · exact context_12_1606_29637
  · exact context_12_1607_29730

theorem selected_cut_00726 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6432) = some ⟨13, 1, 0, 3444, 6432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6432, 1, 16384⟩
    (by decide) selected_cut_00726

theorem selected_cut_00727 : selected 8 ⟨29759, by decide⟩
    (prefixPartial 13 6433) = some ⟨13, 2, 0, 29759, 6433, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_6433_29759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6433 ⟨29759, by decide⟩ :=
  accepted_of_selected 13 6433 ⟨29759, by decide⟩ ⟨13, 2, 0, 29759, 6433, 2069, 16384⟩
    (by decide) selected_cut_00727

theorem selected_cut_00728 : selected 8 ⟨29783, by decide⟩
    (prefixPartial 13 6434) = some ⟨13, 2, 0, 29783, 6434, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_6434_29783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6434 ⟨29783, by decide⟩ :=
  accepted_of_selected 13 6434 ⟨29783, by decide⟩ ⟨13, 2, 0, 29783, 6434, 1677, 16384⟩
    (by decide) selected_cut_00728

theorem selected_cut_00729 : selected 8 ⟨29797, by decide⟩
    (prefixPartial 13 6435) = some ⟨13, 2, 0, 29797, 6435, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_6435_29797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6435 ⟨29797, by decide⟩ :=
  accepted_of_selected 13 6435 ⟨29797, by decide⟩ ⟨13, 2, 0, 29797, 6435, 1025, 16384⟩
    (by decide) selected_cut_00729

theorem unmarked_context_12_1608_29798 : frontier 9 ⟨29798, by decide⟩
    (prefixCache 12 1608) (prefixPartial 12 1608) = false := by
  decide +kernel

theorem node_context_12_1608_29798 : EJMOriginalGlobalDAGData.nodes 9 ⟨29798, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29759, by decide⟩,⟨29783, by decide⟩,⟨29797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1608_29798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1608 ⟨29798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1608
    ⟨29798, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29759, by decide⟩,⟨29783, by decide⟩,⟨29797, by decide⟩]) unmarked_context_12_1608_29798 node_context_12_1608_29798
  intro a
  fin_cases a
  · exact context_13_6432_3444
  · exact context_13_6433_29759
  · exact context_13_6434_29783
  · exact context_13_6435_29797

theorem selected_cut_00730 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6436) = some ⟨13, 1, 0, 3444, 6436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6436, 1, 16384⟩
    (by decide) selected_cut_00730

theorem selected_cut_00731 : selected 8 ⟨29829, by decide⟩
    (prefixPartial 13 6437) = some ⟨13, 2, 0, 29829, 6437, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_6437_29829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6437 ⟨29829, by decide⟩ :=
  accepted_of_selected 13 6437 ⟨29829, by decide⟩ ⟨13, 2, 0, 29829, 6437, 2253, 16384⟩
    (by decide) selected_cut_00731

theorem selected_cut_00732 : selected 8 ⟨29855, by decide⟩
    (prefixPartial 13 6438) = some ⟨13, 2, 0, 29855, 6438, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_6438_29855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6438 ⟨29855, by decide⟩ :=
  accepted_of_selected 13 6438 ⟨29855, by decide⟩ ⟨13, 2, 0, 29855, 6438, 1757, 16384⟩
    (by decide) selected_cut_00732

theorem selected_cut_00733 : selected 8 ⟨29869, by decide⟩
    (prefixPartial 13 6439) = some ⟨13, 2, 0, 29869, 6439, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_6439_29869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6439 ⟨29869, by decide⟩ :=
  accepted_of_selected 13 6439 ⟨29869, by decide⟩ ⟨13, 2, 0, 29869, 6439, 1077, 16384⟩
    (by decide) selected_cut_00733

theorem unmarked_context_12_1609_29870 : frontier 9 ⟨29870, by decide⟩
    (prefixCache 12 1609) (prefixPartial 12 1609) = false := by
  decide +kernel

theorem node_context_12_1609_29870 : EJMOriginalGlobalDAGData.nodes 9 ⟨29870, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29829, by decide⟩,⟨29855, by decide⟩,⟨29869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1609_29870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1609 ⟨29870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1609
    ⟨29870, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29829, by decide⟩,⟨29855, by decide⟩,⟨29869, by decide⟩]) unmarked_context_12_1609_29870 node_context_12_1609_29870
  intro a
  fin_cases a
  · exact context_13_6436_3444
  · exact context_13_6437_29829
  · exact context_13_6438_29855
  · exact context_13_6439_29869

theorem selected_cut_00734 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6440) = some ⟨13, 1, 0, 3444, 6440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6440, 1, 16384⟩
    (by decide) selected_cut_00734

theorem selected_cut_00735 : selected 8 ⟨29939, by decide⟩
    (prefixPartial 13 6441) = some ⟨13, 2, 0, 29939, 6441, 3541, 16384⟩ := by
  decide +kernel

theorem context_13_6441_29939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6441 ⟨29939, by decide⟩ :=
  accepted_of_selected 13 6441 ⟨29939, by decide⟩ ⟨13, 2, 0, 29939, 6441, 3541, 16384⟩
    (by decide) selected_cut_00735

theorem selected_cut_00736 : selected 8 ⟨30018, by decide⟩
    (prefixPartial 13 6442) = some ⟨13, 2, 0, 30018, 6442, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_6442_30018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6442 ⟨30018, by decide⟩ :=
  accepted_of_selected 13 6442 ⟨30018, by decide⟩ ⟨13, 2, 0, 30018, 6442, 2821, 16384⟩
    (by decide) selected_cut_00736

theorem selected_cut_00737 : selected 8 ⟨30050, by decide⟩
    (prefixPartial 13 6443) = some ⟨13, 2, 0, 30050, 6443, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_6443_30050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6443 ⟨30050, by decide⟩ :=
  accepted_of_selected 13 6443 ⟨30050, by decide⟩ ⟨13, 2, 0, 30050, 6443, 1433, 16384⟩
    (by decide) selected_cut_00737

theorem unmarked_context_12_1610_30051 : frontier 9 ⟨30051, by decide⟩
    (prefixCache 12 1610) (prefixPartial 12 1610) = false := by
  decide +kernel

theorem node_context_12_1610_30051 : EJMOriginalGlobalDAGData.nodes 9 ⟨30051, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨29939, by decide⟩,⟨30018, by decide⟩,⟨30050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1610_30051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1610 ⟨30051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1610
    ⟨30051, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨29939, by decide⟩,⟨30018, by decide⟩,⟨30050, by decide⟩]) unmarked_context_12_1610_30051 node_context_12_1610_30051
  intro a
  fin_cases a
  · exact context_13_6440_3444
  · exact context_13_6441_29939
  · exact context_13_6442_30018
  · exact context_13_6443_30050

theorem selected_cut_00738 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6444) = some ⟨13, 1, 0, 3444, 6444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6444, 1, 16384⟩
    (by decide) selected_cut_00738

theorem selected_cut_00739 : selected 8 ⟨30087, by decide⟩
    (prefixPartial 13 6445) = some ⟨13, 2, 0, 30087, 6445, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_6445_30087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6445 ⟨30087, by decide⟩ :=
  accepted_of_selected 13 6445 ⟨30087, by decide⟩ ⟨13, 2, 0, 30087, 6445, 2429, 16384⟩
    (by decide) selected_cut_00739

theorem selected_cut_00740 : selected 8 ⟨30121, by decide⟩
    (prefixPartial 13 6446) = some ⟨13, 2, 0, 30121, 6446, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_6446_30121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6446 ⟨30121, by decide⟩ :=
  accepted_of_selected 13 6446 ⟨30121, by decide⟩ ⟨13, 2, 0, 30121, 6446, 1881, 16384⟩
    (by decide) selected_cut_00740

theorem selected_cut_00741 : selected 8 ⟨30134, by decide⟩
    (prefixPartial 13 6447) = some ⟨13, 2, 0, 30134, 6447, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_6447_30134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6447 ⟨30134, by decide⟩ :=
  accepted_of_selected 13 6447 ⟨30134, by decide⟩ ⟨13, 2, 0, 30134, 6447, 1089, 16384⟩
    (by decide) selected_cut_00741

theorem unmarked_context_12_1611_30135 : frontier 9 ⟨30135, by decide⟩
    (prefixCache 12 1611) (prefixPartial 12 1611) = false := by
  decide +kernel

theorem node_context_12_1611_30135 : EJMOriginalGlobalDAGData.nodes 9 ⟨30135, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30087, by decide⟩,⟨30121, by decide⟩,⟨30134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1611_30135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1611 ⟨30135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1611
    ⟨30135, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30087, by decide⟩,⟨30121, by decide⟩,⟨30134, by decide⟩]) unmarked_context_12_1611_30135 node_context_12_1611_30135
  intro a
  fin_cases a
  · exact context_13_6444_3444
  · exact context_13_6445_30087
  · exact context_13_6446_30121
  · exact context_13_6447_30134

theorem unmarked_context_11_402_30136 : frontier 10 ⟨30136, by decide⟩
    (prefixCache 11 402) (prefixPartial 11 402) = false := by
  decide +kernel

theorem node_context_11_402_30136 : EJMOriginalGlobalDAGData.nodes 10 ⟨30136, by decide⟩ =
    .split (coordinate 11) (![⟨29798, by decide⟩,⟨29870, by decide⟩,⟨30051, by decide⟩,⟨30135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_402_30136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 402 ⟨30136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 402
    ⟨30136, by decide⟩ (by decide) (![⟨29798, by decide⟩,⟨29870, by decide⟩,⟨30051, by decide⟩,⟨30135, by decide⟩]) unmarked_context_11_402_30136 node_context_11_402_30136
  intro a
  fin_cases a
  · exact context_12_1608_29798
  · exact context_12_1609_29870
  · exact context_12_1610_30051
  · exact context_12_1611_30135

theorem selected_cut_00742 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6448) = some ⟨13, 1, 0, 3444, 6448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6448, 1, 16384⟩
    (by decide) selected_cut_00742

theorem selected_cut_00743 : selected 8 ⟨30169, by decide⟩
    (prefixPartial 13 6449) = some ⟨13, 2, 0, 30169, 6449, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_6449_30169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6449 ⟨30169, by decide⟩ :=
  accepted_of_selected 13 6449 ⟨30169, by decide⟩ ⟨13, 2, 0, 30169, 6449, 2013, 16384⟩
    (by decide) selected_cut_00743

theorem selected_cut_00744 : selected 8 ⟨30202, by decide⟩
    (prefixPartial 13 6450) = some ⟨13, 2, 0, 30202, 6450, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_6450_30202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6450 ⟨30202, by decide⟩ :=
  accepted_of_selected 13 6450 ⟨30202, by decide⟩ ⟨13, 2, 0, 30202, 6450, 1849, 16384⟩
    (by decide) selected_cut_00744

theorem selected_cut_00745 : selected 8 ⟨30217, by decide⟩
    (prefixPartial 13 6451) = some ⟨13, 2, 0, 30217, 6451, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_6451_30217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6451 ⟨30217, by decide⟩ :=
  accepted_of_selected 13 6451 ⟨30217, by decide⟩ ⟨13, 2, 0, 30217, 6451, 1113, 16384⟩
    (by decide) selected_cut_00745

theorem unmarked_context_12_1612_30218 : frontier 9 ⟨30218, by decide⟩
    (prefixCache 12 1612) (prefixPartial 12 1612) = false := by
  decide +kernel

theorem node_context_12_1612_30218 : EJMOriginalGlobalDAGData.nodes 9 ⟨30218, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30169, by decide⟩,⟨30202, by decide⟩,⟨30217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1612_30218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1612 ⟨30218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1612
    ⟨30218, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30169, by decide⟩,⟨30202, by decide⟩,⟨30217, by decide⟩]) unmarked_context_12_1612_30218 node_context_12_1612_30218
  intro a
  fin_cases a
  · exact context_13_6448_3444
  · exact context_13_6449_30169
  · exact context_13_6450_30202
  · exact context_13_6451_30217

theorem selected_cut_00746 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6452) = some ⟨13, 1, 0, 3444, 6452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6452, 1, 16384⟩
    (by decide) selected_cut_00746

theorem selected_cut_00747 : selected 8 ⟨30257, by decide⟩
    (prefixPartial 13 6453) = some ⟨13, 2, 0, 30257, 6453, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_6453_30257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6453 ⟨30257, by decide⟩ :=
  accepted_of_selected 13 6453 ⟨30257, by decide⟩ ⟨13, 2, 0, 30257, 6453, 2365, 16384⟩
    (by decide) selected_cut_00747

theorem selected_cut_00748 : selected 8 ⟨30288, by decide⟩
    (prefixPartial 13 6454) = some ⟨13, 2, 0, 30288, 6454, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_6454_30288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6454 ⟨30288, by decide⟩ :=
  accepted_of_selected 13 6454 ⟨30288, by decide⟩ ⟨13, 2, 0, 30288, 6454, 1761, 16384⟩
    (by decide) selected_cut_00748

theorem selected_cut_00749 : selected 8 ⟨30311, by decide⟩
    (prefixPartial 13 6455) = some ⟨13, 2, 0, 30311, 6455, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_6455_30311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6455 ⟨30311, by decide⟩ :=
  accepted_of_selected 13 6455 ⟨30311, by decide⟩ ⟨13, 2, 0, 30311, 6455, 1161, 16384⟩
    (by decide) selected_cut_00749

theorem unmarked_context_12_1613_30312 : frontier 9 ⟨30312, by decide⟩
    (prefixCache 12 1613) (prefixPartial 12 1613) = false := by
  decide +kernel

theorem node_context_12_1613_30312 : EJMOriginalGlobalDAGData.nodes 9 ⟨30312, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30257, by decide⟩,⟨30288, by decide⟩,⟨30311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1613_30312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1613 ⟨30312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1613
    ⟨30312, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30257, by decide⟩,⟨30288, by decide⟩,⟨30311, by decide⟩]) unmarked_context_12_1613_30312 node_context_12_1613_30312
  intro a
  fin_cases a
  · exact context_13_6452_3444
  · exact context_13_6453_30257
  · exact context_13_6454_30288
  · exact context_13_6455_30311

theorem selected_cut_00750 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6456) = some ⟨13, 1, 0, 3444, 6456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6456, 1, 16384⟩
    (by decide) selected_cut_00750

theorem selected_cut_00751 : selected 8 ⟨30349, by decide⟩
    (prefixPartial 13 6457) = some ⟨13, 2, 0, 30349, 6457, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_6457_30349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6457 ⟨30349, by decide⟩ :=
  accepted_of_selected 13 6457 ⟨30349, by decide⟩ ⟨13, 2, 0, 30349, 6457, 2329, 16384⟩
    (by decide) selected_cut_00751

theorem selected_cut_00752 : selected 8 ⟨30383, by decide⟩
    (prefixPartial 13 6458) = some ⟨13, 2, 0, 30383, 6458, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_6458_30383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6458 ⟨30383, by decide⟩ :=
  accepted_of_selected 13 6458 ⟨30383, by decide⟩ ⟨13, 2, 0, 30383, 6458, 1761, 16384⟩
    (by decide) selected_cut_00752

theorem selected_cut_00753 : selected 8 ⟨30401, by decide⟩
    (prefixPartial 13 6459) = some ⟨13, 2, 0, 30401, 6459, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_6459_30401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6459 ⟨30401, by decide⟩ :=
  accepted_of_selected 13 6459 ⟨30401, by decide⟩ ⟨13, 2, 0, 30401, 6459, 1189, 16384⟩
    (by decide) selected_cut_00753

theorem unmarked_context_12_1614_30402 : frontier 9 ⟨30402, by decide⟩
    (prefixCache 12 1614) (prefixPartial 12 1614) = false := by
  decide +kernel

theorem node_context_12_1614_30402 : EJMOriginalGlobalDAGData.nodes 9 ⟨30402, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30349, by decide⟩,⟨30383, by decide⟩,⟨30401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1614_30402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1614 ⟨30402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1614
    ⟨30402, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30349, by decide⟩,⟨30383, by decide⟩,⟨30401, by decide⟩]) unmarked_context_12_1614_30402 node_context_12_1614_30402
  intro a
  fin_cases a
  · exact context_13_6456_3444
  · exact context_13_6457_30349
  · exact context_13_6458_30383
  · exact context_13_6459_30401

theorem selected_cut_00754 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6460) = some ⟨13, 1, 0, 3444, 6460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6460, 1, 16384⟩
    (by decide) selected_cut_00754

theorem selected_cut_00755 : selected 8 ⟨30437, by decide⟩
    (prefixPartial 13 6461) = some ⟨13, 2, 0, 30437, 6461, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_6461_30437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6461 ⟨30437, by decide⟩ :=
  accepted_of_selected 13 6461 ⟨30437, by decide⟩ ⟨13, 2, 0, 30437, 6461, 2061, 16384⟩
    (by decide) selected_cut_00755

theorem selected_cut_00756 : selected 8 ⟨30471, by decide⟩
    (prefixPartial 13 6462) = some ⟨13, 2, 0, 30471, 6462, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_6462_30471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6462 ⟨30471, by decide⟩ :=
  accepted_of_selected 13 6462 ⟨30471, by decide⟩ ⟨13, 2, 0, 30471, 6462, 1745, 16384⟩
    (by decide) selected_cut_00756

theorem selected_cut_00757 : selected 8 ⟨30487, by decide⟩
    (prefixPartial 13 6463) = some ⟨13, 2, 0, 30487, 6463, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_6463_30487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6463 ⟨30487, by decide⟩ :=
  accepted_of_selected 13 6463 ⟨30487, by decide⟩ ⟨13, 2, 0, 30487, 6463, 1153, 16384⟩
    (by decide) selected_cut_00757

theorem unmarked_context_12_1615_30488 : frontier 9 ⟨30488, by decide⟩
    (prefixCache 12 1615) (prefixPartial 12 1615) = false := by
  decide +kernel

theorem node_context_12_1615_30488 : EJMOriginalGlobalDAGData.nodes 9 ⟨30488, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30437, by decide⟩,⟨30471, by decide⟩,⟨30487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1615_30488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1615 ⟨30488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1615
    ⟨30488, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30437, by decide⟩,⟨30471, by decide⟩,⟨30487, by decide⟩]) unmarked_context_12_1615_30488 node_context_12_1615_30488
  intro a
  fin_cases a
  · exact context_13_6460_3444
  · exact context_13_6461_30437
  · exact context_13_6462_30471
  · exact context_13_6463_30487

theorem unmarked_context_11_403_30489 : frontier 10 ⟨30489, by decide⟩
    (prefixCache 11 403) (prefixPartial 11 403) = false := by
  decide +kernel

theorem node_context_11_403_30489 : EJMOriginalGlobalDAGData.nodes 10 ⟨30489, by decide⟩ =
    .split (coordinate 11) (![⟨30218, by decide⟩,⟨30312, by decide⟩,⟨30402, by decide⟩,⟨30488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_403_30489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 403 ⟨30489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 403
    ⟨30489, by decide⟩ (by decide) (![⟨30218, by decide⟩,⟨30312, by decide⟩,⟨30402, by decide⟩,⟨30488, by decide⟩]) unmarked_context_11_403_30489 node_context_11_403_30489
  intro a
  fin_cases a
  · exact context_12_1612_30218
  · exact context_12_1613_30312
  · exact context_12_1614_30402
  · exact context_12_1615_30488

theorem unmarked_context_10_100_30490 : frontier 11 ⟨30490, by decide⟩
    (prefixCache 10 100) (prefixPartial 10 100) = false := by
  decide +kernel

theorem node_context_10_100_30490 : EJMOriginalGlobalDAGData.nodes 11 ⟨30490, by decide⟩ =
    .split (coordinate 10) (![⟨29416, by decide⟩,⟨29731, by decide⟩,⟨30136, by decide⟩,⟨30489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_100_30490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 100 ⟨30490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 100
    ⟨30490, by decide⟩ (by decide) (![⟨29416, by decide⟩,⟨29731, by decide⟩,⟨30136, by decide⟩,⟨30489, by decide⟩]) unmarked_context_10_100_30490 node_context_10_100_30490
  intro a
  fin_cases a
  · exact context_11_400_29416
  · exact context_11_401_29731
  · exact context_11_402_30136
  · exact context_11_403_30489

theorem selected_cut_00758 : selected 9 ⟨30550, by decide⟩
    (prefixPartial 12 1616) = some ⟨12, 2, 0, 30550, 1616, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_1616_30550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1616 ⟨30550, by decide⟩ :=
  accepted_of_selected 12 1616 ⟨30550, by decide⟩ ⟨12, 2, 0, 30550, 1616, 3849, 65536⟩
    (by decide) selected_cut_00758

theorem selected_cut_00759 : selected 9 ⟨30606, by decide⟩
    (prefixPartial 12 1617) = some ⟨12, 2, 0, 30606, 1617, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_1617_30606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1617 ⟨30606, by decide⟩ :=
  accepted_of_selected 12 1617 ⟨30606, by decide⟩ ⟨12, 2, 0, 30606, 1617, 3509, 65536⟩
    (by decide) selected_cut_00759

theorem selected_cut_00760 : selected 9 ⟨30659, by decide⟩
    (prefixPartial 12 1618) = some ⟨12, 2, 0, 30659, 1618, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_1618_30659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1618 ⟨30659, by decide⟩ :=
  accepted_of_selected 12 1618 ⟨30659, by decide⟩ ⟨12, 2, 0, 30659, 1618, 3089, 65536⟩
    (by decide) selected_cut_00760

theorem selected_cut_00761 : selected 9 ⟨30716, by decide⟩
    (prefixPartial 12 1619) = some ⟨12, 2, 0, 30716, 1619, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_1619_30716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1619 ⟨30716, by decide⟩ :=
  accepted_of_selected 12 1619 ⟨30716, by decide⟩ ⟨12, 2, 0, 30716, 1619, 3493, 65536⟩
    (by decide) selected_cut_00761

theorem unmarked_context_11_404_30717 : frontier 10 ⟨30717, by decide⟩
    (prefixCache 11 404) (prefixPartial 11 404) = false := by
  decide +kernel

theorem node_context_11_404_30717 : EJMOriginalGlobalDAGData.nodes 10 ⟨30717, by decide⟩ =
    .split (coordinate 11) (![⟨30550, by decide⟩,⟨30606, by decide⟩,⟨30659, by decide⟩,⟨30716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_404_30717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 404 ⟨30717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 404
    ⟨30717, by decide⟩ (by decide) (![⟨30550, by decide⟩,⟨30606, by decide⟩,⟨30659, by decide⟩,⟨30716, by decide⟩]) unmarked_context_11_404_30717 node_context_11_404_30717
  intro a
  fin_cases a
  · exact context_12_1616_30550
  · exact context_12_1617_30606
  · exact context_12_1618_30659
  · exact context_12_1619_30716

theorem selected_cut_00762 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6480) = some ⟨13, 1, 0, 3444, 6480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6480, 1, 16384⟩
    (by decide) selected_cut_00762

theorem selected_cut_00763 : selected 8 ⟨30784, by decide⟩
    (prefixPartial 13 6481) = some ⟨13, 2, 0, 30784, 6481, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_6481_30784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6481 ⟨30784, by decide⟩ :=
  accepted_of_selected 13 6481 ⟨30784, by decide⟩ ⟨13, 2, 0, 30784, 6481, 2677, 16384⟩
    (by decide) selected_cut_00763

theorem selected_cut_00764 : selected 8 ⟨30840, by decide⟩
    (prefixPartial 13 6482) = some ⟨13, 2, 0, 30840, 6482, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_6482_30840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6482 ⟨30840, by decide⟩ :=
  accepted_of_selected 13 6482 ⟨30840, by decide⟩ ⟨13, 2, 0, 30840, 6482, 2093, 16384⟩
    (by decide) selected_cut_00764

theorem selected_cut_00765 : selected 8 ⟨30871, by decide⟩
    (prefixPartial 13 6483) = some ⟨13, 2, 0, 30871, 6483, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_6483_30871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6483 ⟨30871, by decide⟩ :=
  accepted_of_selected 13 6483 ⟨30871, by decide⟩ ⟨13, 2, 0, 30871, 6483, 1433, 16384⟩
    (by decide) selected_cut_00765

theorem unmarked_context_12_1620_30872 : frontier 9 ⟨30872, by decide⟩
    (prefixCache 12 1620) (prefixPartial 12 1620) = false := by
  decide +kernel

theorem node_context_12_1620_30872 : EJMOriginalGlobalDAGData.nodes 9 ⟨30872, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30784, by decide⟩,⟨30840, by decide⟩,⟨30871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1620_30872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1620 ⟨30872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1620
    ⟨30872, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30784, by decide⟩,⟨30840, by decide⟩,⟨30871, by decide⟩]) unmarked_context_12_1620_30872 node_context_12_1620_30872
  intro a
  fin_cases a
  · exact context_13_6480_3444
  · exact context_13_6481_30784
  · exact context_13_6482_30840
  · exact context_13_6483_30871

theorem selected_cut_00766 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6484) = some ⟨13, 1, 0, 3444, 6484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6484, 1, 16384⟩
    (by decide) selected_cut_00766

theorem selected_cut_00767 : selected 8 ⟨30930, by decide⟩
    (prefixPartial 13 6485) = some ⟨13, 2, 0, 30930, 6485, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_6485_30930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6485 ⟨30930, by decide⟩ :=
  accepted_of_selected 13 6485 ⟨30930, by decide⟩ ⟨13, 2, 0, 30930, 6485, 2665, 16384⟩
    (by decide) selected_cut_00767

theorem selected_cut_00768 : selected 8 ⟨30978, by decide⟩
    (prefixPartial 13 6486) = some ⟨13, 2, 0, 30978, 6486, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_6486_30978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6486 ⟨30978, by decide⟩ :=
  accepted_of_selected 13 6486 ⟨30978, by decide⟩ ⟨13, 2, 0, 30978, 6486, 1841, 16384⟩
    (by decide) selected_cut_00768

theorem selected_cut_00769 : selected 8 ⟨31005, by decide⟩
    (prefixPartial 13 6487) = some ⟨13, 2, 0, 31005, 6487, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_6487_31005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6487 ⟨31005, by decide⟩ :=
  accepted_of_selected 13 6487 ⟨31005, by decide⟩ ⟨13, 2, 0, 31005, 6487, 1449, 16384⟩
    (by decide) selected_cut_00769

theorem unmarked_context_12_1621_31006 : frontier 9 ⟨31006, by decide⟩
    (prefixCache 12 1621) (prefixPartial 12 1621) = false := by
  decide +kernel

theorem node_context_12_1621_31006 : EJMOriginalGlobalDAGData.nodes 9 ⟨31006, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨30930, by decide⟩,⟨30978, by decide⟩,⟨31005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1621_31006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1621 ⟨31006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1621
    ⟨31006, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨30930, by decide⟩,⟨30978, by decide⟩,⟨31005, by decide⟩]) unmarked_context_12_1621_31006 node_context_12_1621_31006
  intro a
  fin_cases a
  · exact context_13_6484_3444
  · exact context_13_6485_30930
  · exact context_13_6486_30978
  · exact context_13_6487_31005

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
