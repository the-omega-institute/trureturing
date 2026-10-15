/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover266
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_25635 : selected 8 ⟨649481, by decide⟩
    (prefixPartial 13 352299) = some ⟨13, 2, 0, 649481, 352299, 141, 16384⟩ := by
  decide +kernel

theorem context_13_352299_649481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352299 ⟨649481, by decide⟩ :=
  accepted_of_selected 13 352299 ⟨649481, by decide⟩ ⟨13, 2, 0, 649481, 352299, 141, 16384⟩
    (by decide) selected_cut_25635

theorem unmarked_context_12_88074_649482 : frontier 9 ⟨649482, by decide⟩
    (prefixCache 12 88074) (prefixPartial 12 88074) = false := by
  decide +kernel

theorem node_context_12_88074_649482 : EJMOriginalGlobalDAGData.nodes 9 ⟨649482, by decide⟩ =
    .split (coordinate 12) (![⟨649408, by decide⟩,⟨649458, by decide⟩,⟨649478, by decide⟩,⟨649481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88074_649482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88074 ⟨649482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88074
    ⟨649482, by decide⟩ (by decide) (![⟨649408, by decide⟩,⟨649458, by decide⟩,⟨649478, by decide⟩,⟨649481, by decide⟩]) unmarked_context_12_88074_649482 node_context_12_88074_649482
  intro a
  fin_cases a
  · exact context_13_352296_649408
  · exact context_13_352297_649458
  · exact context_13_352298_649478
  · exact context_13_352299_649481

theorem selected_cut_25636 : selected 8 ⟨649548, by decide⟩
    (prefixPartial 13 352300) = some ⟨13, 2, 0, 649548, 352300, 3369, 16384⟩ := by
  decide +kernel

theorem context_13_352300_649548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352300 ⟨649548, by decide⟩ :=
  accepted_of_selected 13 352300 ⟨649548, by decide⟩ ⟨13, 2, 0, 649548, 352300, 3369, 16384⟩
    (by decide) selected_cut_25636

theorem selected_cut_25637 : selected 8 ⟨649610, by decide⟩
    (prefixPartial 13 352301) = some ⟨13, 2, 0, 649610, 352301, 3413, 16384⟩ := by
  decide +kernel

theorem context_13_352301_649610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352301 ⟨649610, by decide⟩ :=
  accepted_of_selected 13 352301 ⟨649610, by decide⟩ ⟨13, 2, 0, 649610, 352301, 3413, 16384⟩
    (by decide) selected_cut_25637

theorem selected_cut_25638 : selected 8 ⟨649630, by decide⟩
    (prefixPartial 13 352302) = some ⟨13, 2, 0, 649630, 352302, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_352302_649630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352302 ⟨649630, by decide⟩ :=
  accepted_of_selected 13 352302 ⟨649630, by decide⟩ ⟨13, 2, 0, 649630, 352302, 2333, 16384⟩
    (by decide) selected_cut_25638

theorem selected_cut_25639 : selected 8 ⟨649636, by decide⟩
    (prefixPartial 13 352303) = some ⟨13, 2, 0, 649636, 352303, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_352303_649636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352303 ⟨649636, by decide⟩ :=
  accepted_of_selected 13 352303 ⟨649636, by decide⟩ ⟨13, 2, 0, 649636, 352303, 1201, 16384⟩
    (by decide) selected_cut_25639

theorem unmarked_context_12_88075_649637 : frontier 9 ⟨649637, by decide⟩
    (prefixCache 12 88075) (prefixPartial 12 88075) = false := by
  decide +kernel

theorem node_context_12_88075_649637 : EJMOriginalGlobalDAGData.nodes 9 ⟨649637, by decide⟩ =
    .split (coordinate 12) (![⟨649548, by decide⟩,⟨649610, by decide⟩,⟨649630, by decide⟩,⟨649636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88075_649637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88075 ⟨649637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88075
    ⟨649637, by decide⟩ (by decide) (![⟨649548, by decide⟩,⟨649610, by decide⟩,⟨649630, by decide⟩,⟨649636, by decide⟩]) unmarked_context_12_88075_649637 node_context_12_88075_649637
  intro a
  fin_cases a
  · exact context_13_352300_649548
  · exact context_13_352301_649610
  · exact context_13_352302_649630
  · exact context_13_352303_649636

theorem unmarked_context_11_22018_649638 : frontier 10 ⟨649638, by decide⟩
    (prefixCache 11 22018) (prefixPartial 11 22018) = false := by
  decide +kernel

theorem node_context_11_22018_649638 : EJMOriginalGlobalDAGData.nodes 10 ⟨649638, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨649325, by decide⟩,⟨649482, by decide⟩,⟨649637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22018_649638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22018 ⟨649638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22018
    ⟨649638, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨649325, by decide⟩,⟨649482, by decide⟩,⟨649637, by decide⟩]) unmarked_context_11_22018_649638 node_context_11_22018_649638
  intro a
  fin_cases a
  · exact context_12_88072_448748
  · exact context_12_88073_649325
  · exact context_12_88074_649482
  · exact context_12_88075_649637

theorem selected_cut_25640 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88076) = some ⟨12, 1, 0, 448748, 88076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88076_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88076 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88076 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88076, 1, 65536⟩
    (by decide) selected_cut_25640

theorem selected_cut_25641 : selected 8 ⟨649709, by decide⟩
    (prefixPartial 13 352308) = some ⟨13, 2, 0, 649709, 352308, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_352308_649709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352308 ⟨649709, by decide⟩ :=
  accepted_of_selected 13 352308 ⟨649709, by decide⟩ ⟨13, 2, 0, 649709, 352308, 3317, 16384⟩
    (by decide) selected_cut_25641

theorem selected_cut_25642 : selected 8 ⟨649767, by decide⟩
    (prefixPartial 13 352309) = some ⟨13, 2, 0, 649767, 352309, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_352309_649767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352309 ⟨649767, by decide⟩ :=
  accepted_of_selected 13 352309 ⟨649767, by decide⟩ ⟨13, 2, 0, 649767, 352309, 2773, 16384⟩
    (by decide) selected_cut_25642

theorem selected_cut_25643 : selected 8 ⟨649803, by decide⟩
    (prefixPartial 13 352310) = some ⟨13, 2, 0, 649803, 352310, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_352310_649803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352310 ⟨649803, by decide⟩ :=
  accepted_of_selected 13 352310 ⟨649803, by decide⟩ ⟨13, 2, 0, 649803, 352310, 2329, 16384⟩
    (by decide) selected_cut_25643

theorem selected_cut_25644 : selected 8 ⟨649816, by decide⟩
    (prefixPartial 13 352311) = some ⟨13, 2, 0, 649816, 352311, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_352311_649816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352311 ⟨649816, by decide⟩ :=
  accepted_of_selected 13 352311 ⟨649816, by decide⟩ ⟨13, 2, 0, 649816, 352311, 1233, 16384⟩
    (by decide) selected_cut_25644

theorem unmarked_context_12_88077_649817 : frontier 9 ⟨649817, by decide⟩
    (prefixCache 12 88077) (prefixPartial 12 88077) = false := by
  decide +kernel

theorem node_context_12_88077_649817 : EJMOriginalGlobalDAGData.nodes 9 ⟨649817, by decide⟩ =
    .split (coordinate 12) (![⟨649709, by decide⟩,⟨649767, by decide⟩,⟨649803, by decide⟩,⟨649816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88077_649817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88077 ⟨649817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88077
    ⟨649817, by decide⟩ (by decide) (![⟨649709, by decide⟩,⟨649767, by decide⟩,⟨649803, by decide⟩,⟨649816, by decide⟩]) unmarked_context_12_88077_649817 node_context_12_88077_649817
  intro a
  fin_cases a
  · exact context_13_352308_649709
  · exact context_13_352309_649767
  · exact context_13_352310_649803
  · exact context_13_352311_649816

theorem selected_cut_25645 : selected 8 ⟨649887, by decide⟩
    (prefixPartial 13 352312) = some ⟨13, 2, 0, 649887, 352312, 3521, 16384⟩ := by
  decide +kernel

theorem context_13_352312_649887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352312 ⟨649887, by decide⟩ :=
  accepted_of_selected 13 352312 ⟨649887, by decide⟩ ⟨13, 2, 0, 649887, 352312, 3521, 16384⟩
    (by decide) selected_cut_25645

theorem selected_cut_25646 : selected 8 ⟨649941, by decide⟩
    (prefixPartial 13 352313) = some ⟨13, 2, 0, 649941, 352313, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_352313_649941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352313 ⟨649941, by decide⟩ :=
  accepted_of_selected 13 352313 ⟨649941, by decide⟩ ⟨13, 2, 0, 649941, 352313, 3205, 16384⟩
    (by decide) selected_cut_25646

theorem selected_cut_25647 : selected 8 ⟨649977, by decide⟩
    (prefixPartial 13 352314) = some ⟨13, 2, 0, 649977, 352314, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_352314_649977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352314 ⟨649977, by decide⟩ :=
  accepted_of_selected 13 352314 ⟨649977, by decide⟩ ⟨13, 2, 0, 649977, 352314, 2413, 16384⟩
    (by decide) selected_cut_25647

theorem selected_cut_25648 : selected 8 ⟨649992, by decide⟩
    (prefixPartial 13 352315) = some ⟨13, 2, 0, 649992, 352315, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_352315_649992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352315 ⟨649992, by decide⟩ :=
  accepted_of_selected 13 352315 ⟨649992, by decide⟩ ⟨13, 2, 0, 649992, 352315, 1261, 16384⟩
    (by decide) selected_cut_25648

theorem unmarked_context_12_88078_649993 : frontier 9 ⟨649993, by decide⟩
    (prefixCache 12 88078) (prefixPartial 12 88078) = false := by
  decide +kernel

theorem node_context_12_88078_649993 : EJMOriginalGlobalDAGData.nodes 9 ⟨649993, by decide⟩ =
    .split (coordinate 12) (![⟨649887, by decide⟩,⟨649941, by decide⟩,⟨649977, by decide⟩,⟨649992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88078_649993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88078 ⟨649993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88078
    ⟨649993, by decide⟩ (by decide) (![⟨649887, by decide⟩,⟨649941, by decide⟩,⟨649977, by decide⟩,⟨649992, by decide⟩]) unmarked_context_12_88078_649993 node_context_12_88078_649993
  intro a
  fin_cases a
  · exact context_13_352312_649887
  · exact context_13_352313_649941
  · exact context_13_352314_649977
  · exact context_13_352315_649992

theorem selected_cut_25649 : selected 8 ⟨650069, by decide⟩
    (prefixPartial 13 352316) = some ⟨13, 2, 0, 650069, 352316, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_352316_650069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352316 ⟨650069, by decide⟩ :=
  accepted_of_selected 13 352316 ⟨650069, by decide⟩ ⟨13, 2, 0, 650069, 352316, 2873, 16384⟩
    (by decide) selected_cut_25649

theorem selected_cut_25650 : selected 8 ⟨650148, by decide⟩
    (prefixPartial 13 352317) = some ⟨13, 2, 0, 650148, 352317, 3433, 16384⟩ := by
  decide +kernel

theorem context_13_352317_650148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352317 ⟨650148, by decide⟩ :=
  accepted_of_selected 13 352317 ⟨650148, by decide⟩ ⟨13, 2, 0, 650148, 352317, 3433, 16384⟩
    (by decide) selected_cut_25650

theorem selected_cut_25651 : selected 8 ⟨650172, by decide⟩
    (prefixPartial 13 352318) = some ⟨13, 2, 0, 650172, 352318, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_352318_650172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352318 ⟨650172, by decide⟩ :=
  accepted_of_selected 13 352318 ⟨650172, by decide⟩ ⟨13, 2, 0, 650172, 352318, 2277, 16384⟩
    (by decide) selected_cut_25651

theorem selected_cut_25652 : selected 8 ⟨650182, by decide⟩
    (prefixPartial 13 352319) = some ⟨13, 2, 0, 650182, 352319, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_352319_650182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352319 ⟨650182, by decide⟩ :=
  accepted_of_selected 13 352319 ⟨650182, by decide⟩ ⟨13, 2, 0, 650182, 352319, 1181, 16384⟩
    (by decide) selected_cut_25652

theorem unmarked_context_12_88079_650183 : frontier 9 ⟨650183, by decide⟩
    (prefixCache 12 88079) (prefixPartial 12 88079) = false := by
  decide +kernel

theorem node_context_12_88079_650183 : EJMOriginalGlobalDAGData.nodes 9 ⟨650183, by decide⟩ =
    .split (coordinate 12) (![⟨650069, by decide⟩,⟨650148, by decide⟩,⟨650172, by decide⟩,⟨650182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88079_650183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88079 ⟨650183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88079
    ⟨650183, by decide⟩ (by decide) (![⟨650069, by decide⟩,⟨650148, by decide⟩,⟨650172, by decide⟩,⟨650182, by decide⟩]) unmarked_context_12_88079_650183 node_context_12_88079_650183
  intro a
  fin_cases a
  · exact context_13_352316_650069
  · exact context_13_352317_650148
  · exact context_13_352318_650172
  · exact context_13_352319_650182

theorem unmarked_context_11_22019_650184 : frontier 10 ⟨650184, by decide⟩
    (prefixCache 11 22019) (prefixPartial 11 22019) = false := by
  decide +kernel

theorem node_context_11_22019_650184 : EJMOriginalGlobalDAGData.nodes 10 ⟨650184, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨649817, by decide⟩,⟨649993, by decide⟩,⟨650183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22019_650184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22019 ⟨650184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22019
    ⟨650184, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨649817, by decide⟩,⟨649993, by decide⟩,⟨650183, by decide⟩]) unmarked_context_11_22019_650184 node_context_11_22019_650184
  intro a
  fin_cases a
  · exact context_12_88076_448748
  · exact context_12_88077_649817
  · exact context_12_88078_649993
  · exact context_12_88079_650183

theorem unmarked_context_10_5504_650185 : frontier 11 ⟨650185, by decide⟩
    (prefixCache 10 5504) (prefixPartial 10 5504) = false := by
  decide +kernel

theorem node_context_10_5504_650185 : EJMOriginalGlobalDAGData.nodes 11 ⟨650185, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨649162, by decide⟩,⟨649638, by decide⟩,⟨650184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5504_650185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5504 ⟨650185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5504
    ⟨650185, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨649162, by decide⟩,⟨649638, by decide⟩,⟨650184, by decide⟩]) unmarked_context_10_5504_650185 node_context_10_5504_650185
  intro a
  fin_cases a
  · exact context_11_22016_434745
  · exact context_11_22017_649162
  · exact context_11_22018_649638
  · exact context_11_22019_650184

theorem selected_cut_25653 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 88080) = some ⟨12, 1, 0, 641337, 88080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88080_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88080 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 88080 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 88080, 1, 65536⟩
    (by decide) selected_cut_25653

theorem selected_cut_25654 : selected 8 ⟨650225, by decide⟩
    (prefixPartial 13 352324) = some ⟨13, 2, 0, 650225, 352324, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_352324_650225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352324 ⟨650225, by decide⟩ :=
  accepted_of_selected 13 352324 ⟨650225, by decide⟩ ⟨13, 2, 0, 650225, 352324, 1897, 16384⟩
    (by decide) selected_cut_25654

theorem selected_cut_25655 : selected 8 ⟨650256, by decide⟩
    (prefixPartial 13 352325) = some ⟨13, 2, 0, 650256, 352325, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_352325_650256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352325 ⟨650256, by decide⟩ :=
  accepted_of_selected 13 352325 ⟨650256, by decide⟩ ⟨13, 2, 0, 650256, 352325, 1749, 16384⟩
    (by decide) selected_cut_25655

theorem selected_cut_25656 : selected 8 ⟨650279, by decide⟩
    (prefixPartial 13 352326) = some ⟨13, 2, 0, 650279, 352326, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_352326_650279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352326 ⟨650279, by decide⟩ :=
  accepted_of_selected 13 352326 ⟨650279, by decide⟩ ⟨13, 2, 0, 650279, 352326, 1525, 16384⟩
    (by decide) selected_cut_25656

theorem selected_cut_25657 : selected 8 ⟨650288, by decide⟩
    (prefixPartial 13 352327) = some ⟨13, 2, 0, 650288, 352327, 873, 16384⟩ := by
  decide +kernel

theorem context_13_352327_650288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352327 ⟨650288, by decide⟩ :=
  accepted_of_selected 13 352327 ⟨650288, by decide⟩ ⟨13, 2, 0, 650288, 352327, 873, 16384⟩
    (by decide) selected_cut_25657

theorem unmarked_context_12_88081_650289 : frontier 9 ⟨650289, by decide⟩
    (prefixCache 12 88081) (prefixPartial 12 88081) = false := by
  decide +kernel

theorem node_context_12_88081_650289 : EJMOriginalGlobalDAGData.nodes 9 ⟨650289, by decide⟩ =
    .split (coordinate 12) (![⟨650225, by decide⟩,⟨650256, by decide⟩,⟨650279, by decide⟩,⟨650288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88081_650289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88081 ⟨650289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88081
    ⟨650289, by decide⟩ (by decide) (![⟨650225, by decide⟩,⟨650256, by decide⟩,⟨650279, by decide⟩,⟨650288, by decide⟩]) unmarked_context_12_88081_650289 node_context_12_88081_650289
  intro a
  fin_cases a
  · exact context_13_352324_650225
  · exact context_13_352325_650256
  · exact context_13_352326_650279
  · exact context_13_352327_650288

theorem selected_cut_25658 : selected 8 ⟨650337, by decide⟩
    (prefixPartial 13 352328) = some ⟨13, 2, 0, 650337, 352328, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_352328_650337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352328 ⟨650337, by decide⟩ :=
  accepted_of_selected 13 352328 ⟨650337, by decide⟩ ⟨13, 2, 0, 650337, 352328, 2101, 16384⟩
    (by decide) selected_cut_25658

theorem selected_cut_25659 : selected 8 ⟨650363, by decide⟩
    (prefixPartial 13 352329) = some ⟨13, 2, 0, 650363, 352329, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_352329_650363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352329 ⟨650363, by decide⟩ :=
  accepted_of_selected 13 352329 ⟨650363, by decide⟩ ⟨13, 2, 0, 650363, 352329, 1973, 16384⟩
    (by decide) selected_cut_25659

theorem selected_cut_25660 : selected 8 ⟨650383, by decide⟩
    (prefixPartial 13 352330) = some ⟨13, 2, 0, 650383, 352330, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_352330_650383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352330 ⟨650383, by decide⟩ :=
  accepted_of_selected 13 352330 ⟨650383, by decide⟩ ⟨13, 2, 0, 650383, 352330, 1665, 16384⟩
    (by decide) selected_cut_25660

theorem selected_cut_25661 : selected 8 ⟨650393, by decide⟩
    (prefixPartial 13 352331) = some ⟨13, 2, 0, 650393, 352331, 969, 16384⟩ := by
  decide +kernel

theorem context_13_352331_650393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352331 ⟨650393, by decide⟩ :=
  accepted_of_selected 13 352331 ⟨650393, by decide⟩ ⟨13, 2, 0, 650393, 352331, 969, 16384⟩
    (by decide) selected_cut_25661

theorem unmarked_context_12_88082_650394 : frontier 9 ⟨650394, by decide⟩
    (prefixCache 12 88082) (prefixPartial 12 88082) = false := by
  decide +kernel

theorem node_context_12_88082_650394 : EJMOriginalGlobalDAGData.nodes 9 ⟨650394, by decide⟩ =
    .split (coordinate 12) (![⟨650337, by decide⟩,⟨650363, by decide⟩,⟨650383, by decide⟩,⟨650393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88082_650394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88082 ⟨650394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88082
    ⟨650394, by decide⟩ (by decide) (![⟨650337, by decide⟩,⟨650363, by decide⟩,⟨650383, by decide⟩,⟨650393, by decide⟩]) unmarked_context_12_88082_650394 node_context_12_88082_650394
  intro a
  fin_cases a
  · exact context_13_352328_650337
  · exact context_13_352329_650363
  · exact context_13_352330_650383
  · exact context_13_352331_650393

theorem selected_cut_25662 : selected 8 ⟨650434, by decide⟩
    (prefixPartial 13 352332) = some ⟨13, 2, 0, 650434, 352332, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_352332_650434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352332 ⟨650434, by decide⟩ :=
  accepted_of_selected 13 352332 ⟨650434, by decide⟩ ⟨13, 2, 0, 650434, 352332, 2129, 16384⟩
    (by decide) selected_cut_25662

theorem selected_cut_25663 : selected 8 ⟨650471, by decide⟩
    (prefixPartial 13 352333) = some ⟨13, 2, 0, 650471, 352333, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_352333_650471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352333 ⟨650471, by decide⟩ :=
  accepted_of_selected 13 352333 ⟨650471, by decide⟩ ⟨13, 2, 0, 650471, 352333, 2169, 16384⟩
    (by decide) selected_cut_25663

theorem selected_cut_25664 : selected 8 ⟨650494, by decide⟩
    (prefixPartial 13 352334) = some ⟨13, 2, 0, 650494, 352334, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_352334_650494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352334 ⟨650494, by decide⟩ :=
  accepted_of_selected 13 352334 ⟨650494, by decide⟩ ⟨13, 2, 0, 650494, 352334, 1765, 16384⟩
    (by decide) selected_cut_25664

theorem selected_cut_25665 : selected 8 ⟨650498, by decide⟩
    (prefixPartial 13 352335) = some ⟨13, 2, 0, 650498, 352335, 769, 16384⟩ := by
  decide +kernel

theorem context_13_352335_650498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352335 ⟨650498, by decide⟩ :=
  accepted_of_selected 13 352335 ⟨650498, by decide⟩ ⟨13, 2, 0, 650498, 352335, 769, 16384⟩
    (by decide) selected_cut_25665

theorem unmarked_context_12_88083_650499 : frontier 9 ⟨650499, by decide⟩
    (prefixCache 12 88083) (prefixPartial 12 88083) = false := by
  decide +kernel

theorem node_context_12_88083_650499 : EJMOriginalGlobalDAGData.nodes 9 ⟨650499, by decide⟩ =
    .split (coordinate 12) (![⟨650434, by decide⟩,⟨650471, by decide⟩,⟨650494, by decide⟩,⟨650498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88083_650499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88083 ⟨650499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88083
    ⟨650499, by decide⟩ (by decide) (![⟨650434, by decide⟩,⟨650471, by decide⟩,⟨650494, by decide⟩,⟨650498, by decide⟩]) unmarked_context_12_88083_650499 node_context_12_88083_650499
  intro a
  fin_cases a
  · exact context_13_352332_650434
  · exact context_13_352333_650471
  · exact context_13_352334_650494
  · exact context_13_352335_650498

theorem unmarked_context_11_22020_650500 : frontier 10 ⟨650500, by decide⟩
    (prefixCache 11 22020) (prefixPartial 11 22020) = false := by
  decide +kernel

theorem node_context_11_22020_650500 : EJMOriginalGlobalDAGData.nodes 10 ⟨650500, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨650289, by decide⟩,⟨650394, by decide⟩,⟨650499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22020_650500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22020 ⟨650500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22020
    ⟨650500, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨650289, by decide⟩,⟨650394, by decide⟩,⟨650499, by decide⟩]) unmarked_context_11_22020_650500 node_context_11_22020_650500
  intro a
  fin_cases a
  · exact context_12_88080_641337
  · exact context_12_88081_650289
  · exact context_12_88082_650394
  · exact context_12_88083_650499

theorem selected_cut_25666 : selected 8 ⟨650523, by decide⟩
    (prefixPartial 13 352336) = some ⟨13, 2, 0, 650523, 352336, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_352336_650523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352336 ⟨650523, by decide⟩ :=
  accepted_of_selected 13 352336 ⟨650523, by decide⟩ ⟨13, 2, 0, 650523, 352336, 1329, 16384⟩
    (by decide) selected_cut_25666

theorem selected_cut_25667 : selected 8 ⟨650574, by decide⟩
    (prefixPartial 13 352337) = some ⟨13, 2, 0, 650574, 352337, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_352337_650574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352337 ⟨650574, by decide⟩ :=
  accepted_of_selected 13 352337 ⟨650574, by decide⟩ ⟨13, 2, 0, 650574, 352337, 2549, 16384⟩
    (by decide) selected_cut_25667

theorem selected_cut_25668 : selected 8 ⟨650593, by decide⟩
    (prefixPartial 13 352338) = some ⟨13, 2, 0, 650593, 352338, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_352338_650593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352338 ⟨650593, by decide⟩ :=
  accepted_of_selected 13 352338 ⟨650593, by decide⟩ ⟨13, 2, 0, 650593, 352338, 1497, 16384⟩
    (by decide) selected_cut_25668

theorem selected_cut_25669 : selected 8 ⟨650599, by decide⟩
    (prefixPartial 13 352339) = some ⟨13, 2, 0, 650599, 352339, 957, 16384⟩ := by
  decide +kernel

theorem context_13_352339_650599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352339 ⟨650599, by decide⟩ :=
  accepted_of_selected 13 352339 ⟨650599, by decide⟩ ⟨13, 2, 0, 650599, 352339, 957, 16384⟩
    (by decide) selected_cut_25669

theorem unmarked_context_12_88084_650600 : frontier 9 ⟨650600, by decide⟩
    (prefixCache 12 88084) (prefixPartial 12 88084) = false := by
  decide +kernel

theorem node_context_12_88084_650600 : EJMOriginalGlobalDAGData.nodes 9 ⟨650600, by decide⟩ =
    .split (coordinate 12) (![⟨650523, by decide⟩,⟨650574, by decide⟩,⟨650593, by decide⟩,⟨650599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88084_650600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88084 ⟨650600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88084
    ⟨650600, by decide⟩ (by decide) (![⟨650523, by decide⟩,⟨650574, by decide⟩,⟨650593, by decide⟩,⟨650599, by decide⟩]) unmarked_context_12_88084_650600 node_context_12_88084_650600
  intro a
  fin_cases a
  · exact context_13_352336_650523
  · exact context_13_352337_650574
  · exact context_13_352338_650593
  · exact context_13_352339_650599

theorem selected_cut_25670 : selected 8 ⟨650628, by decide⟩
    (prefixPartial 13 352340) = some ⟨13, 2, 0, 650628, 352340, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_352340_650628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352340 ⟨650628, by decide⟩ :=
  accepted_of_selected 13 352340 ⟨650628, by decide⟩ ⟨13, 2, 0, 650628, 352340, 1497, 16384⟩
    (by decide) selected_cut_25670

theorem selected_cut_25671 : selected 8 ⟨650659, by decide⟩
    (prefixPartial 13 352341) = some ⟨13, 2, 0, 650659, 352341, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_352341_650659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352341 ⟨650659, by decide⟩ :=
  accepted_of_selected 13 352341 ⟨650659, by decide⟩ ⟨13, 2, 0, 650659, 352341, 1841, 16384⟩
    (by decide) selected_cut_25671

theorem selected_cut_25672 : selected 8 ⟨650676, by decide⟩
    (prefixPartial 13 352342) = some ⟨13, 2, 0, 650676, 352342, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_352342_650676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352342 ⟨650676, by decide⟩ :=
  accepted_of_selected 13 352342 ⟨650676, by decide⟩ ⟨13, 2, 0, 650676, 352342, 1361, 16384⟩
    (by decide) selected_cut_25672

theorem selected_cut_25673 : selected 8 ⟨650684, by decide⟩
    (prefixPartial 13 352343) = some ⟨13, 2, 0, 650684, 352343, 893, 16384⟩ := by
  decide +kernel

theorem context_13_352343_650684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352343 ⟨650684, by decide⟩ :=
  accepted_of_selected 13 352343 ⟨650684, by decide⟩ ⟨13, 2, 0, 650684, 352343, 893, 16384⟩
    (by decide) selected_cut_25673

theorem unmarked_context_12_88085_650685 : frontier 9 ⟨650685, by decide⟩
    (prefixCache 12 88085) (prefixPartial 12 88085) = false := by
  decide +kernel

theorem node_context_12_88085_650685 : EJMOriginalGlobalDAGData.nodes 9 ⟨650685, by decide⟩ =
    .split (coordinate 12) (![⟨650628, by decide⟩,⟨650659, by decide⟩,⟨650676, by decide⟩,⟨650684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88085_650685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88085 ⟨650685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88085
    ⟨650685, by decide⟩ (by decide) (![⟨650628, by decide⟩,⟨650659, by decide⟩,⟨650676, by decide⟩,⟨650684, by decide⟩]) unmarked_context_12_88085_650685 node_context_12_88085_650685
  intro a
  fin_cases a
  · exact context_13_352340_650628
  · exact context_13_352341_650659
  · exact context_13_352342_650676
  · exact context_13_352343_650684

theorem selected_cut_25674 : selected 8 ⟨650720, by decide⟩
    (prefixPartial 13 352344) = some ⟨13, 2, 0, 650720, 352344, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_352344_650720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352344 ⟨650720, by decide⟩ :=
  accepted_of_selected 13 352344 ⟨650720, by decide⟩ ⟨13, 2, 0, 650720, 352344, 1985, 16384⟩
    (by decide) selected_cut_25674

theorem selected_cut_25675 : selected 8 ⟨650760, by decide⟩
    (prefixPartial 13 352345) = some ⟨13, 2, 0, 650760, 352345, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_352345_650760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352345 ⟨650760, by decide⟩ :=
  accepted_of_selected 13 352345 ⟨650760, by decide⟩ ⟨13, 2, 0, 650760, 352345, 2521, 16384⟩
    (by decide) selected_cut_25675

theorem selected_cut_25676 : selected 8 ⟨650775, by decide⟩
    (prefixPartial 13 352346) = some ⟨13, 2, 0, 650775, 352346, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_352346_650775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352346 ⟨650775, by decide⟩ :=
  accepted_of_selected 13 352346 ⟨650775, by decide⟩ ⟨13, 2, 0, 650775, 352346, 1609, 16384⟩
    (by decide) selected_cut_25676

theorem selected_cut_25677 : selected 8 ⟨650783, by decide⟩
    (prefixPartial 13 352347) = some ⟨13, 2, 0, 650783, 352347, 985, 16384⟩ := by
  decide +kernel

theorem context_13_352347_650783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352347 ⟨650783, by decide⟩ :=
  accepted_of_selected 13 352347 ⟨650783, by decide⟩ ⟨13, 2, 0, 650783, 352347, 985, 16384⟩
    (by decide) selected_cut_25677

theorem unmarked_context_12_88086_650784 : frontier 9 ⟨650784, by decide⟩
    (prefixCache 12 88086) (prefixPartial 12 88086) = false := by
  decide +kernel

theorem node_context_12_88086_650784 : EJMOriginalGlobalDAGData.nodes 9 ⟨650784, by decide⟩ =
    .split (coordinate 12) (![⟨650720, by decide⟩,⟨650760, by decide⟩,⟨650775, by decide⟩,⟨650783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88086_650784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88086 ⟨650784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88086
    ⟨650784, by decide⟩ (by decide) (![⟨650720, by decide⟩,⟨650760, by decide⟩,⟨650775, by decide⟩,⟨650783, by decide⟩]) unmarked_context_12_88086_650784 node_context_12_88086_650784
  intro a
  fin_cases a
  · exact context_13_352344_650720
  · exact context_13_352345_650760
  · exact context_13_352346_650775
  · exact context_13_352347_650783

theorem selected_cut_25678 : selected 8 ⟨650819, by decide⟩
    (prefixPartial 13 352348) = some ⟨13, 2, 0, 650819, 352348, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_352348_650819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352348 ⟨650819, by decide⟩ :=
  accepted_of_selected 13 352348 ⟨650819, by decide⟩ ⟨13, 2, 0, 650819, 352348, 1957, 16384⟩
    (by decide) selected_cut_25678

theorem selected_cut_25679 : selected 8 ⟨650876, by decide⟩
    (prefixPartial 13 352349) = some ⟨13, 2, 0, 650876, 352349, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_352349_650876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352349 ⟨650876, by decide⟩ :=
  accepted_of_selected 13 352349 ⟨650876, by decide⟩ ⟨13, 2, 0, 650876, 352349, 2785, 16384⟩
    (by decide) selected_cut_25679

theorem selected_cut_25680 : selected 8 ⟨650893, by decide⟩
    (prefixPartial 13 352350) = some ⟨13, 2, 0, 650893, 352350, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_352350_650893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352350 ⟨650893, by decide⟩ :=
  accepted_of_selected 13 352350 ⟨650893, by decide⟩ ⟨13, 2, 0, 650893, 352350, 1609, 16384⟩
    (by decide) selected_cut_25680

theorem selected_cut_25681 : selected 8 ⟨650901, by decide⟩
    (prefixPartial 13 352351) = some ⟨13, 2, 0, 650901, 352351, 853, 16384⟩ := by
  decide +kernel

theorem context_13_352351_650901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352351 ⟨650901, by decide⟩ :=
  accepted_of_selected 13 352351 ⟨650901, by decide⟩ ⟨13, 2, 0, 650901, 352351, 853, 16384⟩
    (by decide) selected_cut_25681

theorem unmarked_context_12_88087_650902 : frontier 9 ⟨650902, by decide⟩
    (prefixCache 12 88087) (prefixPartial 12 88087) = false := by
  decide +kernel

theorem node_context_12_88087_650902 : EJMOriginalGlobalDAGData.nodes 9 ⟨650902, by decide⟩ =
    .split (coordinate 12) (![⟨650819, by decide⟩,⟨650876, by decide⟩,⟨650893, by decide⟩,⟨650901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88087_650902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88087 ⟨650902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88087
    ⟨650902, by decide⟩ (by decide) (![⟨650819, by decide⟩,⟨650876, by decide⟩,⟨650893, by decide⟩,⟨650901, by decide⟩]) unmarked_context_12_88087_650902 node_context_12_88087_650902
  intro a
  fin_cases a
  · exact context_13_352348_650819
  · exact context_13_352349_650876
  · exact context_13_352350_650893
  · exact context_13_352351_650901

theorem unmarked_context_11_22021_650903 : frontier 10 ⟨650903, by decide⟩
    (prefixCache 11 22021) (prefixPartial 11 22021) = false := by
  decide +kernel

theorem node_context_11_22021_650903 : EJMOriginalGlobalDAGData.nodes 10 ⟨650903, by decide⟩ =
    .split (coordinate 11) (![⟨650600, by decide⟩,⟨650685, by decide⟩,⟨650784, by decide⟩,⟨650902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22021_650903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22021 ⟨650903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22021
    ⟨650903, by decide⟩ (by decide) (![⟨650600, by decide⟩,⟨650685, by decide⟩,⟨650784, by decide⟩,⟨650902, by decide⟩]) unmarked_context_11_22021_650903 node_context_11_22021_650903
  intro a
  fin_cases a
  · exact context_12_88084_650600
  · exact context_12_88085_650685
  · exact context_12_88086_650784
  · exact context_12_88087_650902

theorem selected_cut_25682 : selected 8 ⟨650925, by decide⟩
    (prefixPartial 13 352352) = some ⟨13, 2, 0, 650925, 352352, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_352352_650925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352352 ⟨650925, by decide⟩ :=
  accepted_of_selected 13 352352 ⟨650925, by decide⟩ ⟨13, 2, 0, 650925, 352352, 1145, 16384⟩
    (by decide) selected_cut_25682

theorem selected_cut_25683 : selected 8 ⟨650963, by decide⟩
    (prefixPartial 13 352353) = some ⟨13, 2, 0, 650963, 352353, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_352353_650963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352353 ⟨650963, by decide⟩ :=
  accepted_of_selected 13 352353 ⟨650963, by decide⟩ ⟨13, 2, 0, 650963, 352353, 2177, 16384⟩
    (by decide) selected_cut_25683

theorem selected_cut_25684 : selected 8 ⟨650995, by decide⟩
    (prefixPartial 13 352354) = some ⟨13, 2, 0, 650995, 352354, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_352354_650995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352354 ⟨650995, by decide⟩ :=
  accepted_of_selected 13 352354 ⟨650995, by decide⟩ ⟨13, 2, 0, 650995, 352354, 1733, 16384⟩
    (by decide) selected_cut_25684

theorem selected_cut_25685 : selected 8 ⟨651001, by decide⟩
    (prefixPartial 13 352355) = some ⟨13, 2, 0, 651001, 352355, 889, 16384⟩ := by
  decide +kernel

theorem context_13_352355_651001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352355 ⟨651001, by decide⟩ :=
  accepted_of_selected 13 352355 ⟨651001, by decide⟩ ⟨13, 2, 0, 651001, 352355, 889, 16384⟩
    (by decide) selected_cut_25685

theorem unmarked_context_12_88088_651002 : frontier 9 ⟨651002, by decide⟩
    (prefixCache 12 88088) (prefixPartial 12 88088) = false := by
  decide +kernel

theorem node_context_12_88088_651002 : EJMOriginalGlobalDAGData.nodes 9 ⟨651002, by decide⟩ =
    .split (coordinate 12) (![⟨650925, by decide⟩,⟨650963, by decide⟩,⟨650995, by decide⟩,⟨651001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88088_651002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88088 ⟨651002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88088
    ⟨651002, by decide⟩ (by decide) (![⟨650925, by decide⟩,⟨650963, by decide⟩,⟨650995, by decide⟩,⟨651001, by decide⟩]) unmarked_context_12_88088_651002 node_context_12_88088_651002
  intro a
  fin_cases a
  · exact context_13_352352_650925
  · exact context_13_352353_650963
  · exact context_13_352354_650995
  · exact context_13_352355_651001

theorem selected_cut_25686 : selected 8 ⟨651029, by decide⟩
    (prefixPartial 13 352356) = some ⟨13, 2, 0, 651029, 352356, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_352356_651029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352356 ⟨651029, by decide⟩ :=
  accepted_of_selected 13 352356 ⟨651029, by decide⟩ ⟨13, 2, 0, 651029, 352356, 1385, 16384⟩
    (by decide) selected_cut_25686

theorem selected_cut_25687 : selected 8 ⟨651055, by decide⟩
    (prefixPartial 13 352357) = some ⟨13, 2, 0, 651055, 352357, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_352357_651055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352357 ⟨651055, by decide⟩ :=
  accepted_of_selected 13 352357 ⟨651055, by decide⟩ ⟨13, 2, 0, 651055, 352357, 1897, 16384⟩
    (by decide) selected_cut_25687

theorem selected_cut_25688 : selected 8 ⟨651080, by decide⟩
    (prefixPartial 13 352358) = some ⟨13, 2, 0, 651080, 352358, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_352358_651080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352358 ⟨651080, by decide⟩ :=
  accepted_of_selected 13 352358 ⟨651080, by decide⟩ ⟨13, 2, 0, 651080, 352358, 1817, 16384⟩
    (by decide) selected_cut_25688

theorem selected_cut_25689 : selected 8 ⟨651087, by decide⟩
    (prefixPartial 13 352359) = some ⟨13, 2, 0, 651087, 352359, 977, 16384⟩ := by
  decide +kernel

theorem context_13_352359_651087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352359 ⟨651087, by decide⟩ :=
  accepted_of_selected 13 352359 ⟨651087, by decide⟩ ⟨13, 2, 0, 651087, 352359, 977, 16384⟩
    (by decide) selected_cut_25689

theorem unmarked_context_12_88089_651088 : frontier 9 ⟨651088, by decide⟩
    (prefixCache 12 88089) (prefixPartial 12 88089) = false := by
  decide +kernel

theorem node_context_12_88089_651088 : EJMOriginalGlobalDAGData.nodes 9 ⟨651088, by decide⟩ =
    .split (coordinate 12) (![⟨651029, by decide⟩,⟨651055, by decide⟩,⟨651080, by decide⟩,⟨651087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88089_651088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88089 ⟨651088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88089
    ⟨651088, by decide⟩ (by decide) (![⟨651029, by decide⟩,⟨651055, by decide⟩,⟨651080, by decide⟩,⟨651087, by decide⟩]) unmarked_context_12_88089_651088 node_context_12_88089_651088
  intro a
  fin_cases a
  · exact context_13_352356_651029
  · exact context_13_352357_651055
  · exact context_13_352358_651080
  · exact context_13_352359_651087

theorem selected_cut_25690 : selected 8 ⟨651125, by decide⟩
    (prefixPartial 13 352360) = some ⟨13, 2, 0, 651125, 352360, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_352360_651125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352360 ⟨651125, by decide⟩ :=
  accepted_of_selected 13 352360 ⟨651125, by decide⟩ ⟨13, 2, 0, 651125, 352360, 1417, 16384⟩
    (by decide) selected_cut_25690

theorem selected_cut_25691 : selected 8 ⟨651155, by decide⟩
    (prefixPartial 13 352361) = some ⟨13, 2, 0, 651155, 352361, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_352361_651155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352361 ⟨651155, by decide⟩ :=
  accepted_of_selected 13 352361 ⟨651155, by decide⟩ ⟨13, 2, 0, 651155, 352361, 2081, 16384⟩
    (by decide) selected_cut_25691

theorem selected_cut_25692 : selected 8 ⟨651173, by decide⟩
    (prefixPartial 13 352362) = some ⟨13, 2, 0, 651173, 352362, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_352362_651173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352362 ⟨651173, by decide⟩ :=
  accepted_of_selected 13 352362 ⟨651173, by decide⟩ ⟨13, 2, 0, 651173, 352362, 1605, 16384⟩
    (by decide) selected_cut_25692

theorem selected_cut_25693 : selected 8 ⟨651180, by decide⟩
    (prefixPartial 13 352363) = some ⟨13, 2, 0, 651180, 352363, 961, 16384⟩ := by
  decide +kernel

theorem context_13_352363_651180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352363 ⟨651180, by decide⟩ :=
  accepted_of_selected 13 352363 ⟨651180, by decide⟩ ⟨13, 2, 0, 651180, 352363, 961, 16384⟩
    (by decide) selected_cut_25693

theorem unmarked_context_12_88090_651181 : frontier 9 ⟨651181, by decide⟩
    (prefixCache 12 88090) (prefixPartial 12 88090) = false := by
  decide +kernel

theorem node_context_12_88090_651181 : EJMOriginalGlobalDAGData.nodes 9 ⟨651181, by decide⟩ =
    .split (coordinate 12) (![⟨651125, by decide⟩,⟨651155, by decide⟩,⟨651173, by decide⟩,⟨651180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88090_651181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88090 ⟨651181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88090
    ⟨651181, by decide⟩ (by decide) (![⟨651125, by decide⟩,⟨651155, by decide⟩,⟨651173, by decide⟩,⟨651180, by decide⟩]) unmarked_context_12_88090_651181 node_context_12_88090_651181
  intro a
  fin_cases a
  · exact context_13_352360_651125
  · exact context_13_352361_651155
  · exact context_13_352362_651173
  · exact context_13_352363_651180

theorem selected_cut_25694 : selected 8 ⟨651213, by decide⟩
    (prefixPartial 13 352364) = some ⟨13, 2, 0, 651213, 352364, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_352364_651213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352364 ⟨651213, by decide⟩ :=
  accepted_of_selected 13 352364 ⟨651213, by decide⟩ ⟨13, 2, 0, 651213, 352364, 1637, 16384⟩
    (by decide) selected_cut_25694

theorem selected_cut_25695 : selected 8 ⟨651256, by decide⟩
    (prefixPartial 13 352365) = some ⟨13, 2, 0, 651256, 352365, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_352365_651256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352365 ⟨651256, by decide⟩ :=
  accepted_of_selected 13 352365 ⟨651256, by decide⟩ ⟨13, 2, 0, 651256, 352365, 2557, 16384⟩
    (by decide) selected_cut_25695

theorem selected_cut_25696 : selected 8 ⟨651278, by decide⟩
    (prefixPartial 13 352366) = some ⟨13, 2, 0, 651278, 352366, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_352366_651278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352366 ⟨651278, by decide⟩ :=
  accepted_of_selected 13 352366 ⟨651278, by decide⟩ ⟨13, 2, 0, 651278, 352366, 1889, 16384⟩
    (by decide) selected_cut_25696

theorem selected_cut_25697 : selected 8 ⟨651284, by decide⟩
    (prefixPartial 13 352367) = some ⟨13, 2, 0, 651284, 352367, 921, 16384⟩ := by
  decide +kernel

theorem context_13_352367_651284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352367 ⟨651284, by decide⟩ :=
  accepted_of_selected 13 352367 ⟨651284, by decide⟩ ⟨13, 2, 0, 651284, 352367, 921, 16384⟩
    (by decide) selected_cut_25697

theorem unmarked_context_12_88091_651285 : frontier 9 ⟨651285, by decide⟩
    (prefixCache 12 88091) (prefixPartial 12 88091) = false := by
  decide +kernel

theorem node_context_12_88091_651285 : EJMOriginalGlobalDAGData.nodes 9 ⟨651285, by decide⟩ =
    .split (coordinate 12) (![⟨651213, by decide⟩,⟨651256, by decide⟩,⟨651278, by decide⟩,⟨651284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88091_651285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88091 ⟨651285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88091
    ⟨651285, by decide⟩ (by decide) (![⟨651213, by decide⟩,⟨651256, by decide⟩,⟨651278, by decide⟩,⟨651284, by decide⟩]) unmarked_context_12_88091_651285 node_context_12_88091_651285
  intro a
  fin_cases a
  · exact context_13_352364_651213
  · exact context_13_352365_651256
  · exact context_13_352366_651278
  · exact context_13_352367_651284

theorem unmarked_context_11_22022_651286 : frontier 10 ⟨651286, by decide⟩
    (prefixCache 11 22022) (prefixPartial 11 22022) = false := by
  decide +kernel

theorem node_context_11_22022_651286 : EJMOriginalGlobalDAGData.nodes 10 ⟨651286, by decide⟩ =
    .split (coordinate 11) (![⟨651002, by decide⟩,⟨651088, by decide⟩,⟨651181, by decide⟩,⟨651285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22022_651286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22022 ⟨651286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22022
    ⟨651286, by decide⟩ (by decide) (![⟨651002, by decide⟩,⟨651088, by decide⟩,⟨651181, by decide⟩,⟨651285, by decide⟩]) unmarked_context_11_22022_651286 node_context_11_22022_651286
  intro a
  fin_cases a
  · exact context_12_88088_651002
  · exact context_12_88089_651088
  · exact context_12_88090_651181
  · exact context_12_88091_651285

theorem selected_cut_25698 : selected 8 ⟨651308, by decide⟩
    (prefixPartial 13 352368) = some ⟨13, 2, 0, 651308, 352368, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_352368_651308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352368 ⟨651308, by decide⟩ :=
  accepted_of_selected 13 352368 ⟨651308, by decide⟩ ⟨13, 2, 0, 651308, 352368, 1141, 16384⟩
    (by decide) selected_cut_25698

theorem selected_cut_25699 : selected 8 ⟨651360, by decide⟩
    (prefixPartial 13 352369) = some ⟨13, 2, 0, 651360, 352369, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_352369_651360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352369 ⟨651360, by decide⟩ :=
  accepted_of_selected 13 352369 ⟨651360, by decide⟩ ⟨13, 2, 0, 651360, 352369, 2373, 16384⟩
    (by decide) selected_cut_25699

theorem selected_cut_25700 : selected 8 ⟨651399, by decide⟩
    (prefixPartial 13 352370) = some ⟨13, 2, 0, 651399, 352370, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_352370_651399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352370 ⟨651399, by decide⟩ :=
  accepted_of_selected 13 352370 ⟨651399, by decide⟩ ⟨13, 2, 0, 651399, 352370, 1777, 16384⟩
    (by decide) selected_cut_25700

theorem selected_cut_25701 : selected 8 ⟨651405, by decide⟩
    (prefixPartial 13 352371) = some ⟨13, 2, 0, 651405, 352371, 917, 16384⟩ := by
  decide +kernel

theorem context_13_352371_651405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352371 ⟨651405, by decide⟩ :=
  accepted_of_selected 13 352371 ⟨651405, by decide⟩ ⟨13, 2, 0, 651405, 352371, 917, 16384⟩
    (by decide) selected_cut_25701

theorem unmarked_context_12_88092_651406 : frontier 9 ⟨651406, by decide⟩
    (prefixCache 12 88092) (prefixPartial 12 88092) = false := by
  decide +kernel

theorem node_context_12_88092_651406 : EJMOriginalGlobalDAGData.nodes 9 ⟨651406, by decide⟩ =
    .split (coordinate 12) (![⟨651308, by decide⟩,⟨651360, by decide⟩,⟨651399, by decide⟩,⟨651405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88092_651406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88092 ⟨651406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88092
    ⟨651406, by decide⟩ (by decide) (![⟨651308, by decide⟩,⟨651360, by decide⟩,⟨651399, by decide⟩,⟨651405, by decide⟩]) unmarked_context_12_88092_651406 node_context_12_88092_651406
  intro a
  fin_cases a
  · exact context_13_352368_651308
  · exact context_13_352369_651360
  · exact context_13_352370_651399
  · exact context_13_352371_651405

theorem selected_cut_25702 : selected 8 ⟨651435, by decide⟩
    (prefixPartial 13 352372) = some ⟨13, 2, 0, 651435, 352372, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_352372_651435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352372 ⟨651435, by decide⟩ :=
  accepted_of_selected 13 352372 ⟨651435, by decide⟩ ⟨13, 2, 0, 651435, 352372, 1341, 16384⟩
    (by decide) selected_cut_25702

theorem selected_cut_25703 : selected 8 ⟨651466, by decide⟩
    (prefixPartial 13 352373) = some ⟨13, 2, 0, 651466, 352373, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_352373_651466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352373 ⟨651466, by decide⟩ :=
  accepted_of_selected 13 352373 ⟨651466, by decide⟩ ⟨13, 2, 0, 651466, 352373, 2101, 16384⟩
    (by decide) selected_cut_25703

theorem selected_cut_25704 : selected 8 ⟨651498, by decide⟩
    (prefixPartial 13 352374) = some ⟨13, 2, 0, 651498, 352374, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_352374_651498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352374 ⟨651498, by decide⟩ :=
  accepted_of_selected 13 352374 ⟨651498, by decide⟩ ⟨13, 2, 0, 651498, 352374, 1965, 16384⟩
    (by decide) selected_cut_25704

theorem selected_cut_25705 : selected 8 ⟨651506, by decide⟩
    (prefixPartial 13 352375) = some ⟨13, 2, 0, 651506, 352375, 961, 16384⟩ := by
  decide +kernel

theorem context_13_352375_651506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352375 ⟨651506, by decide⟩ :=
  accepted_of_selected 13 352375 ⟨651506, by decide⟩ ⟨13, 2, 0, 651506, 352375, 961, 16384⟩
    (by decide) selected_cut_25705

theorem unmarked_context_12_88093_651507 : frontier 9 ⟨651507, by decide⟩
    (prefixCache 12 88093) (prefixPartial 12 88093) = false := by
  decide +kernel

theorem node_context_12_88093_651507 : EJMOriginalGlobalDAGData.nodes 9 ⟨651507, by decide⟩ =
    .split (coordinate 12) (![⟨651435, by decide⟩,⟨651466, by decide⟩,⟨651498, by decide⟩,⟨651506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88093_651507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88093 ⟨651507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88093
    ⟨651507, by decide⟩ (by decide) (![⟨651435, by decide⟩,⟨651466, by decide⟩,⟨651498, by decide⟩,⟨651506, by decide⟩]) unmarked_context_12_88093_651507 node_context_12_88093_651507
  intro a
  fin_cases a
  · exact context_13_352372_651435
  · exact context_13_352373_651466
  · exact context_13_352374_651498
  · exact context_13_352375_651506

theorem selected_cut_25706 : selected 8 ⟨651538, by decide⟩
    (prefixPartial 13 352376) = some ⟨13, 2, 0, 651538, 352376, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_352376_651538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352376 ⟨651538, by decide⟩ :=
  accepted_of_selected 13 352376 ⟨651538, by decide⟩ ⟨13, 2, 0, 651538, 352376, 1521, 16384⟩
    (by decide) selected_cut_25706

theorem selected_cut_25707 : selected 8 ⟨651579, by decide⟩
    (prefixPartial 13 352377) = some ⟨13, 2, 0, 651579, 352377, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_352377_651579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352377 ⟨651579, by decide⟩ :=
  accepted_of_selected 13 352377 ⟨651579, by decide⟩ ⟨13, 2, 0, 651579, 352377, 2389, 16384⟩
    (by decide) selected_cut_25707

theorem selected_cut_25708 : selected 8 ⟨651607, by decide⟩
    (prefixPartial 13 352378) = some ⟨13, 2, 0, 651607, 352378, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_352378_651607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352378 ⟨651607, by decide⟩ :=
  accepted_of_selected 13 352378 ⟨651607, by decide⟩ ⟨13, 2, 0, 651607, 352378, 1953, 16384⟩
    (by decide) selected_cut_25708

theorem selected_cut_25709 : selected 8 ⟨651615, by decide⟩
    (prefixPartial 13 352379) = some ⟨13, 2, 0, 651615, 352379, 957, 16384⟩ := by
  decide +kernel

theorem context_13_352379_651615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352379 ⟨651615, by decide⟩ :=
  accepted_of_selected 13 352379 ⟨651615, by decide⟩ ⟨13, 2, 0, 651615, 352379, 957, 16384⟩
    (by decide) selected_cut_25709

theorem unmarked_context_12_88094_651616 : frontier 9 ⟨651616, by decide⟩
    (prefixCache 12 88094) (prefixPartial 12 88094) = false := by
  decide +kernel

theorem node_context_12_88094_651616 : EJMOriginalGlobalDAGData.nodes 9 ⟨651616, by decide⟩ =
    .split (coordinate 12) (![⟨651538, by decide⟩,⟨651579, by decide⟩,⟨651607, by decide⟩,⟨651615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88094_651616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88094 ⟨651616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88094
    ⟨651616, by decide⟩ (by decide) (![⟨651538, by decide⟩,⟨651579, by decide⟩,⟨651607, by decide⟩,⟨651615, by decide⟩]) unmarked_context_12_88094_651616 node_context_12_88094_651616
  intro a
  fin_cases a
  · exact context_13_352376_651538
  · exact context_13_352377_651579
  · exact context_13_352378_651607
  · exact context_13_352379_651615

theorem selected_cut_25710 : selected 8 ⟨651644, by decide⟩
    (prefixPartial 13 352380) = some ⟨13, 2, 0, 651644, 352380, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_352380_651644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352380 ⟨651644, by decide⟩ :=
  accepted_of_selected 13 352380 ⟨651644, by decide⟩ ⟨13, 2, 0, 651644, 352380, 1341, 16384⟩
    (by decide) selected_cut_25710

theorem selected_cut_25711 : selected 8 ⟨651691, by decide⟩
    (prefixPartial 13 352381) = some ⟨13, 2, 0, 651691, 352381, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_352381_651691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352381 ⟨651691, by decide⟩ :=
  accepted_of_selected 13 352381 ⟨651691, by decide⟩ ⟨13, 2, 0, 651691, 352381, 2433, 16384⟩
    (by decide) selected_cut_25711

theorem selected_cut_25712 : selected 8 ⟨651713, by decide⟩
    (prefixPartial 13 352382) = some ⟨13, 2, 0, 651713, 352382, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_352382_651713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352382 ⟨651713, by decide⟩ :=
  accepted_of_selected 13 352382 ⟨651713, by decide⟩ ⟨13, 2, 0, 651713, 352382, 1769, 16384⟩
    (by decide) selected_cut_25712

theorem selected_cut_25713 : selected 8 ⟨651719, by decide⟩
    (prefixPartial 13 352383) = some ⟨13, 2, 0, 651719, 352383, 765, 16384⟩ := by
  decide +kernel

theorem context_13_352383_651719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352383 ⟨651719, by decide⟩ :=
  accepted_of_selected 13 352383 ⟨651719, by decide⟩ ⟨13, 2, 0, 651719, 352383, 765, 16384⟩
    (by decide) selected_cut_25713

theorem unmarked_context_12_88095_651720 : frontier 9 ⟨651720, by decide⟩
    (prefixCache 12 88095) (prefixPartial 12 88095) = false := by
  decide +kernel

theorem node_context_12_88095_651720 : EJMOriginalGlobalDAGData.nodes 9 ⟨651720, by decide⟩ =
    .split (coordinate 12) (![⟨651644, by decide⟩,⟨651691, by decide⟩,⟨651713, by decide⟩,⟨651719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88095_651720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88095 ⟨651720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88095
    ⟨651720, by decide⟩ (by decide) (![⟨651644, by decide⟩,⟨651691, by decide⟩,⟨651713, by decide⟩,⟨651719, by decide⟩]) unmarked_context_12_88095_651720 node_context_12_88095_651720
  intro a
  fin_cases a
  · exact context_13_352380_651644
  · exact context_13_352381_651691
  · exact context_13_352382_651713
  · exact context_13_352383_651719

theorem unmarked_context_11_22023_651721 : frontier 10 ⟨651721, by decide⟩
    (prefixCache 11 22023) (prefixPartial 11 22023) = false := by
  decide +kernel

theorem node_context_11_22023_651721 : EJMOriginalGlobalDAGData.nodes 10 ⟨651721, by decide⟩ =
    .split (coordinate 11) (![⟨651406, by decide⟩,⟨651507, by decide⟩,⟨651616, by decide⟩,⟨651720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22023_651721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22023 ⟨651721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22023
    ⟨651721, by decide⟩ (by decide) (![⟨651406, by decide⟩,⟨651507, by decide⟩,⟨651616, by decide⟩,⟨651720, by decide⟩]) unmarked_context_11_22023_651721 node_context_11_22023_651721
  intro a
  fin_cases a
  · exact context_12_88092_651406
  · exact context_12_88093_651507
  · exact context_12_88094_651616
  · exact context_12_88095_651720

theorem unmarked_context_10_5505_651722 : frontier 11 ⟨651722, by decide⟩
    (prefixCache 10 5505) (prefixPartial 10 5505) = false := by
  decide +kernel

theorem node_context_10_5505_651722 : EJMOriginalGlobalDAGData.nodes 11 ⟨651722, by decide⟩ =
    .split (coordinate 10) (![⟨650500, by decide⟩,⟨650903, by decide⟩,⟨651286, by decide⟩,⟨651721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5505_651722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5505 ⟨651722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5505
    ⟨651722, by decide⟩ (by decide) (![⟨650500, by decide⟩,⟨650903, by decide⟩,⟨651286, by decide⟩,⟨651721, by decide⟩]) unmarked_context_10_5505_651722 node_context_10_5505_651722
  intro a
  fin_cases a
  · exact context_11_22020_650500
  · exact context_11_22021_650903
  · exact context_11_22022_651286
  · exact context_11_22023_651721

theorem selected_cut_25714 : selected 9 ⟨355612, by decide⟩
    (prefixPartial 12 88096) = some ⟨12, 1, 0, 355612, 88096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88096_355612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88096 ⟨355612, by decide⟩ :=
  accepted_of_selected 12 88096 ⟨355612, by decide⟩ ⟨12, 1, 0, 355612, 88096, 1, 65536⟩
    (by decide) selected_cut_25714

theorem selected_cut_25715 : selected 8 ⟨651745, by decide⟩
    (prefixPartial 13 352388) = some ⟨13, 2, 0, 651745, 352388, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_352388_651745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352388 ⟨651745, by decide⟩ :=
  accepted_of_selected 13 352388 ⟨651745, by decide⟩ ⟨13, 2, 0, 651745, 352388, 1321, 16384⟩
    (by decide) selected_cut_25715

theorem selected_cut_25716 : selected 8 ⟨651770, by decide⟩
    (prefixPartial 13 352389) = some ⟨13, 2, 0, 651770, 352389, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_352389_651770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352389 ⟨651770, by decide⟩ :=
  accepted_of_selected 13 352389 ⟨651770, by decide⟩ ⟨13, 2, 0, 651770, 352389, 1601, 16384⟩
    (by decide) selected_cut_25716

theorem selected_cut_25717 : selected 8 ⟨651786, by decide⟩
    (prefixPartial 13 352390) = some ⟨13, 2, 0, 651786, 352390, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_352390_651786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352390 ⟨651786, by decide⟩ :=
  accepted_of_selected 13 352390 ⟨651786, by decide⟩ ⟨13, 2, 0, 651786, 352390, 1201, 16384⟩
    (by decide) selected_cut_25717

theorem selected_cut_25718 : selected 8 ⟨651791, by decide⟩
    (prefixPartial 13 352391) = some ⟨13, 2, 0, 651791, 352391, 825, 16384⟩ := by
  decide +kernel

theorem context_13_352391_651791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352391 ⟨651791, by decide⟩ :=
  accepted_of_selected 13 352391 ⟨651791, by decide⟩ ⟨13, 2, 0, 651791, 352391, 825, 16384⟩
    (by decide) selected_cut_25718

theorem unmarked_context_12_88097_651792 : frontier 9 ⟨651792, by decide⟩
    (prefixCache 12 88097) (prefixPartial 12 88097) = false := by
  decide +kernel

theorem node_context_12_88097_651792 : EJMOriginalGlobalDAGData.nodes 9 ⟨651792, by decide⟩ =
    .split (coordinate 12) (![⟨651745, by decide⟩,⟨651770, by decide⟩,⟨651786, by decide⟩,⟨651791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88097_651792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88097 ⟨651792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88097
    ⟨651792, by decide⟩ (by decide) (![⟨651745, by decide⟩,⟨651770, by decide⟩,⟨651786, by decide⟩,⟨651791, by decide⟩]) unmarked_context_12_88097_651792 node_context_12_88097_651792
  intro a
  fin_cases a
  · exact context_13_352388_651745
  · exact context_13_352389_651770
  · exact context_13_352390_651786
  · exact context_13_352391_651791

theorem selected_cut_25719 : selected 8 ⟨651816, by decide⟩
    (prefixPartial 13 352392) = some ⟨13, 2, 0, 651816, 352392, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_352392_651816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352392 ⟨651816, by decide⟩ :=
  accepted_of_selected 13 352392 ⟨651816, by decide⟩ ⟨13, 2, 0, 651816, 352392, 1265, 16384⟩
    (by decide) selected_cut_25719

theorem selected_cut_25720 : selected 8 ⟨651846, by decide⟩
    (prefixPartial 13 352393) = some ⟨13, 2, 0, 651846, 352393, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_352393_651846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352393 ⟨651846, by decide⟩ :=
  accepted_of_selected 13 352393 ⟨651846, by decide⟩ ⟨13, 2, 0, 651846, 352393, 2137, 16384⟩
    (by decide) selected_cut_25720

theorem selected_cut_25721 : selected 8 ⟨651864, by decide⟩
    (prefixPartial 13 352394) = some ⟨13, 2, 0, 651864, 352394, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_352394_651864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352394 ⟨651864, by decide⟩ :=
  accepted_of_selected 13 352394 ⟨651864, by decide⟩ ⟨13, 2, 0, 651864, 352394, 1365, 16384⟩
    (by decide) selected_cut_25721

theorem selected_cut_25722 : selected 8 ⟨651870, by decide⟩
    (prefixPartial 13 352395) = some ⟨13, 2, 0, 651870, 352395, 925, 16384⟩ := by
  decide +kernel

theorem context_13_352395_651870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352395 ⟨651870, by decide⟩ :=
  accepted_of_selected 13 352395 ⟨651870, by decide⟩ ⟨13, 2, 0, 651870, 352395, 925, 16384⟩
    (by decide) selected_cut_25722

theorem unmarked_context_12_88098_651871 : frontier 9 ⟨651871, by decide⟩
    (prefixCache 12 88098) (prefixPartial 12 88098) = false := by
  decide +kernel

theorem node_context_12_88098_651871 : EJMOriginalGlobalDAGData.nodes 9 ⟨651871, by decide⟩ =
    .split (coordinate 12) (![⟨651816, by decide⟩,⟨651846, by decide⟩,⟨651864, by decide⟩,⟨651870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88098_651871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88098 ⟨651871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88098
    ⟨651871, by decide⟩ (by decide) (![⟨651816, by decide⟩,⟨651846, by decide⟩,⟨651864, by decide⟩,⟨651870, by decide⟩]) unmarked_context_12_88098_651871 node_context_12_88098_651871
  intro a
  fin_cases a
  · exact context_13_352392_651816
  · exact context_13_352393_651846
  · exact context_13_352394_651864
  · exact context_13_352395_651870

theorem selected_cut_25723 : selected 8 ⟨651893, by decide⟩
    (prefixPartial 13 352396) = some ⟨13, 2, 0, 651893, 352396, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_352396_651893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352396 ⟨651893, by decide⟩ :=
  accepted_of_selected 13 352396 ⟨651893, by decide⟩ ⟨13, 2, 0, 651893, 352396, 1213, 16384⟩
    (by decide) selected_cut_25723

theorem selected_cut_25724 : selected 8 ⟨651928, by decide⟩
    (prefixPartial 13 352397) = some ⟨13, 2, 0, 651928, 352397, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_352397_651928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352397 ⟨651928, by decide⟩ :=
  accepted_of_selected 13 352397 ⟨651928, by decide⟩ ⟨13, 2, 0, 651928, 352397, 2249, 16384⟩
    (by decide) selected_cut_25724

theorem selected_cut_25725 : selected 8 ⟨651943, by decide⟩
    (prefixPartial 13 352398) = some ⟨13, 2, 0, 651943, 352398, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_352398_651943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352398 ⟨651943, by decide⟩ :=
  accepted_of_selected 13 352398 ⟨651943, by decide⟩ ⟨13, 2, 0, 651943, 352398, 1273, 16384⟩
    (by decide) selected_cut_25725

theorem selected_cut_25726 : selected 8 ⟨651948, by decide⟩
    (prefixPartial 13 352399) = some ⟨13, 2, 0, 651948, 352399, 777, 16384⟩ := by
  decide +kernel

theorem context_13_352399_651948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352399 ⟨651948, by decide⟩ :=
  accepted_of_selected 13 352399 ⟨651948, by decide⟩ ⟨13, 2, 0, 651948, 352399, 777, 16384⟩
    (by decide) selected_cut_25726

theorem unmarked_context_12_88099_651949 : frontier 9 ⟨651949, by decide⟩
    (prefixCache 12 88099) (prefixPartial 12 88099) = false := by
  decide +kernel

theorem node_context_12_88099_651949 : EJMOriginalGlobalDAGData.nodes 9 ⟨651949, by decide⟩ =
    .split (coordinate 12) (![⟨651893, by decide⟩,⟨651928, by decide⟩,⟨651943, by decide⟩,⟨651948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88099_651949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88099 ⟨651949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88099
    ⟨651949, by decide⟩ (by decide) (![⟨651893, by decide⟩,⟨651928, by decide⟩,⟨651943, by decide⟩,⟨651948, by decide⟩]) unmarked_context_12_88099_651949 node_context_12_88099_651949
  intro a
  fin_cases a
  · exact context_13_352396_651893
  · exact context_13_352397_651928
  · exact context_13_352398_651943
  · exact context_13_352399_651948

theorem unmarked_context_11_22024_651950 : frontier 10 ⟨651950, by decide⟩
    (prefixCache 11 22024) (prefixPartial 11 22024) = false := by
  decide +kernel

theorem node_context_11_22024_651950 : EJMOriginalGlobalDAGData.nodes 10 ⟨651950, by decide⟩ =
    .split (coordinate 11) (![⟨355612, by decide⟩,⟨651792, by decide⟩,⟨651871, by decide⟩,⟨651949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22024_651950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22024 ⟨651950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22024
    ⟨651950, by decide⟩ (by decide) (![⟨355612, by decide⟩,⟨651792, by decide⟩,⟨651871, by decide⟩,⟨651949, by decide⟩]) unmarked_context_11_22024_651950 node_context_11_22024_651950
  intro a
  fin_cases a
  · exact context_12_88096_355612
  · exact context_12_88097_651792
  · exact context_12_88098_651871
  · exact context_12_88099_651949

theorem selected_cut_25727 : selected 8 ⟨651962, by decide⟩
    (prefixPartial 13 352400) = some ⟨13, 2, 0, 651962, 352400, 821, 16384⟩ := by
  decide +kernel

theorem context_13_352400_651962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352400 ⟨651962, by decide⟩ :=
  accepted_of_selected 13 352400 ⟨651962, by decide⟩ ⟨13, 2, 0, 651962, 352400, 821, 16384⟩
    (by decide) selected_cut_25727

theorem selected_cut_25728 : selected 8 ⟨652008, by decide⟩
    (prefixPartial 13 352401) = some ⟨13, 2, 0, 652008, 352401, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_352401_652008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352401 ⟨652008, by decide⟩ :=
  accepted_of_selected 13 352401 ⟨652008, by decide⟩ ⟨13, 2, 0, 652008, 352401, 2253, 16384⟩
    (by decide) selected_cut_25728

theorem selected_cut_25729 : selected 8 ⟨652025, by decide⟩
    (prefixPartial 13 352402) = some ⟨13, 2, 0, 652025, 352402, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_352402_652025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352402 ⟨652025, by decide⟩ :=
  accepted_of_selected 13 352402 ⟨652025, by decide⟩ ⟨13, 2, 0, 652025, 352402, 1273, 16384⟩
    (by decide) selected_cut_25729

theorem selected_cut_25730 : selected 8 ⟨652030, by decide⟩
    (prefixPartial 13 352403) = some ⟨13, 2, 0, 652030, 352403, 853, 16384⟩ := by
  decide +kernel

theorem context_13_352403_652030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352403 ⟨652030, by decide⟩ :=
  accepted_of_selected 13 352403 ⟨652030, by decide⟩ ⟨13, 2, 0, 652030, 352403, 853, 16384⟩
    (by decide) selected_cut_25730

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
