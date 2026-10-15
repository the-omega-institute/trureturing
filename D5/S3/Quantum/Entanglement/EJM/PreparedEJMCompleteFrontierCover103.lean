/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover102
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09891 : selected 9 ⟨272285, by decide⟩
    (prefixPartial 12 24735) = some ⟨12, 2, 0, 272285, 24735, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_24735_272285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24735 ⟨272285, by decide⟩ :=
  accepted_of_selected 12 24735 ⟨272285, by decide⟩ ⟨12, 2, 0, 272285, 24735, 1925, 65536⟩
    (by decide) selected_cut_09891

theorem unmarked_context_11_6183_272286 : frontier 10 ⟨272286, by decide⟩
    (prefixCache 11 6183) (prefixPartial 11 6183) = false := by
  decide +kernel

theorem node_context_11_6183_272286 : EJMOriginalGlobalDAGData.nodes 10 ⟨272286, by decide⟩ =
    .split (coordinate 11) (![⟨272216, by decide⟩,⟨272240, by decide⟩,⟨272264, by decide⟩,⟨272285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6183_272286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6183 ⟨272286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6183
    ⟨272286, by decide⟩ (by decide) (![⟨272216, by decide⟩,⟨272240, by decide⟩,⟨272264, by decide⟩,⟨272285, by decide⟩]) unmarked_context_11_6183_272286 node_context_11_6183_272286
  intro a
  fin_cases a
  · exact context_12_24732_272216
  · exact context_12_24733_272240
  · exact context_12_24734_272264
  · exact context_12_24735_272285

theorem unmarked_context_10_1545_272287 : frontier 11 ⟨272287, by decide⟩
    (prefixCache 10 1545) (prefixPartial 10 1545) = false := by
  decide +kernel

theorem node_context_10_1545_272287 : EJMOriginalGlobalDAGData.nodes 11 ⟨272287, by decide⟩ =
    .split (coordinate 10) (![⟨272010, by decide⟩,⟨272099, by decide⟩,⟨272196, by decide⟩,⟨272286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1545_272287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1545 ⟨272287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1545
    ⟨272287, by decide⟩ (by decide) (![⟨272010, by decide⟩,⟨272099, by decide⟩,⟨272196, by decide⟩,⟨272286, by decide⟩]) unmarked_context_10_1545_272287 node_context_10_1545_272287
  intro a
  fin_cases a
  · exact context_11_6180_272010
  · exact context_11_6181_272099
  · exact context_11_6182_272196
  · exact context_11_6183_272286

theorem selected_cut_09892 : selected 9 ⟨272312, by decide⟩
    (prefixPartial 12 24736) = some ⟨12, 2, 0, 272312, 24736, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_24736_272312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24736 ⟨272312, by decide⟩ :=
  accepted_of_selected 12 24736 ⟨272312, by decide⟩ ⟨12, 2, 0, 272312, 24736, 2197, 65536⟩
    (by decide) selected_cut_09892

theorem selected_cut_09893 : selected 9 ⟨272334, by decide⟩
    (prefixPartial 12 24737) = some ⟨12, 2, 0, 272334, 24737, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_24737_272334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24737 ⟨272334, by decide⟩ :=
  accepted_of_selected 12 24737 ⟨272334, by decide⟩ ⟨12, 2, 0, 272334, 24737, 1485, 65536⟩
    (by decide) selected_cut_09893

theorem selected_cut_09894 : selected 9 ⟨272355, by decide⟩
    (prefixPartial 12 24738) = some ⟨12, 2, 0, 272355, 24738, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_24738_272355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24738 ⟨272355, by decide⟩ :=
  accepted_of_selected 12 24738 ⟨272355, by decide⟩ ⟨12, 2, 0, 272355, 24738, 1453, 65536⟩
    (by decide) selected_cut_09894

theorem selected_cut_09895 : selected 9 ⟨272372, by decide⟩
    (prefixPartial 12 24739) = some ⟨12, 2, 0, 272372, 24739, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_24739_272372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24739 ⟨272372, by decide⟩ :=
  accepted_of_selected 12 24739 ⟨272372, by decide⟩ ⟨12, 2, 0, 272372, 24739, 1417, 65536⟩
    (by decide) selected_cut_09895

theorem unmarked_context_11_6184_272373 : frontier 10 ⟨272373, by decide⟩
    (prefixCache 11 6184) (prefixPartial 11 6184) = false := by
  decide +kernel

theorem node_context_11_6184_272373 : EJMOriginalGlobalDAGData.nodes 10 ⟨272373, by decide⟩ =
    .split (coordinate 11) (![⟨272312, by decide⟩,⟨272334, by decide⟩,⟨272355, by decide⟩,⟨272372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6184_272373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6184 ⟨272373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6184
    ⟨272373, by decide⟩ (by decide) (![⟨272312, by decide⟩,⟨272334, by decide⟩,⟨272355, by decide⟩,⟨272372, by decide⟩]) unmarked_context_11_6184_272373 node_context_11_6184_272373
  intro a
  fin_cases a
  · exact context_12_24736_272312
  · exact context_12_24737_272334
  · exact context_12_24738_272355
  · exact context_12_24739_272372

theorem selected_cut_09896 : selected 9 ⟨272391, by decide⟩
    (prefixPartial 12 24740) = some ⟨12, 2, 0, 272391, 24740, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_24740_272391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24740 ⟨272391, by decide⟩ :=
  accepted_of_selected 12 24740 ⟨272391, by decide⟩ ⟨12, 2, 0, 272391, 24740, 1405, 65536⟩
    (by decide) selected_cut_09896

theorem selected_cut_09897 : selected 9 ⟨272409, by decide⟩
    (prefixPartial 12 24741) = some ⟨12, 2, 0, 272409, 24741, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_24741_272409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24741 ⟨272409, by decide⟩ :=
  accepted_of_selected 12 24741 ⟨272409, by decide⟩ ⟨12, 2, 0, 272409, 24741, 1613, 65536⟩
    (by decide) selected_cut_09897

theorem selected_cut_09898 : selected 9 ⟨272428, by decide⟩
    (prefixPartial 12 24742) = some ⟨12, 2, 0, 272428, 24742, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_24742_272428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24742 ⟨272428, by decide⟩ :=
  accepted_of_selected 12 24742 ⟨272428, by decide⟩ ⟨12, 2, 0, 272428, 24742, 1657, 65536⟩
    (by decide) selected_cut_09898

theorem selected_cut_09899 : selected 9 ⟨272446, by decide⟩
    (prefixPartial 12 24743) = some ⟨12, 2, 0, 272446, 24743, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_24743_272446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24743 ⟨272446, by decide⟩ :=
  accepted_of_selected 12 24743 ⟨272446, by decide⟩ ⟨12, 2, 0, 272446, 24743, 1685, 65536⟩
    (by decide) selected_cut_09899

theorem unmarked_context_11_6185_272447 : frontier 10 ⟨272447, by decide⟩
    (prefixCache 11 6185) (prefixPartial 11 6185) = false := by
  decide +kernel

theorem node_context_11_6185_272447 : EJMOriginalGlobalDAGData.nodes 10 ⟨272447, by decide⟩ =
    .split (coordinate 11) (![⟨272391, by decide⟩,⟨272409, by decide⟩,⟨272428, by decide⟩,⟨272446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6185_272447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6185 ⟨272447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6185
    ⟨272447, by decide⟩ (by decide) (![⟨272391, by decide⟩,⟨272409, by decide⟩,⟨272428, by decide⟩,⟨272446, by decide⟩]) unmarked_context_11_6185_272447 node_context_11_6185_272447
  intro a
  fin_cases a
  · exact context_12_24740_272391
  · exact context_12_24741_272409
  · exact context_12_24742_272428
  · exact context_12_24743_272446

theorem selected_cut_09900 : selected 9 ⟨272465, by decide⟩
    (prefixPartial 12 24744) = some ⟨12, 2, 0, 272465, 24744, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_24744_272465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24744 ⟨272465, by decide⟩ :=
  accepted_of_selected 12 24744 ⟨272465, by decide⟩ ⟨12, 2, 0, 272465, 24744, 1425, 65536⟩
    (by decide) selected_cut_09900

theorem selected_cut_09901 : selected 9 ⟨272488, by decide⟩
    (prefixPartial 12 24745) = some ⟨12, 2, 0, 272488, 24745, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_24745_272488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24745 ⟨272488, by decide⟩ :=
  accepted_of_selected 12 24745 ⟨272488, by decide⟩ ⟨12, 2, 0, 272488, 24745, 1557, 65536⟩
    (by decide) selected_cut_09901

theorem selected_cut_09902 : selected 9 ⟨272510, by decide⟩
    (prefixPartial 12 24746) = some ⟨12, 2, 0, 272510, 24746, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_24746_272510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24746 ⟨272510, by decide⟩ :=
  accepted_of_selected 12 24746 ⟨272510, by decide⟩ ⟨12, 2, 0, 272510, 24746, 1465, 65536⟩
    (by decide) selected_cut_09902

theorem selected_cut_09903 : selected 9 ⟨272530, by decide⟩
    (prefixPartial 12 24747) = some ⟨12, 2, 0, 272530, 24747, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_24747_272530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24747 ⟨272530, by decide⟩ :=
  accepted_of_selected 12 24747 ⟨272530, by decide⟩ ⟨12, 2, 0, 272530, 24747, 1617, 65536⟩
    (by decide) selected_cut_09903

theorem unmarked_context_11_6186_272531 : frontier 10 ⟨272531, by decide⟩
    (prefixCache 11 6186) (prefixPartial 11 6186) = false := by
  decide +kernel

theorem node_context_11_6186_272531 : EJMOriginalGlobalDAGData.nodes 10 ⟨272531, by decide⟩ =
    .split (coordinate 11) (![⟨272465, by decide⟩,⟨272488, by decide⟩,⟨272510, by decide⟩,⟨272530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6186_272531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6186 ⟨272531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6186
    ⟨272531, by decide⟩ (by decide) (![⟨272465, by decide⟩,⟨272488, by decide⟩,⟨272510, by decide⟩,⟨272530, by decide⟩]) unmarked_context_11_6186_272531 node_context_11_6186_272531
  intro a
  fin_cases a
  · exact context_12_24744_272465
  · exact context_12_24745_272488
  · exact context_12_24746_272510
  · exact context_12_24747_272530

theorem selected_cut_09904 : selected 9 ⟨272545, by decide⟩
    (prefixPartial 12 24748) = some ⟨12, 2, 0, 272545, 24748, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_24748_272545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24748 ⟨272545, by decide⟩ :=
  accepted_of_selected 12 24748 ⟨272545, by decide⟩ ⟨12, 2, 0, 272545, 24748, 1309, 65536⟩
    (by decide) selected_cut_09904

theorem selected_cut_09905 : selected 9 ⟨272559, by decide⟩
    (prefixPartial 12 24749) = some ⟨12, 2, 0, 272559, 24749, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_24749_272559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24749 ⟨272559, by decide⟩ :=
  accepted_of_selected 12 24749 ⟨272559, by decide⟩ ⟨12, 2, 0, 272559, 24749, 1509, 65536⟩
    (by decide) selected_cut_09905

theorem selected_cut_09906 : selected 9 ⟨272576, by decide⟩
    (prefixPartial 12 24750) = some ⟨12, 2, 0, 272576, 24750, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_24750_272576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24750 ⟨272576, by decide⟩ :=
  accepted_of_selected 12 24750 ⟨272576, by decide⟩ ⟨12, 2, 0, 272576, 24750, 1473, 65536⟩
    (by decide) selected_cut_09906

theorem selected_cut_09907 : selected 9 ⟨272593, by decide⟩
    (prefixPartial 12 24751) = some ⟨12, 2, 0, 272593, 24751, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_24751_272593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24751 ⟨272593, by decide⟩ :=
  accepted_of_selected 12 24751 ⟨272593, by decide⟩ ⟨12, 2, 0, 272593, 24751, 1433, 65536⟩
    (by decide) selected_cut_09907

theorem unmarked_context_11_6187_272594 : frontier 10 ⟨272594, by decide⟩
    (prefixCache 11 6187) (prefixPartial 11 6187) = false := by
  decide +kernel

theorem node_context_11_6187_272594 : EJMOriginalGlobalDAGData.nodes 10 ⟨272594, by decide⟩ =
    .split (coordinate 11) (![⟨272545, by decide⟩,⟨272559, by decide⟩,⟨272576, by decide⟩,⟨272593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6187_272594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6187 ⟨272594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6187
    ⟨272594, by decide⟩ (by decide) (![⟨272545, by decide⟩,⟨272559, by decide⟩,⟨272576, by decide⟩,⟨272593, by decide⟩]) unmarked_context_11_6187_272594 node_context_11_6187_272594
  intro a
  fin_cases a
  · exact context_12_24748_272545
  · exact context_12_24749_272559
  · exact context_12_24750_272576
  · exact context_12_24751_272593

theorem unmarked_context_10_1546_272595 : frontier 11 ⟨272595, by decide⟩
    (prefixCache 10 1546) (prefixPartial 10 1546) = false := by
  decide +kernel

theorem node_context_10_1546_272595 : EJMOriginalGlobalDAGData.nodes 11 ⟨272595, by decide⟩ =
    .split (coordinate 10) (![⟨272373, by decide⟩,⟨272447, by decide⟩,⟨272531, by decide⟩,⟨272594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1546_272595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1546 ⟨272595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1546
    ⟨272595, by decide⟩ (by decide) (![⟨272373, by decide⟩,⟨272447, by decide⟩,⟨272531, by decide⟩,⟨272594, by decide⟩]) unmarked_context_10_1546_272595 node_context_10_1546_272595
  intro a
  fin_cases a
  · exact context_11_6184_272373
  · exact context_11_6185_272447
  · exact context_11_6186_272531
  · exact context_11_6187_272594

theorem selected_cut_09908 : selected 9 ⟨272613, by decide⟩
    (prefixPartial 12 24752) = some ⟨12, 2, 0, 272613, 24752, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_24752_272613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24752 ⟨272613, by decide⟩ :=
  accepted_of_selected 12 24752 ⟨272613, by decide⟩ ⟨12, 2, 0, 272613, 24752, 1697, 65536⟩
    (by decide) selected_cut_09908

theorem selected_cut_09909 : selected 9 ⟨272628, by decide⟩
    (prefixPartial 12 24753) = some ⟨12, 2, 0, 272628, 24753, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_24753_272628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24753 ⟨272628, by decide⟩ :=
  accepted_of_selected 12 24753 ⟨272628, by decide⟩ ⟨12, 2, 0, 272628, 24753, 1145, 65536⟩
    (by decide) selected_cut_09909

theorem selected_cut_09910 : selected 9 ⟨272643, by decide⟩
    (prefixPartial 12 24754) = some ⟨12, 2, 0, 272643, 24754, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_24754_272643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24754 ⟨272643, by decide⟩ :=
  accepted_of_selected 12 24754 ⟨272643, by decide⟩ ⟨12, 2, 0, 272643, 24754, 1121, 65536⟩
    (by decide) selected_cut_09910

theorem selected_cut_09911 : selected 9 ⟨272655, by decide⟩
    (prefixPartial 12 24755) = some ⟨12, 2, 0, 272655, 24755, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_24755_272655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24755 ⟨272655, by decide⟩ :=
  accepted_of_selected 12 24755 ⟨272655, by decide⟩ ⟨12, 2, 0, 272655, 24755, 1237, 65536⟩
    (by decide) selected_cut_09911

theorem unmarked_context_11_6188_272656 : frontier 10 ⟨272656, by decide⟩
    (prefixCache 11 6188) (prefixPartial 11 6188) = false := by
  decide +kernel

theorem node_context_11_6188_272656 : EJMOriginalGlobalDAGData.nodes 10 ⟨272656, by decide⟩ =
    .split (coordinate 11) (![⟨272613, by decide⟩,⟨272628, by decide⟩,⟨272643, by decide⟩,⟨272655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6188_272656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6188 ⟨272656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6188
    ⟨272656, by decide⟩ (by decide) (![⟨272613, by decide⟩,⟨272628, by decide⟩,⟨272643, by decide⟩,⟨272655, by decide⟩]) unmarked_context_11_6188_272656 node_context_11_6188_272656
  intro a
  fin_cases a
  · exact context_12_24752_272613
  · exact context_12_24753_272628
  · exact context_12_24754_272643
  · exact context_12_24755_272655

theorem selected_cut_09912 : selected 9 ⟨272671, by decide⟩
    (prefixPartial 12 24756) = some ⟨12, 2, 0, 272671, 24756, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_24756_272671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24756 ⟨272671, by decide⟩ :=
  accepted_of_selected 12 24756 ⟨272671, by decide⟩ ⟨12, 2, 0, 272671, 24756, 1297, 65536⟩
    (by decide) selected_cut_09912

theorem selected_cut_09913 : selected 9 ⟨272690, by decide⟩
    (prefixPartial 12 24757) = some ⟨12, 2, 0, 272690, 24757, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_24757_272690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24757 ⟨272690, by decide⟩ :=
  accepted_of_selected 12 24757 ⟨272690, by decide⟩ ⟨12, 2, 0, 272690, 24757, 1341, 65536⟩
    (by decide) selected_cut_09913

theorem selected_cut_09914 : selected 9 ⟨272700, by decide⟩
    (prefixPartial 12 24758) = some ⟨12, 2, 0, 272700, 24758, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_24758_272700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24758 ⟨272700, by decide⟩ :=
  accepted_of_selected 12 24758 ⟨272700, by decide⟩ ⟨12, 2, 0, 272700, 24758, 1397, 65536⟩
    (by decide) selected_cut_09914

theorem selected_cut_09915 : selected 9 ⟨272715, by decide⟩
    (prefixPartial 12 24759) = some ⟨12, 2, 0, 272715, 24759, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_24759_272715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24759 ⟨272715, by decide⟩ :=
  accepted_of_selected 12 24759 ⟨272715, by decide⟩ ⟨12, 2, 0, 272715, 24759, 1537, 65536⟩
    (by decide) selected_cut_09915

theorem unmarked_context_11_6189_272716 : frontier 10 ⟨272716, by decide⟩
    (prefixCache 11 6189) (prefixPartial 11 6189) = false := by
  decide +kernel

theorem node_context_11_6189_272716 : EJMOriginalGlobalDAGData.nodes 10 ⟨272716, by decide⟩ =
    .split (coordinate 11) (![⟨272671, by decide⟩,⟨272690, by decide⟩,⟨272700, by decide⟩,⟨272715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6189_272716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6189 ⟨272716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6189
    ⟨272716, by decide⟩ (by decide) (![⟨272671, by decide⟩,⟨272690, by decide⟩,⟨272700, by decide⟩,⟨272715, by decide⟩]) unmarked_context_11_6189_272716 node_context_11_6189_272716
  intro a
  fin_cases a
  · exact context_12_24756_272671
  · exact context_12_24757_272690
  · exact context_12_24758_272700
  · exact context_12_24759_272715

theorem selected_cut_09916 : selected 9 ⟨272730, by decide⟩
    (prefixPartial 12 24760) = some ⟨12, 2, 0, 272730, 24760, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_24760_272730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24760 ⟨272730, by decide⟩ :=
  accepted_of_selected 12 24760 ⟨272730, by decide⟩ ⟨12, 2, 0, 272730, 24760, 1245, 65536⟩
    (by decide) selected_cut_09916

theorem selected_cut_09917 : selected 9 ⟨272744, by decide⟩
    (prefixPartial 12 24761) = some ⟨12, 2, 0, 272744, 24761, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_24761_272744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24761 ⟨272744, by decide⟩ :=
  accepted_of_selected 12 24761 ⟨272744, by decide⟩ ⟨12, 2, 0, 272744, 24761, 1205, 65536⟩
    (by decide) selected_cut_09917

theorem selected_cut_09918 : selected 9 ⟨272758, by decide⟩
    (prefixPartial 12 24762) = some ⟨12, 2, 0, 272758, 24762, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_24762_272758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24762 ⟨272758, by decide⟩ :=
  accepted_of_selected 12 24762 ⟨272758, by decide⟩ ⟨12, 2, 0, 272758, 24762, 1233, 65536⟩
    (by decide) selected_cut_09918

theorem selected_cut_09919 : selected 9 ⟨272770, by decide⟩
    (prefixPartial 12 24763) = some ⟨12, 2, 0, 272770, 24763, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_24763_272770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24763 ⟨272770, by decide⟩ :=
  accepted_of_selected 12 24763 ⟨272770, by decide⟩ ⟨12, 2, 0, 272770, 24763, 1377, 65536⟩
    (by decide) selected_cut_09919

theorem unmarked_context_11_6190_272771 : frontier 10 ⟨272771, by decide⟩
    (prefixCache 11 6190) (prefixPartial 11 6190) = false := by
  decide +kernel

theorem node_context_11_6190_272771 : EJMOriginalGlobalDAGData.nodes 10 ⟨272771, by decide⟩ =
    .split (coordinate 11) (![⟨272730, by decide⟩,⟨272744, by decide⟩,⟨272758, by decide⟩,⟨272770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6190_272771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6190 ⟨272771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6190
    ⟨272771, by decide⟩ (by decide) (![⟨272730, by decide⟩,⟨272744, by decide⟩,⟨272758, by decide⟩,⟨272770, by decide⟩]) unmarked_context_11_6190_272771 node_context_11_6190_272771
  intro a
  fin_cases a
  · exact context_12_24760_272730
  · exact context_12_24761_272744
  · exact context_12_24762_272758
  · exact context_12_24763_272770

theorem selected_cut_09920 : selected 9 ⟨272782, by decide⟩
    (prefixPartial 12 24764) = some ⟨12, 2, 0, 272782, 24764, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_24764_272782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24764 ⟨272782, by decide⟩ :=
  accepted_of_selected 12 24764 ⟨272782, by decide⟩ ⟨12, 2, 0, 272782, 24764, 1037, 65536⟩
    (by decide) selected_cut_09920

theorem selected_cut_09921 : selected 9 ⟨272795, by decide⟩
    (prefixPartial 12 24765) = some ⟨12, 2, 0, 272795, 24765, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_24765_272795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24765 ⟨272795, by decide⟩ :=
  accepted_of_selected 12 24765 ⟨272795, by decide⟩ ⟨12, 2, 0, 272795, 24765, 1057, 65536⟩
    (by decide) selected_cut_09921

theorem selected_cut_09922 : selected 9 ⟨272811, by decide⟩
    (prefixPartial 12 24766) = some ⟨12, 2, 0, 272811, 24766, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_24766_272811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24766 ⟨272811, by decide⟩ :=
  accepted_of_selected 12 24766 ⟨272811, by decide⟩ ⟨12, 2, 0, 272811, 24766, 1045, 65536⟩
    (by decide) selected_cut_09922

theorem selected_cut_09923 : selected 9 ⟨272829, by decide⟩
    (prefixPartial 12 24767) = some ⟨12, 2, 0, 272829, 24767, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_24767_272829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24767 ⟨272829, by decide⟩ :=
  accepted_of_selected 12 24767 ⟨272829, by decide⟩ ⟨12, 2, 0, 272829, 24767, 1145, 65536⟩
    (by decide) selected_cut_09923

theorem unmarked_context_11_6191_272830 : frontier 10 ⟨272830, by decide⟩
    (prefixCache 11 6191) (prefixPartial 11 6191) = false := by
  decide +kernel

theorem node_context_11_6191_272830 : EJMOriginalGlobalDAGData.nodes 10 ⟨272830, by decide⟩ =
    .split (coordinate 11) (![⟨272782, by decide⟩,⟨272795, by decide⟩,⟨272811, by decide⟩,⟨272829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6191_272830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6191 ⟨272830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6191
    ⟨272830, by decide⟩ (by decide) (![⟨272782, by decide⟩,⟨272795, by decide⟩,⟨272811, by decide⟩,⟨272829, by decide⟩]) unmarked_context_11_6191_272830 node_context_11_6191_272830
  intro a
  fin_cases a
  · exact context_12_24764_272782
  · exact context_12_24765_272795
  · exact context_12_24766_272811
  · exact context_12_24767_272829

theorem unmarked_context_10_1547_272831 : frontier 11 ⟨272831, by decide⟩
    (prefixCache 10 1547) (prefixPartial 10 1547) = false := by
  decide +kernel

theorem node_context_10_1547_272831 : EJMOriginalGlobalDAGData.nodes 11 ⟨272831, by decide⟩ =
    .split (coordinate 10) (![⟨272656, by decide⟩,⟨272716, by decide⟩,⟨272771, by decide⟩,⟨272830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1547_272831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1547 ⟨272831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1547
    ⟨272831, by decide⟩ (by decide) (![⟨272656, by decide⟩,⟨272716, by decide⟩,⟨272771, by decide⟩,⟨272830, by decide⟩]) unmarked_context_10_1547_272831 node_context_10_1547_272831
  intro a
  fin_cases a
  · exact context_11_6188_272656
  · exact context_11_6189_272716
  · exact context_11_6190_272771
  · exact context_11_6191_272830

theorem unmarked_context_9_386_272832 : frontier 12 ⟨272832, by decide⟩
    (prefixCache 9 386) (prefixPartial 9 386) = false := by
  decide +kernel

theorem node_context_9_386_272832 : EJMOriginalGlobalDAGData.nodes 12 ⟨272832, by decide⟩ =
    .split (coordinate 9) (![⟨271906, by decide⟩,⟨272287, by decide⟩,⟨272595, by decide⟩,⟨272831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_386_272832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 386 ⟨272832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 386
    ⟨272832, by decide⟩ (by decide) (![⟨271906, by decide⟩,⟨272287, by decide⟩,⟨272595, by decide⟩,⟨272831, by decide⟩]) unmarked_context_9_386_272832 node_context_9_386_272832
  intro a
  fin_cases a
  · exact context_10_1544_271906
  · exact context_10_1545_272287
  · exact context_10_1546_272595
  · exact context_10_1547_272831

theorem selected_cut_09924 : selected 10 ⟨272865, by decide⟩
    (prefixPartial 11 6192) = some ⟨11, 2, 0, 272865, 6192, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_6192_272865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6192 ⟨272865, by decide⟩ :=
  accepted_of_selected 11 6192 ⟨272865, by decide⟩ ⟨11, 2, 0, 272865, 6192, 2737, 262144⟩
    (by decide) selected_cut_09924

theorem selected_cut_09925 : selected 10 ⟨272891, by decide⟩
    (prefixPartial 11 6193) = some ⟨11, 2, 0, 272891, 6193, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_6193_272891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6193 ⟨272891, by decide⟩ :=
  accepted_of_selected 11 6193 ⟨272891, by decide⟩ ⟨11, 2, 0, 272891, 6193, 2569, 262144⟩
    (by decide) selected_cut_09925

theorem selected_cut_09926 : selected 10 ⟨272916, by decide⟩
    (prefixPartial 11 6194) = some ⟨11, 2, 0, 272916, 6194, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_6194_272916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6194 ⟨272916, by decide⟩ :=
  accepted_of_selected 11 6194 ⟨272916, by decide⟩ ⟨11, 2, 0, 272916, 6194, 2449, 262144⟩
    (by decide) selected_cut_09926

theorem selected_cut_09927 : selected 10 ⟨272945, by decide⟩
    (prefixPartial 11 6195) = some ⟨11, 2, 0, 272945, 6195, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_6195_272945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6195 ⟨272945, by decide⟩ :=
  accepted_of_selected 11 6195 ⟨272945, by decide⟩ ⟨11, 2, 0, 272945, 6195, 2449, 262144⟩
    (by decide) selected_cut_09927

theorem unmarked_context_10_1548_272946 : frontier 11 ⟨272946, by decide⟩
    (prefixCache 10 1548) (prefixPartial 10 1548) = false := by
  decide +kernel

theorem node_context_10_1548_272946 : EJMOriginalGlobalDAGData.nodes 11 ⟨272946, by decide⟩ =
    .split (coordinate 10) (![⟨272865, by decide⟩,⟨272891, by decide⟩,⟨272916, by decide⟩,⟨272945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1548_272946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1548 ⟨272946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1548
    ⟨272946, by decide⟩ (by decide) (![⟨272865, by decide⟩,⟨272891, by decide⟩,⟨272916, by decide⟩,⟨272945, by decide⟩]) unmarked_context_10_1548_272946 node_context_10_1548_272946
  intro a
  fin_cases a
  · exact context_11_6192_272865
  · exact context_11_6193_272891
  · exact context_11_6194_272916
  · exact context_11_6195_272945

theorem selected_cut_09928 : selected 10 ⟨272970, by decide⟩
    (prefixPartial 11 6196) = some ⟨11, 2, 0, 272970, 6196, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_6196_272970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6196 ⟨272970, by decide⟩ :=
  accepted_of_selected 11 6196 ⟨272970, by decide⟩ ⟨11, 2, 0, 272970, 6196, 2397, 262144⟩
    (by decide) selected_cut_09928

theorem selected_cut_09929 : selected 10 ⟨272990, by decide⟩
    (prefixPartial 11 6197) = some ⟨11, 2, 0, 272990, 6197, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_6197_272990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6197 ⟨272990, by decide⟩ :=
  accepted_of_selected 11 6197 ⟨272990, by decide⟩ ⟨11, 2, 0, 272990, 6197, 2185, 262144⟩
    (by decide) selected_cut_09929

theorem selected_cut_09930 : selected 10 ⟨273014, by decide⟩
    (prefixPartial 11 6198) = some ⟨11, 2, 0, 273014, 6198, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_6198_273014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6198 ⟨273014, by decide⟩ :=
  accepted_of_selected 11 6198 ⟨273014, by decide⟩ ⟨11, 2, 0, 273014, 6198, 1961, 262144⟩
    (by decide) selected_cut_09930

theorem selected_cut_09931 : selected 10 ⟨273034, by decide⟩
    (prefixPartial 11 6199) = some ⟨11, 2, 0, 273034, 6199, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_6199_273034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6199 ⟨273034, by decide⟩ :=
  accepted_of_selected 11 6199 ⟨273034, by decide⟩ ⟨11, 2, 0, 273034, 6199, 1697, 262144⟩
    (by decide) selected_cut_09931

theorem unmarked_context_10_1549_273035 : frontier 11 ⟨273035, by decide⟩
    (prefixCache 10 1549) (prefixPartial 10 1549) = false := by
  decide +kernel

theorem node_context_10_1549_273035 : EJMOriginalGlobalDAGData.nodes 11 ⟨273035, by decide⟩ =
    .split (coordinate 10) (![⟨272970, by decide⟩,⟨272990, by decide⟩,⟨273014, by decide⟩,⟨273034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1549_273035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1549 ⟨273035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1549
    ⟨273035, by decide⟩ (by decide) (![⟨272970, by decide⟩,⟨272990, by decide⟩,⟨273014, by decide⟩,⟨273034, by decide⟩]) unmarked_context_10_1549_273035 node_context_10_1549_273035
  intro a
  fin_cases a
  · exact context_11_6196_272970
  · exact context_11_6197_272990
  · exact context_11_6198_273014
  · exact context_11_6199_273034

theorem selected_cut_09932 : selected 10 ⟨273051, by decide⟩
    (prefixPartial 11 6200) = some ⟨11, 2, 0, 273051, 6200, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_6200_273051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6200 ⟨273051, by decide⟩ :=
  accepted_of_selected 11 6200 ⟨273051, by decide⟩ ⟨11, 2, 0, 273051, 6200, 1401, 262144⟩
    (by decide) selected_cut_09932

theorem selected_cut_09933 : selected 10 ⟨273067, by decide⟩
    (prefixPartial 11 6201) = some ⟨11, 2, 0, 273067, 6201, 1225, 262144⟩ := by
  decide +kernel

theorem context_11_6201_273067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6201 ⟨273067, by decide⟩ :=
  accepted_of_selected 11 6201 ⟨273067, by decide⟩ ⟨11, 2, 0, 273067, 6201, 1225, 262144⟩
    (by decide) selected_cut_09933

theorem selected_cut_09934 : selected 10 ⟨273083, by decide⟩
    (prefixPartial 11 6202) = some ⟨11, 2, 0, 273083, 6202, 1073, 262144⟩ := by
  decide +kernel

theorem context_11_6202_273083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6202 ⟨273083, by decide⟩ :=
  accepted_of_selected 11 6202 ⟨273083, by decide⟩ ⟨11, 2, 0, 273083, 6202, 1073, 262144⟩
    (by decide) selected_cut_09934

theorem selected_cut_09935 : selected 10 ⟨273096, by decide⟩
    (prefixPartial 11 6203) = some ⟨11, 2, 0, 273096, 6203, 901, 262144⟩ := by
  decide +kernel

theorem context_11_6203_273096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6203 ⟨273096, by decide⟩ :=
  accepted_of_selected 11 6203 ⟨273096, by decide⟩ ⟨11, 2, 0, 273096, 6203, 901, 262144⟩
    (by decide) selected_cut_09935

theorem unmarked_context_10_1550_273097 : frontier 11 ⟨273097, by decide⟩
    (prefixCache 10 1550) (prefixPartial 10 1550) = false := by
  decide +kernel

theorem node_context_10_1550_273097 : EJMOriginalGlobalDAGData.nodes 11 ⟨273097, by decide⟩ =
    .split (coordinate 10) (![⟨273051, by decide⟩,⟨273067, by decide⟩,⟨273083, by decide⟩,⟨273096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1550_273097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1550 ⟨273097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1550
    ⟨273097, by decide⟩ (by decide) (![⟨273051, by decide⟩,⟨273067, by decide⟩,⟨273083, by decide⟩,⟨273096, by decide⟩]) unmarked_context_10_1550_273097 node_context_10_1550_273097
  intro a
  fin_cases a
  · exact context_11_6200_273051
  · exact context_11_6201_273067
  · exact context_11_6202_273083
  · exact context_11_6203_273096

theorem selected_cut_09936 : selected 11 ⟨273131, by decide⟩
    (prefixPartial 10 1551) = some ⟨10, 2, 0, 273131, 1551, 1577, 1048576⟩ := by
  decide +kernel

theorem context_10_1551_273131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1551 ⟨273131, by decide⟩ :=
  accepted_of_selected 10 1551 ⟨273131, by decide⟩ ⟨10, 2, 0, 273131, 1551, 1577, 1048576⟩
    (by decide) selected_cut_09936

theorem unmarked_context_9_387_273132 : frontier 12 ⟨273132, by decide⟩
    (prefixCache 9 387) (prefixPartial 9 387) = false := by
  decide +kernel

theorem node_context_9_387_273132 : EJMOriginalGlobalDAGData.nodes 12 ⟨273132, by decide⟩ =
    .split (coordinate 9) (![⟨272946, by decide⟩,⟨273035, by decide⟩,⟨273097, by decide⟩,⟨273131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_387_273132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 387 ⟨273132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 387
    ⟨273132, by decide⟩ (by decide) (![⟨272946, by decide⟩,⟨273035, by decide⟩,⟨273097, by decide⟩,⟨273131, by decide⟩]) unmarked_context_9_387_273132 node_context_9_387_273132
  intro a
  fin_cases a
  · exact context_10_1548_272946
  · exact context_10_1549_273035
  · exact context_10_1550_273097
  · exact context_10_1551_273131

theorem unmarked_context_8_96_273133 : frontier 13 ⟨273133, by decide⟩
    (prefixCache 8 96) (prefixPartial 8 96) = false := by
  decide +kernel

theorem node_context_8_96_273133 : EJMOriginalGlobalDAGData.nodes 13 ⟨273133, by decide⟩ =
    .split (coordinate 8) (![⟨268616, by decide⟩,⟨271475, by decide⟩,⟨272832, by decide⟩,⟨273132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_96_273133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 96 ⟨273133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 96
    ⟨273133, by decide⟩ (by decide) (![⟨268616, by decide⟩,⟨271475, by decide⟩,⟨272832, by decide⟩,⟨273132, by decide⟩]) unmarked_context_8_96_273133 node_context_8_96_273133
  intro a
  fin_cases a
  · exact context_9_384_268616
  · exact context_9_385_271475
  · exact context_9_386_272832
  · exact context_9_387_273132

theorem selected_cut_09937 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 6208) = some ⟨11, 1, 0, 167448, 6208, 1, 262144⟩ := by
  decide +kernel

theorem context_11_6208_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6208 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 6208 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 6208, 1, 262144⟩
    (by decide) selected_cut_09937

theorem selected_cut_09938 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 24836) = some ⟨12, 1, 0, 34034, 24836, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24836_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24836 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 24836 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 24836, 1, 65536⟩
    (by decide) selected_cut_09938

theorem selected_cut_09939 : selected 7 ⟨273183, by decide⟩
    (prefixPartial 14 397392) = some ⟨14, 2, 0, 273183, 397392, 2129, 4096⟩ := by
  decide +kernel

theorem context_14_397392_273183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397392 ⟨273183, by decide⟩ :=
  accepted_of_selected 14 397392 ⟨273183, by decide⟩ ⟨14, 2, 0, 273183, 397392, 2129, 4096⟩
    (by decide) selected_cut_09939

theorem selected_cut_09940 : selected 7 ⟨273196, by decide⟩
    (prefixPartial 14 397393) = some ⟨14, 2, 0, 273196, 397393, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_397393_273196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397393 ⟨273196, by decide⟩ :=
  accepted_of_selected 14 397393 ⟨273196, by decide⟩ ⟨14, 2, 0, 273196, 397393, 1069, 4096⟩
    (by decide) selected_cut_09940

theorem selected_cut_09941 : selected 7 ⟨273216, by decide⟩
    (prefixPartial 14 397394) = some ⟨14, 2, 0, 273216, 397394, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_397394_273216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397394 ⟨273216, by decide⟩ :=
  accepted_of_selected 14 397394 ⟨273216, by decide⟩ ⟨14, 2, 0, 273216, 397394, 1321, 4096⟩
    (by decide) selected_cut_09941

theorem selected_cut_09942 : selected 7 ⟨273240, by decide⟩
    (prefixPartial 14 397395) = some ⟨14, 2, 0, 273240, 397395, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_397395_273240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397395 ⟨273240, by decide⟩ :=
  accepted_of_selected 14 397395 ⟨273240, by decide⟩ ⟨14, 2, 0, 273240, 397395, 1429, 4096⟩
    (by decide) selected_cut_09942

theorem unmarked_context_13_99348_273241 : frontier 8 ⟨273241, by decide⟩
    (prefixCache 13 99348) (prefixPartial 13 99348) = false := by
  decide +kernel

theorem node_context_13_99348_273241 : EJMOriginalGlobalDAGData.nodes 8 ⟨273241, by decide⟩ =
    .split (coordinate 13) (![⟨273183, by decide⟩,⟨273196, by decide⟩,⟨273216, by decide⟩,⟨273240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_99348_273241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99348 ⟨273241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 99348
    ⟨273241, by decide⟩ (by decide) (![⟨273183, by decide⟩,⟨273196, by decide⟩,⟨273216, by decide⟩,⟨273240, by decide⟩]) unmarked_context_13_99348_273241 node_context_13_99348_273241
  intro a
  fin_cases a
  · exact context_14_397392_273183
  · exact context_14_397393_273196
  · exact context_14_397394_273216
  · exact context_14_397395_273240

theorem selected_cut_09943 : selected 7 ⟨273272, by decide⟩
    (prefixPartial 14 397396) = some ⟨14, 2, 0, 273272, 397396, 1525, 4096⟩ := by
  decide +kernel

theorem context_14_397396_273272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397396 ⟨273272, by decide⟩ :=
  accepted_of_selected 14 397396 ⟨273272, by decide⟩ ⟨14, 2, 0, 273272, 397396, 1525, 4096⟩
    (by decide) selected_cut_09943

theorem selected_cut_09944 : selected 7 ⟨273286, by decide⟩
    (prefixPartial 14 397397) = some ⟨14, 2, 0, 273286, 397397, 845, 4096⟩ := by
  decide +kernel

theorem context_14_397397_273286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397397 ⟨273286, by decide⟩ :=
  accepted_of_selected 14 397397 ⟨273286, by decide⟩ ⟨14, 2, 0, 273286, 397397, 845, 4096⟩
    (by decide) selected_cut_09944

theorem selected_cut_09945 : selected 7 ⟨273321, by decide⟩
    (prefixPartial 14 397398) = some ⟨14, 2, 0, 273321, 397398, 1533, 4096⟩ := by
  decide +kernel

theorem context_14_397398_273321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397398 ⟨273321, by decide⟩ :=
  accepted_of_selected 14 397398 ⟨273321, by decide⟩ ⟨14, 2, 0, 273321, 397398, 1533, 4096⟩
    (by decide) selected_cut_09945

theorem selected_cut_09946 : selected 7 ⟨273343, by decide⟩
    (prefixPartial 14 397399) = some ⟨14, 2, 0, 273343, 397399, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_397399_273343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397399 ⟨273343, by decide⟩ :=
  accepted_of_selected 14 397399 ⟨273343, by decide⟩ ⟨14, 2, 0, 273343, 397399, 1277, 4096⟩
    (by decide) selected_cut_09946

theorem unmarked_context_13_99349_273344 : frontier 8 ⟨273344, by decide⟩
    (prefixCache 13 99349) (prefixPartial 13 99349) = false := by
  decide +kernel

theorem node_context_13_99349_273344 : EJMOriginalGlobalDAGData.nodes 8 ⟨273344, by decide⟩ =
    .split (coordinate 13) (![⟨273272, by decide⟩,⟨273286, by decide⟩,⟨273321, by decide⟩,⟨273343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_99349_273344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99349 ⟨273344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 99349
    ⟨273344, by decide⟩ (by decide) (![⟨273272, by decide⟩,⟨273286, by decide⟩,⟨273321, by decide⟩,⟨273343, by decide⟩]) unmarked_context_13_99349_273344 node_context_13_99349_273344
  intro a
  fin_cases a
  · exact context_14_397396_273272
  · exact context_14_397397_273286
  · exact context_14_397398_273321
  · exact context_14_397399_273343

theorem selected_cut_09947 : selected 8 ⟨273420, by decide⟩
    (prefixPartial 13 99350) = some ⟨13, 2, 0, 273420, 99350, 3197, 16384⟩ := by
  decide +kernel

theorem context_13_99350_273420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99350 ⟨273420, by decide⟩ :=
  accepted_of_selected 13 99350 ⟨273420, by decide⟩ ⟨13, 2, 0, 273420, 99350, 3197, 16384⟩
    (by decide) selected_cut_09947

theorem selected_cut_09948 : selected 8 ⟨273449, by decide⟩
    (prefixPartial 13 99351) = some ⟨13, 2, 0, 273449, 99351, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_99351_273449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99351 ⟨273449, by decide⟩ :=
  accepted_of_selected 13 99351 ⟨273449, by decide⟩ ⟨13, 2, 0, 273449, 99351, 1465, 16384⟩
    (by decide) selected_cut_09948

theorem unmarked_context_12_24837_273450 : frontier 9 ⟨273450, by decide⟩
    (prefixCache 12 24837) (prefixPartial 12 24837) = false := by
  decide +kernel

theorem node_context_12_24837_273450 : EJMOriginalGlobalDAGData.nodes 9 ⟨273450, by decide⟩ =
    .split (coordinate 12) (![⟨273241, by decide⟩,⟨273344, by decide⟩,⟨273420, by decide⟩,⟨273449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24837_273450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24837 ⟨273450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24837
    ⟨273450, by decide⟩ (by decide) (![⟨273241, by decide⟩,⟨273344, by decide⟩,⟨273420, by decide⟩,⟨273449, by decide⟩]) unmarked_context_12_24837_273450 node_context_12_24837_273450
  intro a
  fin_cases a
  · exact context_13_99348_273241
  · exact context_13_99349_273344
  · exact context_13_99350_273420
  · exact context_13_99351_273449

theorem selected_cut_09949 : selected 8 ⟨273498, by decide⟩
    (prefixPartial 13 99352) = some ⟨13, 2, 0, 273498, 99352, 3805, 16384⟩ := by
  decide +kernel

theorem context_13_99352_273498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99352 ⟨273498, by decide⟩ :=
  accepted_of_selected 13 99352 ⟨273498, by decide⟩ ⟨13, 2, 0, 273498, 99352, 3805, 16384⟩
    (by decide) selected_cut_09949

theorem selected_cut_09950 : selected 8 ⟨273528, by decide⟩
    (prefixPartial 13 99353) = some ⟨13, 2, 0, 273528, 99353, 3125, 16384⟩ := by
  decide +kernel

theorem context_13_99353_273528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99353 ⟨273528, by decide⟩ :=
  accepted_of_selected 13 99353 ⟨273528, by decide⟩ ⟨13, 2, 0, 273528, 99353, 3125, 16384⟩
    (by decide) selected_cut_09950

theorem selected_cut_09951 : selected 8 ⟨273547, by decide⟩
    (prefixPartial 13 99354) = some ⟨13, 2, 0, 273547, 99354, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_99354_273547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99354 ⟨273547, by decide⟩ :=
  accepted_of_selected 13 99354 ⟨273547, by decide⟩ ⟨13, 2, 0, 273547, 99354, 2289, 16384⟩
    (by decide) selected_cut_09951

theorem selected_cut_09952 : selected 8 ⟨273554, by decide⟩
    (prefixPartial 13 99355) = some ⟨13, 2, 0, 273554, 99355, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_99355_273554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99355 ⟨273554, by decide⟩ :=
  accepted_of_selected 13 99355 ⟨273554, by decide⟩ ⟨13, 2, 0, 273554, 99355, 1101, 16384⟩
    (by decide) selected_cut_09952

theorem unmarked_context_12_24838_273555 : frontier 9 ⟨273555, by decide⟩
    (prefixCache 12 24838) (prefixPartial 12 24838) = false := by
  decide +kernel

theorem node_context_12_24838_273555 : EJMOriginalGlobalDAGData.nodes 9 ⟨273555, by decide⟩ =
    .split (coordinate 12) (![⟨273498, by decide⟩,⟨273528, by decide⟩,⟨273547, by decide⟩,⟨273554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24838_273555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24838 ⟨273555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24838
    ⟨273555, by decide⟩ (by decide) (![⟨273498, by decide⟩,⟨273528, by decide⟩,⟨273547, by decide⟩,⟨273554, by decide⟩]) unmarked_context_12_24838_273555 node_context_12_24838_273555
  intro a
  fin_cases a
  · exact context_13_99352_273498
  · exact context_13_99353_273528
  · exact context_13_99354_273547
  · exact context_13_99355_273554

theorem selected_cut_09953 : selected 7 ⟨273574, by decide⟩
    (prefixPartial 14 397424) = some ⟨14, 2, 0, 273574, 397424, 937, 4096⟩ := by
  decide +kernel

theorem context_14_397424_273574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397424 ⟨273574, by decide⟩ :=
  accepted_of_selected 14 397424 ⟨273574, by decide⟩ ⟨14, 2, 0, 273574, 397424, 937, 4096⟩
    (by decide) selected_cut_09953

theorem selected_cut_09954 : selected 7 ⟨273585, by decide⟩
    (prefixPartial 14 397425) = some ⟨14, 2, 0, 273585, 397425, 977, 4096⟩ := by
  decide +kernel

theorem context_14_397425_273585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397425 ⟨273585, by decide⟩ :=
  accepted_of_selected 14 397425 ⟨273585, by decide⟩ ⟨14, 2, 0, 273585, 397425, 977, 4096⟩
    (by decide) selected_cut_09954

theorem selected_cut_09955 : selected 7 ⟨273598, by decide⟩
    (prefixPartial 14 397426) = some ⟨14, 2, 0, 273598, 397426, 1141, 4096⟩ := by
  decide +kernel

theorem context_14_397426_273598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397426 ⟨273598, by decide⟩ :=
  accepted_of_selected 14 397426 ⟨273598, by decide⟩ ⟨14, 2, 0, 273598, 397426, 1141, 4096⟩
    (by decide) selected_cut_09955

theorem selected_cut_09956 : selected 7 ⟨273608, by decide⟩
    (prefixPartial 14 397427) = some ⟨14, 2, 0, 273608, 397427, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_397427_273608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 397427 ⟨273608, by decide⟩ :=
  accepted_of_selected 14 397427 ⟨273608, by decide⟩ ⟨14, 2, 0, 273608, 397427, 1081, 4096⟩
    (by decide) selected_cut_09956

theorem unmarked_context_13_99356_273609 : frontier 8 ⟨273609, by decide⟩
    (prefixCache 13 99356) (prefixPartial 13 99356) = false := by
  decide +kernel

theorem node_context_13_99356_273609 : EJMOriginalGlobalDAGData.nodes 8 ⟨273609, by decide⟩ =
    .split (coordinate 13) (![⟨273574, by decide⟩,⟨273585, by decide⟩,⟨273598, by decide⟩,⟨273608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_99356_273609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99356 ⟨273609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 99356
    ⟨273609, by decide⟩ (by decide) (![⟨273574, by decide⟩,⟨273585, by decide⟩,⟨273598, by decide⟩,⟨273608, by decide⟩]) unmarked_context_13_99356_273609 node_context_13_99356_273609
  intro a
  fin_cases a
  · exact context_14_397424_273574
  · exact context_14_397425_273585
  · exact context_14_397426_273598
  · exact context_14_397427_273608

theorem selected_cut_09957 : selected 8 ⟨273644, by decide⟩
    (prefixPartial 13 99357) = some ⟨13, 2, 0, 273644, 99357, 3273, 16384⟩ := by
  decide +kernel

theorem context_13_99357_273644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99357 ⟨273644, by decide⟩ :=
  accepted_of_selected 13 99357 ⟨273644, by decide⟩ ⟨13, 2, 0, 273644, 99357, 3273, 16384⟩
    (by decide) selected_cut_09957

theorem selected_cut_09958 : selected 8 ⟨273665, by decide⟩
    (prefixPartial 13 99358) = some ⟨13, 2, 0, 273665, 99358, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_99358_273665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99358 ⟨273665, by decide⟩ :=
  accepted_of_selected 13 99358 ⟨273665, by decide⟩ ⟨13, 2, 0, 273665, 99358, 2313, 16384⟩
    (by decide) selected_cut_09958

theorem selected_cut_09959 : selected 8 ⟨273675, by decide⟩
    (prefixPartial 13 99359) = some ⟨13, 2, 0, 273675, 99359, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_99359_273675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99359 ⟨273675, by decide⟩ :=
  accepted_of_selected 13 99359 ⟨273675, by decide⟩ ⟨13, 2, 0, 273675, 99359, 1169, 16384⟩
    (by decide) selected_cut_09959

theorem unmarked_context_12_24839_273676 : frontier 9 ⟨273676, by decide⟩
    (prefixCache 12 24839) (prefixPartial 12 24839) = false := by
  decide +kernel

theorem node_context_12_24839_273676 : EJMOriginalGlobalDAGData.nodes 9 ⟨273676, by decide⟩ =
    .split (coordinate 12) (![⟨273609, by decide⟩,⟨273644, by decide⟩,⟨273665, by decide⟩,⟨273675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24839_273676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24839 ⟨273676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24839
    ⟨273676, by decide⟩ (by decide) (![⟨273609, by decide⟩,⟨273644, by decide⟩,⟨273665, by decide⟩,⟨273675, by decide⟩]) unmarked_context_12_24839_273676 node_context_12_24839_273676
  intro a
  fin_cases a
  · exact context_13_99356_273609
  · exact context_13_99357_273644
  · exact context_13_99358_273665
  · exact context_13_99359_273675

theorem unmarked_context_11_6209_273677 : frontier 10 ⟨273677, by decide⟩
    (prefixCache 11 6209) (prefixPartial 11 6209) = false := by
  decide +kernel

theorem node_context_11_6209_273677 : EJMOriginalGlobalDAGData.nodes 10 ⟨273677, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨273450, by decide⟩,⟨273555, by decide⟩,⟨273676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6209_273677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6209 ⟨273677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6209
    ⟨273677, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨273450, by decide⟩,⟨273555, by decide⟩,⟨273676, by decide⟩]) unmarked_context_11_6209_273677 node_context_11_6209_273677
  intro a
  fin_cases a
  · exact context_12_24836_34034
  · exact context_12_24837_273450
  · exact context_12_24838_273555
  · exact context_12_24839_273676

theorem selected_cut_09960 : selected 8 ⟨273739, by decide⟩
    (prefixPartial 13 99360) = some ⟨13, 2, 0, 273739, 99360, 3637, 16384⟩ := by
  decide +kernel

theorem context_13_99360_273739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99360 ⟨273739, by decide⟩ :=
  accepted_of_selected 13 99360 ⟨273739, by decide⟩ ⟨13, 2, 0, 273739, 99360, 3637, 16384⟩
    (by decide) selected_cut_09960

theorem selected_cut_09961 : selected 8 ⟨273786, by decide⟩
    (prefixPartial 13 99361) = some ⟨13, 2, 0, 273786, 99361, 3241, 16384⟩ := by
  decide +kernel

theorem context_13_99361_273786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99361 ⟨273786, by decide⟩ :=
  accepted_of_selected 13 99361 ⟨273786, by decide⟩ ⟨13, 2, 0, 273786, 99361, 3241, 16384⟩
    (by decide) selected_cut_09961

theorem selected_cut_09962 : selected 8 ⟨273811, by decide⟩
    (prefixPartial 13 99362) = some ⟨13, 2, 0, 273811, 99362, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_99362_273811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99362 ⟨273811, by decide⟩ :=
  accepted_of_selected 13 99362 ⟨273811, by decide⟩ ⟨13, 2, 0, 273811, 99362, 2437, 16384⟩
    (by decide) selected_cut_09962

theorem selected_cut_09963 : selected 8 ⟨273823, by decide⟩
    (prefixPartial 13 99363) = some ⟨13, 2, 0, 273823, 99363, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_99363_273823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99363 ⟨273823, by decide⟩ :=
  accepted_of_selected 13 99363 ⟨273823, by decide⟩ ⟨13, 2, 0, 273823, 99363, 1137, 16384⟩
    (by decide) selected_cut_09963

theorem unmarked_context_12_24840_273824 : frontier 9 ⟨273824, by decide⟩
    (prefixCache 12 24840) (prefixPartial 12 24840) = false := by
  decide +kernel

theorem node_context_12_24840_273824 : EJMOriginalGlobalDAGData.nodes 9 ⟨273824, by decide⟩ =
    .split (coordinate 12) (![⟨273739, by decide⟩,⟨273786, by decide⟩,⟨273811, by decide⟩,⟨273823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24840_273824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24840 ⟨273824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24840
    ⟨273824, by decide⟩ (by decide) (![⟨273739, by decide⟩,⟨273786, by decide⟩,⟨273811, by decide⟩,⟨273823, by decide⟩]) unmarked_context_12_24840_273824 node_context_12_24840_273824
  intro a
  fin_cases a
  · exact context_13_99360_273739
  · exact context_13_99361_273786
  · exact context_13_99362_273811
  · exact context_13_99363_273823

theorem selected_cut_09964 : selected 8 ⟨273871, by decide⟩
    (prefixPartial 13 99364) = some ⟨13, 2, 0, 273871, 99364, 3265, 16384⟩ := by
  decide +kernel

theorem context_13_99364_273871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99364 ⟨273871, by decide⟩ :=
  accepted_of_selected 13 99364 ⟨273871, by decide⟩ ⟨13, 2, 0, 273871, 99364, 3265, 16384⟩
    (by decide) selected_cut_09964

theorem selected_cut_09965 : selected 8 ⟨273913, by decide⟩
    (prefixPartial 13 99365) = some ⟨13, 2, 0, 273913, 99365, 3253, 16384⟩ := by
  decide +kernel

theorem context_13_99365_273913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99365 ⟨273913, by decide⟩ :=
  accepted_of_selected 13 99365 ⟨273913, by decide⟩ ⟨13, 2, 0, 273913, 99365, 3253, 16384⟩
    (by decide) selected_cut_09965

theorem selected_cut_09966 : selected 8 ⟨273937, by decide⟩
    (prefixPartial 13 99366) = some ⟨13, 2, 0, 273937, 99366, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_99366_273937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99366 ⟨273937, by decide⟩ :=
  accepted_of_selected 13 99366 ⟨273937, by decide⟩ ⟨13, 2, 0, 273937, 99366, 2397, 16384⟩
    (by decide) selected_cut_09966

theorem selected_cut_09967 : selected 8 ⟨273945, by decide⟩
    (prefixPartial 13 99367) = some ⟨13, 2, 0, 273945, 99367, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_99367_273945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99367 ⟨273945, by decide⟩ :=
  accepted_of_selected 13 99367 ⟨273945, by decide⟩ ⟨13, 2, 0, 273945, 99367, 1141, 16384⟩
    (by decide) selected_cut_09967

theorem unmarked_context_12_24841_273946 : frontier 9 ⟨273946, by decide⟩
    (prefixCache 12 24841) (prefixPartial 12 24841) = false := by
  decide +kernel

theorem node_context_12_24841_273946 : EJMOriginalGlobalDAGData.nodes 9 ⟨273946, by decide⟩ =
    .split (coordinate 12) (![⟨273871, by decide⟩,⟨273913, by decide⟩,⟨273937, by decide⟩,⟨273945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24841_273946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24841 ⟨273946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24841
    ⟨273946, by decide⟩ (by decide) (![⟨273871, by decide⟩,⟨273913, by decide⟩,⟨273937, by decide⟩,⟨273945, by decide⟩]) unmarked_context_12_24841_273946 node_context_12_24841_273946
  intro a
  fin_cases a
  · exact context_13_99364_273871
  · exact context_13_99365_273913
  · exact context_13_99366_273937
  · exact context_13_99367_273945

theorem selected_cut_09968 : selected 8 ⟨273989, by decide⟩
    (prefixPartial 13 99368) = some ⟨13, 2, 0, 273989, 99368, 3409, 16384⟩ := by
  decide +kernel

theorem context_13_99368_273989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99368 ⟨273989, by decide⟩ :=
  accepted_of_selected 13 99368 ⟨273989, by decide⟩ ⟨13, 2, 0, 273989, 99368, 3409, 16384⟩
    (by decide) selected_cut_09968

theorem selected_cut_09969 : selected 8 ⟨274026, by decide⟩
    (prefixPartial 13 99369) = some ⟨13, 2, 0, 274026, 99369, 3461, 16384⟩ := by
  decide +kernel

theorem context_13_99369_274026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99369 ⟨274026, by decide⟩ :=
  accepted_of_selected 13 99369 ⟨274026, by decide⟩ ⟨13, 2, 0, 274026, 99369, 3461, 16384⟩
    (by decide) selected_cut_09969

theorem selected_cut_09970 : selected 8 ⟨274053, by decide⟩
    (prefixPartial 13 99370) = some ⟨13, 2, 0, 274053, 99370, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_99370_274053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99370 ⟨274053, by decide⟩ :=
  accepted_of_selected 13 99370 ⟨274053, by decide⟩ ⟨13, 2, 0, 274053, 99370, 2417, 16384⟩
    (by decide) selected_cut_09970

theorem selected_cut_09971 : selected 8 ⟨274060, by decide⟩
    (prefixPartial 13 99371) = some ⟨13, 2, 0, 274060, 99371, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_99371_274060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99371 ⟨274060, by decide⟩ :=
  accepted_of_selected 13 99371 ⟨274060, by decide⟩ ⟨13, 2, 0, 274060, 99371, 1081, 16384⟩
    (by decide) selected_cut_09971

theorem unmarked_context_12_24842_274061 : frontier 9 ⟨274061, by decide⟩
    (prefixCache 12 24842) (prefixPartial 12 24842) = false := by
  decide +kernel

theorem node_context_12_24842_274061 : EJMOriginalGlobalDAGData.nodes 9 ⟨274061, by decide⟩ =
    .split (coordinate 12) (![⟨273989, by decide⟩,⟨274026, by decide⟩,⟨274053, by decide⟩,⟨274060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24842_274061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24842 ⟨274061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24842
    ⟨274061, by decide⟩ (by decide) (![⟨273989, by decide⟩,⟨274026, by decide⟩,⟨274053, by decide⟩,⟨274060, by decide⟩]) unmarked_context_12_24842_274061 node_context_12_24842_274061
  intro a
  fin_cases a
  · exact context_13_99368_273989
  · exact context_13_99369_274026
  · exact context_13_99370_274053
  · exact context_13_99371_274060

theorem selected_cut_09972 : selected 8 ⟨274118, by decide⟩
    (prefixPartial 13 99372) = some ⟨13, 2, 0, 274118, 99372, 3865, 16384⟩ := by
  decide +kernel

theorem context_13_99372_274118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99372 ⟨274118, by decide⟩ :=
  accepted_of_selected 13 99372 ⟨274118, by decide⟩ ⟨13, 2, 0, 274118, 99372, 3865, 16384⟩
    (by decide) selected_cut_09972

theorem selected_cut_09973 : selected 8 ⟨274169, by decide⟩
    (prefixPartial 13 99373) = some ⟨13, 2, 0, 274169, 99373, 3837, 16384⟩ := by
  decide +kernel

theorem context_13_99373_274169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99373 ⟨274169, by decide⟩ :=
  accepted_of_selected 13 99373 ⟨274169, by decide⟩ ⟨13, 2, 0, 274169, 99373, 3837, 16384⟩
    (by decide) selected_cut_09973

theorem selected_cut_09974 : selected 8 ⟨274192, by decide⟩
    (prefixPartial 13 99374) = some ⟨13, 2, 0, 274192, 99374, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_99374_274192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99374 ⟨274192, by decide⟩ :=
  accepted_of_selected 13 99374 ⟨274192, by decide⟩ ⟨13, 2, 0, 274192, 99374, 2409, 16384⟩
    (by decide) selected_cut_09974

theorem selected_cut_09975 : selected 8 ⟨274200, by decide⟩
    (prefixPartial 13 99375) = some ⟨13, 2, 0, 274200, 99375, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_99375_274200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99375 ⟨274200, by decide⟩ :=
  accepted_of_selected 13 99375 ⟨274200, by decide⟩ ⟨13, 2, 0, 274200, 99375, 1181, 16384⟩
    (by decide) selected_cut_09975

theorem unmarked_context_12_24843_274201 : frontier 9 ⟨274201, by decide⟩
    (prefixCache 12 24843) (prefixPartial 12 24843) = false := by
  decide +kernel

theorem node_context_12_24843_274201 : EJMOriginalGlobalDAGData.nodes 9 ⟨274201, by decide⟩ =
    .split (coordinate 12) (![⟨274118, by decide⟩,⟨274169, by decide⟩,⟨274192, by decide⟩,⟨274200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24843_274201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24843 ⟨274201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24843
    ⟨274201, by decide⟩ (by decide) (![⟨274118, by decide⟩,⟨274169, by decide⟩,⟨274192, by decide⟩,⟨274200, by decide⟩]) unmarked_context_12_24843_274201 node_context_12_24843_274201
  intro a
  fin_cases a
  · exact context_13_99372_274118
  · exact context_13_99373_274169
  · exact context_13_99374_274192
  · exact context_13_99375_274200

theorem unmarked_context_11_6210_274202 : frontier 10 ⟨274202, by decide⟩
    (prefixCache 11 6210) (prefixPartial 11 6210) = false := by
  decide +kernel

theorem node_context_11_6210_274202 : EJMOriginalGlobalDAGData.nodes 10 ⟨274202, by decide⟩ =
    .split (coordinate 11) (![⟨273824, by decide⟩,⟨273946, by decide⟩,⟨274061, by decide⟩,⟨274201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6210_274202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6210 ⟨274202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6210
    ⟨274202, by decide⟩ (by decide) (![⟨273824, by decide⟩,⟨273946, by decide⟩,⟨274061, by decide⟩,⟨274201, by decide⟩]) unmarked_context_11_6210_274202 node_context_11_6210_274202
  intro a
  fin_cases a
  · exact context_12_24840_273824
  · exact context_12_24841_273946
  · exact context_12_24842_274061
  · exact context_12_24843_274201

theorem selected_cut_09976 : selected 8 ⟨274232, by decide⟩
    (prefixPartial 13 99376) = some ⟨13, 2, 0, 274232, 99376, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_99376_274232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99376 ⟨274232, by decide⟩ :=
  accepted_of_selected 13 99376 ⟨274232, by decide⟩ ⟨13, 2, 0, 274232, 99376, 1265, 16384⟩
    (by decide) selected_cut_09976

theorem selected_cut_09977 : selected 8 ⟨274267, by decide⟩
    (prefixPartial 13 99377) = some ⟨13, 2, 0, 274267, 99377, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_99377_274267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99377 ⟨274267, by decide⟩ :=
  accepted_of_selected 13 99377 ⟨274267, by decide⟩ ⟨13, 2, 0, 274267, 99377, 1745, 16384⟩
    (by decide) selected_cut_09977

theorem selected_cut_09978 : selected 8 ⟨274322, by decide⟩
    (prefixPartial 13 99378) = some ⟨13, 2, 0, 274322, 99378, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_99378_274322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99378 ⟨274322, by decide⟩ :=
  accepted_of_selected 13 99378 ⟨274322, by decide⟩ ⟨13, 2, 0, 274322, 99378, 1985, 16384⟩
    (by decide) selected_cut_09978

theorem selected_cut_09979 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 99379) = some ⟨13, 1, 0, 265883, 99379, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99379_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99379 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 99379 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 99379, 1, 16384⟩
    (by decide) selected_cut_09979

theorem unmarked_context_12_24844_274323 : frontier 9 ⟨274323, by decide⟩
    (prefixCache 12 24844) (prefixPartial 12 24844) = false := by
  decide +kernel

theorem node_context_12_24844_274323 : EJMOriginalGlobalDAGData.nodes 9 ⟨274323, by decide⟩ =
    .split (coordinate 12) (![⟨274232, by decide⟩,⟨274267, by decide⟩,⟨274322, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24844_274323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24844 ⟨274323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24844
    ⟨274323, by decide⟩ (by decide) (![⟨274232, by decide⟩,⟨274267, by decide⟩,⟨274322, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_24844_274323 node_context_12_24844_274323
  intro a
  fin_cases a
  · exact context_13_99376_274232
  · exact context_13_99377_274267
  · exact context_13_99378_274322
  · exact context_13_99379_265883

theorem selected_cut_09980 : selected 8 ⟨274368, by decide⟩
    (prefixPartial 13 99380) = some ⟨13, 2, 0, 274368, 99380, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_99380_274368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99380 ⟨274368, by decide⟩ :=
  accepted_of_selected 13 99380 ⟨274368, by decide⟩ ⟨13, 2, 0, 274368, 99380, 3005, 16384⟩
    (by decide) selected_cut_09980

theorem selected_cut_09981 : selected 8 ⟨274405, by decide⟩
    (prefixPartial 13 99381) = some ⟨13, 2, 0, 274405, 99381, 3397, 16384⟩ := by
  decide +kernel

theorem context_13_99381_274405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99381 ⟨274405, by decide⟩ :=
  accepted_of_selected 13 99381 ⟨274405, by decide⟩ ⟨13, 2, 0, 274405, 99381, 3397, 16384⟩
    (by decide) selected_cut_09981

theorem selected_cut_09982 : selected 8 ⟨274432, by decide⟩
    (prefixPartial 13 99382) = some ⟨13, 2, 0, 274432, 99382, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_99382_274432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99382 ⟨274432, by decide⟩ :=
  accepted_of_selected 13 99382 ⟨274432, by decide⟩ ⟨13, 2, 0, 274432, 99382, 2369, 16384⟩
    (by decide) selected_cut_09982

theorem selected_cut_09983 : selected 8 ⟨274442, by decide⟩
    (prefixPartial 13 99383) = some ⟨13, 2, 0, 274442, 99383, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_99383_274442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99383 ⟨274442, by decide⟩ :=
  accepted_of_selected 13 99383 ⟨274442, by decide⟩ ⟨13, 2, 0, 274442, 99383, 1113, 16384⟩
    (by decide) selected_cut_09983

theorem unmarked_context_12_24845_274443 : frontier 9 ⟨274443, by decide⟩
    (prefixCache 12 24845) (prefixPartial 12 24845) = false := by
  decide +kernel

theorem node_context_12_24845_274443 : EJMOriginalGlobalDAGData.nodes 9 ⟨274443, by decide⟩ =
    .split (coordinate 12) (![⟨274368, by decide⟩,⟨274405, by decide⟩,⟨274432, by decide⟩,⟨274442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24845_274443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24845 ⟨274443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24845
    ⟨274443, by decide⟩ (by decide) (![⟨274368, by decide⟩,⟨274405, by decide⟩,⟨274432, by decide⟩,⟨274442, by decide⟩]) unmarked_context_12_24845_274443 node_context_12_24845_274443
  intro a
  fin_cases a
  · exact context_13_99380_274368
  · exact context_13_99381_274405
  · exact context_13_99382_274432
  · exact context_13_99383_274442

theorem selected_cut_09984 : selected 8 ⟨274484, by decide⟩
    (prefixPartial 13 99384) = some ⟨13, 2, 0, 274484, 99384, 3249, 16384⟩ := by
  decide +kernel

theorem context_13_99384_274484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99384 ⟨274484, by decide⟩ :=
  accepted_of_selected 13 99384 ⟨274484, by decide⟩ ⟨13, 2, 0, 274484, 99384, 3249, 16384⟩
    (by decide) selected_cut_09984

theorem selected_cut_09985 : selected 8 ⟨274529, by decide⟩
    (prefixPartial 13 99385) = some ⟨13, 2, 0, 274529, 99385, 3661, 16384⟩ := by
  decide +kernel

theorem context_13_99385_274529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99385 ⟨274529, by decide⟩ :=
  accepted_of_selected 13 99385 ⟨274529, by decide⟩ ⟨13, 2, 0, 274529, 99385, 3661, 16384⟩
    (by decide) selected_cut_09985

theorem selected_cut_09986 : selected 8 ⟨274555, by decide⟩
    (prefixPartial 13 99386) = some ⟨13, 2, 0, 274555, 99386, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_99386_274555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99386 ⟨274555, by decide⟩ :=
  accepted_of_selected 13 99386 ⟨274555, by decide⟩ ⟨13, 2, 0, 274555, 99386, 2333, 16384⟩
    (by decide) selected_cut_09986

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
