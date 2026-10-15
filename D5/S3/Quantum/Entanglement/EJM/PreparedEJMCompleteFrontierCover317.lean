/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover316
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30435 : selected 9 ⟨769652, by decide⟩
    (prefixPartial 12 104565) = some ⟨12, 2, 0, 769652, 104565, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_104565_769652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104565 ⟨769652, by decide⟩ :=
  accepted_of_selected 12 104565 ⟨769652, by decide⟩ ⟨12, 2, 0, 769652, 104565, 1501, 65536⟩
    (by decide) selected_cut_30435

theorem selected_cut_30436 : selected 9 ⟨769685, by decide⟩
    (prefixPartial 12 104566) = some ⟨12, 2, 0, 769685, 104566, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_104566_769685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104566 ⟨769685, by decide⟩ :=
  accepted_of_selected 12 104566 ⟨769685, by decide⟩ ⟨12, 2, 0, 769685, 104566, 1505, 65536⟩
    (by decide) selected_cut_30436

theorem selected_cut_30437 : selected 9 ⟨769719, by decide⟩
    (prefixPartial 12 104567) = some ⟨12, 2, 0, 769719, 104567, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_104567_769719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104567 ⟨769719, by decide⟩ :=
  accepted_of_selected 12 104567 ⟨769719, by decide⟩ ⟨12, 2, 0, 769719, 104567, 1589, 65536⟩
    (by decide) selected_cut_30437

theorem unmarked_context_11_26141_769720 : frontier 10 ⟨769720, by decide⟩
    (prefixCache 11 26141) (prefixPartial 11 26141) = false := by
  decide +kernel

theorem node_context_11_26141_769720 : EJMOriginalGlobalDAGData.nodes 10 ⟨769720, by decide⟩ =
    .split (coordinate 11) (![⟨769616, by decide⟩,⟨769652, by decide⟩,⟨769685, by decide⟩,⟨769719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26141_769720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26141 ⟨769720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26141
    ⟨769720, by decide⟩ (by decide) (![⟨769616, by decide⟩,⟨769652, by decide⟩,⟨769685, by decide⟩,⟨769719, by decide⟩]) unmarked_context_11_26141_769720 node_context_11_26141_769720
  intro a
  fin_cases a
  · exact context_12_104564_769616
  · exact context_12_104565_769652
  · exact context_12_104566_769685
  · exact context_12_104567_769719

theorem selected_cut_30438 : selected 9 ⟨769751, by decide⟩
    (prefixPartial 12 104568) = some ⟨12, 2, 0, 769751, 104568, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_104568_769751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104568 ⟨769751, by decide⟩ :=
  accepted_of_selected 12 104568 ⟨769751, by decide⟩ ⟨12, 2, 0, 769751, 104568, 1449, 65536⟩
    (by decide) selected_cut_30438

theorem selected_cut_30439 : selected 9 ⟨769785, by decide⟩
    (prefixPartial 12 104569) = some ⟨12, 2, 0, 769785, 104569, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_104569_769785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104569 ⟨769785, by decide⟩ :=
  accepted_of_selected 12 104569 ⟨769785, by decide⟩ ⟨12, 2, 0, 769785, 104569, 1337, 65536⟩
    (by decide) selected_cut_30439

theorem selected_cut_30440 : selected 9 ⟨769811, by decide⟩
    (prefixPartial 12 104570) = some ⟨12, 2, 0, 769811, 104570, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_104570_769811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104570 ⟨769811, by decide⟩ :=
  accepted_of_selected 12 104570 ⟨769811, by decide⟩ ⟨12, 2, 0, 769811, 104570, 1169, 65536⟩
    (by decide) selected_cut_30440

theorem selected_cut_30441 : selected 9 ⟨769838, by decide⟩
    (prefixPartial 12 104571) = some ⟨12, 2, 0, 769838, 104571, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_104571_769838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104571 ⟨769838, by decide⟩ :=
  accepted_of_selected 12 104571 ⟨769838, by decide⟩ ⟨12, 2, 0, 769838, 104571, 1261, 65536⟩
    (by decide) selected_cut_30441

theorem unmarked_context_11_26142_769839 : frontier 10 ⟨769839, by decide⟩
    (prefixCache 11 26142) (prefixPartial 11 26142) = false := by
  decide +kernel

theorem node_context_11_26142_769839 : EJMOriginalGlobalDAGData.nodes 10 ⟨769839, by decide⟩ =
    .split (coordinate 11) (![⟨769751, by decide⟩,⟨769785, by decide⟩,⟨769811, by decide⟩,⟨769838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26142_769839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26142 ⟨769839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26142
    ⟨769839, by decide⟩ (by decide) (![⟨769751, by decide⟩,⟨769785, by decide⟩,⟨769811, by decide⟩,⟨769838, by decide⟩]) unmarked_context_11_26142_769839 node_context_11_26142_769839
  intro a
  fin_cases a
  · exact context_12_104568_769751
  · exact context_12_104569_769785
  · exact context_12_104570_769811
  · exact context_12_104571_769838

theorem selected_cut_30442 : selected 10 ⟨769917, by decide⟩
    (prefixPartial 11 26143) = some ⟨11, 2, 0, 769917, 26143, 4081, 262144⟩ := by
  decide +kernel

theorem context_11_26143_769917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26143 ⟨769917, by decide⟩ :=
  accepted_of_selected 11 26143 ⟨769917, by decide⟩ ⟨11, 2, 0, 769917, 26143, 4081, 262144⟩
    (by decide) selected_cut_30442

theorem unmarked_context_10_6535_769918 : frontier 11 ⟨769918, by decide⟩
    (prefixCache 10 6535) (prefixPartial 10 6535) = false := by
  decide +kernel

theorem node_context_10_6535_769918 : EJMOriginalGlobalDAGData.nodes 11 ⟨769918, by decide⟩ =
    .split (coordinate 10) (![⟨769576, by decide⟩,⟨769720, by decide⟩,⟨769839, by decide⟩,⟨769917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6535_769918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6535 ⟨769918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6535
    ⟨769918, by decide⟩ (by decide) (![⟨769576, by decide⟩,⟨769720, by decide⟩,⟨769839, by decide⟩,⟨769917, by decide⟩]) unmarked_context_10_6535_769918 node_context_10_6535_769918
  intro a
  fin_cases a
  · exact context_11_26140_769576
  · exact context_11_26141_769720
  · exact context_11_26142_769839
  · exact context_11_26143_769917

theorem unmarked_context_9_1633_769919 : frontier 12 ⟨769919, by decide⟩
    (prefixCache 9 1633) (prefixPartial 9 1633) = false := by
  decide +kernel

theorem node_context_9_1633_769919 : EJMOriginalGlobalDAGData.nodes 12 ⟨769919, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨768638, by decide⟩,⟨769364, by decide⟩,⟨769918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1633_769919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1633 ⟨769919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1633
    ⟨769919, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨768638, by decide⟩,⟨769364, by decide⟩,⟨769918, by decide⟩]) unmarked_context_9_1633_769919 node_context_9_1633_769919
  intro a
  fin_cases a
  · exact context_10_6532_3442
  · exact context_10_6533_768638
  · exact context_10_6534_769364
  · exact context_10_6535_769918

theorem selected_cut_30443 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6536) = some ⟨10, 1, 0, 3442, 6536, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6536_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6536 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6536 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6536, 1, 1048576⟩
    (by decide) selected_cut_30443

theorem selected_cut_30444 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6537) = some ⟨10, 1, 0, 3442, 6537, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6537_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6537 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6537 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6537, 1, 1048576⟩
    (by decide) selected_cut_30444

theorem selected_cut_30445 : selected 11 ⟨769993, by decide⟩
    (prefixPartial 10 6538) = some ⟨10, 2, 0, 769993, 6538, 2793, 1048576⟩ := by
  decide +kernel

theorem context_10_6538_769993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6538 ⟨769993, by decide⟩ :=
  accepted_of_selected 10 6538 ⟨769993, by decide⟩ ⟨10, 2, 0, 769993, 6538, 2793, 1048576⟩
    (by decide) selected_cut_30445

theorem selected_cut_30446 : selected 10 ⟨770030, by decide⟩
    (prefixPartial 11 26156) = some ⟨11, 2, 0, 770030, 26156, 1333, 262144⟩ := by
  decide +kernel

theorem context_11_26156_770030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26156 ⟨770030, by decide⟩ :=
  accepted_of_selected 11 26156 ⟨770030, by decide⟩ ⟨11, 2, 0, 770030, 26156, 1333, 262144⟩
    (by decide) selected_cut_30446

theorem selected_cut_30447 : selected 10 ⟨770098, by decide⟩
    (prefixPartial 11 26157) = some ⟨11, 2, 0, 770098, 26157, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_26157_770098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26157 ⟨770098, by decide⟩ :=
  accepted_of_selected 11 26157 ⟨770098, by decide⟩ ⟨11, 2, 0, 770098, 26157, 2329, 262144⟩
    (by decide) selected_cut_30447

theorem selected_cut_30448 : selected 10 ⟨770142, by decide⟩
    (prefixPartial 11 26158) = some ⟨11, 2, 0, 770142, 26158, 1185, 262144⟩ := by
  decide +kernel

theorem context_11_26158_770142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26158 ⟨770142, by decide⟩ :=
  accepted_of_selected 11 26158 ⟨770142, by decide⟩ ⟨11, 2, 0, 770142, 26158, 1185, 262144⟩
    (by decide) selected_cut_30448

theorem selected_cut_30449 : selected 10 ⟨770170, by decide⟩
    (prefixPartial 11 26159) = some ⟨11, 2, 0, 770170, 26159, 853, 262144⟩ := by
  decide +kernel

theorem context_11_26159_770170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26159 ⟨770170, by decide⟩ :=
  accepted_of_selected 11 26159 ⟨770170, by decide⟩ ⟨11, 2, 0, 770170, 26159, 853, 262144⟩
    (by decide) selected_cut_30449

theorem unmarked_context_10_6539_770171 : frontier 11 ⟨770171, by decide⟩
    (prefixCache 10 6539) (prefixPartial 10 6539) = false := by
  decide +kernel

theorem node_context_10_6539_770171 : EJMOriginalGlobalDAGData.nodes 11 ⟨770171, by decide⟩ =
    .split (coordinate 10) (![⟨770030, by decide⟩,⟨770098, by decide⟩,⟨770142, by decide⟩,⟨770170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6539_770171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6539 ⟨770171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6539
    ⟨770171, by decide⟩ (by decide) (![⟨770030, by decide⟩,⟨770098, by decide⟩,⟨770142, by decide⟩,⟨770170, by decide⟩]) unmarked_context_10_6539_770171 node_context_10_6539_770171
  intro a
  fin_cases a
  · exact context_11_26156_770030
  · exact context_11_26157_770098
  · exact context_11_26158_770142
  · exact context_11_26159_770170

theorem unmarked_context_9_1634_770172 : frontier 12 ⟨770172, by decide⟩
    (prefixCache 9 1634) (prefixPartial 9 1634) = false := by
  decide +kernel

theorem node_context_9_1634_770172 : EJMOriginalGlobalDAGData.nodes 12 ⟨770172, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨769993, by decide⟩,⟨770171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1634_770172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1634 ⟨770172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1634
    ⟨770172, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨769993, by decide⟩,⟨770171, by decide⟩]) unmarked_context_9_1634_770172 node_context_9_1634_770172
  intro a
  fin_cases a
  · exact context_10_6536_3442
  · exact context_10_6537_3442
  · exact context_10_6538_769993
  · exact context_10_6539_770171

theorem selected_cut_30450 : selected 12 ⟨770190, by decide⟩
    (prefixPartial 9 1635) = some ⟨9, 2, 0, 770190, 1635, 805, 4194304⟩ := by
  decide +kernel

theorem context_9_1635_770190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1635 ⟨770190, by decide⟩ :=
  accepted_of_selected 9 1635 ⟨770190, by decide⟩ ⟨9, 2, 0, 770190, 1635, 805, 4194304⟩
    (by decide) selected_cut_30450

theorem unmarked_context_8_408_770191 : frontier 13 ⟨770191, by decide⟩
    (prefixCache 8 408) (prefixPartial 8 408) = false := by
  decide +kernel

theorem node_context_8_408_770191 : EJMOriginalGlobalDAGData.nodes 13 ⟨770191, by decide⟩ =
    .split (coordinate 8) (![⟨767916, by decide⟩,⟨769919, by decide⟩,⟨770172, by decide⟩,⟨770190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_408_770191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 408 ⟨770191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 408
    ⟨770191, by decide⟩ (by decide) (![⟨767916, by decide⟩,⟨769919, by decide⟩,⟨770172, by decide⟩,⟨770190, by decide⟩]) unmarked_context_8_408_770191 node_context_8_408_770191
  intro a
  fin_cases a
  · exact context_9_1632_767916
  · exact context_9_1633_769919
  · exact context_9_1634_770172
  · exact context_9_1635_770190

theorem selected_cut_30451 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26176) = some ⟨11, 1, 0, 434745, 26176, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26176_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26176 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26176 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26176, 1, 262144⟩
    (by decide) selected_cut_30451

theorem selected_cut_30452 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104708) = some ⟨12, 1, 0, 895, 104708, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104708_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104708 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104708 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104708, 1, 65536⟩
    (by decide) selected_cut_30452

theorem selected_cut_30453 : selected 7 ⟨770266, by decide⟩
    (prefixPartial 14 1675344) = some ⟨14, 2, 0, 770266, 1675344, 589, 4096⟩ := by
  decide +kernel

theorem context_14_1675344_770266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675344 ⟨770266, by decide⟩ :=
  accepted_of_selected 14 1675344 ⟨770266, by decide⟩ ⟨14, 2, 0, 770266, 1675344, 589, 4096⟩
    (by decide) selected_cut_30453

theorem selected_cut_30454 : selected 7 ⟨770429, by decide⟩
    (prefixPartial 14 1675345) = some ⟨14, 2, 0, 770429, 1675345, 2557, 4096⟩ := by
  decide +kernel

theorem context_14_1675345_770429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675345 ⟨770429, by decide⟩ :=
  accepted_of_selected 14 1675345 ⟨770429, by decide⟩ ⟨14, 2, 0, 770429, 1675345, 2557, 4096⟩
    (by decide) selected_cut_30454

theorem selected_cut_30455 : selected 7 ⟨770526, by decide⟩
    (prefixPartial 14 1675346) = some ⟨14, 2, 0, 770526, 1675346, 1369, 4096⟩ := by
  decide +kernel

theorem context_14_1675346_770526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675346 ⟨770526, by decide⟩ :=
  accepted_of_selected 14 1675346 ⟨770526, by decide⟩ ⟨14, 2, 0, 770526, 1675346, 1369, 4096⟩
    (by decide) selected_cut_30455

theorem selected_cut_30456 : selected 7 ⟨770618, by decide⟩
    (prefixPartial 14 1675347) = some ⟨14, 2, 0, 770618, 1675347, 1469, 4096⟩ := by
  decide +kernel

theorem context_14_1675347_770618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675347 ⟨770618, by decide⟩ :=
  accepted_of_selected 14 1675347 ⟨770618, by decide⟩ ⟨14, 2, 0, 770618, 1675347, 1469, 4096⟩
    (by decide) selected_cut_30456

theorem unmarked_context_13_418836_770619 : frontier 8 ⟨770619, by decide⟩
    (prefixCache 13 418836) (prefixPartial 13 418836) = false := by
  decide +kernel

theorem node_context_13_418836_770619 : EJMOriginalGlobalDAGData.nodes 8 ⟨770619, by decide⟩ =
    .split (coordinate 13) (![⟨770266, by decide⟩,⟨770429, by decide⟩,⟨770526, by decide⟩,⟨770618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_418836_770619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418836 ⟨770619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 418836
    ⟨770619, by decide⟩ (by decide) (![⟨770266, by decide⟩,⟨770429, by decide⟩,⟨770526, by decide⟩,⟨770618, by decide⟩]) unmarked_context_13_418836_770619 node_context_13_418836_770619
  intro a
  fin_cases a
  · exact context_14_1675344_770266
  · exact context_14_1675345_770429
  · exact context_14_1675346_770526
  · exact context_14_1675347_770618

theorem selected_cut_30457 : selected 8 ⟨770812, by decide⟩
    (prefixPartial 13 418837) = some ⟨13, 2, 0, 770812, 418837, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_418837_770812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418837 ⟨770812, by decide⟩ :=
  accepted_of_selected 13 418837 ⟨770812, by decide⟩ ⟨13, 2, 0, 770812, 418837, 1757, 16384⟩
    (by decide) selected_cut_30457

theorem selected_cut_30458 : selected 8 ⟨770833, by decide⟩
    (prefixPartial 13 418838) = some ⟨13, 2, 0, 770833, 418838, 149, 16384⟩ := by
  decide +kernel

theorem context_13_418838_770833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418838 ⟨770833, by decide⟩ :=
  accepted_of_selected 13 418838 ⟨770833, by decide⟩ ⟨13, 2, 0, 770833, 418838, 149, 16384⟩
    (by decide) selected_cut_30458

theorem selected_cut_30459 : selected 8 ⟨770835, by decide⟩
    (prefixPartial 13 418839) = some ⟨13, 2, 0, 770835, 418839, 25, 16384⟩ := by
  decide +kernel

theorem context_13_418839_770835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418839 ⟨770835, by decide⟩ :=
  accepted_of_selected 13 418839 ⟨770835, by decide⟩ ⟨13, 2, 0, 770835, 418839, 25, 16384⟩
    (by decide) selected_cut_30459

theorem unmarked_context_12_104709_770836 : frontier 9 ⟨770836, by decide⟩
    (prefixCache 12 104709) (prefixPartial 12 104709) = false := by
  decide +kernel

theorem node_context_12_104709_770836 : EJMOriginalGlobalDAGData.nodes 9 ⟨770836, by decide⟩ =
    .split (coordinate 12) (![⟨770619, by decide⟩,⟨770812, by decide⟩,⟨770833, by decide⟩,⟨770835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104709_770836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104709 ⟨770836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104709
    ⟨770836, by decide⟩ (by decide) (![⟨770619, by decide⟩,⟨770812, by decide⟩,⟨770833, by decide⟩,⟨770835, by decide⟩]) unmarked_context_12_104709_770836 node_context_12_104709_770836
  intro a
  fin_cases a
  · exact context_13_418836_770619
  · exact context_13_418837_770812
  · exact context_13_418838_770833
  · exact context_13_418839_770835

theorem selected_cut_30460 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 104710) = some ⟨12, 1, 0, 763842, 104710, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104710_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104710 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 104710 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 104710, 1, 65536⟩
    (by decide) selected_cut_30460

theorem selected_cut_30461 : selected 7 ⟨770866, by decide⟩
    (prefixPartial 14 1675376) = some ⟨14, 2, 0, 770866, 1675376, 449, 4096⟩ := by
  decide +kernel

theorem context_14_1675376_770866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675376 ⟨770866, by decide⟩ :=
  accepted_of_selected 14 1675376 ⟨770866, by decide⟩ ⟨14, 2, 0, 770866, 1675376, 449, 4096⟩
    (by decide) selected_cut_30461

theorem selected_cut_30462 : selected 7 ⟨770906, by decide⟩
    (prefixPartial 14 1675377) = some ⟨14, 2, 0, 770906, 1675377, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_1675377_770906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675377 ⟨770906, by decide⟩ :=
  accepted_of_selected 14 1675377 ⟨770906, by decide⟩ ⟨14, 2, 0, 770906, 1675377, 1189, 4096⟩
    (by decide) selected_cut_30462

theorem selected_cut_30463 : selected 7 ⟨770942, by decide⟩
    (prefixPartial 14 1675378) = some ⟨14, 2, 0, 770942, 1675378, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_1675378_770942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675378 ⟨770942, by decide⟩ :=
  accepted_of_selected 14 1675378 ⟨770942, by decide⟩ ⟨14, 2, 0, 770942, 1675378, 1061, 4096⟩
    (by decide) selected_cut_30463

theorem selected_cut_30464 : selected 7 ⟨770989, by decide⟩
    (prefixPartial 14 1675379) = some ⟨14, 2, 0, 770989, 1675379, 1537, 4096⟩ := by
  decide +kernel

theorem context_14_1675379_770989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675379 ⟨770989, by decide⟩ :=
  accepted_of_selected 14 1675379 ⟨770989, by decide⟩ ⟨14, 2, 0, 770989, 1675379, 1537, 4096⟩
    (by decide) selected_cut_30464

theorem unmarked_context_13_418844_770990 : frontier 8 ⟨770990, by decide⟩
    (prefixCache 13 418844) (prefixPartial 13 418844) = false := by
  decide +kernel

theorem node_context_13_418844_770990 : EJMOriginalGlobalDAGData.nodes 8 ⟨770990, by decide⟩ =
    .split (coordinate 13) (![⟨770866, by decide⟩,⟨770906, by decide⟩,⟨770942, by decide⟩,⟨770989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_418844_770990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418844 ⟨770990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 418844
    ⟨770990, by decide⟩ (by decide) (![⟨770866, by decide⟩,⟨770906, by decide⟩,⟨770942, by decide⟩,⟨770989, by decide⟩]) unmarked_context_13_418844_770990 node_context_13_418844_770990
  intro a
  fin_cases a
  · exact context_14_1675376_770866
  · exact context_14_1675377_770906
  · exact context_14_1675378_770942
  · exact context_14_1675379_770989

theorem selected_cut_30465 : selected 7 ⟨771028, by decide⟩
    (prefixPartial 14 1675380) = some ⟨14, 2, 0, 771028, 1675380, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_1675380_771028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675380 ⟨771028, by decide⟩ :=
  accepted_of_selected 14 1675380 ⟨771028, by decide⟩ ⟨14, 2, 0, 771028, 1675380, 1273, 4096⟩
    (by decide) selected_cut_30465

theorem selected_cut_30466 : selected 7 ⟨771068, by decide⟩
    (prefixPartial 14 1675381) = some ⟨14, 2, 0, 771068, 1675381, 1389, 4096⟩ := by
  decide +kernel

theorem context_14_1675381_771068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675381 ⟨771068, by decide⟩ :=
  accepted_of_selected 14 1675381 ⟨771068, by decide⟩ ⟨14, 2, 0, 771068, 1675381, 1389, 4096⟩
    (by decide) selected_cut_30466

theorem selected_cut_30467 : selected 7 ⟨771112, by decide⟩
    (prefixPartial 14 1675382) = some ⟨14, 2, 0, 771112, 1675382, 1445, 4096⟩ := by
  decide +kernel

theorem context_14_1675382_771112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675382 ⟨771112, by decide⟩ :=
  accepted_of_selected 14 1675382 ⟨771112, by decide⟩ ⟨14, 2, 0, 771112, 1675382, 1445, 4096⟩
    (by decide) selected_cut_30467

theorem selected_cut_30468 : selected 7 ⟨771147, by decide⟩
    (prefixPartial 14 1675383) = some ⟨14, 2, 0, 771147, 1675383, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_1675383_771147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1675383 ⟨771147, by decide⟩ :=
  accepted_of_selected 14 1675383 ⟨771147, by decide⟩ ⟨14, 2, 0, 771147, 1675383, 1553, 4096⟩
    (by decide) selected_cut_30468

theorem unmarked_context_13_418845_771148 : frontier 8 ⟨771148, by decide⟩
    (prefixCache 13 418845) (prefixPartial 13 418845) = false := by
  decide +kernel

theorem node_context_13_418845_771148 : EJMOriginalGlobalDAGData.nodes 8 ⟨771148, by decide⟩ =
    .split (coordinate 13) (![⟨771028, by decide⟩,⟨771068, by decide⟩,⟨771112, by decide⟩,⟨771147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_418845_771148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418845 ⟨771148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 418845
    ⟨771148, by decide⟩ (by decide) (![⟨771028, by decide⟩,⟨771068, by decide⟩,⟨771112, by decide⟩,⟨771147, by decide⟩]) unmarked_context_13_418845_771148 node_context_13_418845_771148
  intro a
  fin_cases a
  · exact context_14_1675380_771028
  · exact context_14_1675381_771068
  · exact context_14_1675382_771112
  · exact context_14_1675383_771147

theorem selected_cut_30469 : selected 8 ⟨771270, by decide⟩
    (prefixPartial 13 418846) = some ⟨13, 2, 0, 771270, 418846, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_418846_771270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418846 ⟨771270, by decide⟩ :=
  accepted_of_selected 13 418846 ⟨771270, by decide⟩ ⟨13, 2, 0, 771270, 418846, 2677, 16384⟩
    (by decide) selected_cut_30469

theorem selected_cut_30470 : selected 8 ⟨771329, by decide⟩
    (prefixPartial 13 418847) = some ⟨13, 2, 0, 771329, 418847, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_418847_771329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418847 ⟨771329, by decide⟩ :=
  accepted_of_selected 13 418847 ⟨771329, by decide⟩ ⟨13, 2, 0, 771329, 418847, 1385, 16384⟩
    (by decide) selected_cut_30470

theorem unmarked_context_12_104711_771330 : frontier 9 ⟨771330, by decide⟩
    (prefixCache 12 104711) (prefixPartial 12 104711) = false := by
  decide +kernel

theorem node_context_12_104711_771330 : EJMOriginalGlobalDAGData.nodes 9 ⟨771330, by decide⟩ =
    .split (coordinate 12) (![⟨770990, by decide⟩,⟨771148, by decide⟩,⟨771270, by decide⟩,⟨771329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104711_771330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104711 ⟨771330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104711
    ⟨771330, by decide⟩ (by decide) (![⟨770990, by decide⟩,⟨771148, by decide⟩,⟨771270, by decide⟩,⟨771329, by decide⟩]) unmarked_context_12_104711_771330 node_context_12_104711_771330
  intro a
  fin_cases a
  · exact context_13_418844_770990
  · exact context_13_418845_771148
  · exact context_13_418846_771270
  · exact context_13_418847_771329

theorem unmarked_context_11_26177_771331 : frontier 10 ⟨771331, by decide⟩
    (prefixCache 11 26177) (prefixPartial 11 26177) = false := by
  decide +kernel

theorem node_context_11_26177_771331 : EJMOriginalGlobalDAGData.nodes 10 ⟨771331, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨770836, by decide⟩,⟨763842, by decide⟩,⟨771330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26177_771331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26177 ⟨771331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26177
    ⟨771331, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨770836, by decide⟩,⟨763842, by decide⟩,⟨771330, by decide⟩]) unmarked_context_11_26177_771331 node_context_11_26177_771331
  intro a
  fin_cases a
  · exact context_12_104708_895
  · exact context_12_104709_770836
  · exact context_12_104710_763842
  · exact context_12_104711_771330

theorem selected_cut_30471 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 26178) = some ⟨11, 1, 0, 764169, 26178, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26178_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26178 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 26178 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 26178, 1, 262144⟩
    (by decide) selected_cut_30471

theorem selected_cut_30472 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104716) = some ⟨12, 1, 0, 895, 104716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104716_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104716 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104716 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104716, 1, 65536⟩
    (by decide) selected_cut_30472

theorem selected_cut_30473 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104717) = some ⟨12, 1, 0, 895, 104717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104717_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104717 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104717 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104717, 1, 65536⟩
    (by decide) selected_cut_30473

theorem selected_cut_30474 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104718) = some ⟨12, 1, 0, 895, 104718, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104718_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104718 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104718 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104718, 1, 65536⟩
    (by decide) selected_cut_30474

theorem selected_cut_30475 : selected 8 ⟨771479, by decide⟩
    (prefixPartial 13 418876) = some ⟨13, 2, 0, 771479, 418876, 3981, 16384⟩ := by
  decide +kernel

theorem context_13_418876_771479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418876 ⟨771479, by decide⟩ :=
  accepted_of_selected 13 418876 ⟨771479, by decide⟩ ⟨13, 2, 0, 771479, 418876, 3981, 16384⟩
    (by decide) selected_cut_30475

theorem selected_cut_30476 : selected 8 ⟨771635, by decide⟩
    (prefixPartial 13 418877) = some ⟨13, 2, 0, 771635, 418877, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_418877_771635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418877 ⟨771635, by decide⟩ :=
  accepted_of_selected 13 418877 ⟨771635, by decide⟩ ⟨13, 2, 0, 771635, 418877, 3033, 16384⟩
    (by decide) selected_cut_30476

theorem selected_cut_30477 : selected 8 ⟨771681, by decide⟩
    (prefixPartial 13 418878) = some ⟨13, 2, 0, 771681, 418878, 673, 16384⟩ := by
  decide +kernel

theorem context_13_418878_771681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418878 ⟨771681, by decide⟩ :=
  accepted_of_selected 13 418878 ⟨771681, by decide⟩ ⟨13, 2, 0, 771681, 418878, 673, 16384⟩
    (by decide) selected_cut_30477

theorem selected_cut_30478 : selected 8 ⟨771697, by decide⟩
    (prefixPartial 13 418879) = some ⟨13, 2, 0, 771697, 418879, 169, 16384⟩ := by
  decide +kernel

theorem context_13_418879_771697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418879 ⟨771697, by decide⟩ :=
  accepted_of_selected 13 418879 ⟨771697, by decide⟩ ⟨13, 2, 0, 771697, 418879, 169, 16384⟩
    (by decide) selected_cut_30478

theorem unmarked_context_12_104719_771698 : frontier 9 ⟨771698, by decide⟩
    (prefixCache 12 104719) (prefixPartial 12 104719) = false := by
  decide +kernel

theorem node_context_12_104719_771698 : EJMOriginalGlobalDAGData.nodes 9 ⟨771698, by decide⟩ =
    .split (coordinate 12) (![⟨771479, by decide⟩,⟨771635, by decide⟩,⟨771681, by decide⟩,⟨771697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104719_771698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104719 ⟨771698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104719
    ⟨771698, by decide⟩ (by decide) (![⟨771479, by decide⟩,⟨771635, by decide⟩,⟨771681, by decide⟩,⟨771697, by decide⟩]) unmarked_context_12_104719_771698 node_context_12_104719_771698
  intro a
  fin_cases a
  · exact context_13_418876_771479
  · exact context_13_418877_771635
  · exact context_13_418878_771681
  · exact context_13_418879_771697

theorem unmarked_context_11_26179_771699 : frontier 10 ⟨771699, by decide⟩
    (prefixCache 11 26179) (prefixPartial 11 26179) = false := by
  decide +kernel

theorem node_context_11_26179_771699 : EJMOriginalGlobalDAGData.nodes 10 ⟨771699, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨895, by decide⟩,⟨771698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26179_771699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26179 ⟨771699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26179
    ⟨771699, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨895, by decide⟩,⟨771698, by decide⟩]) unmarked_context_11_26179_771699 node_context_11_26179_771699
  intro a
  fin_cases a
  · exact context_12_104716_895
  · exact context_12_104717_895
  · exact context_12_104718_895
  · exact context_12_104719_771698

theorem unmarked_context_10_6544_771700 : frontier 11 ⟨771700, by decide⟩
    (prefixCache 10 6544) (prefixPartial 10 6544) = false := by
  decide +kernel

theorem node_context_10_6544_771700 : EJMOriginalGlobalDAGData.nodes 11 ⟨771700, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨771331, by decide⟩,⟨764169, by decide⟩,⟨771699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6544_771700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6544 ⟨771700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6544
    ⟨771700, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨771331, by decide⟩,⟨764169, by decide⟩,⟨771699, by decide⟩]) unmarked_context_10_6544_771700 node_context_10_6544_771700
  intro a
  fin_cases a
  · exact context_11_26176_434745
  · exact context_11_26177_771331
  · exact context_11_26178_764169
  · exact context_11_26179_771699

theorem selected_cut_30479 : selected 8 ⟨771748, by decide⟩
    (prefixPartial 13 418880) = some ⟨13, 2, 0, 771748, 418880, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_418880_771748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418880 ⟨771748, by decide⟩ :=
  accepted_of_selected 13 418880 ⟨771748, by decide⟩ ⟨13, 2, 0, 771748, 418880, 2053, 16384⟩
    (by decide) selected_cut_30479

theorem selected_cut_30480 : selected 8 ⟨771785, by decide⟩
    (prefixPartial 13 418881) = some ⟨13, 2, 0, 771785, 418881, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_418881_771785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418881 ⟨771785, by decide⟩ :=
  accepted_of_selected 13 418881 ⟨771785, by decide⟩ ⟨13, 2, 0, 771785, 418881, 2049, 16384⟩
    (by decide) selected_cut_30480

theorem selected_cut_30481 : selected 8 ⟨771818, by decide⟩
    (prefixPartial 13 418882) = some ⟨13, 2, 0, 771818, 418882, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_418882_771818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418882 ⟨771818, by decide⟩ :=
  accepted_of_selected 13 418882 ⟨771818, by decide⟩ ⟨13, 2, 0, 771818, 418882, 1285, 16384⟩
    (by decide) selected_cut_30481

theorem selected_cut_30482 : selected 8 ⟨771830, by decide⟩
    (prefixPartial 13 418883) = some ⟨13, 2, 0, 771830, 418883, 861, 16384⟩ := by
  decide +kernel

theorem context_13_418883_771830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418883 ⟨771830, by decide⟩ :=
  accepted_of_selected 13 418883 ⟨771830, by decide⟩ ⟨13, 2, 0, 771830, 418883, 861, 16384⟩
    (by decide) selected_cut_30482

theorem unmarked_context_12_104720_771831 : frontier 9 ⟨771831, by decide⟩
    (prefixCache 12 104720) (prefixPartial 12 104720) = false := by
  decide +kernel

theorem node_context_12_104720_771831 : EJMOriginalGlobalDAGData.nodes 9 ⟨771831, by decide⟩ =
    .split (coordinate 12) (![⟨771748, by decide⟩,⟨771785, by decide⟩,⟨771818, by decide⟩,⟨771830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104720_771831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104720 ⟨771831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104720
    ⟨771831, by decide⟩ (by decide) (![⟨771748, by decide⟩,⟨771785, by decide⟩,⟨771818, by decide⟩,⟨771830, by decide⟩]) unmarked_context_12_104720_771831 node_context_12_104720_771831
  intro a
  fin_cases a
  · exact context_13_418880_771748
  · exact context_13_418881_771785
  · exact context_13_418882_771818
  · exact context_13_418883_771830

theorem selected_cut_30483 : selected 8 ⟨771876, by decide⟩
    (prefixPartial 13 418884) = some ⟨13, 2, 0, 771876, 418884, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_418884_771876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418884 ⟨771876, by decide⟩ :=
  accepted_of_selected 13 418884 ⟨771876, by decide⟩ ⟨13, 2, 0, 771876, 418884, 2129, 16384⟩
    (by decide) selected_cut_30483

theorem selected_cut_30484 : selected 8 ⟨771914, by decide⟩
    (prefixPartial 13 418885) = some ⟨13, 2, 0, 771914, 418885, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_418885_771914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418885 ⟨771914, by decide⟩ :=
  accepted_of_selected 13 418885 ⟨771914, by decide⟩ ⟨13, 2, 0, 771914, 418885, 1725, 16384⟩
    (by decide) selected_cut_30484

theorem selected_cut_30485 : selected 8 ⟨771944, by decide⟩
    (prefixPartial 13 418886) = some ⟨13, 2, 0, 771944, 418886, 597, 16384⟩ := by
  decide +kernel

theorem context_13_418886_771944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418886 ⟨771944, by decide⟩ :=
  accepted_of_selected 13 418886 ⟨771944, by decide⟩ ⟨13, 2, 0, 771944, 418886, 597, 16384⟩
    (by decide) selected_cut_30485

theorem selected_cut_30486 : selected 8 ⟨771962, by decide⟩
    (prefixPartial 13 418887) = some ⟨13, 2, 0, 771962, 418887, 241, 16384⟩ := by
  decide +kernel

theorem context_13_418887_771962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418887 ⟨771962, by decide⟩ :=
  accepted_of_selected 13 418887 ⟨771962, by decide⟩ ⟨13, 2, 0, 771962, 418887, 241, 16384⟩
    (by decide) selected_cut_30486

theorem unmarked_context_12_104721_771963 : frontier 9 ⟨771963, by decide⟩
    (prefixCache 12 104721) (prefixPartial 12 104721) = false := by
  decide +kernel

theorem node_context_12_104721_771963 : EJMOriginalGlobalDAGData.nodes 9 ⟨771963, by decide⟩ =
    .split (coordinate 12) (![⟨771876, by decide⟩,⟨771914, by decide⟩,⟨771944, by decide⟩,⟨771962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104721_771963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104721 ⟨771963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104721
    ⟨771963, by decide⟩ (by decide) (![⟨771876, by decide⟩,⟨771914, by decide⟩,⟨771944, by decide⟩,⟨771962, by decide⟩]) unmarked_context_12_104721_771963 node_context_12_104721_771963
  intro a
  fin_cases a
  · exact context_13_418884_771876
  · exact context_13_418885_771914
  · exact context_13_418886_771944
  · exact context_13_418887_771962

theorem selected_cut_30487 : selected 8 ⟨772021, by decide⟩
    (prefixPartial 13 418888) = some ⟨13, 2, 0, 772021, 418888, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_418888_772021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418888 ⟨772021, by decide⟩ :=
  accepted_of_selected 13 418888 ⟨772021, by decide⟩ ⟨13, 2, 0, 772021, 418888, 2525, 16384⟩
    (by decide) selected_cut_30487

theorem selected_cut_30488 : selected 8 ⟨772076, by decide⟩
    (prefixPartial 13 418889) = some ⟨13, 2, 0, 772076, 418889, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_418889_772076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418889 ⟨772076, by decide⟩ :=
  accepted_of_selected 13 418889 ⟨772076, by decide⟩ ⟨13, 2, 0, 772076, 418889, 2545, 16384⟩
    (by decide) selected_cut_30488

theorem selected_cut_30489 : selected 8 ⟨772126, by decide⟩
    (prefixPartial 13 418890) = some ⟨13, 2, 0, 772126, 418890, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_418890_772126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418890 ⟨772126, by decide⟩ :=
  accepted_of_selected 13 418890 ⟨772126, by decide⟩ ⟨13, 2, 0, 772126, 418890, 1593, 16384⟩
    (by decide) selected_cut_30489

theorem selected_cut_30490 : selected 8 ⟨772157, by decide⟩
    (prefixPartial 13 418891) = some ⟨13, 2, 0, 772157, 418891, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_418891_772157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418891 ⟨772157, by decide⟩ :=
  accepted_of_selected 13 418891 ⟨772157, by decide⟩ ⟨13, 2, 0, 772157, 418891, 1089, 16384⟩
    (by decide) selected_cut_30490

theorem unmarked_context_12_104722_772158 : frontier 9 ⟨772158, by decide⟩
    (prefixCache 12 104722) (prefixPartial 12 104722) = false := by
  decide +kernel

theorem node_context_12_104722_772158 : EJMOriginalGlobalDAGData.nodes 9 ⟨772158, by decide⟩ =
    .split (coordinate 12) (![⟨772021, by decide⟩,⟨772076, by decide⟩,⟨772126, by decide⟩,⟨772157, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104722_772158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104722 ⟨772158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104722
    ⟨772158, by decide⟩ (by decide) (![⟨772021, by decide⟩,⟨772076, by decide⟩,⟨772126, by decide⟩,⟨772157, by decide⟩]) unmarked_context_12_104722_772158 node_context_12_104722_772158
  intro a
  fin_cases a
  · exact context_13_418888_772021
  · exact context_13_418889_772076
  · exact context_13_418890_772126
  · exact context_13_418891_772157

theorem selected_cut_30491 : selected 8 ⟨772212, by decide⟩
    (prefixPartial 13 418892) = some ⟨13, 2, 0, 772212, 418892, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_418892_772212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418892 ⟨772212, by decide⟩ :=
  accepted_of_selected 13 418892 ⟨772212, by decide⟩ ⟨13, 2, 0, 772212, 418892, 2625, 16384⟩
    (by decide) selected_cut_30491

theorem selected_cut_30492 : selected 8 ⟨772263, by decide⟩
    (prefixPartial 13 418893) = some ⟨13, 2, 0, 772263, 418893, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_418893_772263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418893 ⟨772263, by decide⟩ :=
  accepted_of_selected 13 418893 ⟨772263, by decide⟩ ⟨13, 2, 0, 772263, 418893, 2677, 16384⟩
    (by decide) selected_cut_30492

theorem selected_cut_30493 : selected 8 ⟨772317, by decide⟩
    (prefixPartial 13 418894) = some ⟨13, 2, 0, 772317, 418894, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_418894_772317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418894 ⟨772317, by decide⟩ :=
  accepted_of_selected 13 418894 ⟨772317, by decide⟩ ⟨13, 2, 0, 772317, 418894, 1765, 16384⟩
    (by decide) selected_cut_30493

theorem selected_cut_30494 : selected 8 ⟨772342, by decide⟩
    (prefixPartial 13 418895) = some ⟨13, 2, 0, 772342, 418895, 993, 16384⟩ := by
  decide +kernel

theorem context_13_418895_772342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418895 ⟨772342, by decide⟩ :=
  accepted_of_selected 13 418895 ⟨772342, by decide⟩ ⟨13, 2, 0, 772342, 418895, 993, 16384⟩
    (by decide) selected_cut_30494

theorem unmarked_context_12_104723_772343 : frontier 9 ⟨772343, by decide⟩
    (prefixCache 12 104723) (prefixPartial 12 104723) = false := by
  decide +kernel

theorem node_context_12_104723_772343 : EJMOriginalGlobalDAGData.nodes 9 ⟨772343, by decide⟩ =
    .split (coordinate 12) (![⟨772212, by decide⟩,⟨772263, by decide⟩,⟨772317, by decide⟩,⟨772342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104723_772343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104723 ⟨772343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104723
    ⟨772343, by decide⟩ (by decide) (![⟨772212, by decide⟩,⟨772263, by decide⟩,⟨772317, by decide⟩,⟨772342, by decide⟩]) unmarked_context_12_104723_772343 node_context_12_104723_772343
  intro a
  fin_cases a
  · exact context_13_418892_772212
  · exact context_13_418893_772263
  · exact context_13_418894_772317
  · exact context_13_418895_772342

theorem unmarked_context_11_26180_772344 : frontier 10 ⟨772344, by decide⟩
    (prefixCache 11 26180) (prefixPartial 11 26180) = false := by
  decide +kernel

theorem node_context_11_26180_772344 : EJMOriginalGlobalDAGData.nodes 10 ⟨772344, by decide⟩ =
    .split (coordinate 11) (![⟨771831, by decide⟩,⟨771963, by decide⟩,⟨772158, by decide⟩,⟨772343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26180_772344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26180 ⟨772344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26180
    ⟨772344, by decide⟩ (by decide) (![⟨771831, by decide⟩,⟨771963, by decide⟩,⟨772158, by decide⟩,⟨772343, by decide⟩]) unmarked_context_11_26180_772344 node_context_11_26180_772344
  intro a
  fin_cases a
  · exact context_12_104720_771831
  · exact context_12_104721_771963
  · exact context_12_104722_772158
  · exact context_12_104723_772343

theorem selected_cut_30495 : selected 9 ⟨772505, by decide⟩
    (prefixPartial 12 104724) = some ⟨12, 2, 0, 772505, 104724, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_104724_772505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104724 ⟨772505, by decide⟩ :=
  accepted_of_selected 12 104724 ⟨772505, by decide⟩ ⟨12, 2, 0, 772505, 104724, 3877, 65536⟩
    (by decide) selected_cut_30495

theorem selected_cut_30496 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 104725) = some ⟨12, 1, 0, 772506, 104725, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104725_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104725 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 104725 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 104725, 1, 65536⟩
    (by decide) selected_cut_30496

theorem selected_cut_30497 : selected 8 ⟨772544, by decide⟩
    (prefixPartial 13 418904) = some ⟨13, 2, 0, 772544, 418904, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_418904_772544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418904 ⟨772544, by decide⟩ :=
  accepted_of_selected 13 418904 ⟨772544, by decide⟩ ⟨13, 2, 0, 772544, 418904, 2005, 16384⟩
    (by decide) selected_cut_30497

theorem selected_cut_30498 : selected 8 ⟨772581, by decide⟩
    (prefixPartial 13 418905) = some ⟨13, 2, 0, 772581, 418905, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_418905_772581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418905 ⟨772581, by decide⟩ :=
  accepted_of_selected 13 418905 ⟨772581, by decide⟩ ⟨13, 2, 0, 772581, 418905, 2361, 16384⟩
    (by decide) selected_cut_30498

theorem selected_cut_30499 : selected 8 ⟨772605, by decide⟩
    (prefixPartial 13 418906) = some ⟨13, 2, 0, 772605, 418906, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_418906_772605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418906 ⟨772605, by decide⟩ :=
  accepted_of_selected 13 418906 ⟨772605, by decide⟩ ⟨13, 2, 0, 772605, 418906, 1161, 16384⟩
    (by decide) selected_cut_30499

theorem selected_cut_30500 : selected 8 ⟨772627, by decide⟩
    (prefixPartial 13 418907) = some ⟨13, 2, 0, 772627, 418907, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_418907_772627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418907 ⟨772627, by decide⟩ :=
  accepted_of_selected 13 418907 ⟨772627, by decide⟩ ⟨13, 2, 0, 772627, 418907, 1113, 16384⟩
    (by decide) selected_cut_30500

theorem unmarked_context_12_104726_772628 : frontier 9 ⟨772628, by decide⟩
    (prefixCache 12 104726) (prefixPartial 12 104726) = false := by
  decide +kernel

theorem node_context_12_104726_772628 : EJMOriginalGlobalDAGData.nodes 9 ⟨772628, by decide⟩ =
    .split (coordinate 12) (![⟨772544, by decide⟩,⟨772581, by decide⟩,⟨772605, by decide⟩,⟨772627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104726_772628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104726 ⟨772628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104726
    ⟨772628, by decide⟩ (by decide) (![⟨772544, by decide⟩,⟨772581, by decide⟩,⟨772605, by decide⟩,⟨772627, by decide⟩]) unmarked_context_12_104726_772628 node_context_12_104726_772628
  intro a
  fin_cases a
  · exact context_13_418904_772544
  · exact context_13_418905_772581
  · exact context_13_418906_772605
  · exact context_13_418907_772627

theorem selected_cut_30501 : selected 8 ⟨772670, by decide⟩
    (prefixPartial 13 418908) = some ⟨13, 2, 0, 772670, 418908, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_418908_772670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418908 ⟨772670, by decide⟩ :=
  accepted_of_selected 13 418908 ⟨772670, by decide⟩ ⟨13, 2, 0, 772670, 418908, 2029, 16384⟩
    (by decide) selected_cut_30501

theorem selected_cut_30502 : selected 8 ⟨772716, by decide⟩
    (prefixPartial 13 418909) = some ⟨13, 2, 0, 772716, 418909, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_418909_772716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418909 ⟨772716, by decide⟩ :=
  accepted_of_selected 13 418909 ⟨772716, by decide⟩ ⟨13, 2, 0, 772716, 418909, 2525, 16384⟩
    (by decide) selected_cut_30502

theorem selected_cut_30503 : selected 8 ⟨772741, by decide⟩
    (prefixPartial 13 418910) = some ⟨13, 2, 0, 772741, 418910, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_418910_772741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418910 ⟨772741, by decide⟩ :=
  accepted_of_selected 13 418910 ⟨772741, by decide⟩ ⟨13, 2, 0, 772741, 418910, 1433, 16384⟩
    (by decide) selected_cut_30503

theorem selected_cut_30504 : selected 8 ⟨772755, by decide⟩
    (prefixPartial 13 418911) = some ⟨13, 2, 0, 772755, 418911, 901, 16384⟩ := by
  decide +kernel

theorem context_13_418911_772755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418911 ⟨772755, by decide⟩ :=
  accepted_of_selected 13 418911 ⟨772755, by decide⟩ ⟨13, 2, 0, 772755, 418911, 901, 16384⟩
    (by decide) selected_cut_30504

theorem unmarked_context_12_104727_772756 : frontier 9 ⟨772756, by decide⟩
    (prefixCache 12 104727) (prefixPartial 12 104727) = false := by
  decide +kernel

theorem node_context_12_104727_772756 : EJMOriginalGlobalDAGData.nodes 9 ⟨772756, by decide⟩ =
    .split (coordinate 12) (![⟨772670, by decide⟩,⟨772716, by decide⟩,⟨772741, by decide⟩,⟨772755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104727_772756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104727 ⟨772756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104727
    ⟨772756, by decide⟩ (by decide) (![⟨772670, by decide⟩,⟨772716, by decide⟩,⟨772741, by decide⟩,⟨772755, by decide⟩]) unmarked_context_12_104727_772756 node_context_12_104727_772756
  intro a
  fin_cases a
  · exact context_13_418908_772670
  · exact context_13_418909_772716
  · exact context_13_418910_772741
  · exact context_13_418911_772755

theorem unmarked_context_11_26181_772757 : frontier 10 ⟨772757, by decide⟩
    (prefixCache 11 26181) (prefixPartial 11 26181) = false := by
  decide +kernel

theorem node_context_11_26181_772757 : EJMOriginalGlobalDAGData.nodes 10 ⟨772757, by decide⟩ =
    .split (coordinate 11) (![⟨772505, by decide⟩,⟨772506, by decide⟩,⟨772628, by decide⟩,⟨772756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26181_772757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26181 ⟨772757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26181
    ⟨772757, by decide⟩ (by decide) (![⟨772505, by decide⟩,⟨772506, by decide⟩,⟨772628, by decide⟩,⟨772756, by decide⟩]) unmarked_context_11_26181_772757 node_context_11_26181_772757
  intro a
  fin_cases a
  · exact context_12_104724_772505
  · exact context_12_104725_772506
  · exact context_12_104726_772628
  · exact context_12_104727_772756

theorem selected_cut_30505 : selected 8 ⟨772780, by decide⟩
    (prefixPartial 13 418912) = some ⟨13, 2, 0, 772780, 418912, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_418912_772780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418912 ⟨772780, by decide⟩ :=
  accepted_of_selected 13 418912 ⟨772780, by decide⟩ ⟨13, 2, 0, 772780, 418912, 1633, 16384⟩
    (by decide) selected_cut_30505

theorem selected_cut_30506 : selected 8 ⟨772811, by decide⟩
    (prefixPartial 13 418913) = some ⟨13, 2, 0, 772811, 418913, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_418913_772811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418913 ⟨772811, by decide⟩ :=
  accepted_of_selected 13 418913 ⟨772811, by decide⟩ ⟨13, 2, 0, 772811, 418913, 1925, 16384⟩
    (by decide) selected_cut_30506

theorem selected_cut_30507 : selected 8 ⟨772852, by decide⟩
    (prefixPartial 13 418914) = some ⟨13, 2, 0, 772852, 418914, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_418914_772852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418914 ⟨772852, by decide⟩ :=
  accepted_of_selected 13 418914 ⟨772852, by decide⟩ ⟨13, 2, 0, 772852, 418914, 1405, 16384⟩
    (by decide) selected_cut_30507

theorem selected_cut_30508 : selected 8 ⟨772879, by decide⟩
    (prefixPartial 13 418915) = some ⟨13, 2, 0, 772879, 418915, 913, 16384⟩ := by
  decide +kernel

theorem context_13_418915_772879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418915 ⟨772879, by decide⟩ :=
  accepted_of_selected 13 418915 ⟨772879, by decide⟩ ⟨13, 2, 0, 772879, 418915, 913, 16384⟩
    (by decide) selected_cut_30508

theorem unmarked_context_12_104728_772880 : frontier 9 ⟨772880, by decide⟩
    (prefixCache 12 104728) (prefixPartial 12 104728) = false := by
  decide +kernel

theorem node_context_12_104728_772880 : EJMOriginalGlobalDAGData.nodes 9 ⟨772880, by decide⟩ =
    .split (coordinate 12) (![⟨772780, by decide⟩,⟨772811, by decide⟩,⟨772852, by decide⟩,⟨772879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104728_772880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104728 ⟨772880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104728
    ⟨772880, by decide⟩ (by decide) (![⟨772780, by decide⟩,⟨772811, by decide⟩,⟨772852, by decide⟩,⟨772879, by decide⟩]) unmarked_context_12_104728_772880 node_context_12_104728_772880
  intro a
  fin_cases a
  · exact context_13_418912_772780
  · exact context_13_418913_772811
  · exact context_13_418914_772852
  · exact context_13_418915_772879

theorem selected_cut_30509 : selected 8 ⟨772905, by decide⟩
    (prefixPartial 13 418916) = some ⟨13, 2, 0, 772905, 418916, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_418916_772905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418916 ⟨772905, by decide⟩ :=
  accepted_of_selected 13 418916 ⟨772905, by decide⟩ ⟨13, 2, 0, 772905, 418916, 1677, 16384⟩
    (by decide) selected_cut_30509

theorem selected_cut_30510 : selected 8 ⟨772932, by decide⟩
    (prefixPartial 13 418917) = some ⟨13, 2, 0, 772932, 418917, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_418917_772932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418917 ⟨772932, by decide⟩ :=
  accepted_of_selected 13 418917 ⟨772932, by decide⟩ ⟨13, 2, 0, 772932, 418917, 1957, 16384⟩
    (by decide) selected_cut_30510

theorem selected_cut_30511 : selected 8 ⟨772949, by decide⟩
    (prefixPartial 13 418918) = some ⟨13, 2, 0, 772949, 418918, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_418918_772949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418918 ⟨772949, by decide⟩ :=
  accepted_of_selected 13 418918 ⟨772949, by decide⟩ ⟨13, 2, 0, 772949, 418918, 1425, 16384⟩
    (by decide) selected_cut_30511

theorem selected_cut_30512 : selected 8 ⟨772968, by decide⟩
    (prefixPartial 13 418919) = some ⟨13, 2, 0, 772968, 418919, 997, 16384⟩ := by
  decide +kernel

theorem context_13_418919_772968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418919 ⟨772968, by decide⟩ :=
  accepted_of_selected 13 418919 ⟨772968, by decide⟩ ⟨13, 2, 0, 772968, 418919, 997, 16384⟩
    (by decide) selected_cut_30512

theorem unmarked_context_12_104729_772969 : frontier 9 ⟨772969, by decide⟩
    (prefixCache 12 104729) (prefixPartial 12 104729) = false := by
  decide +kernel

theorem node_context_12_104729_772969 : EJMOriginalGlobalDAGData.nodes 9 ⟨772969, by decide⟩ =
    .split (coordinate 12) (![⟨772905, by decide⟩,⟨772932, by decide⟩,⟨772949, by decide⟩,⟨772968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104729_772969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104729 ⟨772969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104729
    ⟨772969, by decide⟩ (by decide) (![⟨772905, by decide⟩,⟨772932, by decide⟩,⟨772949, by decide⟩,⟨772968, by decide⟩]) unmarked_context_12_104729_772969 node_context_12_104729_772969
  intro a
  fin_cases a
  · exact context_13_418916_772905
  · exact context_13_418917_772932
  · exact context_13_418918_772949
  · exact context_13_418919_772968

theorem selected_cut_30513 : selected 8 ⟨772994, by decide⟩
    (prefixPartial 13 418920) = some ⟨13, 2, 0, 772994, 418920, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_418920_772994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418920 ⟨772994, by decide⟩ :=
  accepted_of_selected 13 418920 ⟨772994, by decide⟩ ⟨13, 2, 0, 772994, 418920, 1673, 16384⟩
    (by decide) selected_cut_30513

theorem selected_cut_30514 : selected 8 ⟨773025, by decide⟩
    (prefixPartial 13 418921) = some ⟨13, 2, 0, 773025, 418921, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_418921_773025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418921 ⟨773025, by decide⟩ :=
  accepted_of_selected 13 418921 ⟨773025, by decide⟩ ⟨13, 2, 0, 773025, 418921, 2001, 16384⟩
    (by decide) selected_cut_30514

theorem selected_cut_30515 : selected 8 ⟨773060, by decide⟩
    (prefixPartial 13 418922) = some ⟨13, 2, 0, 773060, 418922, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_418922_773060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418922 ⟨773060, by decide⟩ :=
  accepted_of_selected 13 418922 ⟨773060, by decide⟩ ⟨13, 2, 0, 773060, 418922, 1425, 16384⟩
    (by decide) selected_cut_30515

theorem selected_cut_30516 : selected 8 ⟨773078, by decide⟩
    (prefixPartial 13 418923) = some ⟨13, 2, 0, 773078, 418923, 989, 16384⟩ := by
  decide +kernel

theorem context_13_418923_773078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418923 ⟨773078, by decide⟩ :=
  accepted_of_selected 13 418923 ⟨773078, by decide⟩ ⟨13, 2, 0, 773078, 418923, 989, 16384⟩
    (by decide) selected_cut_30516

theorem unmarked_context_12_104730_773079 : frontier 9 ⟨773079, by decide⟩
    (prefixCache 12 104730) (prefixPartial 12 104730) = false := by
  decide +kernel

theorem node_context_12_104730_773079 : EJMOriginalGlobalDAGData.nodes 9 ⟨773079, by decide⟩ =
    .split (coordinate 12) (![⟨772994, by decide⟩,⟨773025, by decide⟩,⟨773060, by decide⟩,⟨773078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104730_773079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104730 ⟨773079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104730
    ⟨773079, by decide⟩ (by decide) (![⟨772994, by decide⟩,⟨773025, by decide⟩,⟨773060, by decide⟩,⟨773078, by decide⟩]) unmarked_context_12_104730_773079 node_context_12_104730_773079
  intro a
  fin_cases a
  · exact context_13_418920_772994
  · exact context_13_418921_773025
  · exact context_13_418922_773060
  · exact context_13_418923_773078

theorem selected_cut_30517 : selected 8 ⟨773116, by decide⟩
    (prefixPartial 13 418924) = some ⟨13, 2, 0, 773116, 418924, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_418924_773116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418924 ⟨773116, by decide⟩ :=
  accepted_of_selected 13 418924 ⟨773116, by decide⟩ ⟨13, 2, 0, 773116, 418924, 1753, 16384⟩
    (by decide) selected_cut_30517

theorem selected_cut_30518 : selected 8 ⟨773165, by decide⟩
    (prefixPartial 13 418925) = some ⟨13, 2, 0, 773165, 418925, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_418925_773165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418925 ⟨773165, by decide⟩ :=
  accepted_of_selected 13 418925 ⟨773165, by decide⟩ ⟨13, 2, 0, 773165, 418925, 2269, 16384⟩
    (by decide) selected_cut_30518

theorem selected_cut_30519 : selected 8 ⟨773215, by decide⟩
    (prefixPartial 13 418926) = some ⟨13, 2, 0, 773215, 418926, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_418926_773215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418926 ⟨773215, by decide⟩ :=
  accepted_of_selected 13 418926 ⟨773215, by decide⟩ ⟨13, 2, 0, 773215, 418926, 1517, 16384⟩
    (by decide) selected_cut_30519

theorem selected_cut_30520 : selected 8 ⟨773228, by decide⟩
    (prefixPartial 13 418927) = some ⟨13, 2, 0, 773228, 418927, 917, 16384⟩ := by
  decide +kernel

theorem context_13_418927_773228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418927 ⟨773228, by decide⟩ :=
  accepted_of_selected 13 418927 ⟨773228, by decide⟩ ⟨13, 2, 0, 773228, 418927, 917, 16384⟩
    (by decide) selected_cut_30520

theorem unmarked_context_12_104731_773229 : frontier 9 ⟨773229, by decide⟩
    (prefixCache 12 104731) (prefixPartial 12 104731) = false := by
  decide +kernel

theorem node_context_12_104731_773229 : EJMOriginalGlobalDAGData.nodes 9 ⟨773229, by decide⟩ =
    .split (coordinate 12) (![⟨773116, by decide⟩,⟨773165, by decide⟩,⟨773215, by decide⟩,⟨773228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104731_773229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104731 ⟨773229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104731
    ⟨773229, by decide⟩ (by decide) (![⟨773116, by decide⟩,⟨773165, by decide⟩,⟨773215, by decide⟩,⟨773228, by decide⟩]) unmarked_context_12_104731_773229 node_context_12_104731_773229
  intro a
  fin_cases a
  · exact context_13_418924_773116
  · exact context_13_418925_773165
  · exact context_13_418926_773215
  · exact context_13_418927_773228

theorem unmarked_context_11_26182_773230 : frontier 10 ⟨773230, by decide⟩
    (prefixCache 11 26182) (prefixPartial 11 26182) = false := by
  decide +kernel

theorem node_context_11_26182_773230 : EJMOriginalGlobalDAGData.nodes 10 ⟨773230, by decide⟩ =
    .split (coordinate 11) (![⟨772880, by decide⟩,⟨772969, by decide⟩,⟨773079, by decide⟩,⟨773229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26182_773230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26182 ⟨773230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26182
    ⟨773230, by decide⟩ (by decide) (![⟨772880, by decide⟩,⟨772969, by decide⟩,⟨773079, by decide⟩,⟨773229, by decide⟩]) unmarked_context_11_26182_773230 node_context_11_26182_773230
  intro a
  fin_cases a
  · exact context_12_104728_772880
  · exact context_12_104729_772969
  · exact context_12_104730_773079
  · exact context_12_104731_773229

theorem selected_cut_30521 : selected 8 ⟨773261, by decide⟩
    (prefixPartial 13 418928) = some ⟨13, 2, 0, 773261, 418928, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_418928_773261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418928 ⟨773261, by decide⟩ :=
  accepted_of_selected 13 418928 ⟨773261, by decide⟩ ⟨13, 2, 0, 773261, 418928, 1545, 16384⟩
    (by decide) selected_cut_30521

theorem selected_cut_30522 : selected 8 ⟨773303, by decide⟩
    (prefixPartial 13 418929) = some ⟨13, 2, 0, 773303, 418929, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_418929_773303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418929 ⟨773303, by decide⟩ :=
  accepted_of_selected 13 418929 ⟨773303, by decide⟩ ⟨13, 2, 0, 773303, 418929, 1981, 16384⟩
    (by decide) selected_cut_30522

theorem selected_cut_30523 : selected 8 ⟨773348, by decide⟩
    (prefixPartial 13 418930) = some ⟨13, 2, 0, 773348, 418930, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_418930_773348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418930 ⟨773348, by decide⟩ :=
  accepted_of_selected 13 418930 ⟨773348, by decide⟩ ⟨13, 2, 0, 773348, 418930, 1445, 16384⟩
    (by decide) selected_cut_30523

theorem selected_cut_30524 : selected 8 ⟨773369, by decide⟩
    (prefixPartial 13 418931) = some ⟨13, 2, 0, 773369, 418931, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_418931_773369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418931 ⟨773369, by decide⟩ :=
  accepted_of_selected 13 418931 ⟨773369, by decide⟩ ⟨13, 2, 0, 773369, 418931, 1037, 16384⟩
    (by decide) selected_cut_30524

theorem unmarked_context_12_104732_773370 : frontier 9 ⟨773370, by decide⟩
    (prefixCache 12 104732) (prefixPartial 12 104732) = false := by
  decide +kernel

theorem node_context_12_104732_773370 : EJMOriginalGlobalDAGData.nodes 9 ⟨773370, by decide⟩ =
    .split (coordinate 12) (![⟨773261, by decide⟩,⟨773303, by decide⟩,⟨773348, by decide⟩,⟨773369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104732_773370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104732 ⟨773370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104732
    ⟨773370, by decide⟩ (by decide) (![⟨773261, by decide⟩,⟨773303, by decide⟩,⟨773348, by decide⟩,⟨773369, by decide⟩]) unmarked_context_12_104732_773370 node_context_12_104732_773370
  intro a
  fin_cases a
  · exact context_13_418928_773261
  · exact context_13_418929_773303
  · exact context_13_418930_773348
  · exact context_13_418931_773369

theorem selected_cut_30525 : selected 8 ⟨773402, by decide⟩
    (prefixPartial 13 418932) = some ⟨13, 2, 0, 773402, 418932, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_418932_773402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418932 ⟨773402, by decide⟩ :=
  accepted_of_selected 13 418932 ⟨773402, by decide⟩ ⟨13, 2, 0, 773402, 418932, 1545, 16384⟩
    (by decide) selected_cut_30525

theorem selected_cut_30526 : selected 8 ⟨773443, by decide⟩
    (prefixPartial 13 418933) = some ⟨13, 2, 0, 773443, 418933, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_418933_773443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418933 ⟨773443, by decide⟩ :=
  accepted_of_selected 13 418933 ⟨773443, by decide⟩ ⟨13, 2, 0, 773443, 418933, 1901, 16384⟩
    (by decide) selected_cut_30526

theorem selected_cut_30527 : selected 8 ⟨773472, by decide⟩
    (prefixPartial 13 418934) = some ⟨13, 2, 0, 773472, 418934, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_418934_773472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418934 ⟨773472, by decide⟩ :=
  accepted_of_selected 13 418934 ⟨773472, by decide⟩ ⟨13, 2, 0, 773472, 418934, 1429, 16384⟩
    (by decide) selected_cut_30527

theorem selected_cut_30528 : selected 8 ⟨773488, by decide⟩
    (prefixPartial 13 418935) = some ⟨13, 2, 0, 773488, 418935, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_418935_773488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418935 ⟨773488, by decide⟩ :=
  accepted_of_selected 13 418935 ⟨773488, by decide⟩ ⟨13, 2, 0, 773488, 418935, 1021, 16384⟩
    (by decide) selected_cut_30528

theorem unmarked_context_12_104733_773489 : frontier 9 ⟨773489, by decide⟩
    (prefixCache 12 104733) (prefixPartial 12 104733) = false := by
  decide +kernel

theorem node_context_12_104733_773489 : EJMOriginalGlobalDAGData.nodes 9 ⟨773489, by decide⟩ =
    .split (coordinate 12) (![⟨773402, by decide⟩,⟨773443, by decide⟩,⟨773472, by decide⟩,⟨773488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104733_773489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104733 ⟨773489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104733
    ⟨773489, by decide⟩ (by decide) (![⟨773402, by decide⟩,⟨773443, by decide⟩,⟨773472, by decide⟩,⟨773488, by decide⟩]) unmarked_context_12_104733_773489 node_context_12_104733_773489
  intro a
  fin_cases a
  · exact context_13_418932_773402
  · exact context_13_418933_773443
  · exact context_13_418934_773472
  · exact context_13_418935_773488

theorem selected_cut_30529 : selected 8 ⟨773519, by decide⟩
    (prefixPartial 13 418936) = some ⟨13, 2, 0, 773519, 418936, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_418936_773519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418936 ⟨773519, by decide⟩ :=
  accepted_of_selected 13 418936 ⟨773519, by decide⟩ ⟨13, 2, 0, 773519, 418936, 1549, 16384⟩
    (by decide) selected_cut_30529

theorem selected_cut_30530 : selected 8 ⟨773565, by decide⟩
    (prefixPartial 13 418937) = some ⟨13, 2, 0, 773565, 418937, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_418937_773565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418937 ⟨773565, by decide⟩ :=
  accepted_of_selected 13 418937 ⟨773565, by decide⟩ ⟨13, 2, 0, 773565, 418937, 2081, 16384⟩
    (by decide) selected_cut_30530

theorem selected_cut_30531 : selected 8 ⟨773602, by decide⟩
    (prefixPartial 13 418938) = some ⟨13, 2, 0, 773602, 418938, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_418938_773602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418938 ⟨773602, by decide⟩ :=
  accepted_of_selected 13 418938 ⟨773602, by decide⟩ ⟨13, 2, 0, 773602, 418938, 1441, 16384⟩
    (by decide) selected_cut_30531

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
