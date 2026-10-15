/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover429
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41283 : selected 9 ⟨1128678, by decide⟩
    (prefixPartial 12 334617) = some ⟨12, 2, 0, 1128678, 334617, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_334617_1128678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334617 ⟨1128678, by decide⟩ :=
  accepted_of_selected 12 334617 ⟨1128678, by decide⟩ ⟨12, 2, 0, 1128678, 334617, 2841, 65536⟩
    (by decide) selected_cut_41283

theorem selected_cut_41284 : selected 9 ⟨1128728, by decide⟩
    (prefixPartial 12 334618) = some ⟨12, 2, 0, 1128728, 334618, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_334618_1128728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334618 ⟨1128728, by decide⟩ :=
  accepted_of_selected 12 334618 ⟨1128728, by decide⟩ ⟨12, 2, 0, 1128728, 334618, 2817, 65536⟩
    (by decide) selected_cut_41284

theorem selected_cut_41285 : selected 9 ⟨1128795, by decide⟩
    (prefixPartial 12 334619) = some ⟨12, 2, 0, 1128795, 334619, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_334619_1128795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334619 ⟨1128795, by decide⟩ :=
  accepted_of_selected 12 334619 ⟨1128795, by decide⟩ ⟨12, 2, 0, 1128795, 334619, 3037, 65536⟩
    (by decide) selected_cut_41285

theorem unmarked_context_11_83654_1128796 : frontier 10 ⟨1128796, by decide⟩
    (prefixCache 11 83654) (prefixPartial 11 83654) = false := by
  decide +kernel

theorem node_context_11_83654_1128796 : EJMOriginalGlobalDAGData.nodes 10 ⟨1128796, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1128678, by decide⟩,⟨1128728, by decide⟩,⟨1128795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83654_1128796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83654 ⟨1128796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83654
    ⟨1128796, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1128678, by decide⟩,⟨1128728, by decide⟩,⟨1128795, by decide⟩]) unmarked_context_11_83654_1128796 node_context_11_83654_1128796
  intro a
  fin_cases a
  · exact context_12_334616_1108174
  · exact context_12_334617_1128678
  · exact context_12_334618_1128728
  · exact context_12_334619_1128795

theorem selected_cut_41286 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334620) = some ⟨12, 1, 0, 1108174, 334620, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334620_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334620 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334620 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334620, 1, 65536⟩
    (by decide) selected_cut_41286

theorem selected_cut_41287 : selected 9 ⟨1128845, by decide⟩
    (prefixPartial 12 334621) = some ⟨12, 2, 0, 1128845, 334621, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_334621_1128845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334621 ⟨1128845, by decide⟩ :=
  accepted_of_selected 12 334621 ⟨1128845, by decide⟩ ⟨12, 2, 0, 1128845, 334621, 2989, 65536⟩
    (by decide) selected_cut_41287

theorem selected_cut_41288 : selected 9 ⟨1128908, by decide⟩
    (prefixPartial 12 334622) = some ⟨12, 2, 0, 1128908, 334622, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_334622_1128908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334622 ⟨1128908, by decide⟩ :=
  accepted_of_selected 12 334622 ⟨1128908, by decide⟩ ⟨12, 2, 0, 1128908, 334622, 3433, 65536⟩
    (by decide) selected_cut_41288

theorem selected_cut_41289 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 334623) = some ⟨12, 1, 0, 903806, 334623, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334623_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334623 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 334623 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 334623, 1, 65536⟩
    (by decide) selected_cut_41289

theorem unmarked_context_11_83655_1128909 : frontier 10 ⟨1128909, by decide⟩
    (prefixCache 11 83655) (prefixPartial 11 83655) = false := by
  decide +kernel

theorem node_context_11_83655_1128909 : EJMOriginalGlobalDAGData.nodes 10 ⟨1128909, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1128845, by decide⟩,⟨1128908, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83655_1128909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83655 ⟨1128909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83655
    ⟨1128909, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1128845, by decide⟩,⟨1128908, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_83655_1128909 node_context_11_83655_1128909
  intro a
  fin_cases a
  · exact context_12_334620_1108174
  · exact context_12_334621_1128845
  · exact context_12_334622_1128908
  · exact context_12_334623_903806

theorem unmarked_context_10_20913_1128910 : frontier 11 ⟨1128910, by decide⟩
    (prefixCache 10 20913) (prefixPartial 10 20913) = false := by
  decide +kernel

theorem node_context_10_20913_1128910 : EJMOriginalGlobalDAGData.nodes 11 ⟨1128910, by decide⟩ =
    .split (coordinate 10) (![⟨1128493, by decide⟩,⟨1128627, by decide⟩,⟨1128796, by decide⟩,⟨1128909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20913_1128910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20913 ⟨1128910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20913
    ⟨1128910, by decide⟩ (by decide) (![⟨1128493, by decide⟩,⟨1128627, by decide⟩,⟨1128796, by decide⟩,⟨1128909, by decide⟩]) unmarked_context_10_20913_1128910 node_context_10_20913_1128910
  intro a
  fin_cases a
  · exact context_11_83652_1128493
  · exact context_11_83653_1128627
  · exact context_11_83654_1128796
  · exact context_11_83655_1128909

theorem selected_cut_41290 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334624) = some ⟨12, 1, 0, 1108174, 334624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334624_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334624 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334624 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334624, 1, 65536⟩
    (by decide) selected_cut_41290

theorem selected_cut_41291 : selected 9 ⟨1128982, by decide⟩
    (prefixPartial 12 334625) = some ⟨12, 2, 0, 1128982, 334625, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_334625_1128982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334625 ⟨1128982, by decide⟩ :=
  accepted_of_selected 12 334625 ⟨1128982, by decide⟩ ⟨12, 2, 0, 1128982, 334625, 3449, 65536⟩
    (by decide) selected_cut_41291

theorem selected_cut_41292 : selected 9 ⟨1129057, by decide⟩
    (prefixPartial 12 334626) = some ⟨12, 2, 0, 1129057, 334626, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_334626_1129057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334626 ⟨1129057, by decide⟩ :=
  accepted_of_selected 12 334626 ⟨1129057, by decide⟩ ⟨12, 2, 0, 1129057, 334626, 3897, 65536⟩
    (by decide) selected_cut_41292

theorem selected_cut_41293 : selected 9 ⟨1129135, by decide⟩
    (prefixPartial 12 334627) = some ⟨12, 2, 0, 1129135, 334627, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_334627_1129135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334627 ⟨1129135, by decide⟩ :=
  accepted_of_selected 12 334627 ⟨1129135, by decide⟩ ⟨12, 2, 0, 1129135, 334627, 3269, 65536⟩
    (by decide) selected_cut_41293

theorem unmarked_context_11_83656_1129136 : frontier 10 ⟨1129136, by decide⟩
    (prefixCache 11 83656) (prefixPartial 11 83656) = false := by
  decide +kernel

theorem node_context_11_83656_1129136 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129136, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1128982, by decide⟩,⟨1129057, by decide⟩,⟨1129135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83656_1129136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83656 ⟨1129136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83656
    ⟨1129136, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1128982, by decide⟩,⟨1129057, by decide⟩,⟨1129135, by decide⟩]) unmarked_context_11_83656_1129136 node_context_11_83656_1129136
  intro a
  fin_cases a
  · exact context_12_334624_1108174
  · exact context_12_334625_1128982
  · exact context_12_334626_1129057
  · exact context_12_334627_1129135

theorem selected_cut_41294 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334628) = some ⟨12, 1, 0, 1108174, 334628, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334628_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334628 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334628 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334628, 1, 65536⟩
    (by decide) selected_cut_41294

theorem selected_cut_41295 : selected 9 ⟨1129208, by decide⟩
    (prefixPartial 12 334629) = some ⟨12, 2, 0, 1129208, 334629, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_334629_1129208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334629 ⟨1129208, by decide⟩ :=
  accepted_of_selected 12 334629 ⟨1129208, by decide⟩ ⟨12, 2, 0, 1129208, 334629, 3581, 65536⟩
    (by decide) selected_cut_41295

theorem selected_cut_41296 : selected 9 ⟨1129263, by decide⟩
    (prefixPartial 12 334630) = some ⟨12, 2, 0, 1129263, 334630, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_334630_1129263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334630 ⟨1129263, by decide⟩ :=
  accepted_of_selected 12 334630 ⟨1129263, by decide⟩ ⟨12, 2, 0, 1129263, 334630, 2973, 65536⟩
    (by decide) selected_cut_41296

theorem selected_cut_41297 : selected 9 ⟨1129318, by decide⟩
    (prefixPartial 12 334631) = some ⟨12, 2, 0, 1129318, 334631, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_334631_1129318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334631 ⟨1129318, by decide⟩ :=
  accepted_of_selected 12 334631 ⟨1129318, by decide⟩ ⟨12, 2, 0, 1129318, 334631, 2713, 65536⟩
    (by decide) selected_cut_41297

theorem unmarked_context_11_83657_1129319 : frontier 10 ⟨1129319, by decide⟩
    (prefixCache 11 83657) (prefixPartial 11 83657) = false := by
  decide +kernel

theorem node_context_11_83657_1129319 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129319, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1129208, by decide⟩,⟨1129263, by decide⟩,⟨1129318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83657_1129319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83657 ⟨1129319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83657
    ⟨1129319, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1129208, by decide⟩,⟨1129263, by decide⟩,⟨1129318, by decide⟩]) unmarked_context_11_83657_1129319 node_context_11_83657_1129319
  intro a
  fin_cases a
  · exact context_12_334628_1108174
  · exact context_12_334629_1129208
  · exact context_12_334630_1129263
  · exact context_12_334631_1129318

theorem selected_cut_41298 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 83658) = some ⟨11, 1, 0, 900587, 83658, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83658_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83658 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 83658 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 83658, 1, 262144⟩
    (by decide) selected_cut_41298

theorem selected_cut_41299 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334636) = some ⟨12, 1, 0, 1108174, 334636, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334636_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334636 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334636 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334636, 1, 65536⟩
    (by decide) selected_cut_41299

theorem selected_cut_41300 : selected 9 ⟨1129369, by decide⟩
    (prefixPartial 12 334637) = some ⟨12, 2, 0, 1129369, 334637, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_334637_1129369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334637 ⟨1129369, by decide⟩ :=
  accepted_of_selected 12 334637 ⟨1129369, by decide⟩ ⟨12, 2, 0, 1129369, 334637, 2853, 65536⟩
    (by decide) selected_cut_41300

theorem selected_cut_41301 : selected 9 ⟨1129434, by decide⟩
    (prefixPartial 12 334638) = some ⟨12, 2, 0, 1129434, 334638, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_334638_1129434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334638 ⟨1129434, by decide⟩ :=
  accepted_of_selected 12 334638 ⟨1129434, by decide⟩ ⟨12, 2, 0, 1129434, 334638, 3421, 65536⟩
    (by decide) selected_cut_41301

theorem selected_cut_41302 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 334639) = some ⟨12, 1, 0, 903806, 334639, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334639_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334639 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 334639 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 334639, 1, 65536⟩
    (by decide) selected_cut_41302

theorem unmarked_context_11_83659_1129435 : frontier 10 ⟨1129435, by decide⟩
    (prefixCache 11 83659) (prefixPartial 11 83659) = false := by
  decide +kernel

theorem node_context_11_83659_1129435 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129435, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1129369, by decide⟩,⟨1129434, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83659_1129435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83659 ⟨1129435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83659
    ⟨1129435, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1129369, by decide⟩,⟨1129434, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_83659_1129435 node_context_11_83659_1129435
  intro a
  fin_cases a
  · exact context_12_334636_1108174
  · exact context_12_334637_1129369
  · exact context_12_334638_1129434
  · exact context_12_334639_903806

theorem unmarked_context_10_20914_1129436 : frontier 11 ⟨1129436, by decide⟩
    (prefixCache 10 20914) (prefixPartial 10 20914) = false := by
  decide +kernel

theorem node_context_10_20914_1129436 : EJMOriginalGlobalDAGData.nodes 11 ⟨1129436, by decide⟩ =
    .split (coordinate 10) (![⟨1129136, by decide⟩,⟨1129319, by decide⟩,⟨900587, by decide⟩,⟨1129435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20914_1129436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20914 ⟨1129436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20914
    ⟨1129436, by decide⟩ (by decide) (![⟨1129136, by decide⟩,⟨1129319, by decide⟩,⟨900587, by decide⟩,⟨1129435, by decide⟩]) unmarked_context_10_20914_1129436 node_context_10_20914_1129436
  intro a
  fin_cases a
  · exact context_11_83656_1129136
  · exact context_11_83657_1129319
  · exact context_11_83658_900587
  · exact context_11_83659_1129435

theorem selected_cut_41303 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334640) = some ⟨12, 1, 0, 1108174, 334640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334640_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334640 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334640 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334640, 1, 65536⟩
    (by decide) selected_cut_41303

theorem selected_cut_41304 : selected 9 ⟨1129493, by decide⟩
    (prefixPartial 12 334641) = some ⟨12, 2, 0, 1129493, 334641, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_334641_1129493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334641 ⟨1129493, by decide⟩ :=
  accepted_of_selected 12 334641 ⟨1129493, by decide⟩ ⟨12, 2, 0, 1129493, 334641, 3165, 65536⟩
    (by decide) selected_cut_41304

theorem selected_cut_41305 : selected 9 ⟨1129546, by decide⟩
    (prefixPartial 12 334642) = some ⟨12, 2, 0, 1129546, 334642, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_334642_1129546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334642 ⟨1129546, by decide⟩ :=
  accepted_of_selected 12 334642 ⟨1129546, by decide⟩ ⟨12, 2, 0, 1129546, 334642, 3513, 65536⟩
    (by decide) selected_cut_41305

theorem selected_cut_41306 : selected 9 ⟨1129601, by decide⟩
    (prefixPartial 12 334643) = some ⟨12, 2, 0, 1129601, 334643, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_334643_1129601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334643 ⟨1129601, by decide⟩ :=
  accepted_of_selected 12 334643 ⟨1129601, by decide⟩ ⟨12, 2, 0, 1129601, 334643, 3041, 65536⟩
    (by decide) selected_cut_41306

theorem unmarked_context_11_83660_1129602 : frontier 10 ⟨1129602, by decide⟩
    (prefixCache 11 83660) (prefixPartial 11 83660) = false := by
  decide +kernel

theorem node_context_11_83660_1129602 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129602, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1129493, by decide⟩,⟨1129546, by decide⟩,⟨1129601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83660_1129602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83660 ⟨1129602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83660
    ⟨1129602, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1129493, by decide⟩,⟨1129546, by decide⟩,⟨1129601, by decide⟩]) unmarked_context_11_83660_1129602 node_context_11_83660_1129602
  intro a
  fin_cases a
  · exact context_12_334640_1108174
  · exact context_12_334641_1129493
  · exact context_12_334642_1129546
  · exact context_12_334643_1129601

theorem selected_cut_41307 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334644) = some ⟨12, 1, 0, 1108174, 334644, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334644_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334644 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334644 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334644, 1, 65536⟩
    (by decide) selected_cut_41307

theorem selected_cut_41308 : selected 9 ⟨1129659, by decide⟩
    (prefixPartial 12 334645) = some ⟨12, 2, 0, 1129659, 334645, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_334645_1129659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334645 ⟨1129659, by decide⟩ :=
  accepted_of_selected 12 334645 ⟨1129659, by decide⟩ ⟨12, 2, 0, 1129659, 334645, 3249, 65536⟩
    (by decide) selected_cut_41308

theorem selected_cut_41309 : selected 9 ⟨1129704, by decide⟩
    (prefixPartial 12 334646) = some ⟨12, 2, 0, 1129704, 334646, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_334646_1129704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334646 ⟨1129704, by decide⟩ :=
  accepted_of_selected 12 334646 ⟨1129704, by decide⟩ ⟨12, 2, 0, 1129704, 334646, 2829, 65536⟩
    (by decide) selected_cut_41309

theorem selected_cut_41310 : selected 9 ⟨1129750, by decide⟩
    (prefixPartial 12 334647) = some ⟨12, 2, 0, 1129750, 334647, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_334647_1129750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334647 ⟨1129750, by decide⟩ :=
  accepted_of_selected 12 334647 ⟨1129750, by decide⟩ ⟨12, 2, 0, 1129750, 334647, 2617, 65536⟩
    (by decide) selected_cut_41310

theorem unmarked_context_11_83661_1129751 : frontier 10 ⟨1129751, by decide⟩
    (prefixCache 11 83661) (prefixPartial 11 83661) = false := by
  decide +kernel

theorem node_context_11_83661_1129751 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129751, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1129659, by decide⟩,⟨1129704, by decide⟩,⟨1129750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83661_1129751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83661 ⟨1129751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83661
    ⟨1129751, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1129659, by decide⟩,⟨1129704, by decide⟩,⟨1129750, by decide⟩]) unmarked_context_11_83661_1129751 node_context_11_83661_1129751
  intro a
  fin_cases a
  · exact context_12_334644_1108174
  · exact context_12_334645_1129659
  · exact context_12_334646_1129704
  · exact context_12_334647_1129750

theorem selected_cut_41311 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334648) = some ⟨12, 1, 0, 1108174, 334648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334648_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334648 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334648 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334648, 1, 65536⟩
    (by decide) selected_cut_41311

theorem selected_cut_41312 : selected 9 ⟨1129790, by decide⟩
    (prefixPartial 12 334649) = some ⟨12, 2, 0, 1129790, 334649, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_334649_1129790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334649 ⟨1129790, by decide⟩ :=
  accepted_of_selected 12 334649 ⟨1129790, by decide⟩ ⟨12, 2, 0, 1129790, 334649, 2617, 65536⟩
    (by decide) selected_cut_41312

theorem selected_cut_41313 : selected 9 ⟨1129836, by decide⟩
    (prefixPartial 12 334650) = some ⟨12, 2, 0, 1129836, 334650, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_334650_1129836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334650 ⟨1129836, by decide⟩ :=
  accepted_of_selected 12 334650 ⟨1129836, by decide⟩ ⟨12, 2, 0, 1129836, 334650, 2601, 65536⟩
    (by decide) selected_cut_41313

theorem selected_cut_41314 : selected 9 ⟨1129884, by decide⟩
    (prefixPartial 12 334651) = some ⟨12, 2, 0, 1129884, 334651, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_334651_1129884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334651 ⟨1129884, by decide⟩ :=
  accepted_of_selected 12 334651 ⟨1129884, by decide⟩ ⟨12, 2, 0, 1129884, 334651, 2657, 65536⟩
    (by decide) selected_cut_41314

theorem unmarked_context_11_83662_1129885 : frontier 10 ⟨1129885, by decide⟩
    (prefixCache 11 83662) (prefixPartial 11 83662) = false := by
  decide +kernel

theorem node_context_11_83662_1129885 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129885, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1129790, by decide⟩,⟨1129836, by decide⟩,⟨1129884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83662_1129885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83662 ⟨1129885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83662
    ⟨1129885, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1129790, by decide⟩,⟨1129836, by decide⟩,⟨1129884, by decide⟩]) unmarked_context_11_83662_1129885 node_context_11_83662_1129885
  intro a
  fin_cases a
  · exact context_12_334648_1108174
  · exact context_12_334649_1129790
  · exact context_12_334650_1129836
  · exact context_12_334651_1129884

theorem selected_cut_41315 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334652) = some ⟨12, 1, 0, 1108174, 334652, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334652_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334652 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334652 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334652, 1, 65536⟩
    (by decide) selected_cut_41315

theorem selected_cut_41316 : selected 9 ⟨1129923, by decide⟩
    (prefixPartial 12 334653) = some ⟨12, 2, 0, 1129923, 334653, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_334653_1129923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334653 ⟨1129923, by decide⟩ :=
  accepted_of_selected 12 334653 ⟨1129923, by decide⟩ ⟨12, 2, 0, 1129923, 334653, 2637, 65536⟩
    (by decide) selected_cut_41316

theorem selected_cut_41317 : selected 9 ⟨1129976, by decide⟩
    (prefixPartial 12 334654) = some ⟨12, 2, 0, 1129976, 334654, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_334654_1129976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334654 ⟨1129976, by decide⟩ :=
  accepted_of_selected 12 334654 ⟨1129976, by decide⟩ ⟨12, 2, 0, 1129976, 334654, 3077, 65536⟩
    (by decide) selected_cut_41317

theorem selected_cut_41318 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 334655) = some ⟨12, 1, 0, 1120582, 334655, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334655_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334655 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 334655 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 334655, 1, 65536⟩
    (by decide) selected_cut_41318

theorem unmarked_context_11_83663_1129977 : frontier 10 ⟨1129977, by decide⟩
    (prefixCache 11 83663) (prefixPartial 11 83663) = false := by
  decide +kernel

theorem node_context_11_83663_1129977 : EJMOriginalGlobalDAGData.nodes 10 ⟨1129977, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1129923, by decide⟩,⟨1129976, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83663_1129977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83663 ⟨1129977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83663
    ⟨1129977, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1129923, by decide⟩,⟨1129976, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_83663_1129977 node_context_11_83663_1129977
  intro a
  fin_cases a
  · exact context_12_334652_1108174
  · exact context_12_334653_1129923
  · exact context_12_334654_1129976
  · exact context_12_334655_1120582

theorem unmarked_context_10_20915_1129978 : frontier 11 ⟨1129978, by decide⟩
    (prefixCache 10 20915) (prefixPartial 10 20915) = false := by
  decide +kernel

theorem node_context_10_20915_1129978 : EJMOriginalGlobalDAGData.nodes 11 ⟨1129978, by decide⟩ =
    .split (coordinate 10) (![⟨1129602, by decide⟩,⟨1129751, by decide⟩,⟨1129885, by decide⟩,⟨1129977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20915_1129978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20915 ⟨1129978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20915
    ⟨1129978, by decide⟩ (by decide) (![⟨1129602, by decide⟩,⟨1129751, by decide⟩,⟨1129885, by decide⟩,⟨1129977, by decide⟩]) unmarked_context_10_20915_1129978 node_context_10_20915_1129978
  intro a
  fin_cases a
  · exact context_11_83660_1129602
  · exact context_11_83661_1129751
  · exact context_11_83662_1129885
  · exact context_11_83663_1129977

theorem unmarked_context_9_5228_1129979 : frontier 12 ⟨1129979, by decide⟩
    (prefixCache 9 5228) (prefixPartial 9 5228) = false := by
  decide +kernel

theorem node_context_9_5228_1129979 : EJMOriginalGlobalDAGData.nodes 12 ⟨1129979, by decide⟩ =
    .split (coordinate 9) (![⟨1128293, by decide⟩,⟨1128910, by decide⟩,⟨1129436, by decide⟩,⟨1129978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5228_1129979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5228 ⟨1129979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5228
    ⟨1129979, by decide⟩ (by decide) (![⟨1128293, by decide⟩,⟨1128910, by decide⟩,⟨1129436, by decide⟩,⟨1129978, by decide⟩]) unmarked_context_9_5228_1129979 node_context_9_5228_1129979
  intro a
  fin_cases a
  · exact context_10_20912_1128293
  · exact context_10_20913_1128910
  · exact context_10_20914_1129436
  · exact context_10_20915_1129978

theorem selected_cut_41319 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 334656) = some ⟨12, 1, 0, 1120586, 334656, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334656_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334656 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 334656 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 334656, 1, 65536⟩
    (by decide) selected_cut_41319

theorem selected_cut_41320 : selected 9 ⟨1130001, by decide⟩
    (prefixPartial 12 334657) = some ⟨12, 2, 0, 1130001, 334657, 905, 65536⟩ := by
  decide +kernel

theorem context_12_334657_1130001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334657 ⟨1130001, by decide⟩ :=
  accepted_of_selected 12 334657 ⟨1130001, by decide⟩ ⟨12, 2, 0, 1130001, 334657, 905, 65536⟩
    (by decide) selected_cut_41320

theorem selected_cut_41321 : selected 9 ⟨1130052, by decide⟩
    (prefixPartial 12 334658) = some ⟨12, 2, 0, 1130052, 334658, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_334658_1130052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334658 ⟨1130052, by decide⟩ :=
  accepted_of_selected 12 334658 ⟨1130052, by decide⟩ ⟨12, 2, 0, 1130052, 334658, 2661, 65536⟩
    (by decide) selected_cut_41321

theorem selected_cut_41322 : selected 9 ⟨1130095, by decide⟩
    (prefixPartial 12 334659) = some ⟨12, 2, 0, 1130095, 334659, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_334659_1130095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334659 ⟨1130095, by decide⟩ :=
  accepted_of_selected 12 334659 ⟨1130095, by decide⟩ ⟨12, 2, 0, 1130095, 334659, 2457, 65536⟩
    (by decide) selected_cut_41322

theorem unmarked_context_11_83664_1130096 : frontier 10 ⟨1130096, by decide⟩
    (prefixCache 11 83664) (prefixPartial 11 83664) = false := by
  decide +kernel

theorem node_context_11_83664_1130096 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130096, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨1130001, by decide⟩,⟨1130052, by decide⟩,⟨1130095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83664_1130096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83664 ⟨1130096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83664
    ⟨1130096, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨1130001, by decide⟩,⟨1130052, by decide⟩,⟨1130095, by decide⟩]) unmarked_context_11_83664_1130096 node_context_11_83664_1130096
  intro a
  fin_cases a
  · exact context_12_334656_1120586
  · exact context_12_334657_1130001
  · exact context_12_334658_1130052
  · exact context_12_334659_1130095

theorem selected_cut_41323 : selected 9 ⟨1130129, by decide⟩
    (prefixPartial 12 334660) = some ⟨12, 2, 0, 1130129, 334660, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_334660_1130129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334660 ⟨1130129, by decide⟩ :=
  accepted_of_selected 12 334660 ⟨1130129, by decide⟩ ⟨12, 2, 0, 1130129, 334660, 2073, 65536⟩
    (by decide) selected_cut_41323

theorem selected_cut_41324 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 334661) = some ⟨12, 1, 0, 170504, 334661, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334661_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334661 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 334661 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 334661, 1, 65536⟩
    (by decide) selected_cut_41324

theorem selected_cut_41325 : selected 9 ⟨1130164, by decide⟩
    (prefixPartial 12 334662) = some ⟨12, 2, 0, 1130164, 334662, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_334662_1130164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334662 ⟨1130164, by decide⟩ :=
  accepted_of_selected 12 334662 ⟨1130164, by decide⟩ ⟨12, 2, 0, 1130164, 334662, 2397, 65536⟩
    (by decide) selected_cut_41325

theorem selected_cut_41326 : selected 9 ⟨1130199, by decide⟩
    (prefixPartial 12 334663) = some ⟨12, 2, 0, 1130199, 334663, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_334663_1130199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334663 ⟨1130199, by decide⟩ :=
  accepted_of_selected 12 334663 ⟨1130199, by decide⟩ ⟨12, 2, 0, 1130199, 334663, 2389, 65536⟩
    (by decide) selected_cut_41326

theorem unmarked_context_11_83665_1130200 : frontier 10 ⟨1130200, by decide⟩
    (prefixCache 11 83665) (prefixPartial 11 83665) = false := by
  decide +kernel

theorem node_context_11_83665_1130200 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130200, by decide⟩ =
    .split (coordinate 11) (![⟨1130129, by decide⟩,⟨170504, by decide⟩,⟨1130164, by decide⟩,⟨1130199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83665_1130200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83665 ⟨1130200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83665
    ⟨1130200, by decide⟩ (by decide) (![⟨1130129, by decide⟩,⟨170504, by decide⟩,⟨1130164, by decide⟩,⟨1130199, by decide⟩]) unmarked_context_11_83665_1130200 node_context_11_83665_1130200
  intro a
  fin_cases a
  · exact context_12_334660_1130129
  · exact context_12_334661_170504
  · exact context_12_334662_1130164
  · exact context_12_334663_1130199

theorem selected_cut_41327 : selected 9 ⟨1130229, by decide⟩
    (prefixPartial 12 334664) = some ⟨12, 2, 0, 1130229, 334664, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_334664_1130229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334664 ⟨1130229, by decide⟩ :=
  accepted_of_selected 12 334664 ⟨1130229, by decide⟩ ⟨12, 2, 0, 1130229, 334664, 2001, 65536⟩
    (by decide) selected_cut_41327

theorem selected_cut_41328 : selected 9 ⟨1130257, by decide⟩
    (prefixPartial 12 334665) = some ⟨12, 2, 0, 1130257, 334665, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_334665_1130257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334665 ⟨1130257, by decide⟩ :=
  accepted_of_selected 12 334665 ⟨1130257, by decide⟩ ⟨12, 2, 0, 1130257, 334665, 2025, 65536⟩
    (by decide) selected_cut_41328

theorem selected_cut_41329 : selected 9 ⟨1130285, by decide⟩
    (prefixPartial 12 334666) = some ⟨12, 2, 0, 1130285, 334666, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_334666_1130285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334666 ⟨1130285, by decide⟩ :=
  accepted_of_selected 12 334666 ⟨1130285, by decide⟩ ⟨12, 2, 0, 1130285, 334666, 2053, 65536⟩
    (by decide) selected_cut_41329

theorem selected_cut_41330 : selected 9 ⟨1130319, by decide⟩
    (prefixPartial 12 334667) = some ⟨12, 2, 0, 1130319, 334667, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_334667_1130319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334667 ⟨1130319, by decide⟩ :=
  accepted_of_selected 12 334667 ⟨1130319, by decide⟩ ⟨12, 2, 0, 1130319, 334667, 2273, 65536⟩
    (by decide) selected_cut_41330

theorem unmarked_context_11_83666_1130320 : frontier 10 ⟨1130320, by decide⟩
    (prefixCache 11 83666) (prefixPartial 11 83666) = false := by
  decide +kernel

theorem node_context_11_83666_1130320 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130320, by decide⟩ =
    .split (coordinate 11) (![⟨1130229, by decide⟩,⟨1130257, by decide⟩,⟨1130285, by decide⟩,⟨1130319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83666_1130320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83666 ⟨1130320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83666
    ⟨1130320, by decide⟩ (by decide) (![⟨1130229, by decide⟩,⟨1130257, by decide⟩,⟨1130285, by decide⟩,⟨1130319, by decide⟩]) unmarked_context_11_83666_1130320 node_context_11_83666_1130320
  intro a
  fin_cases a
  · exact context_12_334664_1130229
  · exact context_12_334665_1130257
  · exact context_12_334666_1130285
  · exact context_12_334667_1130319

theorem selected_cut_41331 : selected 9 ⟨1130355, by decide⟩
    (prefixPartial 12 334668) = some ⟨12, 2, 0, 1130355, 334668, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_334668_1130355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334668 ⟨1130355, by decide⟩ :=
  accepted_of_selected 12 334668 ⟨1130355, by decide⟩ ⟨12, 2, 0, 1130355, 334668, 1913, 65536⟩
    (by decide) selected_cut_41331

theorem selected_cut_41332 : selected 9 ⟨1130386, by decide⟩
    (prefixPartial 12 334669) = some ⟨12, 2, 0, 1130386, 334669, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_334669_1130386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334669 ⟨1130386, by decide⟩ :=
  accepted_of_selected 12 334669 ⟨1130386, by decide⟩ ⟨12, 2, 0, 1130386, 334669, 2037, 65536⟩
    (by decide) selected_cut_41332

theorem selected_cut_41333 : selected 9 ⟨1130426, by decide⟩
    (prefixPartial 12 334670) = some ⟨12, 2, 0, 1130426, 334670, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_334670_1130426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334670 ⟨1130426, by decide⟩ :=
  accepted_of_selected 12 334670 ⟨1130426, by decide⟩ ⟨12, 2, 0, 1130426, 334670, 2329, 65536⟩
    (by decide) selected_cut_41333

theorem selected_cut_41334 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 334671) = some ⟨12, 1, 0, 903806, 334671, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334671_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334671 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 334671 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 334671, 1, 65536⟩
    (by decide) selected_cut_41334

theorem unmarked_context_11_83667_1130427 : frontier 10 ⟨1130427, by decide⟩
    (prefixCache 11 83667) (prefixPartial 11 83667) = false := by
  decide +kernel

theorem node_context_11_83667_1130427 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130427, by decide⟩ =
    .split (coordinate 11) (![⟨1130355, by decide⟩,⟨1130386, by decide⟩,⟨1130426, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83667_1130427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83667 ⟨1130427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83667
    ⟨1130427, by decide⟩ (by decide) (![⟨1130355, by decide⟩,⟨1130386, by decide⟩,⟨1130426, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_83667_1130427 node_context_11_83667_1130427
  intro a
  fin_cases a
  · exact context_12_334668_1130355
  · exact context_12_334669_1130386
  · exact context_12_334670_1130426
  · exact context_12_334671_903806

theorem unmarked_context_10_20916_1130428 : frontier 11 ⟨1130428, by decide⟩
    (prefixCache 10 20916) (prefixPartial 10 20916) = false := by
  decide +kernel

theorem node_context_10_20916_1130428 : EJMOriginalGlobalDAGData.nodes 11 ⟨1130428, by decide⟩ =
    .split (coordinate 10) (![⟨1130096, by decide⟩,⟨1130200, by decide⟩,⟨1130320, by decide⟩,⟨1130427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20916_1130428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20916 ⟨1130428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20916
    ⟨1130428, by decide⟩ (by decide) (![⟨1130096, by decide⟩,⟨1130200, by decide⟩,⟨1130320, by decide⟩,⟨1130427, by decide⟩]) unmarked_context_10_20916_1130428 node_context_10_20916_1130428
  intro a
  fin_cases a
  · exact context_11_83664_1130096
  · exact context_11_83665_1130200
  · exact context_11_83666_1130320
  · exact context_11_83667_1130427

theorem selected_cut_41335 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20917) = some ⟨10, 1, 0, 893098, 20917, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20917_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20917 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20917 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20917, 1, 1048576⟩
    (by decide) selected_cut_41335

theorem selected_cut_41336 : selected 9 ⟨1130463, by decide⟩
    (prefixPartial 12 334688) = some ⟨12, 2, 0, 1130463, 334688, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_334688_1130463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334688 ⟨1130463, by decide⟩ :=
  accepted_of_selected 12 334688 ⟨1130463, by decide⟩ ⟨12, 2, 0, 1130463, 334688, 1845, 65536⟩
    (by decide) selected_cut_41336

theorem selected_cut_41337 : selected 9 ⟨1130500, by decide⟩
    (prefixPartial 12 334689) = some ⟨12, 2, 0, 1130500, 334689, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_334689_1130500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334689 ⟨1130500, by decide⟩ :=
  accepted_of_selected 12 334689 ⟨1130500, by decide⟩ ⟨12, 2, 0, 1130500, 334689, 2129, 65536⟩
    (by decide) selected_cut_41337

theorem selected_cut_41338 : selected 9 ⟨1130544, by decide⟩
    (prefixPartial 12 334690) = some ⟨12, 2, 0, 1130544, 334690, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_334690_1130544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334690 ⟨1130544, by decide⟩ :=
  accepted_of_selected 12 334690 ⟨1130544, by decide⟩ ⟨12, 2, 0, 1130544, 334690, 2465, 65536⟩
    (by decide) selected_cut_41338

theorem selected_cut_41339 : selected 9 ⟨1130580, by decide⟩
    (prefixPartial 12 334691) = some ⟨12, 2, 0, 1130580, 334691, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_334691_1130580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334691 ⟨1130580, by decide⟩ :=
  accepted_of_selected 12 334691 ⟨1130580, by decide⟩ ⟨12, 2, 0, 1130580, 334691, 1997, 65536⟩
    (by decide) selected_cut_41339

theorem unmarked_context_11_83672_1130581 : frontier 10 ⟨1130581, by decide⟩
    (prefixCache 11 83672) (prefixPartial 11 83672) = false := by
  decide +kernel

theorem node_context_11_83672_1130581 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130581, by decide⟩ =
    .split (coordinate 11) (![⟨1130463, by decide⟩,⟨1130500, by decide⟩,⟨1130544, by decide⟩,⟨1130580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83672_1130581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83672 ⟨1130581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83672
    ⟨1130581, by decide⟩ (by decide) (![⟨1130463, by decide⟩,⟨1130500, by decide⟩,⟨1130544, by decide⟩,⟨1130580, by decide⟩]) unmarked_context_11_83672_1130581 node_context_11_83672_1130581
  intro a
  fin_cases a
  · exact context_12_334688_1130463
  · exact context_12_334689_1130500
  · exact context_12_334690_1130544
  · exact context_12_334691_1130580

theorem selected_cut_41340 : selected 9 ⟨1130610, by decide⟩
    (prefixPartial 12 334692) = some ⟨12, 2, 0, 1130610, 334692, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_334692_1130610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334692 ⟨1130610, by decide⟩ :=
  accepted_of_selected 12 334692 ⟨1130610, by decide⟩ ⟨12, 2, 0, 1130610, 334692, 1685, 65536⟩
    (by decide) selected_cut_41340

theorem selected_cut_41341 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 334693) = some ⟨12, 1, 0, 642794, 334693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334693_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334693 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 334693 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 334693, 1, 65536⟩
    (by decide) selected_cut_41341

theorem selected_cut_41342 : selected 9 ⟨1130640, by decide⟩
    (prefixPartial 12 334694) = some ⟨12, 2, 0, 1130640, 334694, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_334694_1130640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334694 ⟨1130640, by decide⟩ :=
  accepted_of_selected 12 334694 ⟨1130640, by decide⟩ ⟨12, 2, 0, 1130640, 334694, 1849, 65536⟩
    (by decide) selected_cut_41342

theorem selected_cut_41343 : selected 9 ⟨1130671, by decide⟩
    (prefixPartial 12 334695) = some ⟨12, 2, 0, 1130671, 334695, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_334695_1130671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334695 ⟨1130671, by decide⟩ :=
  accepted_of_selected 12 334695 ⟨1130671, by decide⟩ ⟨12, 2, 0, 1130671, 334695, 1833, 65536⟩
    (by decide) selected_cut_41343

theorem unmarked_context_11_83673_1130672 : frontier 10 ⟨1130672, by decide⟩
    (prefixCache 11 83673) (prefixPartial 11 83673) = false := by
  decide +kernel

theorem node_context_11_83673_1130672 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130672, by decide⟩ =
    .split (coordinate 11) (![⟨1130610, by decide⟩,⟨642794, by decide⟩,⟨1130640, by decide⟩,⟨1130671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83673_1130672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83673 ⟨1130672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83673
    ⟨1130672, by decide⟩ (by decide) (![⟨1130610, by decide⟩,⟨642794, by decide⟩,⟨1130640, by decide⟩,⟨1130671, by decide⟩]) unmarked_context_11_83673_1130672 node_context_11_83673_1130672
  intro a
  fin_cases a
  · exact context_12_334692_1130610
  · exact context_12_334693_642794
  · exact context_12_334694_1130640
  · exact context_12_334695_1130671

theorem selected_cut_41344 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 83674) = some ⟨11, 1, 0, 900587, 83674, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83674_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83674 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 83674 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 83674, 1, 262144⟩
    (by decide) selected_cut_41344

theorem selected_cut_41345 : selected 9 ⟨1130707, by decide⟩
    (prefixPartial 12 334700) = some ⟨12, 2, 0, 1130707, 334700, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_334700_1130707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334700 ⟨1130707, by decide⟩ :=
  accepted_of_selected 12 334700 ⟨1130707, by decide⟩ ⟨12, 2, 0, 1130707, 334700, 1745, 65536⟩
    (by decide) selected_cut_41345

theorem selected_cut_41346 : selected 9 ⟨1130729, by decide⟩
    (prefixPartial 12 334701) = some ⟨12, 2, 0, 1130729, 334701, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_334701_1130729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334701 ⟨1130729, by decide⟩ :=
  accepted_of_selected 12 334701 ⟨1130729, by decide⟩ ⟨12, 2, 0, 1130729, 334701, 1693, 65536⟩
    (by decide) selected_cut_41346

theorem selected_cut_41347 : selected 9 ⟨1130760, by decide⟩
    (prefixPartial 12 334702) = some ⟨12, 2, 0, 1130760, 334702, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_334702_1130760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334702 ⟨1130760, by decide⟩ :=
  accepted_of_selected 12 334702 ⟨1130760, by decide⟩ ⟨12, 2, 0, 1130760, 334702, 2001, 65536⟩
    (by decide) selected_cut_41347

theorem selected_cut_41348 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 334703) = some ⟨12, 1, 0, 903806, 334703, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334703_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334703 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 334703 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 334703, 1, 65536⟩
    (by decide) selected_cut_41348

theorem unmarked_context_11_83675_1130761 : frontier 10 ⟨1130761, by decide⟩
    (prefixCache 11 83675) (prefixPartial 11 83675) = false := by
  decide +kernel

theorem node_context_11_83675_1130761 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130761, by decide⟩ =
    .split (coordinate 11) (![⟨1130707, by decide⟩,⟨1130729, by decide⟩,⟨1130760, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83675_1130761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83675 ⟨1130761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83675
    ⟨1130761, by decide⟩ (by decide) (![⟨1130707, by decide⟩,⟨1130729, by decide⟩,⟨1130760, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_83675_1130761 node_context_11_83675_1130761
  intro a
  fin_cases a
  · exact context_12_334700_1130707
  · exact context_12_334701_1130729
  · exact context_12_334702_1130760
  · exact context_12_334703_903806

theorem unmarked_context_10_20918_1130762 : frontier 11 ⟨1130762, by decide⟩
    (prefixCache 10 20918) (prefixPartial 10 20918) = false := by
  decide +kernel

theorem node_context_10_20918_1130762 : EJMOriginalGlobalDAGData.nodes 11 ⟨1130762, by decide⟩ =
    .split (coordinate 10) (![⟨1130581, by decide⟩,⟨1130672, by decide⟩,⟨900587, by decide⟩,⟨1130761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20918_1130762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20918 ⟨1130762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20918
    ⟨1130762, by decide⟩ (by decide) (![⟨1130581, by decide⟩,⟨1130672, by decide⟩,⟨900587, by decide⟩,⟨1130761, by decide⟩]) unmarked_context_10_20918_1130762 node_context_10_20918_1130762
  intro a
  fin_cases a
  · exact context_11_83672_1130581
  · exact context_11_83673_1130672
  · exact context_11_83674_900587
  · exact context_11_83675_1130761

theorem selected_cut_41349 : selected 9 ⟨1130800, by decide⟩
    (prefixPartial 12 334704) = some ⟨12, 2, 0, 1130800, 334704, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_334704_1130800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334704 ⟨1130800, by decide⟩ :=
  accepted_of_selected 12 334704 ⟨1130800, by decide⟩ ⟨12, 2, 0, 1130800, 334704, 1801, 65536⟩
    (by decide) selected_cut_41349

theorem selected_cut_41350 : selected 9 ⟨1130830, by decide⟩
    (prefixPartial 12 334705) = some ⟨12, 2, 0, 1130830, 334705, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_334705_1130830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334705 ⟨1130830, by decide⟩ :=
  accepted_of_selected 12 334705 ⟨1130830, by decide⟩ ⟨12, 2, 0, 1130830, 334705, 2009, 65536⟩
    (by decide) selected_cut_41350

theorem selected_cut_41351 : selected 9 ⟨1130875, by decide⟩
    (prefixPartial 12 334706) = some ⟨12, 2, 0, 1130875, 334706, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_334706_1130875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334706 ⟨1130875, by decide⟩ :=
  accepted_of_selected 12 334706 ⟨1130875, by decide⟩ ⟨12, 2, 0, 1130875, 334706, 2189, 65536⟩
    (by decide) selected_cut_41351

theorem selected_cut_41352 : selected 9 ⟨1130914, by decide⟩
    (prefixPartial 12 334707) = some ⟨12, 2, 0, 1130914, 334707, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_334707_1130914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334707 ⟨1130914, by decide⟩ :=
  accepted_of_selected 12 334707 ⟨1130914, by decide⟩ ⟨12, 2, 0, 1130914, 334707, 1969, 65536⟩
    (by decide) selected_cut_41352

theorem unmarked_context_11_83676_1130915 : frontier 10 ⟨1130915, by decide⟩
    (prefixCache 11 83676) (prefixPartial 11 83676) = false := by
  decide +kernel

theorem node_context_11_83676_1130915 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130915, by decide⟩ =
    .split (coordinate 11) (![⟨1130800, by decide⟩,⟨1130830, by decide⟩,⟨1130875, by decide⟩,⟨1130914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83676_1130915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83676 ⟨1130915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83676
    ⟨1130915, by decide⟩ (by decide) (![⟨1130800, by decide⟩,⟨1130830, by decide⟩,⟨1130875, by decide⟩,⟨1130914, by decide⟩]) unmarked_context_11_83676_1130915 node_context_11_83676_1130915
  intro a
  fin_cases a
  · exact context_12_334704_1130800
  · exact context_12_334705_1130830
  · exact context_12_334706_1130875
  · exact context_12_334707_1130914

theorem selected_cut_41353 : selected 9 ⟨1130943, by decide⟩
    (prefixPartial 12 334708) = some ⟨12, 2, 0, 1130943, 334708, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_334708_1130943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334708 ⟨1130943, by decide⟩ :=
  accepted_of_selected 12 334708 ⟨1130943, by decide⟩ ⟨12, 2, 0, 1130943, 334708, 1689, 65536⟩
    (by decide) selected_cut_41353

theorem selected_cut_41354 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 334709) = some ⟨12, 1, 0, 642794, 334709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334709_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334709 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 334709 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 334709, 1, 65536⟩
    (by decide) selected_cut_41354

theorem selected_cut_41355 : selected 9 ⟨1130970, by decide⟩
    (prefixPartial 12 334710) = some ⟨12, 2, 0, 1130970, 334710, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_334710_1130970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334710 ⟨1130970, by decide⟩ :=
  accepted_of_selected 12 334710 ⟨1130970, by decide⟩ ⟨12, 2, 0, 1130970, 334710, 1833, 65536⟩
    (by decide) selected_cut_41355

theorem selected_cut_41356 : selected 9 ⟨1130997, by decide⟩
    (prefixPartial 12 334711) = some ⟨12, 2, 0, 1130997, 334711, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_334711_1130997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334711 ⟨1130997, by decide⟩ :=
  accepted_of_selected 12 334711 ⟨1130997, by decide⟩ ⟨12, 2, 0, 1130997, 334711, 1841, 65536⟩
    (by decide) selected_cut_41356

theorem unmarked_context_11_83677_1130998 : frontier 10 ⟨1130998, by decide⟩
    (prefixCache 11 83677) (prefixPartial 11 83677) = false := by
  decide +kernel

theorem node_context_11_83677_1130998 : EJMOriginalGlobalDAGData.nodes 10 ⟨1130998, by decide⟩ =
    .split (coordinate 11) (![⟨1130943, by decide⟩,⟨642794, by decide⟩,⟨1130970, by decide⟩,⟨1130997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83677_1130998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83677 ⟨1130998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83677
    ⟨1130998, by decide⟩ (by decide) (![⟨1130943, by decide⟩,⟨642794, by decide⟩,⟨1130970, by decide⟩,⟨1130997, by decide⟩]) unmarked_context_11_83677_1130998 node_context_11_83677_1130998
  intro a
  fin_cases a
  · exact context_12_334708_1130943
  · exact context_12_334709_642794
  · exact context_12_334710_1130970
  · exact context_12_334711_1130997

theorem selected_cut_41357 : selected 9 ⟨1131029, by decide⟩
    (prefixPartial 12 334712) = some ⟨12, 2, 0, 1131029, 334712, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_334712_1131029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334712 ⟨1131029, by decide⟩ :=
  accepted_of_selected 12 334712 ⟨1131029, by decide⟩ ⟨12, 2, 0, 1131029, 334712, 1701, 65536⟩
    (by decide) selected_cut_41357

theorem selected_cut_41358 : selected 9 ⟨1131060, by decide⟩
    (prefixPartial 12 334713) = some ⟨12, 2, 0, 1131060, 334713, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_334713_1131060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334713 ⟨1131060, by decide⟩ :=
  accepted_of_selected 12 334713 ⟨1131060, by decide⟩ ⟨12, 2, 0, 1131060, 334713, 1689, 65536⟩
    (by decide) selected_cut_41358

theorem selected_cut_41359 : selected 9 ⟨1131081, by decide⟩
    (prefixPartial 12 334714) = some ⟨12, 2, 0, 1131081, 334714, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_334714_1131081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334714 ⟨1131081, by decide⟩ :=
  accepted_of_selected 12 334714 ⟨1131081, by decide⟩ ⟨12, 2, 0, 1131081, 334714, 1665, 65536⟩
    (by decide) selected_cut_41359

theorem selected_cut_41360 : selected 9 ⟨1131114, by decide⟩
    (prefixPartial 12 334715) = some ⟨12, 2, 0, 1131114, 334715, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_334715_1131114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334715 ⟨1131114, by decide⟩ :=
  accepted_of_selected 12 334715 ⟨1131114, by decide⟩ ⟨12, 2, 0, 1131114, 334715, 1805, 65536⟩
    (by decide) selected_cut_41360

theorem unmarked_context_11_83678_1131115 : frontier 10 ⟨1131115, by decide⟩
    (prefixCache 11 83678) (prefixPartial 11 83678) = false := by
  decide +kernel

theorem node_context_11_83678_1131115 : EJMOriginalGlobalDAGData.nodes 10 ⟨1131115, by decide⟩ =
    .split (coordinate 11) (![⟨1131029, by decide⟩,⟨1131060, by decide⟩,⟨1131081, by decide⟩,⟨1131114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83678_1131115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83678 ⟨1131115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83678
    ⟨1131115, by decide⟩ (by decide) (![⟨1131029, by decide⟩,⟨1131060, by decide⟩,⟨1131081, by decide⟩,⟨1131114, by decide⟩]) unmarked_context_11_83678_1131115 node_context_11_83678_1131115
  intro a
  fin_cases a
  · exact context_12_334712_1131029
  · exact context_12_334713_1131060
  · exact context_12_334714_1131081
  · exact context_12_334715_1131114

theorem selected_cut_41361 : selected 9 ⟨1131140, by decide⟩
    (prefixPartial 12 334716) = some ⟨12, 2, 0, 1131140, 334716, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_334716_1131140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334716 ⟨1131140, by decide⟩ :=
  accepted_of_selected 12 334716 ⟨1131140, by decide⟩ ⟨12, 2, 0, 1131140, 334716, 1493, 65536⟩
    (by decide) selected_cut_41361

theorem selected_cut_41362 : selected 9 ⟨1131160, by decide⟩
    (prefixPartial 12 334717) = some ⟨12, 2, 0, 1131160, 334717, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_334717_1131160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334717 ⟨1131160, by decide⟩ :=
  accepted_of_selected 12 334717 ⟨1131160, by decide⟩ ⟨12, 2, 0, 1131160, 334717, 1509, 65536⟩
    (by decide) selected_cut_41362

theorem selected_cut_41363 : selected 9 ⟨1131187, by decide⟩
    (prefixPartial 12 334718) = some ⟨12, 2, 0, 1131187, 334718, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_334718_1131187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334718 ⟨1131187, by decide⟩ :=
  accepted_of_selected 12 334718 ⟨1131187, by decide⟩ ⟨12, 2, 0, 1131187, 334718, 1729, 65536⟩
    (by decide) selected_cut_41363

theorem selected_cut_41364 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 334719) = some ⟨12, 1, 0, 1120582, 334719, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334719_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334719 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 334719 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 334719, 1, 65536⟩
    (by decide) selected_cut_41364

theorem unmarked_context_11_83679_1131188 : frontier 10 ⟨1131188, by decide⟩
    (prefixCache 11 83679) (prefixPartial 11 83679) = false := by
  decide +kernel

theorem node_context_11_83679_1131188 : EJMOriginalGlobalDAGData.nodes 10 ⟨1131188, by decide⟩ =
    .split (coordinate 11) (![⟨1131140, by decide⟩,⟨1131160, by decide⟩,⟨1131187, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83679_1131188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83679 ⟨1131188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83679
    ⟨1131188, by decide⟩ (by decide) (![⟨1131140, by decide⟩,⟨1131160, by decide⟩,⟨1131187, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_83679_1131188 node_context_11_83679_1131188
  intro a
  fin_cases a
  · exact context_12_334716_1131140
  · exact context_12_334717_1131160
  · exact context_12_334718_1131187
  · exact context_12_334719_1120582

theorem unmarked_context_10_20919_1131189 : frontier 11 ⟨1131189, by decide⟩
    (prefixCache 10 20919) (prefixPartial 10 20919) = false := by
  decide +kernel

theorem node_context_10_20919_1131189 : EJMOriginalGlobalDAGData.nodes 11 ⟨1131189, by decide⟩ =
    .split (coordinate 10) (![⟨1130915, by decide⟩,⟨1130998, by decide⟩,⟨1131115, by decide⟩,⟨1131188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20919_1131189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20919 ⟨1131189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20919
    ⟨1131189, by decide⟩ (by decide) (![⟨1130915, by decide⟩,⟨1130998, by decide⟩,⟨1131115, by decide⟩,⟨1131188, by decide⟩]) unmarked_context_10_20919_1131189 node_context_10_20919_1131189
  intro a
  fin_cases a
  · exact context_11_83676_1130915
  · exact context_11_83677_1130998
  · exact context_11_83678_1131115
  · exact context_11_83679_1131188

theorem unmarked_context_9_5229_1131190 : frontier 12 ⟨1131190, by decide⟩
    (prefixCache 9 5229) (prefixPartial 9 5229) = false := by
  decide +kernel

theorem node_context_9_5229_1131190 : EJMOriginalGlobalDAGData.nodes 12 ⟨1131190, by decide⟩ =
    .split (coordinate 9) (![⟨1130428, by decide⟩,⟨893098, by decide⟩,⟨1130762, by decide⟩,⟨1131189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5229_1131190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5229 ⟨1131190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5229
    ⟨1131190, by decide⟩ (by decide) (![⟨1130428, by decide⟩,⟨893098, by decide⟩,⟨1130762, by decide⟩,⟨1131189, by decide⟩]) unmarked_context_9_5229_1131190 node_context_9_5229_1131190
  intro a
  fin_cases a
  · exact context_10_20916_1130428
  · exact context_10_20917_893098
  · exact context_10_20918_1130762
  · exact context_10_20919_1131189

theorem selected_cut_41365 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 334720) = some ⟨12, 1, 0, 1120586, 334720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334720_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334720 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 334720 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 334720, 1, 65536⟩
    (by decide) selected_cut_41365

theorem selected_cut_41366 : selected 9 ⟨1131230, by decide⟩
    (prefixPartial 12 334721) = some ⟨12, 2, 0, 1131230, 334721, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_334721_1131230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334721 ⟨1131230, by decide⟩ :=
  accepted_of_selected 12 334721 ⟨1131230, by decide⟩ ⟨12, 2, 0, 1131230, 334721, 1801, 65536⟩
    (by decide) selected_cut_41366

theorem selected_cut_41367 : selected 9 ⟨1131266, by decide⟩
    (prefixPartial 12 334722) = some ⟨12, 2, 0, 1131266, 334722, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_334722_1131266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334722 ⟨1131266, by decide⟩ :=
  accepted_of_selected 12 334722 ⟨1131266, by decide⟩ ⟨12, 2, 0, 1131266, 334722, 1813, 65536⟩
    (by decide) selected_cut_41367

theorem selected_cut_41368 : selected 9 ⟨1131294, by decide⟩
    (prefixPartial 12 334723) = some ⟨12, 2, 0, 1131294, 334723, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_334723_1131294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334723 ⟨1131294, by decide⟩ :=
  accepted_of_selected 12 334723 ⟨1131294, by decide⟩ ⟨12, 2, 0, 1131294, 334723, 1637, 65536⟩
    (by decide) selected_cut_41368

theorem unmarked_context_11_83680_1131295 : frontier 10 ⟨1131295, by decide⟩
    (prefixCache 11 83680) (prefixPartial 11 83680) = false := by
  decide +kernel

theorem node_context_11_83680_1131295 : EJMOriginalGlobalDAGData.nodes 10 ⟨1131295, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨1131230, by decide⟩,⟨1131266, by decide⟩,⟨1131294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83680_1131295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83680 ⟨1131295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83680
    ⟨1131295, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨1131230, by decide⟩,⟨1131266, by decide⟩,⟨1131294, by decide⟩]) unmarked_context_11_83680_1131295 node_context_11_83680_1131295
  intro a
  fin_cases a
  · exact context_12_334720_1120586
  · exact context_12_334721_1131230
  · exact context_12_334722_1131266
  · exact context_12_334723_1131294

theorem selected_cut_41369 : selected 9 ⟨1131319, by decide⟩
    (prefixPartial 12 334724) = some ⟨12, 2, 0, 1131319, 334724, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_334724_1131319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334724 ⟨1131319, by decide⟩ :=
  accepted_of_selected 12 334724 ⟨1131319, by decide⟩ ⟨12, 2, 0, 1131319, 334724, 1261, 65536⟩
    (by decide) selected_cut_41369

theorem selected_cut_41370 : selected 9 ⟨1131353, by decide⟩
    (prefixPartial 12 334725) = some ⟨12, 2, 0, 1131353, 334725, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_334725_1131353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334725 ⟨1131353, by decide⟩ :=
  accepted_of_selected 12 334725 ⟨1131353, by decide⟩ ⟨12, 2, 0, 1131353, 334725, 1693, 65536⟩
    (by decide) selected_cut_41370

theorem selected_cut_41371 : selected 9 ⟨1131376, by decide⟩
    (prefixPartial 12 334726) = some ⟨12, 2, 0, 1131376, 334726, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_334726_1131376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334726 ⟨1131376, by decide⟩ :=
  accepted_of_selected 12 334726 ⟨1131376, by decide⟩ ⟨12, 2, 0, 1131376, 334726, 1397, 65536⟩
    (by decide) selected_cut_41371

theorem selected_cut_41372 : selected 9 ⟨1131397, by decide⟩
    (prefixPartial 12 334727) = some ⟨12, 2, 0, 1131397, 334727, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_334727_1131397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334727 ⟨1131397, by decide⟩ :=
  accepted_of_selected 12 334727 ⟨1131397, by decide⟩ ⟨12, 2, 0, 1131397, 334727, 1465, 65536⟩
    (by decide) selected_cut_41372

theorem unmarked_context_11_83681_1131398 : frontier 10 ⟨1131398, by decide⟩
    (prefixCache 11 83681) (prefixPartial 11 83681) = false := by
  decide +kernel

theorem node_context_11_83681_1131398 : EJMOriginalGlobalDAGData.nodes 10 ⟨1131398, by decide⟩ =
    .split (coordinate 11) (![⟨1131319, by decide⟩,⟨1131353, by decide⟩,⟨1131376, by decide⟩,⟨1131397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83681_1131398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83681 ⟨1131398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83681
    ⟨1131398, by decide⟩ (by decide) (![⟨1131319, by decide⟩,⟨1131353, by decide⟩,⟨1131376, by decide⟩,⟨1131397, by decide⟩]) unmarked_context_11_83681_1131398 node_context_11_83681_1131398
  intro a
  fin_cases a
  · exact context_12_334724_1131319
  · exact context_12_334725_1131353
  · exact context_12_334726_1131376
  · exact context_12_334727_1131397

theorem selected_cut_41373 : selected 10 ⟨1131452, by decide⟩
    (prefixPartial 11 83682) = some ⟨11, 2, 0, 1131452, 83682, 3645, 262144⟩ := by
  decide +kernel

theorem context_11_83682_1131452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83682 ⟨1131452, by decide⟩ :=
  accepted_of_selected 11 83682 ⟨1131452, by decide⟩ ⟨11, 2, 0, 1131452, 83682, 3645, 262144⟩
    (by decide) selected_cut_41373

theorem selected_cut_41374 : selected 10 ⟨1131509, by decide⟩
    (prefixPartial 11 83683) = some ⟨11, 2, 0, 1131509, 83683, 3561, 262144⟩ := by
  decide +kernel

theorem context_11_83683_1131509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83683 ⟨1131509, by decide⟩ :=
  accepted_of_selected 11 83683 ⟨1131509, by decide⟩ ⟨11, 2, 0, 1131509, 83683, 3561, 262144⟩
    (by decide) selected_cut_41374

theorem unmarked_context_10_20920_1131510 : frontier 11 ⟨1131510, by decide⟩
    (prefixCache 10 20920) (prefixPartial 10 20920) = false := by
  decide +kernel

theorem node_context_10_20920_1131510 : EJMOriginalGlobalDAGData.nodes 11 ⟨1131510, by decide⟩ =
    .split (coordinate 10) (![⟨1131295, by decide⟩,⟨1131398, by decide⟩,⟨1131452, by decide⟩,⟨1131509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20920_1131510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20920 ⟨1131510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20920
    ⟨1131510, by decide⟩ (by decide) (![⟨1131295, by decide⟩,⟨1131398, by decide⟩,⟨1131452, by decide⟩,⟨1131509, by decide⟩]) unmarked_context_10_20920_1131510 node_context_10_20920_1131510
  intro a
  fin_cases a
  · exact context_11_83680_1131295
  · exact context_11_83681_1131398
  · exact context_11_83682_1131452
  · exact context_11_83683_1131509

theorem selected_cut_41375 : selected 9 ⟨1131528, by decide⟩
    (prefixPartial 12 334736) = some ⟨12, 2, 0, 1131528, 334736, 985, 65536⟩ := by
  decide +kernel

theorem context_12_334736_1131528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334736 ⟨1131528, by decide⟩ :=
  accepted_of_selected 12 334736 ⟨1131528, by decide⟩ ⟨12, 2, 0, 1131528, 334736, 985, 65536⟩
    (by decide) selected_cut_41375

theorem selected_cut_41376 : selected 9 ⟨1131546, by decide⟩
    (prefixPartial 12 334737) = some ⟨12, 2, 0, 1131546, 334737, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_334737_1131546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334737 ⟨1131546, by decide⟩ :=
  accepted_of_selected 12 334737 ⟨1131546, by decide⟩ ⟨12, 2, 0, 1131546, 334737, 1205, 65536⟩
    (by decide) selected_cut_41376

theorem selected_cut_41377 : selected 9 ⟨1131572, by decide⟩
    (prefixPartial 12 334738) = some ⟨12, 2, 0, 1131572, 334738, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_334738_1131572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334738 ⟨1131572, by decide⟩ :=
  accepted_of_selected 12 334738 ⟨1131572, by decide⟩ ⟨12, 2, 0, 1131572, 334738, 1241, 65536⟩
    (by decide) selected_cut_41377

theorem selected_cut_41378 : selected 9 ⟨1131593, by decide⟩
    (prefixPartial 12 334739) = some ⟨12, 2, 0, 1131593, 334739, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_334739_1131593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334739 ⟨1131593, by decide⟩ :=
  accepted_of_selected 12 334739 ⟨1131593, by decide⟩ ⟨12, 2, 0, 1131593, 334739, 1009, 65536⟩
    (by decide) selected_cut_41378

theorem unmarked_context_11_83684_1131594 : frontier 10 ⟨1131594, by decide⟩
    (prefixCache 11 83684) (prefixPartial 11 83684) = false := by
  decide +kernel

theorem node_context_11_83684_1131594 : EJMOriginalGlobalDAGData.nodes 10 ⟨1131594, by decide⟩ =
    .split (coordinate 11) (![⟨1131528, by decide⟩,⟨1131546, by decide⟩,⟨1131572, by decide⟩,⟨1131593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83684_1131594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83684 ⟨1131594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83684
    ⟨1131594, by decide⟩ (by decide) (![⟨1131528, by decide⟩,⟨1131546, by decide⟩,⟨1131572, by decide⟩,⟨1131593, by decide⟩]) unmarked_context_11_83684_1131594 node_context_11_83684_1131594
  intro a
  fin_cases a
  · exact context_12_334736_1131528
  · exact context_12_334737_1131546
  · exact context_12_334738_1131572
  · exact context_12_334739_1131593

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
