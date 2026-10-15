/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover439
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_21099_1154620 : frontier 11 ⟨1154620, by decide⟩
    (prefixCache 10 21099) (prefixPartial 10 21099) = false := by
  decide +kernel

theorem node_context_10_21099_1154620 : EJMOriginalGlobalDAGData.nodes 11 ⟨1154620, by decide⟩ =
    .split (coordinate 10) (![⟨1154545, by decide⟩,⟨1154583, by decide⟩,⟨1154604, by decide⟩,⟨1154619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21099_1154620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21099 ⟨1154620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21099
    ⟨1154620, by decide⟩ (by decide) (![⟨1154545, by decide⟩,⟨1154583, by decide⟩,⟨1154604, by decide⟩,⟨1154619, by decide⟩]) unmarked_context_10_21099_1154620 node_context_10_21099_1154620
  intro a
  fin_cases a
  · exact context_11_84396_1154545
  · exact context_11_84397_1154583
  · exact context_11_84398_1154604
  · exact context_11_84399_1154619

theorem unmarked_context_9_5274_1154621 : frontier 12 ⟨1154621, by decide⟩
    (prefixCache 9 5274) (prefixPartial 9 5274) = false := by
  decide +kernel

theorem node_context_9_5274_1154621 : EJMOriginalGlobalDAGData.nodes 12 ⟨1154621, by decide⟩ =
    .split (coordinate 9) (![⟨1154322, by decide⟩,⟨1154436, by decide⟩,⟨1154509, by decide⟩,⟨1154620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5274_1154621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5274 ⟨1154621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5274
    ⟨1154621, by decide⟩ (by decide) (![⟨1154322, by decide⟩,⟨1154436, by decide⟩,⟨1154509, by decide⟩,⟨1154620, by decide⟩]) unmarked_context_9_5274_1154621 node_context_9_5274_1154621
  intro a
  fin_cases a
  · exact context_10_21096_1154322
  · exact context_10_21097_1154436
  · exact context_10_21098_1154509
  · exact context_10_21099_1154620

theorem selected_cut_42244 : selected 10 ⟨1154639, by decide⟩
    (prefixPartial 11 84400) = some ⟨11, 2, 0, 1154639, 84400, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_84400_1154639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84400 ⟨1154639, by decide⟩ :=
  accepted_of_selected 11 84400 ⟨1154639, by decide⟩ ⟨11, 2, 0, 1154639, 84400, 1541, 262144⟩
    (by decide) selected_cut_42244

theorem selected_cut_42245 : selected 10 ⟨1154660, by decide⟩
    (prefixPartial 11 84401) = some ⟨11, 2, 0, 1154660, 84401, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_84401_1154660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84401 ⟨1154660, by decide⟩ :=
  accepted_of_selected 11 84401 ⟨1154660, by decide⟩ ⟨11, 2, 0, 1154660, 84401, 1749, 262144⟩
    (by decide) selected_cut_42245

theorem selected_cut_42246 : selected 10 ⟨1154674, by decide⟩
    (prefixPartial 11 84402) = some ⟨11, 2, 0, 1154674, 84402, 1205, 262144⟩ := by
  decide +kernel

theorem context_11_84402_1154674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84402 ⟨1154674, by decide⟩ :=
  accepted_of_selected 11 84402 ⟨1154674, by decide⟩ ⟨11, 2, 0, 1154674, 84402, 1205, 262144⟩
    (by decide) selected_cut_42246

theorem selected_cut_42247 : selected 10 ⟨1154691, by decide⟩
    (prefixPartial 11 84403) = some ⟨11, 2, 0, 1154691, 84403, 1249, 262144⟩ := by
  decide +kernel

theorem context_11_84403_1154691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84403 ⟨1154691, by decide⟩ :=
  accepted_of_selected 11 84403 ⟨1154691, by decide⟩ ⟨11, 2, 0, 1154691, 84403, 1249, 262144⟩
    (by decide) selected_cut_42247

theorem unmarked_context_10_21100_1154692 : frontier 11 ⟨1154692, by decide⟩
    (prefixCache 10 21100) (prefixPartial 10 21100) = false := by
  decide +kernel

theorem node_context_10_21100_1154692 : EJMOriginalGlobalDAGData.nodes 11 ⟨1154692, by decide⟩ =
    .split (coordinate 10) (![⟨1154639, by decide⟩,⟨1154660, by decide⟩,⟨1154674, by decide⟩,⟨1154691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21100_1154692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21100 ⟨1154692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21100
    ⟨1154692, by decide⟩ (by decide) (![⟨1154639, by decide⟩,⟨1154660, by decide⟩,⟨1154674, by decide⟩,⟨1154691, by decide⟩]) unmarked_context_10_21100_1154692 node_context_10_21100_1154692
  intro a
  fin_cases a
  · exact context_11_84400_1154639
  · exact context_11_84401_1154660
  · exact context_11_84402_1154674
  · exact context_11_84403_1154691

theorem selected_cut_42248 : selected 11 ⟨1154713, by decide⟩
    (prefixPartial 10 21101) = some ⟨10, 2, 0, 1154713, 21101, 2809, 1048576⟩ := by
  decide +kernel

theorem context_10_21101_1154713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21101 ⟨1154713, by decide⟩ :=
  accepted_of_selected 10 21101 ⟨1154713, by decide⟩ ⟨10, 2, 0, 1154713, 21101, 2809, 1048576⟩
    (by decide) selected_cut_42248

theorem selected_cut_42249 : selected 11 ⟨1154747, by decide⟩
    (prefixPartial 10 21102) = some ⟨10, 2, 0, 1154747, 21102, 2353, 1048576⟩ := by
  decide +kernel

theorem context_10_21102_1154747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21102 ⟨1154747, by decide⟩ :=
  accepted_of_selected 10 21102 ⟨1154747, by decide⟩ ⟨10, 2, 0, 1154747, 21102, 2353, 1048576⟩
    (by decide) selected_cut_42249

theorem selected_cut_42250 : selected 11 ⟨1118286, by decide⟩
    (prefixPartial 10 21103) = some ⟨10, 2, 0, 1118286, 21103, 469, 1048576⟩ := by
  decide +kernel

theorem context_10_21103_1118286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21103 ⟨1118286, by decide⟩ :=
  accepted_of_selected 10 21103 ⟨1118286, by decide⟩ ⟨10, 2, 0, 1118286, 21103, 469, 1048576⟩
    (by decide) selected_cut_42250

theorem unmarked_context_9_5275_1154748 : frontier 12 ⟨1154748, by decide⟩
    (prefixCache 9 5275) (prefixPartial 9 5275) = false := by
  decide +kernel

theorem node_context_9_5275_1154748 : EJMOriginalGlobalDAGData.nodes 12 ⟨1154748, by decide⟩ =
    .split (coordinate 9) (![⟨1154692, by decide⟩,⟨1154713, by decide⟩,⟨1154747, by decide⟩,⟨1118286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5275_1154748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5275 ⟨1154748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5275
    ⟨1154748, by decide⟩ (by decide) (![⟨1154692, by decide⟩,⟨1154713, by decide⟩,⟨1154747, by decide⟩,⟨1118286, by decide⟩]) unmarked_context_9_5275_1154748 node_context_9_5275_1154748
  intro a
  fin_cases a
  · exact context_10_21100_1154692
  · exact context_10_21101_1154713
  · exact context_10_21102_1154747
  · exact context_10_21103_1118286

theorem unmarked_context_8_1318_1154749 : frontier 13 ⟨1154749, by decide⟩
    (prefixCache 8 1318) (prefixPartial 8 1318) = false := by
  decide +kernel

theorem node_context_8_1318_1154749 : EJMOriginalGlobalDAGData.nodes 13 ⟨1154749, by decide⟩ =
    .split (coordinate 8) (![⟨1153061, by decide⟩,⟨1154100, by decide⟩,⟨1154621, by decide⟩,⟨1154748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1318_1154749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1318 ⟨1154749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1318
    ⟨1154749, by decide⟩ (by decide) (![⟨1153061, by decide⟩,⟨1154100, by decide⟩,⟨1154621, by decide⟩,⟨1154748, by decide⟩]) unmarked_context_8_1318_1154749 node_context_8_1318_1154749
  intro a
  fin_cases a
  · exact context_9_5272_1153061
  · exact context_9_5273_1154100
  · exact context_9_5274_1154621
  · exact context_9_5275_1154748

theorem selected_cut_42251 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84416) = some ⟨11, 1, 0, 434745, 84416, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84416_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84416 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84416 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84416, 1, 262144⟩
    (by decide) selected_cut_42251

theorem selected_cut_42252 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337668) = some ⟨12, 1, 0, 448748, 337668, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337668_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337668 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337668 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337668, 1, 65536⟩
    (by decide) selected_cut_42252

theorem selected_cut_42253 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 337669) = some ⟨12, 1, 0, 34034, 337669, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337669_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337669 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 337669 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 337669, 1, 65536⟩
    (by decide) selected_cut_42253

theorem selected_cut_42254 : selected 9 ⟨1154806, by decide⟩
    (prefixPartial 12 337670) = some ⟨12, 2, 0, 1154806, 337670, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_337670_1154806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337670 ⟨1154806, by decide⟩ :=
  accepted_of_selected 12 337670 ⟨1154806, by decide⟩ ⟨12, 2, 0, 1154806, 337670, 2817, 65536⟩
    (by decide) selected_cut_42254

theorem selected_cut_42255 : selected 9 ⟨1154855, by decide⟩
    (prefixPartial 12 337671) = some ⟨12, 2, 0, 1154855, 337671, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_337671_1154855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337671 ⟨1154855, by decide⟩ :=
  accepted_of_selected 12 337671 ⟨1154855, by decide⟩ ⟨12, 2, 0, 1154855, 337671, 2965, 65536⟩
    (by decide) selected_cut_42255

theorem unmarked_context_11_84417_1154856 : frontier 10 ⟨1154856, by decide⟩
    (prefixCache 11 84417) (prefixPartial 11 84417) = false := by
  decide +kernel

theorem node_context_11_84417_1154856 : EJMOriginalGlobalDAGData.nodes 10 ⟨1154856, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1154806, by decide⟩,⟨1154855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84417_1154856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84417 ⟨1154856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84417
    ⟨1154856, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1154806, by decide⟩,⟨1154855, by decide⟩]) unmarked_context_11_84417_1154856 node_context_11_84417_1154856
  intro a
  fin_cases a
  · exact context_12_337668_448748
  · exact context_12_337669_34034
  · exact context_12_337670_1154806
  · exact context_12_337671_1154855

theorem selected_cut_42256 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337672) = some ⟨12, 1, 0, 448748, 337672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337672_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337672 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337672 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337672, 1, 65536⟩
    (by decide) selected_cut_42256

theorem selected_cut_42257 : selected 9 ⟨1154911, by decide⟩
    (prefixPartial 12 337673) = some ⟨12, 2, 0, 1154911, 337673, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_337673_1154911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337673 ⟨1154911, by decide⟩ :=
  accepted_of_selected 12 337673 ⟨1154911, by decide⟩ ⟨12, 2, 0, 1154911, 337673, 2897, 65536⟩
    (by decide) selected_cut_42257

theorem selected_cut_42258 : selected 9 ⟨1154961, by decide⟩
    (prefixPartial 12 337674) = some ⟨12, 2, 0, 1154961, 337674, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_337674_1154961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337674 ⟨1154961, by decide⟩ :=
  accepted_of_selected 12 337674 ⟨1154961, by decide⟩ ⟨12, 2, 0, 1154961, 337674, 2985, 65536⟩
    (by decide) selected_cut_42258

theorem selected_cut_42259 : selected 9 ⟨1155020, by decide⟩
    (prefixPartial 12 337675) = some ⟨12, 2, 0, 1155020, 337675, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_337675_1155020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337675 ⟨1155020, by decide⟩ :=
  accepted_of_selected 12 337675 ⟨1155020, by decide⟩ ⟨12, 2, 0, 1155020, 337675, 3317, 65536⟩
    (by decide) selected_cut_42259

theorem unmarked_context_11_84418_1155021 : frontier 10 ⟨1155021, by decide⟩
    (prefixCache 11 84418) (prefixPartial 11 84418) = false := by
  decide +kernel

theorem node_context_11_84418_1155021 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155021, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1154911, by decide⟩,⟨1154961, by decide⟩,⟨1155020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84418_1155021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84418 ⟨1155021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84418
    ⟨1155021, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1154911, by decide⟩,⟨1154961, by decide⟩,⟨1155020, by decide⟩]) unmarked_context_11_84418_1155021 node_context_11_84418_1155021
  intro a
  fin_cases a
  · exact context_12_337672_448748
  · exact context_12_337673_1154911
  · exact context_12_337674_1154961
  · exact context_12_337675_1155020

theorem selected_cut_42260 : selected 10 ⟨1155069, by decide⟩
    (prefixPartial 11 84419) = some ⟨11, 2, 0, 1155069, 84419, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_84419_1155069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84419 ⟨1155069, by decide⟩ :=
  accepted_of_selected 11 84419 ⟨1155069, by decide⟩ ⟨11, 2, 0, 1155069, 84419, 2961, 262144⟩
    (by decide) selected_cut_42260

theorem unmarked_context_10_21104_1155070 : frontier 11 ⟨1155070, by decide⟩
    (prefixCache 10 21104) (prefixPartial 10 21104) = false := by
  decide +kernel

theorem node_context_10_21104_1155070 : EJMOriginalGlobalDAGData.nodes 11 ⟨1155070, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1154856, by decide⟩,⟨1155021, by decide⟩,⟨1155069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21104_1155070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21104 ⟨1155070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21104
    ⟨1155070, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1154856, by decide⟩,⟨1155021, by decide⟩,⟨1155069, by decide⟩]) unmarked_context_10_21104_1155070 node_context_10_21104_1155070
  intro a
  fin_cases a
  · exact context_11_84416_434745
  · exact context_11_84417_1154856
  · exact context_11_84418_1155021
  · exact context_11_84419_1155069

theorem selected_cut_42261 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337680) = some ⟨12, 1, 0, 1108174, 337680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337680_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337680 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337680 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337680, 1, 65536⟩
    (by decide) selected_cut_42261

theorem selected_cut_42262 : selected 9 ⟨1155106, by decide⟩
    (prefixPartial 12 337681) = some ⟨12, 2, 0, 1155106, 337681, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_337681_1155106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337681 ⟨1155106, by decide⟩ :=
  accepted_of_selected 12 337681 ⟨1155106, by decide⟩ ⟨12, 2, 0, 1155106, 337681, 2525, 65536⟩
    (by decide) selected_cut_42262

theorem selected_cut_42263 : selected 9 ⟨1155164, by decide⟩
    (prefixPartial 12 337682) = some ⟨12, 2, 0, 1155164, 337682, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_337682_1155164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337682 ⟨1155164, by decide⟩ :=
  accepted_of_selected 12 337682 ⟨1155164, by decide⟩ ⟨12, 2, 0, 1155164, 337682, 3237, 65536⟩
    (by decide) selected_cut_42263

theorem selected_cut_42264 : selected 9 ⟨1155225, by decide⟩
    (prefixPartial 12 337683) = some ⟨12, 2, 0, 1155225, 337683, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_337683_1155225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337683 ⟨1155225, by decide⟩ :=
  accepted_of_selected 12 337683 ⟨1155225, by decide⟩ ⟨12, 2, 0, 1155225, 337683, 3201, 65536⟩
    (by decide) selected_cut_42264

theorem unmarked_context_11_84420_1155226 : frontier 10 ⟨1155226, by decide⟩
    (prefixCache 11 84420) (prefixPartial 11 84420) = false := by
  decide +kernel

theorem node_context_11_84420_1155226 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155226, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155106, by decide⟩,⟨1155164, by decide⟩,⟨1155225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84420_1155226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84420 ⟨1155226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84420
    ⟨1155226, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155106, by decide⟩,⟨1155164, by decide⟩,⟨1155225, by decide⟩]) unmarked_context_11_84420_1155226 node_context_11_84420_1155226
  intro a
  fin_cases a
  · exact context_12_337680_1108174
  · exact context_12_337681_1155106
  · exact context_12_337682_1155164
  · exact context_12_337683_1155225

theorem selected_cut_42265 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84421) = some ⟨11, 1, 0, 892405, 84421, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84421_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84421 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84421 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84421, 1, 262144⟩
    (by decide) selected_cut_42265

theorem selected_cut_42266 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337688) = some ⟨12, 1, 0, 1108174, 337688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337688_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337688 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337688 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337688, 1, 65536⟩
    (by decide) selected_cut_42266

theorem selected_cut_42267 : selected 9 ⟨1155250, by decide⟩
    (prefixPartial 12 337689) = some ⟨12, 2, 0, 1155250, 337689, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_337689_1155250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337689 ⟨1155250, by decide⟩ :=
  accepted_of_selected 12 337689 ⟨1155250, by decide⟩ ⟨12, 2, 0, 1155250, 337689, 2413, 65536⟩
    (by decide) selected_cut_42267

theorem selected_cut_42268 : selected 9 ⟨1155290, by decide⟩
    (prefixPartial 12 337690) = some ⟨12, 2, 0, 1155290, 337690, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_337690_1155290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337690 ⟨1155290, by decide⟩ :=
  accepted_of_selected 12 337690 ⟨1155290, by decide⟩ ⟨12, 2, 0, 1155290, 337690, 2733, 65536⟩
    (by decide) selected_cut_42268

theorem selected_cut_42269 : selected 9 ⟨1155335, by decide⟩
    (prefixPartial 12 337691) = some ⟨12, 2, 0, 1155335, 337691, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_337691_1155335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337691 ⟨1155335, by decide⟩ :=
  accepted_of_selected 12 337691 ⟨1155335, by decide⟩ ⟨12, 2, 0, 1155335, 337691, 2841, 65536⟩
    (by decide) selected_cut_42269

theorem unmarked_context_11_84422_1155336 : frontier 10 ⟨1155336, by decide⟩
    (prefixCache 11 84422) (prefixPartial 11 84422) = false := by
  decide +kernel

theorem node_context_11_84422_1155336 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155336, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155250, by decide⟩,⟨1155290, by decide⟩,⟨1155335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84422_1155336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84422 ⟨1155336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84422
    ⟨1155336, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155250, by decide⟩,⟨1155290, by decide⟩,⟨1155335, by decide⟩]) unmarked_context_11_84422_1155336 node_context_11_84422_1155336
  intro a
  fin_cases a
  · exact context_12_337688_1108174
  · exact context_12_337689_1155250
  · exact context_12_337690_1155290
  · exact context_12_337691_1155335

theorem selected_cut_42270 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337692) = some ⟨12, 1, 0, 1108174, 337692, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337692_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337692 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337692 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337692, 1, 65536⟩
    (by decide) selected_cut_42270

theorem selected_cut_42271 : selected 9 ⟨1155367, by decide⟩
    (prefixPartial 12 337693) = some ⟨12, 2, 0, 1155367, 337693, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_337693_1155367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337693 ⟨1155367, by decide⟩ :=
  accepted_of_selected 12 337693 ⟨1155367, by decide⟩ ⟨12, 2, 0, 1155367, 337693, 2245, 65536⟩
    (by decide) selected_cut_42271

theorem selected_cut_42272 : selected 9 ⟨1155415, by decide⟩
    (prefixPartial 12 337694) = some ⟨12, 2, 0, 1155415, 337694, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_337694_1155415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337694 ⟨1155415, by decide⟩ :=
  accepted_of_selected 12 337694 ⟨1155415, by decide⟩ ⟨12, 2, 0, 1155415, 337694, 2917, 65536⟩
    (by decide) selected_cut_42272

theorem selected_cut_42273 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 337695) = some ⟨12, 1, 0, 903806, 337695, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337695_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337695 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 337695 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 337695, 1, 65536⟩
    (by decide) selected_cut_42273

theorem unmarked_context_11_84423_1155416 : frontier 10 ⟨1155416, by decide⟩
    (prefixCache 11 84423) (prefixPartial 11 84423) = false := by
  decide +kernel

theorem node_context_11_84423_1155416 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155416, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155367, by decide⟩,⟨1155415, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84423_1155416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84423 ⟨1155416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84423
    ⟨1155416, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155367, by decide⟩,⟨1155415, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84423_1155416 node_context_11_84423_1155416
  intro a
  fin_cases a
  · exact context_12_337692_1108174
  · exact context_12_337693_1155367
  · exact context_12_337694_1155415
  · exact context_12_337695_903806

theorem unmarked_context_10_21105_1155417 : frontier 11 ⟨1155417, by decide⟩
    (prefixCache 10 21105) (prefixPartial 10 21105) = false := by
  decide +kernel

theorem node_context_10_21105_1155417 : EJMOriginalGlobalDAGData.nodes 11 ⟨1155417, by decide⟩ =
    .split (coordinate 10) (![⟨1155226, by decide⟩,⟨892405, by decide⟩,⟨1155336, by decide⟩,⟨1155416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21105_1155417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21105 ⟨1155417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21105
    ⟨1155417, by decide⟩ (by decide) (![⟨1155226, by decide⟩,⟨892405, by decide⟩,⟨1155336, by decide⟩,⟨1155416, by decide⟩]) unmarked_context_10_21105_1155417 node_context_10_21105_1155417
  intro a
  fin_cases a
  · exact context_11_84420_1155226
  · exact context_11_84421_892405
  · exact context_11_84422_1155336
  · exact context_11_84423_1155416

theorem selected_cut_42274 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337696) = some ⟨12, 1, 0, 1108174, 337696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337696_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337696 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337696 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337696, 1, 65536⟩
    (by decide) selected_cut_42274

theorem selected_cut_42275 : selected 9 ⟨1155460, by decide⟩
    (prefixPartial 12 337697) = some ⟨12, 2, 0, 1155460, 337697, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_337697_1155460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337697 ⟨1155460, by decide⟩ :=
  accepted_of_selected 12 337697 ⟨1155460, by decide⟩ ⟨12, 2, 0, 1155460, 337697, 2629, 65536⟩
    (by decide) selected_cut_42275

theorem selected_cut_42276 : selected 9 ⟨1155515, by decide⟩
    (prefixPartial 12 337698) = some ⟨12, 2, 0, 1155515, 337698, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_337698_1155515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337698 ⟨1155515, by decide⟩ :=
  accepted_of_selected 12 337698 ⟨1155515, by decide⟩ ⟨12, 2, 0, 1155515, 337698, 3149, 65536⟩
    (by decide) selected_cut_42276

theorem selected_cut_42277 : selected 9 ⟨1155581, by decide⟩
    (prefixPartial 12 337699) = some ⟨12, 2, 0, 1155581, 337699, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_337699_1155581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337699 ⟨1155581, by decide⟩ :=
  accepted_of_selected 12 337699 ⟨1155581, by decide⟩ ⟨12, 2, 0, 1155581, 337699, 3285, 65536⟩
    (by decide) selected_cut_42277

theorem unmarked_context_11_84424_1155582 : frontier 10 ⟨1155582, by decide⟩
    (prefixCache 11 84424) (prefixPartial 11 84424) = false := by
  decide +kernel

theorem node_context_11_84424_1155582 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155582, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155460, by decide⟩,⟨1155515, by decide⟩,⟨1155581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84424_1155582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84424 ⟨1155582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84424
    ⟨1155582, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155460, by decide⟩,⟨1155515, by decide⟩,⟨1155581, by decide⟩]) unmarked_context_11_84424_1155582 node_context_11_84424_1155582
  intro a
  fin_cases a
  · exact context_12_337696_1108174
  · exact context_12_337697_1155460
  · exact context_12_337698_1155515
  · exact context_12_337699_1155581

theorem selected_cut_42278 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337700) = some ⟨12, 1, 0, 1108174, 337700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337700_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337700 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337700 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337700, 1, 65536⟩
    (by decide) selected_cut_42278

theorem selected_cut_42279 : selected 9 ⟨1155610, by decide⟩
    (prefixPartial 12 337701) = some ⟨12, 2, 0, 1155610, 337701, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_337701_1155610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337701 ⟨1155610, by decide⟩ :=
  accepted_of_selected 12 337701 ⟨1155610, by decide⟩ ⟨12, 2, 0, 1155610, 337701, 2177, 65536⟩
    (by decide) selected_cut_42279

theorem selected_cut_42280 : selected 9 ⟨1155653, by decide⟩
    (prefixPartial 12 337702) = some ⟨12, 2, 0, 1155653, 337702, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_337702_1155653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337702 ⟨1155653, by decide⟩ :=
  accepted_of_selected 12 337702 ⟨1155653, by decide⟩ ⟨12, 2, 0, 1155653, 337702, 2497, 65536⟩
    (by decide) selected_cut_42280

theorem selected_cut_42281 : selected 9 ⟨1155700, by decide⟩
    (prefixPartial 12 337703) = some ⟨12, 2, 0, 1155700, 337703, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_337703_1155700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337703 ⟨1155700, by decide⟩ :=
  accepted_of_selected 12 337703 ⟨1155700, by decide⟩ ⟨12, 2, 0, 1155700, 337703, 2693, 65536⟩
    (by decide) selected_cut_42281

theorem unmarked_context_11_84425_1155701 : frontier 10 ⟨1155701, by decide⟩
    (prefixCache 11 84425) (prefixPartial 11 84425) = false := by
  decide +kernel

theorem node_context_11_84425_1155701 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155701, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155610, by decide⟩,⟨1155653, by decide⟩,⟨1155700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84425_1155701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84425 ⟨1155701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84425
    ⟨1155701, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155610, by decide⟩,⟨1155653, by decide⟩,⟨1155700, by decide⟩]) unmarked_context_11_84425_1155701 node_context_11_84425_1155701
  intro a
  fin_cases a
  · exact context_12_337700_1108174
  · exact context_12_337701_1155610
  · exact context_12_337702_1155653
  · exact context_12_337703_1155700

theorem selected_cut_42282 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337704) = some ⟨12, 1, 0, 1108174, 337704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337704_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337704 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337704 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337704, 1, 65536⟩
    (by decide) selected_cut_42282

theorem selected_cut_42283 : selected 9 ⟨1155729, by decide⟩
    (prefixPartial 12 337705) = some ⟨12, 2, 0, 1155729, 337705, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_337705_1155729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337705 ⟨1155729, by decide⟩ :=
  accepted_of_selected 12 337705 ⟨1155729, by decide⟩ ⟨12, 2, 0, 1155729, 337705, 2225, 65536⟩
    (by decide) selected_cut_42283

theorem selected_cut_42284 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 337706) = some ⟨12, 1, 0, 1113261, 337706, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337706_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337706 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 337706 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 337706, 1, 65536⟩
    (by decide) selected_cut_42284

theorem selected_cut_42285 : selected 9 ⟨1155770, by decide⟩
    (prefixPartial 12 337707) = some ⟨12, 2, 0, 1155770, 337707, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_337707_1155770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337707 ⟨1155770, by decide⟩ :=
  accepted_of_selected 12 337707 ⟨1155770, by decide⟩ ⟨12, 2, 0, 1155770, 337707, 2629, 65536⟩
    (by decide) selected_cut_42285

theorem unmarked_context_11_84426_1155771 : frontier 10 ⟨1155771, by decide⟩
    (prefixCache 11 84426) (prefixPartial 11 84426) = false := by
  decide +kernel

theorem node_context_11_84426_1155771 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155771, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155729, by decide⟩,⟨1113261, by decide⟩,⟨1155770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84426_1155771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84426 ⟨1155771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84426
    ⟨1155771, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155729, by decide⟩,⟨1113261, by decide⟩,⟨1155770, by decide⟩]) unmarked_context_11_84426_1155771 node_context_11_84426_1155771
  intro a
  fin_cases a
  · exact context_12_337704_1108174
  · exact context_12_337705_1155729
  · exact context_12_337706_1113261
  · exact context_12_337707_1155770

theorem selected_cut_42286 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337708) = some ⟨12, 1, 0, 1108174, 337708, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337708_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337708 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337708 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337708, 1, 65536⟩
    (by decide) selected_cut_42286

theorem selected_cut_42287 : selected 9 ⟨1155798, by decide⟩
    (prefixPartial 12 337709) = some ⟨12, 2, 0, 1155798, 337709, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_337709_1155798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337709 ⟨1155798, by decide⟩ :=
  accepted_of_selected 12 337709 ⟨1155798, by decide⟩ ⟨12, 2, 0, 1155798, 337709, 2169, 65536⟩
    (by decide) selected_cut_42287

theorem selected_cut_42288 : selected 9 ⟨1155852, by decide⟩
    (prefixPartial 12 337710) = some ⟨12, 2, 0, 1155852, 337710, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_337710_1155852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337710 ⟨1155852, by decide⟩ :=
  accepted_of_selected 12 337710 ⟨1155852, by decide⟩ ⟨12, 2, 0, 1155852, 337710, 2733, 65536⟩
    (by decide) selected_cut_42288

theorem selected_cut_42289 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 337711) = some ⟨12, 1, 0, 903806, 337711, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337711_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337711 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 337711 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 337711, 1, 65536⟩
    (by decide) selected_cut_42289

theorem unmarked_context_11_84427_1155853 : frontier 10 ⟨1155853, by decide⟩
    (prefixCache 11 84427) (prefixPartial 11 84427) = false := by
  decide +kernel

theorem node_context_11_84427_1155853 : EJMOriginalGlobalDAGData.nodes 10 ⟨1155853, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155798, by decide⟩,⟨1155852, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84427_1155853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84427 ⟨1155853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84427
    ⟨1155853, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155798, by decide⟩,⟨1155852, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84427_1155853 node_context_11_84427_1155853
  intro a
  fin_cases a
  · exact context_12_337708_1108174
  · exact context_12_337709_1155798
  · exact context_12_337710_1155852
  · exact context_12_337711_903806

theorem unmarked_context_10_21106_1155854 : frontier 11 ⟨1155854, by decide⟩
    (prefixCache 10 21106) (prefixPartial 10 21106) = false := by
  decide +kernel

theorem node_context_10_21106_1155854 : EJMOriginalGlobalDAGData.nodes 11 ⟨1155854, by decide⟩ =
    .split (coordinate 10) (![⟨1155582, by decide⟩,⟨1155701, by decide⟩,⟨1155771, by decide⟩,⟨1155853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21106_1155854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21106 ⟨1155854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21106
    ⟨1155854, by decide⟩ (by decide) (![⟨1155582, by decide⟩,⟨1155701, by decide⟩,⟨1155771, by decide⟩,⟨1155853, by decide⟩]) unmarked_context_10_21106_1155854 node_context_10_21106_1155854
  intro a
  fin_cases a
  · exact context_11_84424_1155582
  · exact context_11_84425_1155701
  · exact context_11_84426_1155771
  · exact context_11_84427_1155853

theorem selected_cut_42290 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337712) = some ⟨12, 1, 0, 1108174, 337712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337712_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337712 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337712 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337712, 1, 65536⟩
    (by decide) selected_cut_42290

theorem selected_cut_42291 : selected 9 ⟨1155892, by decide⟩
    (prefixPartial 12 337713) = some ⟨12, 2, 0, 1155892, 337713, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_337713_1155892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337713 ⟨1155892, by decide⟩ :=
  accepted_of_selected 12 337713 ⟨1155892, by decide⟩ ⟨12, 2, 0, 1155892, 337713, 2545, 65536⟩
    (by decide) selected_cut_42291

theorem selected_cut_42292 : selected 9 ⟨1155947, by decide⟩
    (prefixPartial 12 337714) = some ⟨12, 2, 0, 1155947, 337714, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_337714_1155947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337714 ⟨1155947, by decide⟩ :=
  accepted_of_selected 12 337714 ⟨1155947, by decide⟩ ⟨12, 2, 0, 1155947, 337714, 3021, 65536⟩
    (by decide) selected_cut_42292

theorem selected_cut_42293 : selected 9 ⟨1156008, by decide⟩
    (prefixPartial 12 337715) = some ⟨12, 2, 0, 1156008, 337715, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_337715_1156008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337715 ⟨1156008, by decide⟩ :=
  accepted_of_selected 12 337715 ⟨1156008, by decide⟩ ⟨12, 2, 0, 1156008, 337715, 3253, 65536⟩
    (by decide) selected_cut_42293

theorem unmarked_context_11_84428_1156009 : frontier 10 ⟨1156009, by decide⟩
    (prefixCache 11 84428) (prefixPartial 11 84428) = false := by
  decide +kernel

theorem node_context_11_84428_1156009 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156009, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1155892, by decide⟩,⟨1155947, by decide⟩,⟨1156008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84428_1156009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84428 ⟨1156009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84428
    ⟨1156009, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1155892, by decide⟩,⟨1155947, by decide⟩,⟨1156008, by decide⟩]) unmarked_context_11_84428_1156009 node_context_11_84428_1156009
  intro a
  fin_cases a
  · exact context_12_337712_1108174
  · exact context_12_337713_1155892
  · exact context_12_337714_1155947
  · exact context_12_337715_1156008

theorem selected_cut_42294 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337716) = some ⟨12, 1, 0, 1108174, 337716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337716_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337716 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337716 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337716, 1, 65536⟩
    (by decide) selected_cut_42294

theorem selected_cut_42295 : selected 9 ⟨1156036, by decide⟩
    (prefixPartial 12 337717) = some ⟨12, 2, 0, 1156036, 337717, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_337717_1156036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337717 ⟨1156036, by decide⟩ :=
  accepted_of_selected 12 337717 ⟨1156036, by decide⟩ ⟨12, 2, 0, 1156036, 337717, 2193, 65536⟩
    (by decide) selected_cut_42295

theorem selected_cut_42296 : selected 9 ⟨1156076, by decide⟩
    (prefixPartial 12 337718) = some ⟨12, 2, 0, 1156076, 337718, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_337718_1156076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337718 ⟨1156076, by decide⟩ :=
  accepted_of_selected 12 337718 ⟨1156076, by decide⟩ ⟨12, 2, 0, 1156076, 337718, 2461, 65536⟩
    (by decide) selected_cut_42296

theorem selected_cut_42297 : selected 9 ⟨1156129, by decide⟩
    (prefixPartial 12 337719) = some ⟨12, 2, 0, 1156129, 337719, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_337719_1156129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337719 ⟨1156129, by decide⟩ :=
  accepted_of_selected 12 337719 ⟨1156129, by decide⟩ ⟨12, 2, 0, 1156129, 337719, 2785, 65536⟩
    (by decide) selected_cut_42297

theorem unmarked_context_11_84429_1156130 : frontier 10 ⟨1156130, by decide⟩
    (prefixCache 11 84429) (prefixPartial 11 84429) = false := by
  decide +kernel

theorem node_context_11_84429_1156130 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156130, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1156036, by decide⟩,⟨1156076, by decide⟩,⟨1156129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84429_1156130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84429 ⟨1156130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84429
    ⟨1156130, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1156036, by decide⟩,⟨1156076, by decide⟩,⟨1156129, by decide⟩]) unmarked_context_11_84429_1156130 node_context_11_84429_1156130
  intro a
  fin_cases a
  · exact context_12_337716_1108174
  · exact context_12_337717_1156036
  · exact context_12_337718_1156076
  · exact context_12_337719_1156129

theorem selected_cut_42298 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337720) = some ⟨12, 1, 0, 1108174, 337720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337720_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337720 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337720 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337720, 1, 65536⟩
    (by decide) selected_cut_42298

theorem selected_cut_42299 : selected 9 ⟨1156159, by decide⟩
    (prefixPartial 12 337721) = some ⟨12, 2, 0, 1156159, 337721, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_337721_1156159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337721 ⟨1156159, by decide⟩ :=
  accepted_of_selected 12 337721 ⟨1156159, by decide⟩ ⟨12, 2, 0, 1156159, 337721, 2277, 65536⟩
    (by decide) selected_cut_42299

theorem selected_cut_42300 : selected 9 ⟨1156202, by decide⟩
    (prefixPartial 12 337722) = some ⟨12, 2, 0, 1156202, 337722, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_337722_1156202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337722 ⟨1156202, by decide⟩ :=
  accepted_of_selected 12 337722 ⟨1156202, by decide⟩ ⟨12, 2, 0, 1156202, 337722, 2477, 65536⟩
    (by decide) selected_cut_42300

theorem selected_cut_42301 : selected 9 ⟨1156250, by decide⟩
    (prefixPartial 12 337723) = some ⟨12, 2, 0, 1156250, 337723, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_337723_1156250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337723 ⟨1156250, by decide⟩ :=
  accepted_of_selected 12 337723 ⟨1156250, by decide⟩ ⟨12, 2, 0, 1156250, 337723, 2737, 65536⟩
    (by decide) selected_cut_42301

theorem unmarked_context_11_84430_1156251 : frontier 10 ⟨1156251, by decide⟩
    (prefixCache 11 84430) (prefixPartial 11 84430) = false := by
  decide +kernel

theorem node_context_11_84430_1156251 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156251, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1156159, by decide⟩,⟨1156202, by decide⟩,⟨1156250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84430_1156251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84430 ⟨1156251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84430
    ⟨1156251, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1156159, by decide⟩,⟨1156202, by decide⟩,⟨1156250, by decide⟩]) unmarked_context_11_84430_1156251 node_context_11_84430_1156251
  intro a
  fin_cases a
  · exact context_12_337720_1108174
  · exact context_12_337721_1156159
  · exact context_12_337722_1156202
  · exact context_12_337723_1156250

theorem selected_cut_42302 : selected 10 ⟨1156294, by decide⟩
    (prefixPartial 11 84431) = some ⟨11, 2, 0, 1156294, 84431, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_84431_1156294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84431 ⟨1156294, by decide⟩ :=
  accepted_of_selected 11 84431 ⟨1156294, by decide⟩ ⟨11, 2, 0, 1156294, 84431, 2569, 262144⟩
    (by decide) selected_cut_42302

theorem unmarked_context_10_21107_1156295 : frontier 11 ⟨1156295, by decide⟩
    (prefixCache 10 21107) (prefixPartial 10 21107) = false := by
  decide +kernel

theorem node_context_10_21107_1156295 : EJMOriginalGlobalDAGData.nodes 11 ⟨1156295, by decide⟩ =
    .split (coordinate 10) (![⟨1156009, by decide⟩,⟨1156130, by decide⟩,⟨1156251, by decide⟩,⟨1156294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21107_1156295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21107 ⟨1156295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21107
    ⟨1156295, by decide⟩ (by decide) (![⟨1156009, by decide⟩,⟨1156130, by decide⟩,⟨1156251, by decide⟩,⟨1156294, by decide⟩]) unmarked_context_10_21107_1156295 node_context_10_21107_1156295
  intro a
  fin_cases a
  · exact context_11_84428_1156009
  · exact context_11_84429_1156130
  · exact context_11_84430_1156251
  · exact context_11_84431_1156294

theorem unmarked_context_9_5276_1156296 : frontier 12 ⟨1156296, by decide⟩
    (prefixCache 9 5276) (prefixPartial 9 5276) = false := by
  decide +kernel

theorem node_context_9_5276_1156296 : EJMOriginalGlobalDAGData.nodes 12 ⟨1156296, by decide⟩ =
    .split (coordinate 9) (![⟨1155070, by decide⟩,⟨1155417, by decide⟩,⟨1155854, by decide⟩,⟨1156295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5276_1156296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5276 ⟨1156296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5276
    ⟨1156296, by decide⟩ (by decide) (![⟨1155070, by decide⟩,⟨1155417, by decide⟩,⟨1155854, by decide⟩,⟨1156295, by decide⟩]) unmarked_context_9_5276_1156296 node_context_9_5276_1156296
  intro a
  fin_cases a
  · exact context_10_21104_1155070
  · exact context_10_21105_1155417
  · exact context_10_21106_1155854
  · exact context_10_21107_1156295

theorem selected_cut_42303 : selected 9 ⟨1113480, by decide⟩
    (prefixPartial 12 337728) = some ⟨12, 1, 0, 1113480, 337728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337728_1113480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337728 ⟨1113480, by decide⟩ :=
  accepted_of_selected 12 337728 ⟨1113480, by decide⟩ ⟨12, 1, 0, 1113480, 337728, 1, 65536⟩
    (by decide) selected_cut_42303

theorem selected_cut_42304 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 337729) = some ⟨12, 1, 0, 170504, 337729, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337729_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337729 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 337729 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 337729, 1, 65536⟩
    (by decide) selected_cut_42304

theorem selected_cut_42305 : selected 9 ⟨1156351, by decide⟩
    (prefixPartial 12 337730) = some ⟨12, 2, 0, 1156351, 337730, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_337730_1156351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337730 ⟨1156351, by decide⟩ :=
  accepted_of_selected 12 337730 ⟨1156351, by decide⟩ ⟨12, 2, 0, 1156351, 337730, 2941, 65536⟩
    (by decide) selected_cut_42305

theorem selected_cut_42306 : selected 9 ⟨1156403, by decide⟩
    (prefixPartial 12 337731) = some ⟨12, 2, 0, 1156403, 337731, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_337731_1156403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337731 ⟨1156403, by decide⟩ :=
  accepted_of_selected 12 337731 ⟨1156403, by decide⟩ ⟨12, 2, 0, 1156403, 337731, 2705, 65536⟩
    (by decide) selected_cut_42306

theorem unmarked_context_11_84432_1156404 : frontier 10 ⟨1156404, by decide⟩
    (prefixCache 11 84432) (prefixPartial 11 84432) = false := by
  decide +kernel

theorem node_context_11_84432_1156404 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156404, by decide⟩ =
    .split (coordinate 11) (![⟨1113480, by decide⟩,⟨170504, by decide⟩,⟨1156351, by decide⟩,⟨1156403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84432_1156404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84432 ⟨1156404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84432
    ⟨1156404, by decide⟩ (by decide) (![⟨1113480, by decide⟩,⟨170504, by decide⟩,⟨1156351, by decide⟩,⟨1156403, by decide⟩]) unmarked_context_11_84432_1156404 node_context_11_84432_1156404
  intro a
  fin_cases a
  · exact context_12_337728_1113480
  · exact context_12_337729_170504
  · exact context_12_337730_1156351
  · exact context_12_337731_1156403

theorem selected_cut_42307 : selected 9 ⟨1156430, by decide⟩
    (prefixPartial 12 337732) = some ⟨12, 2, 0, 1156430, 337732, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_337732_1156430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337732 ⟨1156430, by decide⟩ :=
  accepted_of_selected 12 337732 ⟨1156430, by decide⟩ ⟨12, 2, 0, 1156430, 337732, 1737, 65536⟩
    (by decide) selected_cut_42307

theorem selected_cut_42308 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 337733) = some ⟨12, 1, 0, 170504, 337733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337733_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337733 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 337733 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 337733, 1, 65536⟩
    (by decide) selected_cut_42308

theorem selected_cut_42309 : selected 9 ⟨1156466, by decide⟩
    (prefixPartial 12 337734) = some ⟨12, 2, 0, 1156466, 337734, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_337734_1156466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337734 ⟨1156466, by decide⟩ :=
  accepted_of_selected 12 337734 ⟨1156466, by decide⟩ ⟨12, 2, 0, 1156466, 337734, 2113, 65536⟩
    (by decide) selected_cut_42309

theorem selected_cut_42310 : selected 9 ⟨1156502, by decide⟩
    (prefixPartial 12 337735) = some ⟨12, 2, 0, 1156502, 337735, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_337735_1156502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337735 ⟨1156502, by decide⟩ :=
  accepted_of_selected 12 337735 ⟨1156502, by decide⟩ ⟨12, 2, 0, 1156502, 337735, 2113, 65536⟩
    (by decide) selected_cut_42310

theorem unmarked_context_11_84433_1156503 : frontier 10 ⟨1156503, by decide⟩
    (prefixCache 11 84433) (prefixPartial 11 84433) = false := by
  decide +kernel

theorem node_context_11_84433_1156503 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156503, by decide⟩ =
    .split (coordinate 11) (![⟨1156430, by decide⟩,⟨170504, by decide⟩,⟨1156466, by decide⟩,⟨1156502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84433_1156503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84433 ⟨1156503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84433
    ⟨1156503, by decide⟩ (by decide) (![⟨1156430, by decide⟩,⟨170504, by decide⟩,⟨1156466, by decide⟩,⟨1156502, by decide⟩]) unmarked_context_11_84433_1156503 node_context_11_84433_1156503
  intro a
  fin_cases a
  · exact context_12_337732_1156430
  · exact context_12_337733_170504
  · exact context_12_337734_1156466
  · exact context_12_337735_1156502

theorem selected_cut_42311 : selected 9 ⟨1156541, by decide⟩
    (prefixPartial 12 337736) = some ⟨12, 2, 0, 1156541, 337736, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_337736_1156541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337736 ⟨1156541, by decide⟩ :=
  accepted_of_selected 12 337736 ⟨1156541, by decide⟩ ⟨12, 2, 0, 1156541, 337736, 2085, 65536⟩
    (by decide) selected_cut_42311

theorem selected_cut_42312 : selected 9 ⟨1156570, by decide⟩
    (prefixPartial 12 337737) = some ⟨12, 2, 0, 1156570, 337737, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_337737_1156570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337737 ⟨1156570, by decide⟩ :=
  accepted_of_selected 12 337737 ⟨1156570, by decide⟩ ⟨12, 2, 0, 1156570, 337737, 1997, 65536⟩
    (by decide) selected_cut_42312

theorem selected_cut_42313 : selected 9 ⟨1156610, by decide⟩
    (prefixPartial 12 337738) = some ⟨12, 2, 0, 1156610, 337738, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_337738_1156610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337738 ⟨1156610, by decide⟩ :=
  accepted_of_selected 12 337738 ⟨1156610, by decide⟩ ⟨12, 2, 0, 1156610, 337738, 2437, 65536⟩
    (by decide) selected_cut_42313

theorem selected_cut_42314 : selected 9 ⟨1156652, by decide⟩
    (prefixPartial 12 337739) = some ⟨12, 2, 0, 1156652, 337739, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_337739_1156652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337739 ⟨1156652, by decide⟩ :=
  accepted_of_selected 12 337739 ⟨1156652, by decide⟩ ⟨12, 2, 0, 1156652, 337739, 2397, 65536⟩
    (by decide) selected_cut_42314

theorem unmarked_context_11_84434_1156653 : frontier 10 ⟨1156653, by decide⟩
    (prefixCache 11 84434) (prefixPartial 11 84434) = false := by
  decide +kernel

theorem node_context_11_84434_1156653 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156653, by decide⟩ =
    .split (coordinate 11) (![⟨1156541, by decide⟩,⟨1156570, by decide⟩,⟨1156610, by decide⟩,⟨1156652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84434_1156653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84434 ⟨1156653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84434
    ⟨1156653, by decide⟩ (by decide) (![⟨1156541, by decide⟩,⟨1156570, by decide⟩,⟨1156610, by decide⟩,⟨1156652, by decide⟩]) unmarked_context_11_84434_1156653 node_context_11_84434_1156653
  intro a
  fin_cases a
  · exact context_12_337736_1156541
  · exact context_12_337737_1156570
  · exact context_12_337738_1156610
  · exact context_12_337739_1156652

theorem selected_cut_42315 : selected 9 ⟨1156682, by decide⟩
    (prefixPartial 12 337740) = some ⟨12, 2, 0, 1156682, 337740, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_337740_1156682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337740 ⟨1156682, by decide⟩ :=
  accepted_of_selected 12 337740 ⟨1156682, by decide⟩ ⟨12, 2, 0, 1156682, 337740, 1805, 65536⟩
    (by decide) selected_cut_42315

theorem selected_cut_42316 : selected 9 ⟨1156707, by decide⟩
    (prefixPartial 12 337741) = some ⟨12, 2, 0, 1156707, 337741, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_337741_1156707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337741 ⟨1156707, by decide⟩ :=
  accepted_of_selected 12 337741 ⟨1156707, by decide⟩ ⟨12, 2, 0, 1156707, 337741, 1705, 65536⟩
    (by decide) selected_cut_42316

theorem selected_cut_42317 : selected 9 ⟨1156749, by decide⟩
    (prefixPartial 12 337742) = some ⟨12, 2, 0, 1156749, 337742, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_337742_1156749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337742 ⟨1156749, by decide⟩ :=
  accepted_of_selected 12 337742 ⟨1156749, by decide⟩ ⟨12, 2, 0, 1156749, 337742, 2345, 65536⟩
    (by decide) selected_cut_42317

theorem selected_cut_42318 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 337743) = some ⟨12, 1, 0, 903806, 337743, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337743_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337743 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 337743 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 337743, 1, 65536⟩
    (by decide) selected_cut_42318

theorem unmarked_context_11_84435_1156750 : frontier 10 ⟨1156750, by decide⟩
    (prefixCache 11 84435) (prefixPartial 11 84435) = false := by
  decide +kernel

theorem node_context_11_84435_1156750 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156750, by decide⟩ =
    .split (coordinate 11) (![⟨1156682, by decide⟩,⟨1156707, by decide⟩,⟨1156749, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84435_1156750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84435 ⟨1156750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84435
    ⟨1156750, by decide⟩ (by decide) (![⟨1156682, by decide⟩,⟨1156707, by decide⟩,⟨1156749, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84435_1156750 node_context_11_84435_1156750
  intro a
  fin_cases a
  · exact context_12_337740_1156682
  · exact context_12_337741_1156707
  · exact context_12_337742_1156749
  · exact context_12_337743_903806

theorem unmarked_context_10_21108_1156751 : frontier 11 ⟨1156751, by decide⟩
    (prefixCache 10 21108) (prefixPartial 10 21108) = false := by
  decide +kernel

theorem node_context_10_21108_1156751 : EJMOriginalGlobalDAGData.nodes 11 ⟨1156751, by decide⟩ =
    .split (coordinate 10) (![⟨1156404, by decide⟩,⟨1156503, by decide⟩,⟨1156653, by decide⟩,⟨1156750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21108_1156751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21108 ⟨1156751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21108
    ⟨1156751, by decide⟩ (by decide) (![⟨1156404, by decide⟩,⟨1156503, by decide⟩,⟨1156653, by decide⟩,⟨1156750, by decide⟩]) unmarked_context_10_21108_1156751 node_context_10_21108_1156751
  intro a
  fin_cases a
  · exact context_11_84432_1156404
  · exact context_11_84433_1156503
  · exact context_11_84434_1156653
  · exact context_11_84435_1156750

theorem selected_cut_42319 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21109) = some ⟨10, 1, 0, 893098, 21109, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21109_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21109 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21109 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21109, 1, 1048576⟩
    (by decide) selected_cut_42319

theorem selected_cut_42320 : selected 9 ⟨1156783, by decide⟩
    (prefixPartial 12 337760) = some ⟨12, 2, 0, 1156783, 337760, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_337760_1156783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337760 ⟨1156783, by decide⟩ :=
  accepted_of_selected 12 337760 ⟨1156783, by decide⟩ ⟨12, 2, 0, 1156783, 337760, 1941, 65536⟩
    (by decide) selected_cut_42320

theorem selected_cut_42321 : selected 9 ⟨1156804, by decide⟩
    (prefixPartial 12 337761) = some ⟨12, 2, 0, 1156804, 337761, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_337761_1156804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337761 ⟨1156804, by decide⟩ :=
  accepted_of_selected 12 337761 ⟨1156804, by decide⟩ ⟨12, 2, 0, 1156804, 337761, 1701, 65536⟩
    (by decide) selected_cut_42321

theorem selected_cut_42322 : selected 9 ⟨1156850, by decide⟩
    (prefixPartial 12 337762) = some ⟨12, 2, 0, 1156850, 337762, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_337762_1156850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337762 ⟨1156850, by decide⟩ :=
  accepted_of_selected 12 337762 ⟨1156850, by decide⟩ ⟨12, 2, 0, 1156850, 337762, 2321, 65536⟩
    (by decide) selected_cut_42322

theorem selected_cut_42323 : selected 9 ⟨1156884, by decide⟩
    (prefixPartial 12 337763) = some ⟨12, 2, 0, 1156884, 337763, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_337763_1156884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337763 ⟨1156884, by decide⟩ :=
  accepted_of_selected 12 337763 ⟨1156884, by decide⟩ ⟨12, 2, 0, 1156884, 337763, 2049, 65536⟩
    (by decide) selected_cut_42323

theorem unmarked_context_11_84440_1156885 : frontier 10 ⟨1156885, by decide⟩
    (prefixCache 11 84440) (prefixPartial 11 84440) = false := by
  decide +kernel

theorem node_context_11_84440_1156885 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156885, by decide⟩ =
    .split (coordinate 11) (![⟨1156783, by decide⟩,⟨1156804, by decide⟩,⟨1156850, by decide⟩,⟨1156884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84440_1156885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84440 ⟨1156885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84440
    ⟨1156885, by decide⟩ (by decide) (![⟨1156783, by decide⟩,⟨1156804, by decide⟩,⟨1156850, by decide⟩,⟨1156884, by decide⟩]) unmarked_context_11_84440_1156885 node_context_11_84440_1156885
  intro a
  fin_cases a
  · exact context_12_337760_1156783
  · exact context_12_337761_1156804
  · exact context_12_337762_1156850
  · exact context_12_337763_1156884

theorem selected_cut_42324 : selected 9 ⟨1156904, by decide⟩
    (prefixPartial 12 337764) = some ⟨12, 2, 0, 1156904, 337764, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_337764_1156904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337764 ⟨1156904, by decide⟩ :=
  accepted_of_selected 12 337764 ⟨1156904, by decide⟩ ⟨12, 2, 0, 1156904, 337764, 1529, 65536⟩
    (by decide) selected_cut_42324

theorem selected_cut_42325 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 337765) = some ⟨12, 1, 0, 642794, 337765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337765_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337765 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 337765 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 337765, 1, 65536⟩
    (by decide) selected_cut_42325

theorem selected_cut_42326 : selected 9 ⟨1156926, by decide⟩
    (prefixPartial 12 337766) = some ⟨12, 2, 0, 1156926, 337766, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_337766_1156926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337766 ⟨1156926, by decide⟩ :=
  accepted_of_selected 12 337766 ⟨1156926, by decide⟩ ⟨12, 2, 0, 1156926, 337766, 1645, 65536⟩
    (by decide) selected_cut_42326

theorem selected_cut_42327 : selected 9 ⟨1156946, by decide⟩
    (prefixPartial 12 337767) = some ⟨12, 2, 0, 1156946, 337767, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_337767_1156946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337767 ⟨1156946, by decide⟩ :=
  accepted_of_selected 12 337767 ⟨1156946, by decide⟩ ⟨12, 2, 0, 1156946, 337767, 1605, 65536⟩
    (by decide) selected_cut_42327

theorem unmarked_context_11_84441_1156947 : frontier 10 ⟨1156947, by decide⟩
    (prefixCache 11 84441) (prefixPartial 11 84441) = false := by
  decide +kernel

theorem node_context_11_84441_1156947 : EJMOriginalGlobalDAGData.nodes 10 ⟨1156947, by decide⟩ =
    .split (coordinate 11) (![⟨1156904, by decide⟩,⟨642794, by decide⟩,⟨1156926, by decide⟩,⟨1156946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84441_1156947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84441 ⟨1156947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84441
    ⟨1156947, by decide⟩ (by decide) (![⟨1156904, by decide⟩,⟨642794, by decide⟩,⟨1156926, by decide⟩,⟨1156946, by decide⟩]) unmarked_context_11_84441_1156947 node_context_11_84441_1156947
  intro a
  fin_cases a
  · exact context_12_337764_1156904
  · exact context_12_337765_642794
  · exact context_12_337766_1156926
  · exact context_12_337767_1156946

theorem selected_cut_42328 : selected 9 ⟨1156975, by decide⟩
    (prefixPartial 12 337768) = some ⟨12, 2, 0, 1156975, 337768, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_337768_1156975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337768 ⟨1156975, by decide⟩ :=
  accepted_of_selected 12 337768 ⟨1156975, by decide⟩ ⟨12, 2, 0, 1156975, 337768, 1625, 65536⟩
    (by decide) selected_cut_42328

theorem selected_cut_42329 : selected 9 ⟨1156992, by decide⟩
    (prefixPartial 12 337769) = some ⟨12, 2, 0, 1156992, 337769, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_337769_1156992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337769 ⟨1156992, by decide⟩ :=
  accepted_of_selected 12 337769 ⟨1156992, by decide⟩ ⟨12, 2, 0, 1156992, 337769, 1441, 65536⟩
    (by decide) selected_cut_42329

theorem selected_cut_42330 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 337770) = some ⟨12, 1, 0, 1113261, 337770, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337770_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337770 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 337770 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 337770, 1, 65536⟩
    (by decide) selected_cut_42330

theorem selected_cut_42331 : selected 9 ⟨1157019, by decide⟩
    (prefixPartial 12 337771) = some ⟨12, 2, 0, 1157019, 337771, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_337771_1157019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337771 ⟨1157019, by decide⟩ :=
  accepted_of_selected 12 337771 ⟨1157019, by decide⟩ ⟨12, 2, 0, 1157019, 337771, 1741, 65536⟩
    (by decide) selected_cut_42331

theorem unmarked_context_11_84442_1157020 : frontier 10 ⟨1157020, by decide⟩
    (prefixCache 11 84442) (prefixPartial 11 84442) = false := by
  decide +kernel

theorem node_context_11_84442_1157020 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157020, by decide⟩ =
    .split (coordinate 11) (![⟨1156975, by decide⟩,⟨1156992, by decide⟩,⟨1113261, by decide⟩,⟨1157019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84442_1157020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84442 ⟨1157020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84442
    ⟨1157020, by decide⟩ (by decide) (![⟨1156975, by decide⟩,⟨1156992, by decide⟩,⟨1113261, by decide⟩,⟨1157019, by decide⟩]) unmarked_context_11_84442_1157020 node_context_11_84442_1157020
  intro a
  fin_cases a
  · exact context_12_337768_1156975
  · exact context_12_337769_1156992
  · exact context_12_337770_1113261
  · exact context_12_337771_1157019

theorem selected_cut_42332 : selected 9 ⟨1157043, by decide⟩
    (prefixPartial 12 337772) = some ⟨12, 2, 0, 1157043, 337772, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_337772_1157043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337772 ⟨1157043, by decide⟩ :=
  accepted_of_selected 12 337772 ⟨1157043, by decide⟩ ⟨12, 2, 0, 1157043, 337772, 1529, 65536⟩
    (by decide) selected_cut_42332

theorem selected_cut_42333 : selected 9 ⟨1157059, by decide⟩
    (prefixPartial 12 337773) = some ⟨12, 2, 0, 1157059, 337773, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_337773_1157059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337773 ⟨1157059, by decide⟩ :=
  accepted_of_selected 12 337773 ⟨1157059, by decide⟩ ⟨12, 2, 0, 1157059, 337773, 1417, 65536⟩
    (by decide) selected_cut_42333

theorem selected_cut_42334 : selected 9 ⟨1157090, by decide⟩
    (prefixPartial 12 337774) = some ⟨12, 2, 0, 1157090, 337774, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_337774_1157090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337774 ⟨1157090, by decide⟩ :=
  accepted_of_selected 12 337774 ⟨1157090, by decide⟩ ⟨12, 2, 0, 1157090, 337774, 1841, 65536⟩
    (by decide) selected_cut_42334

theorem selected_cut_42335 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 337775) = some ⟨12, 1, 0, 903806, 337775, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337775_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337775 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 337775 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 337775, 1, 65536⟩
    (by decide) selected_cut_42335

theorem unmarked_context_11_84443_1157091 : frontier 10 ⟨1157091, by decide⟩
    (prefixCache 11 84443) (prefixPartial 11 84443) = false := by
  decide +kernel

theorem node_context_11_84443_1157091 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157091, by decide⟩ =
    .split (coordinate 11) (![⟨1157043, by decide⟩,⟨1157059, by decide⟩,⟨1157090, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84443_1157091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84443 ⟨1157091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84443
    ⟨1157091, by decide⟩ (by decide) (![⟨1157043, by decide⟩,⟨1157059, by decide⟩,⟨1157090, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84443_1157091 node_context_11_84443_1157091
  intro a
  fin_cases a
  · exact context_12_337772_1157043
  · exact context_12_337773_1157059
  · exact context_12_337774_1157090
  · exact context_12_337775_903806

theorem unmarked_context_10_21110_1157092 : frontier 11 ⟨1157092, by decide⟩
    (prefixCache 10 21110) (prefixPartial 10 21110) = false := by
  decide +kernel

theorem node_context_10_21110_1157092 : EJMOriginalGlobalDAGData.nodes 11 ⟨1157092, by decide⟩ =
    .split (coordinate 10) (![⟨1156885, by decide⟩,⟨1156947, by decide⟩,⟨1157020, by decide⟩,⟨1157091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21110_1157092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21110 ⟨1157092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21110
    ⟨1157092, by decide⟩ (by decide) (![⟨1156885, by decide⟩,⟨1156947, by decide⟩,⟨1157020, by decide⟩,⟨1157091, by decide⟩]) unmarked_context_10_21110_1157092 node_context_10_21110_1157092
  intro a
  fin_cases a
  · exact context_11_84440_1156885
  · exact context_11_84441_1156947
  · exact context_11_84442_1157020
  · exact context_11_84443_1157091

theorem selected_cut_42336 : selected 9 ⟨1157123, by decide⟩
    (prefixPartial 12 337776) = some ⟨12, 2, 0, 1157123, 337776, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_337776_1157123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337776 ⟨1157123, by decide⟩ :=
  accepted_of_selected 12 337776 ⟨1157123, by decide⟩ ⟨12, 2, 0, 1157123, 337776, 1957, 65536⟩
    (by decide) selected_cut_42336

theorem selected_cut_42337 : selected 9 ⟨1157149, by decide⟩
    (prefixPartial 12 337777) = some ⟨12, 2, 0, 1157149, 337777, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_337777_1157149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337777 ⟨1157149, by decide⟩ :=
  accepted_of_selected 12 337777 ⟨1157149, by decide⟩ ⟨12, 2, 0, 1157149, 337777, 1713, 65536⟩
    (by decide) selected_cut_42337

theorem selected_cut_42338 : selected 9 ⟨1157190, by decide⟩
    (prefixPartial 12 337778) = some ⟨12, 2, 0, 1157190, 337778, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_337778_1157190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337778 ⟨1157190, by decide⟩ :=
  accepted_of_selected 12 337778 ⟨1157190, by decide⟩ ⟨12, 2, 0, 1157190, 337778, 2205, 65536⟩
    (by decide) selected_cut_42338

theorem selected_cut_42339 : selected 9 ⟨1157225, by decide⟩
    (prefixPartial 12 337779) = some ⟨12, 2, 0, 1157225, 337779, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_337779_1157225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337779 ⟨1157225, by decide⟩ :=
  accepted_of_selected 12 337779 ⟨1157225, by decide⟩ ⟨12, 2, 0, 1157225, 337779, 2141, 65536⟩
    (by decide) selected_cut_42339

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
