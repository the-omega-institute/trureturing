/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover146
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14116 : selected 9 ⟨366357, by decide⟩
    (prefixPartial 12 27055) = some ⟨12, 2, 0, 366357, 27055, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_27055_366357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27055 ⟨366357, by decide⟩ :=
  accepted_of_selected 12 27055 ⟨366357, by decide⟩ ⟨12, 2, 0, 366357, 27055, 1449, 65536⟩
    (by decide) selected_cut_14116

theorem unmarked_context_11_6763_366358 : frontier 10 ⟨366358, by decide⟩
    (prefixCache 11 6763) (prefixPartial 11 6763) = false := by
  decide +kernel

theorem node_context_11_6763_366358 : EJMOriginalGlobalDAGData.nodes 10 ⟨366358, by decide⟩ =
    .split (coordinate 11) (![⟨366313, by decide⟩,⟨366330, by decide⟩,⟨366345, by decide⟩,⟨366357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6763_366358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6763 ⟨366358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6763
    ⟨366358, by decide⟩ (by decide) (![⟨366313, by decide⟩,⟨366330, by decide⟩,⟨366345, by decide⟩,⟨366357, by decide⟩]) unmarked_context_11_6763_366358 node_context_11_6763_366358
  intro a
  fin_cases a
  · exact context_12_27052_366313
  · exact context_12_27053_366330
  · exact context_12_27054_366345
  · exact context_12_27055_366357

theorem unmarked_context_10_1690_366359 : frontier 11 ⟨366359, by decide⟩
    (prefixCache 10 1690) (prefixPartial 10 1690) = false := by
  decide +kernel

theorem node_context_10_1690_366359 : EJMOriginalGlobalDAGData.nodes 11 ⟨366359, by decide⟩ =
    .split (coordinate 10) (![⟨366189, by decide⟩,⟨366261, by decide⟩,⟨366301, by decide⟩,⟨366358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1690_366359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1690 ⟨366359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1690
    ⟨366359, by decide⟩ (by decide) (![⟨366189, by decide⟩,⟨366261, by decide⟩,⟨366301, by decide⟩,⟨366358, by decide⟩]) unmarked_context_10_1690_366359 node_context_10_1690_366359
  intro a
  fin_cases a
  · exact context_11_6760_366189
  · exact context_11_6761_366261
  · exact context_11_6762_366301
  · exact context_11_6763_366358

theorem selected_cut_14117 : selected 9 ⟨366370, by decide⟩
    (prefixPartial 12 27056) = some ⟨12, 2, 0, 366370, 27056, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_27056_366370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27056 ⟨366370, by decide⟩ :=
  accepted_of_selected 12 27056 ⟨366370, by decide⟩ ⟨12, 2, 0, 366370, 27056, 1529, 65536⟩
    (by decide) selected_cut_14117

theorem selected_cut_14118 : selected 9 ⟨366385, by decide⟩
    (prefixPartial 12 27057) = some ⟨12, 2, 0, 366385, 27057, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_27057_366385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27057 ⟨366385, by decide⟩ :=
  accepted_of_selected 12 27057 ⟨366385, by decide⟩ ⟨12, 2, 0, 366385, 27057, 1625, 65536⟩
    (by decide) selected_cut_14118

theorem selected_cut_14119 : selected 9 ⟨366402, by decide⟩
    (prefixPartial 12 27058) = some ⟨12, 2, 0, 366402, 27058, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_27058_366402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27058 ⟨366402, by decide⟩ :=
  accepted_of_selected 12 27058 ⟨366402, by decide⟩ ⟨12, 2, 0, 366402, 27058, 1597, 65536⟩
    (by decide) selected_cut_14119

theorem selected_cut_14120 : selected 9 ⟨366418, by decide⟩
    (prefixPartial 12 27059) = some ⟨12, 2, 0, 366418, 27059, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_27059_366418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27059 ⟨366418, by decide⟩ :=
  accepted_of_selected 12 27059 ⟨366418, by decide⟩ ⟨12, 2, 0, 366418, 27059, 1565, 65536⟩
    (by decide) selected_cut_14120

theorem unmarked_context_11_6764_366419 : frontier 10 ⟨366419, by decide⟩
    (prefixCache 11 6764) (prefixPartial 11 6764) = false := by
  decide +kernel

theorem node_context_11_6764_366419 : EJMOriginalGlobalDAGData.nodes 10 ⟨366419, by decide⟩ =
    .split (coordinate 11) (![⟨366370, by decide⟩,⟨366385, by decide⟩,⟨366402, by decide⟩,⟨366418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6764_366419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6764 ⟨366419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6764
    ⟨366419, by decide⟩ (by decide) (![⟨366370, by decide⟩,⟨366385, by decide⟩,⟨366402, by decide⟩,⟨366418, by decide⟩]) unmarked_context_11_6764_366419 node_context_11_6764_366419
  intro a
  fin_cases a
  · exact context_12_27056_366370
  · exact context_12_27057_366385
  · exact context_12_27058_366402
  · exact context_12_27059_366418

theorem selected_cut_14121 : selected 9 ⟨366429, by decide⟩
    (prefixPartial 12 27060) = some ⟨12, 2, 0, 366429, 27060, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_27060_366429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27060 ⟨366429, by decide⟩ :=
  accepted_of_selected 12 27060 ⟨366429, by decide⟩ ⟨12, 2, 0, 366429, 27060, 1345, 65536⟩
    (by decide) selected_cut_14121

theorem selected_cut_14122 : selected 9 ⟨366447, by decide⟩
    (prefixPartial 12 27061) = some ⟨12, 2, 0, 366447, 27061, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_27061_366447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27061 ⟨366447, by decide⟩ :=
  accepted_of_selected 12 27061 ⟨366447, by decide⟩ ⟨12, 2, 0, 366447, 27061, 1701, 65536⟩
    (by decide) selected_cut_14122

theorem selected_cut_14123 : selected 9 ⟨366460, by decide⟩
    (prefixPartial 12 27062) = some ⟨12, 2, 0, 366460, 27062, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_27062_366460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27062 ⟨366460, by decide⟩ :=
  accepted_of_selected 12 27062 ⟨366460, by decide⟩ ⟨12, 2, 0, 366460, 27062, 1321, 65536⟩
    (by decide) selected_cut_14123

theorem selected_cut_14124 : selected 9 ⟨366472, by decide⟩
    (prefixPartial 12 27063) = some ⟨12, 2, 0, 366472, 27063, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_27063_366472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27063 ⟨366472, by decide⟩ :=
  accepted_of_selected 12 27063 ⟨366472, by decide⟩ ⟨12, 2, 0, 366472, 27063, 1249, 65536⟩
    (by decide) selected_cut_14124

theorem unmarked_context_11_6765_366473 : frontier 10 ⟨366473, by decide⟩
    (prefixCache 11 6765) (prefixPartial 11 6765) = false := by
  decide +kernel

theorem node_context_11_6765_366473 : EJMOriginalGlobalDAGData.nodes 10 ⟨366473, by decide⟩ =
    .split (coordinate 11) (![⟨366429, by decide⟩,⟨366447, by decide⟩,⟨366460, by decide⟩,⟨366472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6765_366473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6765 ⟨366473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6765
    ⟨366473, by decide⟩ (by decide) (![⟨366429, by decide⟩,⟨366447, by decide⟩,⟨366460, by decide⟩,⟨366472, by decide⟩]) unmarked_context_11_6765_366473 node_context_11_6765_366473
  intro a
  fin_cases a
  · exact context_12_27060_366429
  · exact context_12_27061_366447
  · exact context_12_27062_366460
  · exact context_12_27063_366472

theorem selected_cut_14125 : selected 9 ⟨366482, by decide⟩
    (prefixPartial 12 27064) = some ⟨12, 2, 0, 366482, 27064, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_27064_366482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27064 ⟨366482, by decide⟩ :=
  accepted_of_selected 12 27064 ⟨366482, by decide⟩ ⟨12, 2, 0, 366482, 27064, 1293, 65536⟩
    (by decide) selected_cut_14125

theorem selected_cut_14126 : selected 9 ⟨366496, by decide⟩
    (prefixPartial 12 27065) = some ⟨12, 2, 0, 366496, 27065, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_27065_366496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27065 ⟨366496, by decide⟩ :=
  accepted_of_selected 12 27065 ⟨366496, by decide⟩ ⟨12, 2, 0, 366496, 27065, 1297, 65536⟩
    (by decide) selected_cut_14126

theorem selected_cut_14127 : selected 9 ⟨366507, by decide⟩
    (prefixPartial 12 27066) = some ⟨12, 2, 0, 366507, 27066, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_27066_366507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27066 ⟨366507, by decide⟩ :=
  accepted_of_selected 12 27066 ⟨366507, by decide⟩ ⟨12, 2, 0, 366507, 27066, 1245, 65536⟩
    (by decide) selected_cut_14127

theorem selected_cut_14128 : selected 9 ⟨366521, by decide⟩
    (prefixPartial 12 27067) = some ⟨12, 2, 0, 366521, 27067, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_27067_366521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27067 ⟨366521, by decide⟩ :=
  accepted_of_selected 12 27067 ⟨366521, by decide⟩ ⟨12, 2, 0, 366521, 27067, 1169, 65536⟩
    (by decide) selected_cut_14128

theorem unmarked_context_11_6766_366522 : frontier 10 ⟨366522, by decide⟩
    (prefixCache 11 6766) (prefixPartial 11 6766) = false := by
  decide +kernel

theorem node_context_11_6766_366522 : EJMOriginalGlobalDAGData.nodes 10 ⟨366522, by decide⟩ =
    .split (coordinate 11) (![⟨366482, by decide⟩,⟨366496, by decide⟩,⟨366507, by decide⟩,⟨366521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6766_366522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6766 ⟨366522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6766
    ⟨366522, by decide⟩ (by decide) (![⟨366482, by decide⟩,⟨366496, by decide⟩,⟨366507, by decide⟩,⟨366521, by decide⟩]) unmarked_context_11_6766_366522 node_context_11_6766_366522
  intro a
  fin_cases a
  · exact context_12_27064_366482
  · exact context_12_27065_366496
  · exact context_12_27066_366507
  · exact context_12_27067_366521

theorem selected_cut_14129 : selected 9 ⟨366532, by decide⟩
    (prefixPartial 12 27068) = some ⟨12, 2, 0, 366532, 27068, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_27068_366532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27068 ⟨366532, by decide⟩ :=
  accepted_of_selected 12 27068 ⟨366532, by decide⟩ ⟨12, 2, 0, 366532, 27068, 1257, 65536⟩
    (by decide) selected_cut_14129

theorem selected_cut_14130 : selected 9 ⟨366544, by decide⟩
    (prefixPartial 12 27069) = some ⟨12, 2, 0, 366544, 27069, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_27069_366544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27069 ⟨366544, by decide⟩ :=
  accepted_of_selected 12 27069 ⟨366544, by decide⟩ ⟨12, 2, 0, 366544, 27069, 1153, 65536⟩
    (by decide) selected_cut_14130

theorem selected_cut_14131 : selected 9 ⟨366552, by decide⟩
    (prefixPartial 12 27070) = some ⟨12, 2, 0, 366552, 27070, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_27070_366552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27070 ⟨366552, by decide⟩ :=
  accepted_of_selected 12 27070 ⟨366552, by decide⟩ ⟨12, 2, 0, 366552, 27070, 1093, 65536⟩
    (by decide) selected_cut_14131

theorem selected_cut_14132 : selected 9 ⟨366563, by decide⟩
    (prefixPartial 12 27071) = some ⟨12, 2, 0, 366563, 27071, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_27071_366563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27071 ⟨366563, by decide⟩ :=
  accepted_of_selected 12 27071 ⟨366563, by decide⟩ ⟨12, 2, 0, 366563, 27071, 1161, 65536⟩
    (by decide) selected_cut_14132

theorem unmarked_context_11_6767_366564 : frontier 10 ⟨366564, by decide⟩
    (prefixCache 11 6767) (prefixPartial 11 6767) = false := by
  decide +kernel

theorem node_context_11_6767_366564 : EJMOriginalGlobalDAGData.nodes 10 ⟨366564, by decide⟩ =
    .split (coordinate 11) (![⟨366532, by decide⟩,⟨366544, by decide⟩,⟨366552, by decide⟩,⟨366563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6767_366564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6767 ⟨366564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6767
    ⟨366564, by decide⟩ (by decide) (![⟨366532, by decide⟩,⟨366544, by decide⟩,⟨366552, by decide⟩,⟨366563, by decide⟩]) unmarked_context_11_6767_366564 node_context_11_6767_366564
  intro a
  fin_cases a
  · exact context_12_27068_366532
  · exact context_12_27069_366544
  · exact context_12_27070_366552
  · exact context_12_27071_366563

theorem unmarked_context_10_1691_366565 : frontier 11 ⟨366565, by decide⟩
    (prefixCache 10 1691) (prefixPartial 10 1691) = false := by
  decide +kernel

theorem node_context_10_1691_366565 : EJMOriginalGlobalDAGData.nodes 11 ⟨366565, by decide⟩ =
    .split (coordinate 10) (![⟨366419, by decide⟩,⟨366473, by decide⟩,⟨366522, by decide⟩,⟨366564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1691_366565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1691 ⟨366565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1691
    ⟨366565, by decide⟩ (by decide) (![⟨366419, by decide⟩,⟨366473, by decide⟩,⟨366522, by decide⟩,⟨366564, by decide⟩]) unmarked_context_10_1691_366565 node_context_10_1691_366565
  intro a
  fin_cases a
  · exact context_11_6764_366419
  · exact context_11_6765_366473
  · exact context_11_6766_366522
  · exact context_11_6767_366564

theorem unmarked_context_9_422_366566 : frontier 12 ⟨366566, by decide⟩
    (prefixCache 9 422) (prefixPartial 9 422) = false := by
  decide +kernel

theorem node_context_9_422_366566 : EJMOriginalGlobalDAGData.nodes 12 ⟨366566, by decide⟩ =
    .split (coordinate 9) (![⟨365793, by decide⟩,⟨366109, by decide⟩,⟨366359, by decide⟩,⟨366565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_422_366566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 422 ⟨366566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 422
    ⟨366566, by decide⟩ (by decide) (![⟨365793, by decide⟩,⟨366109, by decide⟩,⟨366359, by decide⟩,⟨366565, by decide⟩]) unmarked_context_9_422_366566 node_context_9_422_366566
  intro a
  fin_cases a
  · exact context_10_1688_365793
  · exact context_10_1689_366109
  · exact context_10_1690_366359
  · exact context_10_1691_366565

theorem selected_cut_14133 : selected 9 ⟨366574, by decide⟩
    (prefixPartial 12 27072) = some ⟨12, 2, 0, 366574, 27072, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_27072_366574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27072 ⟨366574, by decide⟩ :=
  accepted_of_selected 12 27072 ⟨366574, by decide⟩ ⟨12, 2, 0, 366574, 27072, 1037, 65536⟩
    (by decide) selected_cut_14133

theorem selected_cut_14134 : selected 9 ⟨366581, by decide⟩
    (prefixPartial 12 27073) = some ⟨12, 2, 0, 366581, 27073, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_27073_366581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27073 ⟨366581, by decide⟩ :=
  accepted_of_selected 12 27073 ⟨366581, by decide⟩ ⟨12, 2, 0, 366581, 27073, 1161, 65536⟩
    (by decide) selected_cut_14134

theorem selected_cut_14135 : selected 9 ⟨366589, by decide⟩
    (prefixPartial 12 27074) = some ⟨12, 2, 0, 366589, 27074, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_27074_366589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27074 ⟨366589, by decide⟩ :=
  accepted_of_selected 12 27074 ⟨366589, by decide⟩ ⟨12, 2, 0, 366589, 27074, 1145, 65536⟩
    (by decide) selected_cut_14135

theorem selected_cut_14136 : selected 9 ⟨366595, by decide⟩
    (prefixPartial 12 27075) = some ⟨12, 2, 0, 366595, 27075, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_27075_366595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27075 ⟨366595, by decide⟩ :=
  accepted_of_selected 12 27075 ⟨366595, by decide⟩ ⟨12, 2, 0, 366595, 27075, 1049, 65536⟩
    (by decide) selected_cut_14136

theorem unmarked_context_11_6768_366596 : frontier 10 ⟨366596, by decide⟩
    (prefixCache 11 6768) (prefixPartial 11 6768) = false := by
  decide +kernel

theorem node_context_11_6768_366596 : EJMOriginalGlobalDAGData.nodes 10 ⟨366596, by decide⟩ =
    .split (coordinate 11) (![⟨366574, by decide⟩,⟨366581, by decide⟩,⟨366589, by decide⟩,⟨366595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6768_366596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6768 ⟨366596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6768
    ⟨366596, by decide⟩ (by decide) (![⟨366574, by decide⟩,⟨366581, by decide⟩,⟨366589, by decide⟩,⟨366595, by decide⟩]) unmarked_context_11_6768_366596 node_context_11_6768_366596
  intro a
  fin_cases a
  · exact context_12_27072_366574
  · exact context_12_27073_366581
  · exact context_12_27074_366589
  · exact context_12_27075_366595

theorem selected_cut_14137 : selected 10 ⟨366633, by decide⟩
    (prefixPartial 11 6769) = some ⟨11, 2, 0, 366633, 6769, 3969, 262144⟩ := by
  decide +kernel

theorem context_11_6769_366633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6769 ⟨366633, by decide⟩ :=
  accepted_of_selected 11 6769 ⟨366633, by decide⟩ ⟨11, 2, 0, 366633, 6769, 3969, 262144⟩
    (by decide) selected_cut_14137

theorem selected_cut_14138 : selected 10 ⟨366660, by decide⟩
    (prefixPartial 11 6770) = some ⟨11, 2, 0, 366660, 6770, 3601, 262144⟩ := by
  decide +kernel

theorem context_11_6770_366660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6770 ⟨366660, by decide⟩ :=
  accepted_of_selected 11 6770 ⟨366660, by decide⟩ ⟨11, 2, 0, 366660, 6770, 3601, 262144⟩
    (by decide) selected_cut_14138

theorem selected_cut_14139 : selected 10 ⟨366703, by decide⟩
    (prefixPartial 11 6771) = some ⟨11, 2, 0, 366703, 6771, 3441, 262144⟩ := by
  decide +kernel

theorem context_11_6771_366703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6771 ⟨366703, by decide⟩ :=
  accepted_of_selected 11 6771 ⟨366703, by decide⟩ ⟨11, 2, 0, 366703, 6771, 3441, 262144⟩
    (by decide) selected_cut_14139

theorem unmarked_context_10_1692_366704 : frontier 11 ⟨366704, by decide⟩
    (prefixCache 10 1692) (prefixPartial 10 1692) = false := by
  decide +kernel

theorem node_context_10_1692_366704 : EJMOriginalGlobalDAGData.nodes 11 ⟨366704, by decide⟩ =
    .split (coordinate 10) (![⟨366596, by decide⟩,⟨366633, by decide⟩,⟨366660, by decide⟩,⟨366703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1692_366704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1692 ⟨366704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1692
    ⟨366704, by decide⟩ (by decide) (![⟨366596, by decide⟩,⟨366633, by decide⟩,⟨366660, by decide⟩,⟨366703, by decide⟩]) unmarked_context_10_1692_366704 node_context_10_1692_366704
  intro a
  fin_cases a
  · exact context_11_6768_366596
  · exact context_11_6769_366633
  · exact context_11_6770_366660
  · exact context_11_6771_366703

theorem selected_cut_14140 : selected 10 ⟨366739, by decide⟩
    (prefixPartial 11 6772) = some ⟨11, 2, 0, 366739, 6772, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_6772_366739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6772 ⟨366739, by decide⟩ :=
  accepted_of_selected 11 6772 ⟨366739, by decide⟩ ⟨11, 2, 0, 366739, 6772, 2897, 262144⟩
    (by decide) selected_cut_14140

theorem selected_cut_14141 : selected 10 ⟨366753, by decide⟩
    (prefixPartial 11 6773) = some ⟨11, 2, 0, 366753, 6773, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_6773_366753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6773 ⟨366753, by decide⟩ :=
  accepted_of_selected 11 6773 ⟨366753, by decide⟩ ⟨11, 2, 0, 366753, 6773, 1769, 262144⟩
    (by decide) selected_cut_14141

theorem selected_cut_14142 : selected 10 ⟨366771, by decide⟩
    (prefixPartial 11 6774) = some ⟨11, 2, 0, 366771, 6774, 2221, 262144⟩ := by
  decide +kernel

theorem context_11_6774_366771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6774 ⟨366771, by decide⟩ :=
  accepted_of_selected 11 6774 ⟨366771, by decide⟩ ⟨11, 2, 0, 366771, 6774, 2221, 262144⟩
    (by decide) selected_cut_14142

theorem selected_cut_14143 : selected 10 ⟨366791, by decide⟩
    (prefixPartial 11 6775) = some ⟨11, 2, 0, 366791, 6775, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_6775_366791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6775 ⟨366791, by decide⟩ :=
  accepted_of_selected 11 6775 ⟨366791, by decide⟩ ⟨11, 2, 0, 366791, 6775, 1949, 262144⟩
    (by decide) selected_cut_14143

theorem unmarked_context_10_1693_366792 : frontier 11 ⟨366792, by decide⟩
    (prefixCache 10 1693) (prefixPartial 10 1693) = false := by
  decide +kernel

theorem node_context_10_1693_366792 : EJMOriginalGlobalDAGData.nodes 11 ⟨366792, by decide⟩ =
    .split (coordinate 10) (![⟨366739, by decide⟩,⟨366753, by decide⟩,⟨366771, by decide⟩,⟨366791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1693_366792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1693 ⟨366792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1693
    ⟨366792, by decide⟩ (by decide) (![⟨366739, by decide⟩,⟨366753, by decide⟩,⟨366771, by decide⟩,⟨366791, by decide⟩]) unmarked_context_10_1693_366792 node_context_10_1693_366792
  intro a
  fin_cases a
  · exact context_11_6772_366739
  · exact context_11_6773_366753
  · exact context_11_6774_366771
  · exact context_11_6775_366791

theorem selected_cut_14144 : selected 10 ⟨366806, by decide⟩
    (prefixPartial 11 6776) = some ⟨11, 2, 0, 366806, 6776, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_6776_366806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6776 ⟨366806, by decide⟩ :=
  accepted_of_selected 11 6776 ⟨366806, by decide⟩ ⟨11, 2, 0, 366806, 6776, 1809, 262144⟩
    (by decide) selected_cut_14144

theorem selected_cut_14145 : selected 10 ⟨366824, by decide⟩
    (prefixPartial 11 6777) = some ⟨11, 2, 0, 366824, 6777, 1485, 262144⟩ := by
  decide +kernel

theorem context_11_6777_366824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6777 ⟨366824, by decide⟩ :=
  accepted_of_selected 11 6777 ⟨366824, by decide⟩ ⟨11, 2, 0, 366824, 6777, 1485, 262144⟩
    (by decide) selected_cut_14145

theorem selected_cut_14146 : selected 10 ⟨366843, by decide⟩
    (prefixPartial 11 6778) = some ⟨11, 2, 0, 366843, 6778, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_6778_366843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6778 ⟨366843, by decide⟩ :=
  accepted_of_selected 11 6778 ⟨366843, by decide⟩ ⟨11, 2, 0, 366843, 6778, 1453, 262144⟩
    (by decide) selected_cut_14146

theorem selected_cut_14147 : selected 10 ⟨366855, by decide⟩
    (prefixPartial 11 6779) = some ⟨11, 2, 0, 366855, 6779, 917, 262144⟩ := by
  decide +kernel

theorem context_11_6779_366855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6779 ⟨366855, by decide⟩ :=
  accepted_of_selected 11 6779 ⟨366855, by decide⟩ ⟨11, 2, 0, 366855, 6779, 917, 262144⟩
    (by decide) selected_cut_14147

theorem unmarked_context_10_1694_366856 : frontier 11 ⟨366856, by decide⟩
    (prefixCache 10 1694) (prefixPartial 10 1694) = false := by
  decide +kernel

theorem node_context_10_1694_366856 : EJMOriginalGlobalDAGData.nodes 11 ⟨366856, by decide⟩ =
    .split (coordinate 10) (![⟨366806, by decide⟩,⟨366824, by decide⟩,⟨366843, by decide⟩,⟨366855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1694_366856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1694 ⟨366856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1694
    ⟨366856, by decide⟩ (by decide) (![⟨366806, by decide⟩,⟨366824, by decide⟩,⟨366843, by decide⟩,⟨366855, by decide⟩]) unmarked_context_10_1694_366856 node_context_10_1694_366856
  intro a
  fin_cases a
  · exact context_11_6776_366806
  · exact context_11_6777_366824
  · exact context_11_6778_366843
  · exact context_11_6779_366855

theorem selected_cut_14148 : selected 11 ⟨366889, by decide⟩
    (prefixPartial 10 1695) = some ⟨10, 2, 0, 366889, 1695, 1909, 1048576⟩ := by
  decide +kernel

theorem context_10_1695_366889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1695 ⟨366889, by decide⟩ :=
  accepted_of_selected 10 1695 ⟨366889, by decide⟩ ⟨10, 2, 0, 366889, 1695, 1909, 1048576⟩
    (by decide) selected_cut_14148

theorem unmarked_context_9_423_366890 : frontier 12 ⟨366890, by decide⟩
    (prefixCache 9 423) (prefixPartial 9 423) = false := by
  decide +kernel

theorem node_context_9_423_366890 : EJMOriginalGlobalDAGData.nodes 12 ⟨366890, by decide⟩ =
    .split (coordinate 9) (![⟨366704, by decide⟩,⟨366792, by decide⟩,⟨366856, by decide⟩,⟨366889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_423_366890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 423 ⟨366890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 423
    ⟨366890, by decide⟩ (by decide) (![⟨366704, by decide⟩,⟨366792, by decide⟩,⟨366856, by decide⟩,⟨366889, by decide⟩]) unmarked_context_9_423_366890 node_context_9_423_366890
  intro a
  fin_cases a
  · exact context_10_1692_366704
  · exact context_10_1693_366792
  · exact context_10_1694_366856
  · exact context_10_1695_366889

theorem unmarked_context_8_105_366891 : frontier 13 ⟨366891, by decide⟩
    (prefixCache 8 105) (prefixPartial 8 105) = false := by
  decide +kernel

theorem node_context_8_105_366891 : EJMOriginalGlobalDAGData.nodes 13 ⟨366891, by decide⟩ =
    .split (coordinate 8) (![⟨362718, by decide⟩,⟨365367, by decide⟩,⟨366566, by decide⟩,⟨366890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_105_366891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 105 ⟨366891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 105
    ⟨366891, by decide⟩ (by decide) (![⟨362718, by decide⟩,⟨365367, by decide⟩,⟨366566, by decide⟩,⟨366890, by decide⟩]) unmarked_context_8_105_366891 node_context_8_105_366891
  intro a
  fin_cases a
  · exact context_9_420_362718
  · exact context_9_421_365367
  · exact context_9_422_366566
  · exact context_9_423_366890

theorem selected_cut_14149 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27136) = some ⟨12, 1, 0, 34034, 27136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27136_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27136 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27136 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27136, 1, 65536⟩
    (by decide) selected_cut_14149

theorem selected_cut_14150 : selected 9 ⟨48867, by decide⟩
    (prefixPartial 12 27137) = some ⟨12, 1, 0, 48867, 27137, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27137_48867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27137 ⟨48867, by decide⟩ :=
  accepted_of_selected 12 27137 ⟨48867, by decide⟩ ⟨12, 1, 0, 48867, 27137, 1, 65536⟩
    (by decide) selected_cut_14150

theorem selected_cut_14151 : selected 9 ⟨347601, by decide⟩
    (prefixPartial 12 27138) = some ⟨12, 1, 0, 347601, 27138, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27138_347601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27138 ⟨347601, by decide⟩ :=
  accepted_of_selected 12 27138 ⟨347601, by decide⟩ ⟨12, 1, 0, 347601, 27138, 1, 65536⟩
    (by decide) selected_cut_14151

theorem selected_cut_14152 : selected 7 ⟨366922, by decide⟩
    (prefixPartial 14 434224) = some ⟨14, 2, 0, 366922, 434224, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_434224_366922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434224 ⟨366922, by decide⟩ :=
  accepted_of_selected 14 434224 ⟨366922, by decide⟩ ⟨14, 2, 0, 366922, 434224, 1285, 4096⟩
    (by decide) selected_cut_14152

theorem selected_cut_14153 : selected 7 ⟨366936, by decide⟩
    (prefixPartial 14 434225) = some ⟨14, 2, 0, 366936, 434225, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_434225_366936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434225 ⟨366936, by decide⟩ :=
  accepted_of_selected 14 434225 ⟨366936, by decide⟩ ⟨14, 2, 0, 366936, 434225, 1157, 4096⟩
    (by decide) selected_cut_14153

theorem selected_cut_14154 : selected 7 ⟨366945, by decide⟩
    (prefixPartial 14 434226) = some ⟨14, 2, 0, 366945, 434226, 905, 4096⟩ := by
  decide +kernel

theorem context_14_434226_366945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434226 ⟨366945, by decide⟩ :=
  accepted_of_selected 14 434226 ⟨366945, by decide⟩ ⟨14, 2, 0, 366945, 434226, 905, 4096⟩
    (by decide) selected_cut_14154

theorem selected_cut_14155 : selected 7 ⟨366961, by decide⟩
    (prefixPartial 14 434227) = some ⟨14, 2, 0, 366961, 434227, 1141, 4096⟩ := by
  decide +kernel

theorem context_14_434227_366961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434227 ⟨366961, by decide⟩ :=
  accepted_of_selected 14 434227 ⟨366961, by decide⟩ ⟨14, 2, 0, 366961, 434227, 1141, 4096⟩
    (by decide) selected_cut_14155

theorem unmarked_context_13_108556_366962 : frontier 8 ⟨366962, by decide⟩
    (prefixCache 13 108556) (prefixPartial 13 108556) = false := by
  decide +kernel

theorem node_context_13_108556_366962 : EJMOriginalGlobalDAGData.nodes 8 ⟨366962, by decide⟩ =
    .split (coordinate 13) (![⟨366922, by decide⟩,⟨366936, by decide⟩,⟨366945, by decide⟩,⟨366961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_108556_366962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108556 ⟨366962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 108556
    ⟨366962, by decide⟩ (by decide) (![⟨366922, by decide⟩,⟨366936, by decide⟩,⟨366945, by decide⟩,⟨366961, by decide⟩]) unmarked_context_13_108556_366962 node_context_13_108556_366962
  intro a
  fin_cases a
  · exact context_14_434224_366922
  · exact context_14_434225_366936
  · exact context_14_434226_366945
  · exact context_14_434227_366961

theorem selected_cut_14156 : selected 8 ⟨367044, by decide⟩
    (prefixPartial 13 108557) = some ⟨13, 2, 0, 367044, 108557, 4005, 16384⟩ := by
  decide +kernel

theorem context_13_108557_367044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108557 ⟨367044, by decide⟩ :=
  accepted_of_selected 13 108557 ⟨367044, by decide⟩ ⟨13, 2, 0, 367044, 108557, 4005, 16384⟩
    (by decide) selected_cut_14156

theorem selected_cut_14157 : selected 8 ⟨367072, by decide⟩
    (prefixPartial 13 108558) = some ⟨13, 2, 0, 367072, 108558, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_108558_367072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108558 ⟨367072, by decide⟩ :=
  accepted_of_selected 13 108558 ⟨367072, by decide⟩ ⟨13, 2, 0, 367072, 108558, 1917, 16384⟩
    (by decide) selected_cut_14157

theorem selected_cut_14158 : selected 8 ⟨367089, by decide⟩
    (prefixPartial 13 108559) = some ⟨13, 2, 0, 367089, 108559, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_108559_367089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108559 ⟨367089, by decide⟩ :=
  accepted_of_selected 13 108559 ⟨367089, by decide⟩ ⟨13, 2, 0, 367089, 108559, 1253, 16384⟩
    (by decide) selected_cut_14158

theorem unmarked_context_12_27139_367090 : frontier 9 ⟨367090, by decide⟩
    (prefixCache 12 27139) (prefixPartial 12 27139) = false := by
  decide +kernel

theorem node_context_12_27139_367090 : EJMOriginalGlobalDAGData.nodes 9 ⟨367090, by decide⟩ =
    .split (coordinate 12) (![⟨366962, by decide⟩,⟨367044, by decide⟩,⟨367072, by decide⟩,⟨367089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27139_367090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27139 ⟨367090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27139
    ⟨367090, by decide⟩ (by decide) (![⟨366962, by decide⟩,⟨367044, by decide⟩,⟨367072, by decide⟩,⟨367089, by decide⟩]) unmarked_context_12_27139_367090 node_context_12_27139_367090
  intro a
  fin_cases a
  · exact context_13_108556_366962
  · exact context_13_108557_367044
  · exact context_13_108558_367072
  · exact context_13_108559_367089

theorem unmarked_context_11_6784_367091 : frontier 10 ⟨367091, by decide⟩
    (prefixCache 11 6784) (prefixPartial 11 6784) = false := by
  decide +kernel

theorem node_context_11_6784_367091 : EJMOriginalGlobalDAGData.nodes 10 ⟨367091, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨48867, by decide⟩,⟨347601, by decide⟩,⟨367090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6784_367091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6784 ⟨367091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6784
    ⟨367091, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨48867, by decide⟩,⟨347601, by decide⟩,⟨367090, by decide⟩]) unmarked_context_11_6784_367091 node_context_11_6784_367091
  intro a
  fin_cases a
  · exact context_12_27136_34034
  · exact context_12_27137_48867
  · exact context_12_27138_347601
  · exact context_12_27139_367090

theorem selected_cut_14159 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27140) = some ⟨12, 1, 0, 34034, 27140, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27140_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27140 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27140 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27140, 1, 65536⟩
    (by decide) selected_cut_14159

theorem selected_cut_14160 : selected 7 ⟨367110, by decide⟩
    (prefixPartial 14 434256) = some ⟨14, 2, 0, 367110, 434256, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_434256_367110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434256 ⟨367110, by decide⟩ :=
  accepted_of_selected 14 434256 ⟨367110, by decide⟩ ⟨14, 2, 0, 367110, 434256, 1217, 4096⟩
    (by decide) selected_cut_14160

theorem selected_cut_14161 : selected 7 ⟨367125, by decide⟩
    (prefixPartial 14 434257) = some ⟨14, 2, 0, 367125, 434257, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_434257_367125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434257 ⟨367125, by decide⟩ :=
  accepted_of_selected 14 434257 ⟨367125, by decide⟩ ⟨14, 2, 0, 367125, 434257, 1113, 4096⟩
    (by decide) selected_cut_14161

theorem selected_cut_14162 : selected 7 ⟨367136, by decide⟩
    (prefixPartial 14 434258) = some ⟨14, 2, 0, 367136, 434258, 837, 4096⟩ := by
  decide +kernel

theorem context_14_434258_367136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434258 ⟨367136, by decide⟩ :=
  accepted_of_selected 14 434258 ⟨367136, by decide⟩ ⟨14, 2, 0, 367136, 434258, 837, 4096⟩
    (by decide) selected_cut_14162

theorem selected_cut_14163 : selected 7 ⟨367147, by decide⟩
    (prefixPartial 14 434259) = some ⟨14, 2, 0, 367147, 434259, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_434259_367147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434259 ⟨367147, by decide⟩ :=
  accepted_of_selected 14 434259 ⟨367147, by decide⟩ ⟨14, 2, 0, 367147, 434259, 1033, 4096⟩
    (by decide) selected_cut_14163

theorem unmarked_context_13_108564_367148 : frontier 8 ⟨367148, by decide⟩
    (prefixCache 13 108564) (prefixPartial 13 108564) = false := by
  decide +kernel

theorem node_context_13_108564_367148 : EJMOriginalGlobalDAGData.nodes 8 ⟨367148, by decide⟩ =
    .split (coordinate 13) (![⟨367110, by decide⟩,⟨367125, by decide⟩,⟨367136, by decide⟩,⟨367147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_108564_367148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108564 ⟨367148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 108564
    ⟨367148, by decide⟩ (by decide) (![⟨367110, by decide⟩,⟨367125, by decide⟩,⟨367136, by decide⟩,⟨367147, by decide⟩]) unmarked_context_13_108564_367148 node_context_13_108564_367148
  intro a
  fin_cases a
  · exact context_14_434256_367110
  · exact context_14_434257_367125
  · exact context_14_434258_367136
  · exact context_14_434259_367147

theorem selected_cut_14164 : selected 8 ⟨367199, by decide⟩
    (prefixPartial 13 108565) = some ⟨13, 2, 0, 367199, 108565, 3309, 16384⟩ := by
  decide +kernel

theorem context_13_108565_367199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108565 ⟨367199, by decide⟩ :=
  accepted_of_selected 13 108565 ⟨367199, by decide⟩ ⟨13, 2, 0, 367199, 108565, 3309, 16384⟩
    (by decide) selected_cut_14164

theorem selected_cut_14165 : selected 8 ⟨367224, by decide⟩
    (prefixPartial 13 108566) = some ⟨13, 2, 0, 367224, 108566, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_108566_367224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108566 ⟨367224, by decide⟩ :=
  accepted_of_selected 13 108566 ⟨367224, by decide⟩ ⟨13, 2, 0, 367224, 108566, 1917, 16384⟩
    (by decide) selected_cut_14165

theorem selected_cut_14166 : selected 8 ⟨367232, by decide⟩
    (prefixPartial 13 108567) = some ⟨13, 2, 0, 367232, 108567, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_108567_367232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108567 ⟨367232, by decide⟩ :=
  accepted_of_selected 13 108567 ⟨367232, by decide⟩ ⟨13, 2, 0, 367232, 108567, 1237, 16384⟩
    (by decide) selected_cut_14166

theorem unmarked_context_12_27141_367233 : frontier 9 ⟨367233, by decide⟩
    (prefixCache 12 27141) (prefixPartial 12 27141) = false := by
  decide +kernel

theorem node_context_12_27141_367233 : EJMOriginalGlobalDAGData.nodes 9 ⟨367233, by decide⟩ =
    .split (coordinate 12) (![⟨367148, by decide⟩,⟨367199, by decide⟩,⟨367224, by decide⟩,⟨367232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27141_367233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27141 ⟨367233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27141
    ⟨367233, by decide⟩ (by decide) (![⟨367148, by decide⟩,⟨367199, by decide⟩,⟨367224, by decide⟩,⟨367232, by decide⟩]) unmarked_context_12_27141_367233 node_context_12_27141_367233
  intro a
  fin_cases a
  · exact context_13_108564_367148
  · exact context_13_108565_367199
  · exact context_13_108566_367224
  · exact context_13_108567_367232

theorem selected_cut_14167 : selected 8 ⟨367274, by decide⟩
    (prefixPartial 13 108568) = some ⟨13, 2, 0, 367274, 108568, 3325, 16384⟩ := by
  decide +kernel

theorem context_13_108568_367274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108568 ⟨367274, by decide⟩ :=
  accepted_of_selected 13 108568 ⟨367274, by decide⟩ ⟨13, 2, 0, 367274, 108568, 3325, 16384⟩
    (by decide) selected_cut_14167

theorem selected_cut_14168 : selected 8 ⟨367328, by decide⟩
    (prefixPartial 13 108569) = some ⟨13, 2, 0, 367328, 108569, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_108569_367328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108569 ⟨367328, by decide⟩ :=
  accepted_of_selected 13 108569 ⟨367328, by decide⟩ ⟨13, 2, 0, 367328, 108569, 3477, 16384⟩
    (by decide) selected_cut_14168

theorem selected_cut_14169 : selected 8 ⟨367367, by decide⟩
    (prefixPartial 13 108570) = some ⟨13, 2, 0, 367367, 108570, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_108570_367367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108570 ⟨367367, by decide⟩ :=
  accepted_of_selected 13 108570 ⟨367367, by decide⟩ ⟨13, 2, 0, 367367, 108570, 2073, 16384⟩
    (by decide) selected_cut_14169

theorem selected_cut_14170 : selected 8 ⟨367373, by decide⟩
    (prefixPartial 13 108571) = some ⟨13, 2, 0, 367373, 108571, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_108571_367373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108571 ⟨367373, by decide⟩ :=
  accepted_of_selected 13 108571 ⟨367373, by decide⟩ ⟨13, 2, 0, 367373, 108571, 1233, 16384⟩
    (by decide) selected_cut_14170

theorem unmarked_context_12_27142_367374 : frontier 9 ⟨367374, by decide⟩
    (prefixCache 12 27142) (prefixPartial 12 27142) = false := by
  decide +kernel

theorem node_context_12_27142_367374 : EJMOriginalGlobalDAGData.nodes 9 ⟨367374, by decide⟩ =
    .split (coordinate 12) (![⟨367274, by decide⟩,⟨367328, by decide⟩,⟨367367, by decide⟩,⟨367373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27142_367374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27142 ⟨367374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27142
    ⟨367374, by decide⟩ (by decide) (![⟨367274, by decide⟩,⟨367328, by decide⟩,⟨367367, by decide⟩,⟨367373, by decide⟩]) unmarked_context_12_27142_367374 node_context_12_27142_367374
  intro a
  fin_cases a
  · exact context_13_108568_367274
  · exact context_13_108569_367328
  · exact context_13_108570_367367
  · exact context_13_108571_367373

theorem selected_cut_14171 : selected 7 ⟨367399, by decide⟩
    (prefixPartial 14 434288) = some ⟨14, 2, 0, 367399, 434288, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_434288_367399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434288 ⟨367399, by decide⟩ :=
  accepted_of_selected 14 434288 ⟨367399, by decide⟩ ⟨14, 2, 0, 367399, 434288, 1081, 4096⟩
    (by decide) selected_cut_14171

theorem selected_cut_14172 : selected 7 ⟨367415, by decide⟩
    (prefixPartial 14 434289) = some ⟨14, 2, 0, 367415, 434289, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_434289_367415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434289 ⟨367415, by decide⟩ :=
  accepted_of_selected 14 434289 ⟨367415, by decide⟩ ⟨14, 2, 0, 367415, 434289, 1229, 4096⟩
    (by decide) selected_cut_14172

theorem selected_cut_14173 : selected 7 ⟨367425, by decide⟩
    (prefixPartial 14 434290) = some ⟨14, 2, 0, 367425, 434290, 969, 4096⟩ := by
  decide +kernel

theorem context_14_434290_367425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434290 ⟨367425, by decide⟩ :=
  accepted_of_selected 14 434290 ⟨367425, by decide⟩ ⟨14, 2, 0, 367425, 434290, 969, 4096⟩
    (by decide) selected_cut_14173

theorem selected_cut_14174 : selected 7 ⟨367444, by decide⟩
    (prefixPartial 14 434291) = some ⟨14, 2, 0, 367444, 434291, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_434291_367444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434291 ⟨367444, by decide⟩ :=
  accepted_of_selected 14 434291 ⟨367444, by decide⟩ ⟨14, 2, 0, 367444, 434291, 1181, 4096⟩
    (by decide) selected_cut_14174

theorem unmarked_context_13_108572_367445 : frontier 8 ⟨367445, by decide⟩
    (prefixCache 13 108572) (prefixPartial 13 108572) = false := by
  decide +kernel

theorem node_context_13_108572_367445 : EJMOriginalGlobalDAGData.nodes 8 ⟨367445, by decide⟩ =
    .split (coordinate 13) (![⟨367399, by decide⟩,⟨367415, by decide⟩,⟨367425, by decide⟩,⟨367444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_108572_367445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108572 ⟨367445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 108572
    ⟨367445, by decide⟩ (by decide) (![⟨367399, by decide⟩,⟨367415, by decide⟩,⟨367425, by decide⟩,⟨367444, by decide⟩]) unmarked_context_13_108572_367445 node_context_13_108572_367445
  intro a
  fin_cases a
  · exact context_14_434288_367399
  · exact context_14_434289_367415
  · exact context_14_434290_367425
  · exact context_14_434291_367444

theorem selected_cut_14175 : selected 8 ⟨367513, by decide⟩
    (prefixPartial 13 108573) = some ⟨13, 2, 0, 367513, 108573, 3965, 16384⟩ := by
  decide +kernel

theorem context_13_108573_367513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108573 ⟨367513, by decide⟩ :=
  accepted_of_selected 13 108573 ⟨367513, by decide⟩ ⟨13, 2, 0, 367513, 108573, 3965, 16384⟩
    (by decide) selected_cut_14175

theorem selected_cut_14176 : selected 8 ⟨367551, by decide⟩
    (prefixPartial 13 108574) = some ⟨13, 2, 0, 367551, 108574, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_108574_367551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108574 ⟨367551, by decide⟩ :=
  accepted_of_selected 13 108574 ⟨367551, by decide⟩ ⟨13, 2, 0, 367551, 108574, 2181, 16384⟩
    (by decide) selected_cut_14176

theorem selected_cut_14177 : selected 8 ⟨367570, by decide⟩
    (prefixPartial 13 108575) = some ⟨13, 2, 0, 367570, 108575, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_108575_367570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108575 ⟨367570, by decide⟩ :=
  accepted_of_selected 13 108575 ⟨367570, by decide⟩ ⟨13, 2, 0, 367570, 108575, 1397, 16384⟩
    (by decide) selected_cut_14177

theorem unmarked_context_12_27143_367571 : frontier 9 ⟨367571, by decide⟩
    (prefixCache 12 27143) (prefixPartial 12 27143) = false := by
  decide +kernel

theorem node_context_12_27143_367571 : EJMOriginalGlobalDAGData.nodes 9 ⟨367571, by decide⟩ =
    .split (coordinate 12) (![⟨367445, by decide⟩,⟨367513, by decide⟩,⟨367551, by decide⟩,⟨367570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27143_367571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27143 ⟨367571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27143
    ⟨367571, by decide⟩ (by decide) (![⟨367445, by decide⟩,⟨367513, by decide⟩,⟨367551, by decide⟩,⟨367570, by decide⟩]) unmarked_context_12_27143_367571 node_context_12_27143_367571
  intro a
  fin_cases a
  · exact context_13_108572_367445
  · exact context_13_108573_367513
  · exact context_13_108574_367551
  · exact context_13_108575_367570

theorem unmarked_context_11_6785_367572 : frontier 10 ⟨367572, by decide⟩
    (prefixCache 11 6785) (prefixPartial 11 6785) = false := by
  decide +kernel

theorem node_context_11_6785_367572 : EJMOriginalGlobalDAGData.nodes 10 ⟨367572, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨367233, by decide⟩,⟨367374, by decide⟩,⟨367571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6785_367572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6785 ⟨367572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6785
    ⟨367572, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨367233, by decide⟩,⟨367374, by decide⟩,⟨367571, by decide⟩]) unmarked_context_11_6785_367572 node_context_11_6785_367572
  intro a
  fin_cases a
  · exact context_12_27140_34034
  · exact context_12_27141_367233
  · exact context_12_27142_367374
  · exact context_12_27143_367571

theorem selected_cut_14178 : selected 8 ⟨367624, by decide⟩
    (prefixPartial 13 108576) = some ⟨13, 2, 0, 367624, 108576, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_108576_367624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108576 ⟨367624, by decide⟩ :=
  accepted_of_selected 13 108576 ⟨367624, by decide⟩ ⟨13, 2, 0, 367624, 108576, 3101, 16384⟩
    (by decide) selected_cut_14178

theorem selected_cut_14179 : selected 8 ⟨367697, by decide⟩
    (prefixPartial 13 108577) = some ⟨13, 2, 0, 367697, 108577, 3741, 16384⟩ := by
  decide +kernel

theorem context_13_108577_367697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108577 ⟨367697, by decide⟩ :=
  accepted_of_selected 13 108577 ⟨367697, by decide⟩ ⟨13, 2, 0, 367697, 108577, 3741, 16384⟩
    (by decide) selected_cut_14179

theorem selected_cut_14180 : selected 8 ⟨367724, by decide⟩
    (prefixPartial 13 108578) = some ⟨13, 2, 0, 367724, 108578, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_108578_367724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108578 ⟨367724, by decide⟩ :=
  accepted_of_selected 13 108578 ⟨367724, by decide⟩ ⟨13, 2, 0, 367724, 108578, 1801, 16384⟩
    (by decide) selected_cut_14180

theorem selected_cut_14181 : selected 8 ⟨367742, by decide⟩
    (prefixPartial 13 108579) = some ⟨13, 2, 0, 367742, 108579, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_108579_367742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108579 ⟨367742, by decide⟩ :=
  accepted_of_selected 13 108579 ⟨367742, by decide⟩ ⟨13, 2, 0, 367742, 108579, 1197, 16384⟩
    (by decide) selected_cut_14181

theorem unmarked_context_12_27144_367743 : frontier 9 ⟨367743, by decide⟩
    (prefixCache 12 27144) (prefixPartial 12 27144) = false := by
  decide +kernel

theorem node_context_12_27144_367743 : EJMOriginalGlobalDAGData.nodes 9 ⟨367743, by decide⟩ =
    .split (coordinate 12) (![⟨367624, by decide⟩,⟨367697, by decide⟩,⟨367724, by decide⟩,⟨367742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27144_367743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27144 ⟨367743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27144
    ⟨367743, by decide⟩ (by decide) (![⟨367624, by decide⟩,⟨367697, by decide⟩,⟨367724, by decide⟩,⟨367742, by decide⟩]) unmarked_context_12_27144_367743 node_context_12_27144_367743
  intro a
  fin_cases a
  · exact context_13_108576_367624
  · exact context_13_108577_367697
  · exact context_13_108578_367724
  · exact context_13_108579_367742

theorem selected_cut_14182 : selected 8 ⟨367798, by decide⟩
    (prefixPartial 13 108580) = some ⟨13, 2, 0, 367798, 108580, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_108580_367798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108580 ⟨367798, by decide⟩ :=
  accepted_of_selected 13 108580 ⟨367798, by decide⟩ ⟨13, 2, 0, 367798, 108580, 3457, 16384⟩
    (by decide) selected_cut_14182

theorem selected_cut_14183 : selected 8 ⟨367846, by decide⟩
    (prefixPartial 13 108581) = some ⟨13, 2, 0, 367846, 108581, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_108581_367846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108581 ⟨367846, by decide⟩ :=
  accepted_of_selected 13 108581 ⟨367846, by decide⟩ ⟨13, 2, 0, 367846, 108581, 3217, 16384⟩
    (by decide) selected_cut_14183

theorem selected_cut_14184 : selected 8 ⟨367864, by decide⟩
    (prefixPartial 13 108582) = some ⟨13, 2, 0, 367864, 108582, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_108582_367864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108582 ⟨367864, by decide⟩ :=
  accepted_of_selected 13 108582 ⟨367864, by decide⟩ ⟨13, 2, 0, 367864, 108582, 1765, 16384⟩
    (by decide) selected_cut_14184

theorem selected_cut_14185 : selected 8 ⟨367874, by decide⟩
    (prefixPartial 13 108583) = some ⟨13, 2, 0, 367874, 108583, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_108583_367874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108583 ⟨367874, by decide⟩ :=
  accepted_of_selected 13 108583 ⟨367874, by decide⟩ ⟨13, 2, 0, 367874, 108583, 1217, 16384⟩
    (by decide) selected_cut_14185

theorem unmarked_context_12_27145_367875 : frontier 9 ⟨367875, by decide⟩
    (prefixCache 12 27145) (prefixPartial 12 27145) = false := by
  decide +kernel

theorem node_context_12_27145_367875 : EJMOriginalGlobalDAGData.nodes 9 ⟨367875, by decide⟩ =
    .split (coordinate 12) (![⟨367798, by decide⟩,⟨367846, by decide⟩,⟨367864, by decide⟩,⟨367874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27145_367875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27145 ⟨367875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27145
    ⟨367875, by decide⟩ (by decide) (![⟨367798, by decide⟩,⟨367846, by decide⟩,⟨367864, by decide⟩,⟨367874, by decide⟩]) unmarked_context_12_27145_367875 node_context_12_27145_367875
  intro a
  fin_cases a
  · exact context_13_108580_367798
  · exact context_13_108581_367846
  · exact context_13_108582_367864
  · exact context_13_108583_367874

theorem selected_cut_14186 : selected 7 ⟨367896, by decide⟩
    (prefixPartial 14 434336) = some ⟨14, 2, 0, 367896, 434336, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_434336_367896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434336 ⟨367896, by decide⟩ :=
  accepted_of_selected 14 434336 ⟨367896, by decide⟩ ⟨14, 2, 0, 367896, 434336, 1185, 4096⟩
    (by decide) selected_cut_14186

theorem selected_cut_14187 : selected 7 ⟨367916, by decide⟩
    (prefixPartial 14 434337) = some ⟨14, 2, 0, 367916, 434337, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_434337_367916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434337 ⟨367916, by decide⟩ :=
  accepted_of_selected 14 434337 ⟨367916, by decide⟩ ⟨14, 2, 0, 367916, 434337, 1361, 4096⟩
    (by decide) selected_cut_14187

theorem selected_cut_14188 : selected 7 ⟨367927, by decide⟩
    (prefixPartial 14 434338) = some ⟨14, 2, 0, 367927, 434338, 1029, 4096⟩ := by
  decide +kernel

theorem context_14_434338_367927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434338 ⟨367927, by decide⟩ :=
  accepted_of_selected 14 434338 ⟨367927, by decide⟩ ⟨14, 2, 0, 367927, 434338, 1029, 4096⟩
    (by decide) selected_cut_14188

theorem selected_cut_14189 : selected 7 ⟨367947, by decide⟩
    (prefixPartial 14 434339) = some ⟨14, 2, 0, 367947, 434339, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_434339_367947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434339 ⟨367947, by decide⟩ :=
  accepted_of_selected 14 434339 ⟨367947, by decide⟩ ⟨14, 2, 0, 367947, 434339, 1189, 4096⟩
    (by decide) selected_cut_14189

theorem unmarked_context_13_108584_367948 : frontier 8 ⟨367948, by decide⟩
    (prefixCache 13 108584) (prefixPartial 13 108584) = false := by
  decide +kernel

theorem node_context_13_108584_367948 : EJMOriginalGlobalDAGData.nodes 8 ⟨367948, by decide⟩ =
    .split (coordinate 13) (![⟨367896, by decide⟩,⟨367916, by decide⟩,⟨367927, by decide⟩,⟨367947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_108584_367948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108584 ⟨367948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 108584
    ⟨367948, by decide⟩ (by decide) (![⟨367896, by decide⟩,⟨367916, by decide⟩,⟨367927, by decide⟩,⟨367947, by decide⟩]) unmarked_context_13_108584_367948 node_context_13_108584_367948
  intro a
  fin_cases a
  · exact context_14_434336_367896
  · exact context_14_434337_367916
  · exact context_14_434338_367927
  · exact context_14_434339_367947

theorem selected_cut_14190 : selected 7 ⟨367988, by decide⟩
    (prefixPartial 14 434340) = some ⟨14, 2, 0, 367988, 434340, 1565, 4096⟩ := by
  decide +kernel

theorem context_14_434340_367988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434340 ⟨367988, by decide⟩ :=
  accepted_of_selected 14 434340 ⟨367988, by decide⟩ ⟨14, 2, 0, 367988, 434340, 1565, 4096⟩
    (by decide) selected_cut_14190

theorem selected_cut_14191 : selected 7 ⟨368028, by decide⟩
    (prefixPartial 14 434341) = some ⟨14, 2, 0, 368028, 434341, 1521, 4096⟩ := by
  decide +kernel

theorem context_14_434341_368028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434341 ⟨368028, by decide⟩ :=
  accepted_of_selected 14 434341 ⟨368028, by decide⟩ ⟨14, 2, 0, 368028, 434341, 1521, 4096⟩
    (by decide) selected_cut_14191

theorem selected_cut_14192 : selected 7 ⟨368050, by decide⟩
    (prefixPartial 14 434342) = some ⟨14, 2, 0, 368050, 434342, 1257, 4096⟩ := by
  decide +kernel

theorem context_14_434342_368050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434342 ⟨368050, by decide⟩ :=
  accepted_of_selected 14 434342 ⟨368050, by decide⟩ ⟨14, 2, 0, 368050, 434342, 1257, 4096⟩
    (by decide) selected_cut_14192

theorem selected_cut_14193 : selected 7 ⟨368075, by decide⟩
    (prefixPartial 14 434343) = some ⟨14, 2, 0, 368075, 434343, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_434343_368075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434343 ⟨368075, by decide⟩ :=
  accepted_of_selected 14 434343 ⟨368075, by decide⟩ ⟨14, 2, 0, 368075, 434343, 1293, 4096⟩
    (by decide) selected_cut_14193

theorem unmarked_context_13_108585_368076 : frontier 8 ⟨368076, by decide⟩
    (prefixCache 13 108585) (prefixPartial 13 108585) = false := by
  decide +kernel

theorem node_context_13_108585_368076 : EJMOriginalGlobalDAGData.nodes 8 ⟨368076, by decide⟩ =
    .split (coordinate 13) (![⟨367988, by decide⟩,⟨368028, by decide⟩,⟨368050, by decide⟩,⟨368075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_108585_368076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108585 ⟨368076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 108585
    ⟨368076, by decide⟩ (by decide) (![⟨367988, by decide⟩,⟨368028, by decide⟩,⟨368050, by decide⟩,⟨368075, by decide⟩]) unmarked_context_13_108585_368076 node_context_13_108585_368076
  intro a
  fin_cases a
  · exact context_14_434340_367988
  · exact context_14_434341_368028
  · exact context_14_434342_368050
  · exact context_14_434343_368075

theorem selected_cut_14194 : selected 8 ⟨368147, by decide⟩
    (prefixPartial 13 108586) = some ⟨13, 2, 0, 368147, 108586, 3017, 16384⟩ := by
  decide +kernel

theorem context_13_108586_368147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108586 ⟨368147, by decide⟩ :=
  accepted_of_selected 13 108586 ⟨368147, by decide⟩ ⟨13, 2, 0, 368147, 108586, 3017, 16384⟩
    (by decide) selected_cut_14194

theorem selected_cut_14195 : selected 8 ⟨368182, by decide⟩
    (prefixPartial 13 108587) = some ⟨13, 2, 0, 368182, 108587, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_108587_368182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108587 ⟨368182, by decide⟩ :=
  accepted_of_selected 13 108587 ⟨368182, by decide⟩ ⟨13, 2, 0, 368182, 108587, 1633, 16384⟩
    (by decide) selected_cut_14195

theorem unmarked_context_12_27146_368183 : frontier 9 ⟨368183, by decide⟩
    (prefixCache 12 27146) (prefixPartial 12 27146) = false := by
  decide +kernel

theorem node_context_12_27146_368183 : EJMOriginalGlobalDAGData.nodes 9 ⟨368183, by decide⟩ =
    .split (coordinate 12) (![⟨367948, by decide⟩,⟨368076, by decide⟩,⟨368147, by decide⟩,⟨368182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27146_368183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27146 ⟨368183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27146
    ⟨368183, by decide⟩ (by decide) (![⟨367948, by decide⟩,⟨368076, by decide⟩,⟨368147, by decide⟩,⟨368182, by decide⟩]) unmarked_context_12_27146_368183 node_context_12_27146_368183
  intro a
  fin_cases a
  · exact context_13_108584_367948
  · exact context_13_108585_368076
  · exact context_13_108586_368147
  · exact context_13_108587_368182

theorem selected_cut_14196 : selected 8 ⟨368233, by decide⟩
    (prefixPartial 13 108588) = some ⟨13, 2, 0, 368233, 108588, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_108588_368233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108588 ⟨368233, by decide⟩ :=
  accepted_of_selected 13 108588 ⟨368233, by decide⟩ ⟨13, 2, 0, 368233, 108588, 3381, 16384⟩
    (by decide) selected_cut_14196

theorem selected_cut_14197 : selected 8 ⟨368295, by decide⟩
    (prefixPartial 13 108589) = some ⟨13, 2, 0, 368295, 108589, 3889, 16384⟩ := by
  decide +kernel

theorem context_13_108589_368295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108589 ⟨368295, by decide⟩ :=
  accepted_of_selected 13 108589 ⟨368295, by decide⟩ ⟨13, 2, 0, 368295, 108589, 3889, 16384⟩
    (by decide) selected_cut_14197

theorem selected_cut_14198 : selected 8 ⟨368313, by decide⟩
    (prefixPartial 13 108590) = some ⟨13, 2, 0, 368313, 108590, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_108590_368313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108590 ⟨368313, by decide⟩ :=
  accepted_of_selected 13 108590 ⟨368313, by decide⟩ ⟨13, 2, 0, 368313, 108590, 1781, 16384⟩
    (by decide) selected_cut_14198

theorem selected_cut_14199 : selected 8 ⟨368322, by decide⟩
    (prefixPartial 13 108591) = some ⟨13, 2, 0, 368322, 108591, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_108591_368322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108591 ⟨368322, by decide⟩ :=
  accepted_of_selected 13 108591 ⟨368322, by decide⟩ ⟨13, 2, 0, 368322, 108591, 1257, 16384⟩
    (by decide) selected_cut_14199

theorem unmarked_context_12_27147_368323 : frontier 9 ⟨368323, by decide⟩
    (prefixCache 12 27147) (prefixPartial 12 27147) = false := by
  decide +kernel

theorem node_context_12_27147_368323 : EJMOriginalGlobalDAGData.nodes 9 ⟨368323, by decide⟩ =
    .split (coordinate 12) (![⟨368233, by decide⟩,⟨368295, by decide⟩,⟨368313, by decide⟩,⟨368322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27147_368323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27147 ⟨368323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27147
    ⟨368323, by decide⟩ (by decide) (![⟨368233, by decide⟩,⟨368295, by decide⟩,⟨368313, by decide⟩,⟨368322, by decide⟩]) unmarked_context_12_27147_368323 node_context_12_27147_368323
  intro a
  fin_cases a
  · exact context_13_108588_368233
  · exact context_13_108589_368295
  · exact context_13_108590_368313
  · exact context_13_108591_368322

theorem unmarked_context_11_6786_368324 : frontier 10 ⟨368324, by decide⟩
    (prefixCache 11 6786) (prefixPartial 11 6786) = false := by
  decide +kernel

theorem node_context_11_6786_368324 : EJMOriginalGlobalDAGData.nodes 10 ⟨368324, by decide⟩ =
    .split (coordinate 11) (![⟨367743, by decide⟩,⟨367875, by decide⟩,⟨368183, by decide⟩,⟨368323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6786_368324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6786 ⟨368324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6786
    ⟨368324, by decide⟩ (by decide) (![⟨367743, by decide⟩,⟨367875, by decide⟩,⟨368183, by decide⟩,⟨368323, by decide⟩]) unmarked_context_11_6786_368324 node_context_11_6786_368324
  intro a
  fin_cases a
  · exact context_12_27144_367743
  · exact context_12_27145_367875
  · exact context_12_27146_368183
  · exact context_12_27147_368323

theorem selected_cut_14200 : selected 8 ⟨368365, by decide⟩
    (prefixPartial 13 108592) = some ⟨13, 2, 0, 368365, 108592, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_108592_368365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108592 ⟨368365, by decide⟩ :=
  accepted_of_selected 13 108592 ⟨368365, by decide⟩ ⟨13, 2, 0, 368365, 108592, 2801, 16384⟩
    (by decide) selected_cut_14200

theorem selected_cut_14201 : selected 7 ⟨368389, by decide⟩
    (prefixPartial 14 434372) = some ⟨14, 2, 0, 368389, 434372, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_434372_368389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434372 ⟨368389, by decide⟩ :=
  accepted_of_selected 14 434372 ⟨368389, by decide⟩ ⟨14, 2, 0, 368389, 434372, 1237, 4096⟩
    (by decide) selected_cut_14201

theorem selected_cut_14202 : selected 7 ⟨368412, by decide⟩
    (prefixPartial 14 434373) = some ⟨14, 2, 0, 368412, 434373, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_434373_368412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434373 ⟨368412, by decide⟩ :=
  accepted_of_selected 14 434373 ⟨368412, by decide⟩ ⟨14, 2, 0, 368412, 434373, 1049, 4096⟩
    (by decide) selected_cut_14202

theorem selected_cut_14203 : selected 7 ⟨368426, by decide⟩
    (prefixPartial 14 434374) = some ⟨14, 2, 0, 368426, 434374, 821, 4096⟩ := by
  decide +kernel

theorem context_14_434374_368426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434374 ⟨368426, by decide⟩ :=
  accepted_of_selected 14 434374 ⟨368426, by decide⟩ ⟨14, 2, 0, 368426, 434374, 821, 4096⟩
    (by decide) selected_cut_14203

theorem selected_cut_14204 : selected 7 ⟨368440, by decide⟩
    (prefixPartial 14 434375) = some ⟨14, 2, 0, 368440, 434375, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_434375_368440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 434375 ⟨368440, by decide⟩ :=
  accepted_of_selected 14 434375 ⟨368440, by decide⟩ ⟨14, 2, 0, 368440, 434375, 1033, 4096⟩
    (by decide) selected_cut_14204

theorem unmarked_context_13_108593_368441 : frontier 8 ⟨368441, by decide⟩
    (prefixCache 13 108593) (prefixPartial 13 108593) = false := by
  decide +kernel

theorem node_context_13_108593_368441 : EJMOriginalGlobalDAGData.nodes 8 ⟨368441, by decide⟩ =
    .split (coordinate 13) (![⟨368389, by decide⟩,⟨368412, by decide⟩,⟨368426, by decide⟩,⟨368440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_108593_368441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108593 ⟨368441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 108593
    ⟨368441, by decide⟩ (by decide) (![⟨368389, by decide⟩,⟨368412, by decide⟩,⟨368426, by decide⟩,⟨368440, by decide⟩]) unmarked_context_13_108593_368441 node_context_13_108593_368441
  intro a
  fin_cases a
  · exact context_14_434372_368389
  · exact context_14_434373_368412
  · exact context_14_434374_368426
  · exact context_14_434375_368440

theorem selected_cut_14205 : selected 8 ⟨368474, by decide⟩
    (prefixPartial 13 108594) = some ⟨13, 2, 0, 368474, 108594, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_108594_368474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108594 ⟨368474, by decide⟩ :=
  accepted_of_selected 13 108594 ⟨368474, by decide⟩ ⟨13, 2, 0, 368474, 108594, 2113, 16384⟩
    (by decide) selected_cut_14205

theorem selected_cut_14206 : selected 8 ⟨368487, by decide⟩
    (prefixPartial 13 108595) = some ⟨13, 2, 0, 368487, 108595, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_108595_368487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108595 ⟨368487, by decide⟩ :=
  accepted_of_selected 13 108595 ⟨368487, by decide⟩ ⟨13, 2, 0, 368487, 108595, 1229, 16384⟩
    (by decide) selected_cut_14206

theorem unmarked_context_12_27148_368488 : frontier 9 ⟨368488, by decide⟩
    (prefixCache 12 27148) (prefixPartial 12 27148) = false := by
  decide +kernel

theorem node_context_12_27148_368488 : EJMOriginalGlobalDAGData.nodes 9 ⟨368488, by decide⟩ =
    .split (coordinate 12) (![⟨368365, by decide⟩,⟨368441, by decide⟩,⟨368474, by decide⟩,⟨368487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27148_368488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27148 ⟨368488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27148
    ⟨368488, by decide⟩ (by decide) (![⟨368365, by decide⟩,⟨368441, by decide⟩,⟨368474, by decide⟩,⟨368487, by decide⟩]) unmarked_context_12_27148_368488 node_context_12_27148_368488
  intro a
  fin_cases a
  · exact context_13_108592_368365
  · exact context_13_108593_368441
  · exact context_13_108594_368474
  · exact context_13_108595_368487

theorem selected_cut_14207 : selected 8 ⟨368549, by decide⟩
    (prefixPartial 13 108596) = some ⟨13, 2, 0, 368549, 108596, 3661, 16384⟩ := by
  decide +kernel

theorem context_13_108596_368549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108596 ⟨368549, by decide⟩ :=
  accepted_of_selected 13 108596 ⟨368549, by decide⟩ ⟨13, 2, 0, 368549, 108596, 3661, 16384⟩
    (by decide) selected_cut_14207

theorem selected_cut_14208 : selected 8 ⟨368614, by decide⟩
    (prefixPartial 13 108597) = some ⟨13, 2, 0, 368614, 108597, 3793, 16384⟩ := by
  decide +kernel

theorem context_13_108597_368614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108597 ⟨368614, by decide⟩ :=
  accepted_of_selected 13 108597 ⟨368614, by decide⟩ ⟨13, 2, 0, 368614, 108597, 3793, 16384⟩
    (by decide) selected_cut_14208

theorem selected_cut_14209 : selected 8 ⟨368638, by decide⟩
    (prefixPartial 13 108598) = some ⟨13, 2, 0, 368638, 108598, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_108598_368638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108598 ⟨368638, by decide⟩ :=
  accepted_of_selected 13 108598 ⟨368638, by decide⟩ ⟨13, 2, 0, 368638, 108598, 1865, 16384⟩
    (by decide) selected_cut_14209

theorem selected_cut_14210 : selected 8 ⟨368646, by decide⟩
    (prefixPartial 13 108599) = some ⟨13, 2, 0, 368646, 108599, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_108599_368646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108599 ⟨368646, by decide⟩ :=
  accepted_of_selected 13 108599 ⟨368646, by decide⟩ ⟨13, 2, 0, 368646, 108599, 1093, 16384⟩
    (by decide) selected_cut_14210

theorem unmarked_context_12_27149_368647 : frontier 9 ⟨368647, by decide⟩
    (prefixCache 12 27149) (prefixPartial 12 27149) = false := by
  decide +kernel

theorem node_context_12_27149_368647 : EJMOriginalGlobalDAGData.nodes 9 ⟨368647, by decide⟩ =
    .split (coordinate 12) (![⟨368549, by decide⟩,⟨368614, by decide⟩,⟨368638, by decide⟩,⟨368646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27149_368647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27149 ⟨368647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27149
    ⟨368647, by decide⟩ (by decide) (![⟨368549, by decide⟩,⟨368614, by decide⟩,⟨368638, by decide⟩,⟨368646, by decide⟩]) unmarked_context_12_27149_368647 node_context_12_27149_368647
  intro a
  fin_cases a
  · exact context_13_108596_368549
  · exact context_13_108597_368614
  · exact context_13_108598_368638
  · exact context_13_108599_368646

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
