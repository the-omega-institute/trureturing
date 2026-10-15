/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00098 : selected 8 ⟨6940, by decide⟩
    (prefixPartial 13 1070) = some ⟨13, 2, 0, 6940, 1070, 813, 16384⟩ := by
  decide +kernel

theorem context_13_1070_6940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1070 ⟨6940, by decide⟩ :=
  accepted_of_selected 13 1070 ⟨6940, by decide⟩ ⟨13, 2, 0, 6940, 1070, 813, 16384⟩
    (by decide) selected_cut_00098

theorem selected_cut_00099 : selected 8 ⟨6965, by decide⟩
    (prefixPartial 13 1071) = some ⟨13, 2, 0, 6965, 1071, 165, 16384⟩ := by
  decide +kernel

theorem context_13_1071_6965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1071 ⟨6965, by decide⟩ :=
  accepted_of_selected 13 1071 ⟨6965, by decide⟩ ⟨13, 2, 0, 6965, 1071, 165, 16384⟩
    (by decide) selected_cut_00099

theorem unmarked_context_12_267_6966 : frontier 9 ⟨6966, by decide⟩
    (prefixCache 12 267) (prefixPartial 12 267) = false := by
  decide +kernel

theorem node_context_12_267_6966 : EJMOriginalGlobalDAGData.nodes 9 ⟨6966, by decide⟩ =
    .split (coordinate 12) (![⟨6786, by decide⟩,⟨6889, by decide⟩,⟨6940, by decide⟩,⟨6965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_267_6966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 267 ⟨6966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 267
    ⟨6966, by decide⟩ (by decide) (![⟨6786, by decide⟩,⟨6889, by decide⟩,⟨6940, by decide⟩,⟨6965, by decide⟩]) unmarked_context_12_267_6966 node_context_12_267_6966
  intro a
  fin_cases a
  · exact context_13_1068_6786
  · exact context_13_1069_6889
  · exact context_13_1070_6940
  · exact context_13_1071_6965

theorem unmarked_context_11_66_6967 : frontier 10 ⟨6967, by decide⟩
    (prefixCache 11 66) (prefixPartial 11 66) = false := by
  decide +kernel

theorem node_context_11_66_6967 : EJMOriginalGlobalDAGData.nodes 10 ⟨6967, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨6657, by decide⟩,⟨6966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_66_6967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 66 ⟨6967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 66
    ⟨6967, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨6657, by decide⟩,⟨6966, by decide⟩]) unmarked_context_11_66_6967 node_context_11_66_6967
  intro a
  fin_cases a
  · exact context_12_264_895
  · exact context_12_265_895
  · exact context_12_266_6657
  · exact context_12_267_6966

theorem selected_cut_00100 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 67) = some ⟨11, 1, 0, 1736, 67, 1, 262144⟩ := by
  decide +kernel

theorem context_11_67_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 67 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 67 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 67, 1, 262144⟩
    (by decide) selected_cut_00100

theorem unmarked_context_10_16_6968 : frontier 11 ⟨6968, by decide⟩
    (prefixCache 10 16) (prefixPartial 10 16) = false := by
  decide +kernel

theorem node_context_10_16_6968 : EJMOriginalGlobalDAGData.nodes 11 ⟨6968, by decide⟩ =
    .split (coordinate 10) (![⟨5847, by decide⟩,⟨6426, by decide⟩,⟨6967, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_16_6968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 16 ⟨6968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 16
    ⟨6968, by decide⟩ (by decide) (![⟨5847, by decide⟩,⟨6426, by decide⟩,⟨6967, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_16_6968 node_context_10_16_6968
  intro a
  fin_cases a
  · exact context_11_64_5847
  · exact context_11_65_6426
  · exact context_11_66_6967
  · exact context_11_67_1736

theorem selected_cut_00101 : selected 8 ⟨7008, by decide⟩
    (prefixPartial 13 1088) = some ⟨13, 2, 0, 7008, 1088, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_1088_7008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1088 ⟨7008, by decide⟩ :=
  accepted_of_selected 13 1088 ⟨7008, by decide⟩ ⟨13, 2, 0, 7008, 1088, 1729, 16384⟩
    (by decide) selected_cut_00101

theorem selected_cut_00102 : selected 8 ⟨7057, by decide⟩
    (prefixPartial 13 1089) = some ⟨13, 2, 0, 7057, 1089, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_1089_7057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1089 ⟨7057, by decide⟩ :=
  accepted_of_selected 13 1089 ⟨7057, by decide⟩ ⟨13, 2, 0, 7057, 1089, 1597, 16384⟩
    (by decide) selected_cut_00102

theorem selected_cut_00103 : selected 8 ⟨7148, by decide⟩
    (prefixPartial 13 1090) = some ⟨13, 2, 0, 7148, 1090, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_1090_7148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1090 ⟨7148, by decide⟩ :=
  accepted_of_selected 13 1090 ⟨7148, by decide⟩ ⟨13, 2, 0, 7148, 1090, 1885, 16384⟩
    (by decide) selected_cut_00103

theorem selected_cut_00104 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 1091) = some ⟨13, 1, 0, 414, 1091, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1091_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1091 ⟨414, by decide⟩ :=
  accepted_of_selected 13 1091 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 1091, 1, 16384⟩
    (by decide) selected_cut_00104

theorem unmarked_context_12_272_7149 : frontier 9 ⟨7149, by decide⟩
    (prefixCache 12 272) (prefixPartial 12 272) = false := by
  decide +kernel

theorem node_context_12_272_7149 : EJMOriginalGlobalDAGData.nodes 9 ⟨7149, by decide⟩ =
    .split (coordinate 12) (![⟨7008, by decide⟩,⟨7057, by decide⟩,⟨7148, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_272_7149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 272 ⟨7149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 272
    ⟨7149, by decide⟩ (by decide) (![⟨7008, by decide⟩,⟨7057, by decide⟩,⟨7148, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_272_7149 node_context_12_272_7149
  intro a
  fin_cases a
  · exact context_13_1088_7008
  · exact context_13_1089_7057
  · exact context_13_1090_7148
  · exact context_13_1091_414

theorem selected_cut_00105 : selected 9 ⟨7259, by decide⟩
    (prefixPartial 12 273) = some ⟨12, 2, 0, 7259, 273, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_273_7259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 273 ⟨7259, by decide⟩ :=
  accepted_of_selected 12 273 ⟨7259, by decide⟩ ⟨12, 2, 0, 7259, 273, 3177, 65536⟩
    (by decide) selected_cut_00105

theorem selected_cut_00106 : selected 8 ⟨7320, by decide⟩
    (prefixPartial 13 1096) = some ⟨13, 2, 0, 7320, 1096, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_1096_7320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1096 ⟨7320, by decide⟩ :=
  accepted_of_selected 13 1096 ⟨7320, by decide⟩ ⟨13, 2, 0, 7320, 1096, 2417, 16384⟩
    (by decide) selected_cut_00106

theorem selected_cut_00107 : selected 8 ⟨7373, by decide⟩
    (prefixPartial 13 1097) = some ⟨13, 2, 0, 7373, 1097, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_1097_7373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1097 ⟨7373, by decide⟩ :=
  accepted_of_selected 13 1097 ⟨7373, by decide⟩ ⟨13, 2, 0, 7373, 1097, 1629, 16384⟩
    (by decide) selected_cut_00107

theorem selected_cut_00108 : selected 8 ⟨7428, by decide⟩
    (prefixPartial 13 1098) = some ⟨13, 2, 0, 7428, 1098, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_1098_7428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1098 ⟨7428, by decide⟩ :=
  accepted_of_selected 13 1098 ⟨7428, by decide⟩ ⟨13, 2, 0, 7428, 1098, 1373, 16384⟩
    (by decide) selected_cut_00108

theorem selected_cut_00109 : selected 8 ⟨7460, by decide⟩
    (prefixPartial 13 1099) = some ⟨13, 2, 0, 7460, 1099, 917, 16384⟩ := by
  decide +kernel

theorem context_13_1099_7460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1099 ⟨7460, by decide⟩ :=
  accepted_of_selected 13 1099 ⟨7460, by decide⟩ ⟨13, 2, 0, 7460, 1099, 917, 16384⟩
    (by decide) selected_cut_00109

theorem unmarked_context_12_274_7461 : frontier 9 ⟨7461, by decide⟩
    (prefixCache 12 274) (prefixPartial 12 274) = false := by
  decide +kernel

theorem node_context_12_274_7461 : EJMOriginalGlobalDAGData.nodes 9 ⟨7461, by decide⟩ =
    .split (coordinate 12) (![⟨7320, by decide⟩,⟨7373, by decide⟩,⟨7428, by decide⟩,⟨7460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_274_7461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 274 ⟨7461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 274
    ⟨7461, by decide⟩ (by decide) (![⟨7320, by decide⟩,⟨7373, by decide⟩,⟨7428, by decide⟩,⟨7460, by decide⟩]) unmarked_context_12_274_7461 node_context_12_274_7461
  intro a
  fin_cases a
  · exact context_13_1096_7320
  · exact context_13_1097_7373
  · exact context_13_1098_7428
  · exact context_13_1099_7460

theorem selected_cut_00110 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 275) = some ⟨12, 1, 0, 893, 275, 1, 65536⟩ := by
  decide +kernel

theorem context_12_275_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 275 ⟨893, by decide⟩ :=
  accepted_of_selected 12 275 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 275, 1, 65536⟩
    (by decide) selected_cut_00110

theorem unmarked_context_11_68_7462 : frontier 10 ⟨7462, by decide⟩
    (prefixCache 11 68) (prefixPartial 11 68) = false := by
  decide +kernel

theorem node_context_11_68_7462 : EJMOriginalGlobalDAGData.nodes 10 ⟨7462, by decide⟩ =
    .split (coordinate 11) (![⟨7149, by decide⟩,⟨7259, by decide⟩,⟨7461, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_68_7462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 68 ⟨7462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 68
    ⟨7462, by decide⟩ (by decide) (![⟨7149, by decide⟩,⟨7259, by decide⟩,⟨7461, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_68_7462 node_context_11_68_7462
  intro a
  fin_cases a
  · exact context_12_272_7149
  · exact context_12_273_7259
  · exact context_12_274_7461
  · exact context_12_275_893

theorem selected_cut_00111 : selected 8 ⟨7496, by decide⟩
    (prefixPartial 13 1104) = some ⟨13, 2, 0, 7496, 1104, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_1104_7496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1104 ⟨7496, by decide⟩ :=
  accepted_of_selected 13 1104 ⟨7496, by decide⟩ ⟨13, 2, 0, 7496, 1104, 1785, 16384⟩
    (by decide) selected_cut_00111

theorem selected_cut_00112 : selected 8 ⟨7549, by decide⟩
    (prefixPartial 13 1105) = some ⟨13, 2, 0, 7549, 1105, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_1105_7549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1105 ⟨7549, by decide⟩ :=
  accepted_of_selected 13 1105 ⟨7549, by decide⟩ ⟨13, 2, 0, 7549, 1105, 1829, 16384⟩
    (by decide) selected_cut_00112

theorem selected_cut_00113 : selected 8 ⟨7631, by decide⟩
    (prefixPartial 13 1106) = some ⟨13, 2, 0, 7631, 1106, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_1106_7631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1106 ⟨7631, by decide⟩ :=
  accepted_of_selected 13 1106 ⟨7631, by decide⟩ ⟨13, 2, 0, 7631, 1106, 2501, 16384⟩
    (by decide) selected_cut_00113

theorem selected_cut_00114 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 1107) = some ⟨13, 1, 0, 414, 1107, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1107_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1107 ⟨414, by decide⟩ :=
  accepted_of_selected 13 1107 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 1107, 1, 16384⟩
    (by decide) selected_cut_00114

theorem unmarked_context_12_276_7632 : frontier 9 ⟨7632, by decide⟩
    (prefixCache 12 276) (prefixPartial 12 276) = false := by
  decide +kernel

theorem node_context_12_276_7632 : EJMOriginalGlobalDAGData.nodes 9 ⟨7632, by decide⟩ =
    .split (coordinate 12) (![⟨7496, by decide⟩,⟨7549, by decide⟩,⟨7631, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_276_7632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 276 ⟨7632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 276
    ⟨7632, by decide⟩ (by decide) (![⟨7496, by decide⟩,⟨7549, by decide⟩,⟨7631, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_276_7632 node_context_12_276_7632
  intro a
  fin_cases a
  · exact context_13_1104_7496
  · exact context_13_1105_7549
  · exact context_13_1106_7631
  · exact context_13_1107_414

theorem selected_cut_00115 : selected 8 ⟨7677, by decide⟩
    (prefixPartial 13 1108) = some ⟨13, 2, 0, 7677, 1108, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_1108_7677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1108 ⟨7677, by decide⟩ :=
  accepted_of_selected 13 1108 ⟨7677, by decide⟩ ⟨13, 2, 0, 7677, 1108, 2361, 16384⟩
    (by decide) selected_cut_00115

theorem selected_cut_00116 : selected 8 ⟨7719, by decide⟩
    (prefixPartial 13 1109) = some ⟨13, 2, 0, 7719, 1109, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_1109_7719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1109 ⟨7719, by decide⟩ :=
  accepted_of_selected 13 1109 ⟨7719, by decide⟩ ⟨13, 2, 0, 7719, 1109, 2025, 16384⟩
    (by decide) selected_cut_00116

theorem selected_cut_00117 : selected 8 ⟨7807, by decide⟩
    (prefixPartial 13 1110) = some ⟨13, 2, 0, 7807, 1110, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_1110_7807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1110 ⟨7807, by decide⟩ :=
  accepted_of_selected 13 1110 ⟨7807, by decide⟩ ⟨13, 2, 0, 7807, 1110, 2765, 16384⟩
    (by decide) selected_cut_00117

theorem selected_cut_00118 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 1111) = some ⟨13, 1, 0, 414, 1111, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1111_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1111 ⟨414, by decide⟩ :=
  accepted_of_selected 13 1111 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 1111, 1, 16384⟩
    (by decide) selected_cut_00118

theorem unmarked_context_12_277_7808 : frontier 9 ⟨7808, by decide⟩
    (prefixCache 12 277) (prefixPartial 12 277) = false := by
  decide +kernel

theorem node_context_12_277_7808 : EJMOriginalGlobalDAGData.nodes 9 ⟨7808, by decide⟩ =
    .split (coordinate 12) (![⟨7677, by decide⟩,⟨7719, by decide⟩,⟨7807, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_277_7808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 277 ⟨7808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 277
    ⟨7808, by decide⟩ (by decide) (![⟨7677, by decide⟩,⟨7719, by decide⟩,⟨7807, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_277_7808 node_context_12_277_7808
  intro a
  fin_cases a
  · exact context_13_1108_7677
  · exact context_13_1109_7719
  · exact context_13_1110_7807
  · exact context_13_1111_414

theorem selected_cut_00119 : selected 8 ⟨7871, by decide⟩
    (prefixPartial 13 1112) = some ⟨13, 2, 0, 7871, 1112, 3273, 16384⟩ := by
  decide +kernel

theorem context_13_1112_7871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1112 ⟨7871, by decide⟩ :=
  accepted_of_selected 13 1112 ⟨7871, by decide⟩ ⟨13, 2, 0, 7871, 1112, 3273, 16384⟩
    (by decide) selected_cut_00119

theorem selected_cut_00120 : selected 8 ⟨7941, by decide⟩
    (prefixPartial 13 1113) = some ⟨13, 2, 0, 7941, 1113, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_1113_7941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1113 ⟨7941, by decide⟩ :=
  accepted_of_selected 13 1113 ⟨7941, by decide⟩ ⟨13, 2, 0, 7941, 1113, 2665, 16384⟩
    (by decide) selected_cut_00120

theorem selected_cut_00121 : selected 8 ⟨8000, by decide⟩
    (prefixPartial 13 1114) = some ⟨13, 2, 0, 8000, 1114, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_1114_8000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1114 ⟨8000, by decide⟩ :=
  accepted_of_selected 13 1114 ⟨8000, by decide⟩ ⟨13, 2, 0, 8000, 1114, 2173, 16384⟩
    (by decide) selected_cut_00121

theorem selected_cut_00122 : selected 8 ⟨8030, by decide⟩
    (prefixPartial 13 1115) = some ⟨13, 2, 0, 8030, 1115, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_1115_8030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1115 ⟨8030, by decide⟩ :=
  accepted_of_selected 13 1115 ⟨8030, by decide⟩ ⟨13, 2, 0, 8030, 1115, 1261, 16384⟩
    (by decide) selected_cut_00122

theorem unmarked_context_12_278_8031 : frontier 9 ⟨8031, by decide⟩
    (prefixCache 12 278) (prefixPartial 12 278) = false := by
  decide +kernel

theorem node_context_12_278_8031 : EJMOriginalGlobalDAGData.nodes 9 ⟨8031, by decide⟩ =
    .split (coordinate 12) (![⟨7871, by decide⟩,⟨7941, by decide⟩,⟨8000, by decide⟩,⟨8030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_278_8031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 278 ⟨8031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 278
    ⟨8031, by decide⟩ (by decide) (![⟨7871, by decide⟩,⟨7941, by decide⟩,⟨8000, by decide⟩,⟨8030, by decide⟩]) unmarked_context_12_278_8031 node_context_12_278_8031
  intro a
  fin_cases a
  · exact context_13_1112_7871
  · exact context_13_1113_7941
  · exact context_13_1114_8000
  · exact context_13_1115_8030

theorem selected_cut_00123 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 279) = some ⟨12, 1, 0, 893, 279, 1, 65536⟩ := by
  decide +kernel

theorem context_12_279_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279 ⟨893, by decide⟩ :=
  accepted_of_selected 12 279 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 279, 1, 65536⟩
    (by decide) selected_cut_00123

theorem unmarked_context_11_69_8032 : frontier 10 ⟨8032, by decide⟩
    (prefixCache 11 69) (prefixPartial 11 69) = false := by
  decide +kernel

theorem node_context_11_69_8032 : EJMOriginalGlobalDAGData.nodes 10 ⟨8032, by decide⟩ =
    .split (coordinate 11) (![⟨7632, by decide⟩,⟨7808, by decide⟩,⟨8031, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_69_8032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69 ⟨8032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 69
    ⟨8032, by decide⟩ (by decide) (![⟨7632, by decide⟩,⟨7808, by decide⟩,⟨8031, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_69_8032 node_context_11_69_8032
  intro a
  fin_cases a
  · exact context_12_276_7632
  · exact context_12_277_7808
  · exact context_12_278_8031
  · exact context_12_279_893

theorem selected_cut_00124 : selected 8 ⟨8108, by decide⟩
    (prefixPartial 13 1120) = some ⟨13, 2, 0, 8108, 1120, 3745, 16384⟩ := by
  decide +kernel

theorem context_13_1120_8108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1120 ⟨8108, by decide⟩ :=
  accepted_of_selected 13 1120 ⟨8108, by decide⟩ ⟨13, 2, 0, 8108, 1120, 3745, 16384⟩
    (by decide) selected_cut_00124

theorem selected_cut_00125 : selected 7 ⟨8139, by decide⟩
    (prefixPartial 14 4484) = some ⟨14, 2, 0, 8139, 4484, 845, 4096⟩ := by
  decide +kernel

theorem context_14_4484_8139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4484 ⟨8139, by decide⟩ :=
  accepted_of_selected 14 4484 ⟨8139, by decide⟩ ⟨14, 2, 0, 8139, 4484, 845, 4096⟩
    (by decide) selected_cut_00125

theorem selected_cut_00126 : selected 7 ⟨8156, by decide⟩
    (prefixPartial 14 4485) = some ⟨14, 2, 0, 8156, 4485, 857, 4096⟩ := by
  decide +kernel

theorem context_14_4485_8156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4485 ⟨8156, by decide⟩ :=
  accepted_of_selected 14 4485 ⟨8156, by decide⟩ ⟨14, 2, 0, 8156, 4485, 857, 4096⟩
    (by decide) selected_cut_00126

theorem selected_cut_00127 : selected 7 ⟨8193, by decide⟩
    (prefixPartial 14 4486) = some ⟨14, 2, 0, 8193, 4486, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_4486_8193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4486 ⟨8193, by decide⟩ :=
  accepted_of_selected 14 4486 ⟨8193, by decide⟩ ⟨14, 2, 0, 8193, 4486, 1429, 4096⟩
    (by decide) selected_cut_00127

theorem selected_cut_00128 : selected 7 ⟨8219, by decide⟩
    (prefixPartial 14 4487) = some ⟨14, 2, 0, 8219, 4487, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_4487_8219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4487 ⟨8219, by decide⟩ :=
  accepted_of_selected 14 4487 ⟨8219, by decide⟩ ⟨14, 2, 0, 8219, 4487, 1161, 4096⟩
    (by decide) selected_cut_00128

theorem unmarked_context_13_1121_8220 : frontier 8 ⟨8220, by decide⟩
    (prefixCache 13 1121) (prefixPartial 13 1121) = false := by
  decide +kernel

theorem node_context_13_1121_8220 : EJMOriginalGlobalDAGData.nodes 8 ⟨8220, by decide⟩ =
    .split (coordinate 13) (![⟨8139, by decide⟩,⟨8156, by decide⟩,⟨8193, by decide⟩,⟨8219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1121_8220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1121 ⟨8220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1121
    ⟨8220, by decide⟩ (by decide) (![⟨8139, by decide⟩,⟨8156, by decide⟩,⟨8193, by decide⟩,⟨8219, by decide⟩]) unmarked_context_13_1121_8220 node_context_13_1121_8220
  intro a
  fin_cases a
  · exact context_14_4484_8139
  · exact context_14_4485_8156
  · exact context_14_4486_8193
  · exact context_14_4487_8219

theorem selected_cut_00129 : selected 8 ⟨8308, by decide⟩
    (prefixPartial 13 1122) = some ⟨13, 2, 0, 8308, 1122, 3369, 16384⟩ := by
  decide +kernel

theorem context_13_1122_8308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1122 ⟨8308, by decide⟩ :=
  accepted_of_selected 13 1122 ⟨8308, by decide⟩ ⟨13, 2, 0, 8308, 1122, 3369, 16384⟩
    (by decide) selected_cut_00129

theorem selected_cut_00130 : selected 8 ⟨8380, by decide⟩
    (prefixPartial 13 1123) = some ⟨13, 2, 0, 8380, 1123, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_1123_8380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1123 ⟨8380, by decide⟩ :=
  accepted_of_selected 13 1123 ⟨8380, by decide⟩ ⟨13, 2, 0, 8380, 1123, 1629, 16384⟩
    (by decide) selected_cut_00130

theorem unmarked_context_12_280_8381 : frontier 9 ⟨8381, by decide⟩
    (prefixCache 12 280) (prefixPartial 12 280) = false := by
  decide +kernel

theorem node_context_12_280_8381 : EJMOriginalGlobalDAGData.nodes 9 ⟨8381, by decide⟩ =
    .split (coordinate 12) (![⟨8108, by decide⟩,⟨8220, by decide⟩,⟨8308, by decide⟩,⟨8380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_280_8381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280 ⟨8381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 280
    ⟨8381, by decide⟩ (by decide) (![⟨8108, by decide⟩,⟨8220, by decide⟩,⟨8308, by decide⟩,⟨8380, by decide⟩]) unmarked_context_12_280_8381 node_context_12_280_8381
  intro a
  fin_cases a
  · exact context_13_1120_8108
  · exact context_13_1121_8220
  · exact context_13_1122_8308
  · exact context_13_1123_8380

theorem selected_cut_00131 : selected 8 ⟨8440, by decide⟩
    (prefixPartial 13 1124) = some ⟨13, 2, 0, 8440, 1124, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_1124_8440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124 ⟨8440, by decide⟩ :=
  accepted_of_selected 13 1124 ⟨8440, by decide⟩ ⟨13, 2, 0, 8440, 1124, 3337, 16384⟩
    (by decide) selected_cut_00131

theorem selected_cut_00132 : selected 8 ⟨8499, by decide⟩
    (prefixPartial 13 1125) = some ⟨13, 2, 0, 8499, 1125, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_1125_8499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1125 ⟨8499, by decide⟩ :=
  accepted_of_selected 13 1125 ⟨8499, by decide⟩ ⟨13, 2, 0, 8499, 1125, 2629, 16384⟩
    (by decide) selected_cut_00132

theorem selected_cut_00133 : selected 8 ⟨8561, by decide⟩
    (prefixPartial 13 1126) = some ⟨13, 2, 0, 8561, 1126, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_1126_8561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1126 ⟨8561, by decide⟩ :=
  accepted_of_selected 13 1126 ⟨8561, by decide⟩ ⟨13, 2, 0, 8561, 1126, 2477, 16384⟩
    (by decide) selected_cut_00133

theorem selected_cut_00134 : selected 8 ⟨8595, by decide⟩
    (prefixPartial 13 1127) = some ⟨13, 2, 0, 8595, 1127, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_1127_8595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1127 ⟨8595, by decide⟩ :=
  accepted_of_selected 13 1127 ⟨8595, by decide⟩ ⟨13, 2, 0, 8595, 1127, 1325, 16384⟩
    (by decide) selected_cut_00134

theorem unmarked_context_12_281_8596 : frontier 9 ⟨8596, by decide⟩
    (prefixCache 12 281) (prefixPartial 12 281) = false := by
  decide +kernel

theorem node_context_12_281_8596 : EJMOriginalGlobalDAGData.nodes 9 ⟨8596, by decide⟩ =
    .split (coordinate 12) (![⟨8440, by decide⟩,⟨8499, by decide⟩,⟨8561, by decide⟩,⟨8595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281_8596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281 ⟨8596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281
    ⟨8596, by decide⟩ (by decide) (![⟨8440, by decide⟩,⟨8499, by decide⟩,⟨8561, by decide⟩,⟨8595, by decide⟩]) unmarked_context_12_281_8596 node_context_12_281_8596
  intro a
  fin_cases a
  · exact context_13_1124_8440
  · exact context_13_1125_8499
  · exact context_13_1126_8561
  · exact context_13_1127_8595

theorem selected_cut_00135 : selected 8 ⟨8656, by decide⟩
    (prefixPartial 13 1128) = some ⟨13, 2, 0, 8656, 1128, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_1128_8656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1128 ⟨8656, by decide⟩ :=
  accepted_of_selected 13 1128 ⟨8656, by decide⟩ ⟨13, 2, 0, 8656, 1128, 3005, 16384⟩
    (by decide) selected_cut_00135

theorem selected_cut_00136 : selected 8 ⟨8712, by decide⟩
    (prefixPartial 13 1129) = some ⟨13, 2, 0, 8712, 1129, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_1129_8712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1129 ⟨8712, by decide⟩ :=
  accepted_of_selected 13 1129 ⟨8712, by decide⟩ ⟨13, 2, 0, 8712, 1129, 2469, 16384⟩
    (by decide) selected_cut_00136

theorem selected_cut_00137 : selected 8 ⟨8748, by decide⟩
    (prefixPartial 13 1130) = some ⟨13, 2, 0, 8748, 1130, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_1130_8748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1130 ⟨8748, by decide⟩ :=
  accepted_of_selected 13 1130 ⟨8748, by decide⟩ ⟨13, 2, 0, 8748, 1130, 2081, 16384⟩
    (by decide) selected_cut_00137

theorem selected_cut_00138 : selected 8 ⟨8767, by decide⟩
    (prefixPartial 13 1131) = some ⟨13, 2, 0, 8767, 1131, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_1131_8767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1131 ⟨8767, by decide⟩ :=
  accepted_of_selected 13 1131 ⟨8767, by decide⟩ ⟨13, 2, 0, 8767, 1131, 1289, 16384⟩
    (by decide) selected_cut_00138

theorem unmarked_context_12_282_8768 : frontier 9 ⟨8768, by decide⟩
    (prefixCache 12 282) (prefixPartial 12 282) = false := by
  decide +kernel

theorem node_context_12_282_8768 : EJMOriginalGlobalDAGData.nodes 9 ⟨8768, by decide⟩ =
    .split (coordinate 12) (![⟨8656, by decide⟩,⟨8712, by decide⟩,⟨8748, by decide⟩,⟨8767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_282_8768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282 ⟨8768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 282
    ⟨8768, by decide⟩ (by decide) (![⟨8656, by decide⟩,⟨8712, by decide⟩,⟨8748, by decide⟩,⟨8767, by decide⟩]) unmarked_context_12_282_8768 node_context_12_282_8768
  intro a
  fin_cases a
  · exact context_13_1128_8656
  · exact context_13_1129_8712
  · exact context_13_1130_8748
  · exact context_13_1131_8767

theorem selected_cut_00139 : selected 8 ⟨8839, by decide⟩
    (prefixPartial 13 1132) = some ⟨13, 2, 0, 8839, 1132, 3277, 16384⟩ := by
  decide +kernel

theorem context_13_1132_8839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132 ⟨8839, by decide⟩ :=
  accepted_of_selected 13 1132 ⟨8839, by decide⟩ ⟨13, 2, 0, 8839, 1132, 3277, 16384⟩
    (by decide) selected_cut_00139

theorem selected_cut_00140 : selected 8 ⟨8896, by decide⟩
    (prefixPartial 13 1133) = some ⟨13, 2, 0, 8896, 1133, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_1133_8896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1133 ⟨8896, by decide⟩ :=
  accepted_of_selected 13 1133 ⟨8896, by decide⟩ ⟨13, 2, 0, 8896, 1133, 2849, 16384⟩
    (by decide) selected_cut_00140

theorem selected_cut_00141 : selected 8 ⟨8952, by decide⟩
    (prefixPartial 13 1134) = some ⟨13, 2, 0, 8952, 1134, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_1134_8952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1134 ⟨8952, by decide⟩ :=
  accepted_of_selected 13 1134 ⟨8952, by decide⟩ ⟨13, 2, 0, 8952, 1134, 2557, 16384⟩
    (by decide) selected_cut_00141

theorem selected_cut_00142 : selected 8 ⟨8979, by decide⟩
    (prefixPartial 13 1135) = some ⟨13, 2, 0, 8979, 1135, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_1135_8979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1135 ⟨8979, by decide⟩ :=
  accepted_of_selected 13 1135 ⟨8979, by decide⟩ ⟨13, 2, 0, 8979, 1135, 1233, 16384⟩
    (by decide) selected_cut_00142

theorem unmarked_context_12_283_8980 : frontier 9 ⟨8980, by decide⟩
    (prefixCache 12 283) (prefixPartial 12 283) = false := by
  decide +kernel

theorem node_context_12_283_8980 : EJMOriginalGlobalDAGData.nodes 9 ⟨8980, by decide⟩ =
    .split (coordinate 12) (![⟨8839, by decide⟩,⟨8896, by decide⟩,⟨8952, by decide⟩,⟨8979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_283_8980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283 ⟨8980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 283
    ⟨8980, by decide⟩ (by decide) (![⟨8839, by decide⟩,⟨8896, by decide⟩,⟨8952, by decide⟩,⟨8979, by decide⟩]) unmarked_context_12_283_8980 node_context_12_283_8980
  intro a
  fin_cases a
  · exact context_13_1132_8839
  · exact context_13_1133_8896
  · exact context_13_1134_8952
  · exact context_13_1135_8979

theorem unmarked_context_11_70_8981 : frontier 10 ⟨8981, by decide⟩
    (prefixCache 11 70) (prefixPartial 11 70) = false := by
  decide +kernel

theorem node_context_11_70_8981 : EJMOriginalGlobalDAGData.nodes 10 ⟨8981, by decide⟩ =
    .split (coordinate 11) (![⟨8381, by decide⟩,⟨8596, by decide⟩,⟨8768, by decide⟩,⟨8980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70_8981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70 ⟨8981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70
    ⟨8981, by decide⟩ (by decide) (![⟨8381, by decide⟩,⟨8596, by decide⟩,⟨8768, by decide⟩,⟨8980, by decide⟩]) unmarked_context_11_70_8981 node_context_11_70_8981
  intro a
  fin_cases a
  · exact context_12_280_8381
  · exact context_12_281_8596
  · exact context_12_282_8768
  · exact context_12_283_8980

theorem selected_cut_00143 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 71) = some ⟨11, 1, 0, 1736, 71, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 71 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 71, 1, 262144⟩
    (by decide) selected_cut_00143

theorem unmarked_context_10_17_8982 : frontier 11 ⟨8982, by decide⟩
    (prefixCache 10 17) (prefixPartial 10 17) = false := by
  decide +kernel

theorem node_context_10_17_8982 : EJMOriginalGlobalDAGData.nodes 11 ⟨8982, by decide⟩ =
    .split (coordinate 10) (![⟨7462, by decide⟩,⟨8032, by decide⟩,⟨8981, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17_8982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17 ⟨8982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17
    ⟨8982, by decide⟩ (by decide) (![⟨7462, by decide⟩,⟨8032, by decide⟩,⟨8981, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17_8982 node_context_10_17_8982
  intro a
  fin_cases a
  · exact context_11_68_7462
  · exact context_11_69_8032
  · exact context_11_70_8981
  · exact context_11_71_1736

theorem selected_cut_00144 : selected 8 ⟨9035, by decide⟩
    (prefixPartial 13 1152) = some ⟨13, 2, 0, 9035, 1152, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_1152_9035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1152 ⟨9035, by decide⟩ :=
  accepted_of_selected 13 1152 ⟨9035, by decide⟩ ⟨13, 2, 0, 9035, 1152, 2361, 16384⟩
    (by decide) selected_cut_00144

theorem selected_cut_00145 : selected 8 ⟨9092, by decide⟩
    (prefixPartial 13 1153) = some ⟨13, 2, 0, 9092, 1153, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_1153_9092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153 ⟨9092, by decide⟩ :=
  accepted_of_selected 13 1153 ⟨9092, by decide⟩ ⟨13, 2, 0, 9092, 1153, 2649, 16384⟩
    (by decide) selected_cut_00145

theorem selected_cut_00146 : selected 8 ⟨9149, by decide⟩
    (prefixPartial 13 1154) = some ⟨13, 2, 0, 9149, 1154, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_1154_9149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154 ⟨9149, by decide⟩ :=
  accepted_of_selected 13 1154 ⟨9149, by decide⟩ ⟨13, 2, 0, 9149, 1154, 1937, 16384⟩
    (by decide) selected_cut_00146

theorem selected_cut_00147 : selected 8 ⟨9180, by decide⟩
    (prefixPartial 13 1155) = some ⟨13, 2, 0, 9180, 1155, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_1155_9180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1155 ⟨9180, by decide⟩ :=
  accepted_of_selected 13 1155 ⟨9180, by decide⟩ ⟨13, 2, 0, 9180, 1155, 1249, 16384⟩
    (by decide) selected_cut_00147

theorem unmarked_context_12_288_9181 : frontier 9 ⟨9181, by decide⟩
    (prefixCache 12 288) (prefixPartial 12 288) = false := by
  decide +kernel

theorem node_context_12_288_9181 : EJMOriginalGlobalDAGData.nodes 9 ⟨9181, by decide⟩ =
    .split (coordinate 12) (![⟨9035, by decide⟩,⟨9092, by decide⟩,⟨9149, by decide⟩,⟨9180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288_9181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288 ⟨9181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288
    ⟨9181, by decide⟩ (by decide) (![⟨9035, by decide⟩,⟨9092, by decide⟩,⟨9149, by decide⟩,⟨9180, by decide⟩]) unmarked_context_12_288_9181 node_context_12_288_9181
  intro a
  fin_cases a
  · exact context_13_1152_9035
  · exact context_13_1153_9092
  · exact context_13_1154_9149
  · exact context_13_1155_9180

theorem selected_cut_00148 : selected 8 ⟨9228, by decide⟩
    (prefixPartial 13 1156) = some ⟨13, 2, 0, 9228, 1156, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_1156_9228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1156 ⟨9228, by decide⟩ :=
  accepted_of_selected 13 1156 ⟨9228, by decide⟩ ⟨13, 2, 0, 9228, 1156, 1297, 16384⟩
    (by decide) selected_cut_00148

theorem selected_cut_00149 : selected 8 ⟨9262, by decide⟩
    (prefixPartial 13 1157) = some ⟨13, 2, 0, 9262, 1157, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_1157_9262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157 ⟨9262, by decide⟩ :=
  accepted_of_selected 13 1157 ⟨9262, by decide⟩ ⟨13, 2, 0, 9262, 1157, 1441, 16384⟩
    (by decide) selected_cut_00149

theorem selected_cut_00150 : selected 8 ⟨9293, by decide⟩
    (prefixPartial 13 1158) = some ⟨13, 2, 0, 9293, 1158, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_1158_9293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1158 ⟨9293, by decide⟩ :=
  accepted_of_selected 13 1158 ⟨9293, by decide⟩ ⟨13, 2, 0, 9293, 1158, 1277, 16384⟩
    (by decide) selected_cut_00150

theorem selected_cut_00151 : selected 8 ⟨9314, by decide⟩
    (prefixPartial 13 1159) = some ⟨13, 2, 0, 9314, 1159, 953, 16384⟩ := by
  decide +kernel

theorem context_13_1159_9314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1159 ⟨9314, by decide⟩ :=
  accepted_of_selected 13 1159 ⟨9314, by decide⟩ ⟨13, 2, 0, 9314, 1159, 953, 16384⟩
    (by decide) selected_cut_00151

theorem unmarked_context_12_289_9315 : frontier 9 ⟨9315, by decide⟩
    (prefixCache 12 289) (prefixPartial 12 289) = false := by
  decide +kernel

theorem node_context_12_289_9315 : EJMOriginalGlobalDAGData.nodes 9 ⟨9315, by decide⟩ =
    .split (coordinate 12) (![⟨9228, by decide⟩,⟨9262, by decide⟩,⟨9293, by decide⟩,⟨9314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_289_9315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289 ⟨9315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 289
    ⟨9315, by decide⟩ (by decide) (![⟨9228, by decide⟩,⟨9262, by decide⟩,⟨9293, by decide⟩,⟨9314, by decide⟩]) unmarked_context_12_289_9315 node_context_12_289_9315
  intro a
  fin_cases a
  · exact context_13_1156_9228
  · exact context_13_1157_9262
  · exact context_13_1158_9293
  · exact context_13_1159_9314

theorem selected_cut_00152 : selected 8 ⟨9352, by decide⟩
    (prefixPartial 13 1160) = some ⟨13, 2, 0, 9352, 1160, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_1160_9352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1160 ⟨9352, by decide⟩ :=
  accepted_of_selected 13 1160 ⟨9352, by decide⟩ ⟨13, 2, 0, 9352, 1160, 1757, 16384⟩
    (by decide) selected_cut_00152

theorem selected_cut_00153 : selected 8 ⟨9396, by decide⟩
    (prefixPartial 13 1161) = some ⟨13, 2, 0, 9396, 1161, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_1161_9396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1161 ⟨9396, by decide⟩ :=
  accepted_of_selected 13 1161 ⟨9396, by decide⟩ ⟨13, 2, 0, 9396, 1161, 1933, 16384⟩
    (by decide) selected_cut_00153

theorem selected_cut_00154 : selected 8 ⟨9427, by decide⟩
    (prefixPartial 13 1162) = some ⟨13, 2, 0, 9427, 1162, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_1162_9427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162 ⟨9427, by decide⟩ :=
  accepted_of_selected 13 1162 ⟨9427, by decide⟩ ⟨13, 2, 0, 9427, 1162, 1481, 16384⟩
    (by decide) selected_cut_00154

theorem selected_cut_00155 : selected 8 ⟨9452, by decide⟩
    (prefixPartial 13 1163) = some ⟨13, 2, 0, 9452, 1163, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1163_9452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1163 ⟨9452, by decide⟩ :=
  accepted_of_selected 13 1163 ⟨9452, by decide⟩ ⟨13, 2, 0, 9452, 1163, 1101, 16384⟩
    (by decide) selected_cut_00155

theorem unmarked_context_12_290_9453 : frontier 9 ⟨9453, by decide⟩
    (prefixCache 12 290) (prefixPartial 12 290) = false := by
  decide +kernel

theorem node_context_12_290_9453 : EJMOriginalGlobalDAGData.nodes 9 ⟨9453, by decide⟩ =
    .split (coordinate 12) (![⟨9352, by decide⟩,⟨9396, by decide⟩,⟨9427, by decide⟩,⟨9452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_290_9453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290 ⟨9453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 290
    ⟨9453, by decide⟩ (by decide) (![⟨9352, by decide⟩,⟨9396, by decide⟩,⟨9427, by decide⟩,⟨9452, by decide⟩]) unmarked_context_12_290_9453 node_context_12_290_9453
  intro a
  fin_cases a
  · exact context_13_1160_9352
  · exact context_13_1161_9396
  · exact context_13_1162_9427
  · exact context_13_1163_9452

theorem selected_cut_00156 : selected 8 ⟨9490, by decide⟩
    (prefixPartial 13 1164) = some ⟨13, 2, 0, 9490, 1164, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_1164_9490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1164 ⟨9490, by decide⟩ :=
  accepted_of_selected 13 1164 ⟨9490, by decide⟩ ⟨13, 2, 0, 9490, 1164, 1545, 16384⟩
    (by decide) selected_cut_00156

theorem selected_cut_00157 : selected 8 ⟨9525, by decide⟩
    (prefixPartial 13 1165) = some ⟨13, 2, 0, 9525, 1165, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_1165_9525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1165 ⟨9525, by decide⟩ :=
  accepted_of_selected 13 1165 ⟨9525, by decide⟩ ⟨13, 2, 0, 9525, 1165, 1641, 16384⟩
    (by decide) selected_cut_00157

theorem selected_cut_00158 : selected 8 ⟨9559, by decide⟩
    (prefixPartial 13 1166) = some ⟨13, 2, 0, 9559, 1166, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1166_9559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1166 ⟨9559, by decide⟩ :=
  accepted_of_selected 13 1166 ⟨9559, by decide⟩ ⟨13, 2, 0, 9559, 1166, 1321, 16384⟩
    (by decide) selected_cut_00158

theorem selected_cut_00159 : selected 8 ⟨9577, by decide⟩
    (prefixPartial 13 1167) = some ⟨13, 2, 0, 9577, 1167, 921, 16384⟩ := by
  decide +kernel

theorem context_13_1167_9577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1167 ⟨9577, by decide⟩ :=
  accepted_of_selected 13 1167 ⟨9577, by decide⟩ ⟨13, 2, 0, 9577, 1167, 921, 16384⟩
    (by decide) selected_cut_00159

theorem unmarked_context_12_291_9578 : frontier 9 ⟨9578, by decide⟩
    (prefixCache 12 291) (prefixPartial 12 291) = false := by
  decide +kernel

theorem node_context_12_291_9578 : EJMOriginalGlobalDAGData.nodes 9 ⟨9578, by decide⟩ =
    .split (coordinate 12) (![⟨9490, by decide⟩,⟨9525, by decide⟩,⟨9559, by decide⟩,⟨9577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_291_9578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 291 ⟨9578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 291
    ⟨9578, by decide⟩ (by decide) (![⟨9490, by decide⟩,⟨9525, by decide⟩,⟨9559, by decide⟩,⟨9577, by decide⟩]) unmarked_context_12_291_9578 node_context_12_291_9578
  intro a
  fin_cases a
  · exact context_13_1164_9490
  · exact context_13_1165_9525
  · exact context_13_1166_9559
  · exact context_13_1167_9577

theorem unmarked_context_11_72_9579 : frontier 10 ⟨9579, by decide⟩
    (prefixCache 11 72) (prefixPartial 11 72) = false := by
  decide +kernel

theorem node_context_11_72_9579 : EJMOriginalGlobalDAGData.nodes 10 ⟨9579, by decide⟩ =
    .split (coordinate 11) (![⟨9181, by decide⟩,⟨9315, by decide⟩,⟨9453, by decide⟩,⟨9578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72_9579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72 ⟨9579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72
    ⟨9579, by decide⟩ (by decide) (![⟨9181, by decide⟩,⟨9315, by decide⟩,⟨9453, by decide⟩,⟨9578, by decide⟩]) unmarked_context_11_72_9579 node_context_11_72_9579
  intro a
  fin_cases a
  · exact context_12_288_9181
  · exact context_12_289_9315
  · exact context_12_290_9453
  · exact context_12_291_9578

theorem selected_cut_00160 : selected 8 ⟨9643, by decide⟩
    (prefixPartial 13 1168) = some ⟨13, 2, 0, 9643, 1168, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_1168_9643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1168 ⟨9643, by decide⟩ :=
  accepted_of_selected 13 1168 ⟨9643, by decide⟩ ⟨13, 2, 0, 9643, 1168, 2253, 16384⟩
    (by decide) selected_cut_00160

theorem selected_cut_00161 : selected 8 ⟨9712, by decide⟩
    (prefixPartial 13 1169) = some ⟨13, 2, 0, 9712, 1169, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_1169_9712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1169 ⟨9712, by decide⟩ :=
  accepted_of_selected 13 1169 ⟨9712, by decide⟩ ⟨13, 2, 0, 9712, 1169, 3245, 16384⟩
    (by decide) selected_cut_00161

theorem selected_cut_00162 : selected 8 ⟨9802, by decide⟩
    (prefixPartial 13 1170) = some ⟨13, 2, 0, 9802, 1170, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_1170_9802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1170 ⟨9802, by decide⟩ :=
  accepted_of_selected 13 1170 ⟨9802, by decide⟩ ⟨13, 2, 0, 9802, 1170, 2933, 16384⟩
    (by decide) selected_cut_00162

theorem selected_cut_00163 : selected 8 ⟨9864, by decide⟩
    (prefixPartial 13 1171) = some ⟨13, 2, 0, 9864, 1171, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_1171_9864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1171 ⟨9864, by decide⟩ :=
  accepted_of_selected 13 1171 ⟨9864, by decide⟩ ⟨13, 2, 0, 9864, 1171, 1669, 16384⟩
    (by decide) selected_cut_00163

theorem unmarked_context_12_292_9865 : frontier 9 ⟨9865, by decide⟩
    (prefixCache 12 292) (prefixPartial 12 292) = false := by
  decide +kernel

theorem node_context_12_292_9865 : EJMOriginalGlobalDAGData.nodes 9 ⟨9865, by decide⟩ =
    .split (coordinate 12) (![⟨9643, by decide⟩,⟨9712, by decide⟩,⟨9802, by decide⟩,⟨9864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_292_9865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 292 ⟨9865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 292
    ⟨9865, by decide⟩ (by decide) (![⟨9643, by decide⟩,⟨9712, by decide⟩,⟨9802, by decide⟩,⟨9864, by decide⟩]) unmarked_context_12_292_9865 node_context_12_292_9865
  intro a
  fin_cases a
  · exact context_13_1168_9643
  · exact context_13_1169_9712
  · exact context_13_1170_9802
  · exact context_13_1171_9864

theorem selected_cut_00164 : selected 8 ⟨9932, by decide⟩
    (prefixPartial 13 1172) = some ⟨13, 2, 0, 9932, 1172, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_1172_9932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1172 ⟨9932, by decide⟩ :=
  accepted_of_selected 13 1172 ⟨9932, by decide⟩ ⟨13, 2, 0, 9932, 1172, 2521, 16384⟩
    (by decide) selected_cut_00164

theorem selected_cut_00165 : selected 8 ⟨10002, by decide⟩
    (prefixPartial 13 1173) = some ⟨13, 2, 0, 10002, 1173, 3865, 16384⟩ := by
  decide +kernel

theorem context_13_1173_10002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1173 ⟨10002, by decide⟩ :=
  accepted_of_selected 13 1173 ⟨10002, by decide⟩ ⟨13, 2, 0, 10002, 1173, 3865, 16384⟩
    (by decide) selected_cut_00165

theorem selected_cut_00166 : selected 8 ⟨10083, by decide⟩
    (prefixPartial 13 1174) = some ⟨13, 2, 0, 10083, 1174, 3241, 16384⟩ := by
  decide +kernel

theorem context_13_1174_10083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1174 ⟨10083, by decide⟩ :=
  accepted_of_selected 13 1174 ⟨10083, by decide⟩ ⟨13, 2, 0, 10083, 1174, 3241, 16384⟩
    (by decide) selected_cut_00166

theorem selected_cut_00167 : selected 8 ⟨10160, by decide⟩
    (prefixPartial 13 1175) = some ⟨13, 2, 0, 10160, 1175, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_1175_10160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1175 ⟨10160, by decide⟩ :=
  accepted_of_selected 13 1175 ⟨10160, by decide⟩ ⟨13, 2, 0, 10160, 1175, 1865, 16384⟩
    (by decide) selected_cut_00167

theorem unmarked_context_12_293_10161 : frontier 9 ⟨10161, by decide⟩
    (prefixCache 12 293) (prefixPartial 12 293) = false := by
  decide +kernel

theorem node_context_12_293_10161 : EJMOriginalGlobalDAGData.nodes 9 ⟨10161, by decide⟩ =
    .split (coordinate 12) (![⟨9932, by decide⟩,⟨10002, by decide⟩,⟨10083, by decide⟩,⟨10160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_293_10161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 293 ⟨10161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 293
    ⟨10161, by decide⟩ (by decide) (![⟨9932, by decide⟩,⟨10002, by decide⟩,⟨10083, by decide⟩,⟨10160, by decide⟩]) unmarked_context_12_293_10161 node_context_12_293_10161
  intro a
  fin_cases a
  · exact context_13_1172_9932
  · exact context_13_1173_10002
  · exact context_13_1174_10083
  · exact context_13_1175_10160

theorem selected_cut_00168 : selected 8 ⟨10214, by decide⟩
    (prefixPartial 13 1176) = some ⟨13, 2, 0, 10214, 1176, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_1176_10214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1176 ⟨10214, by decide⟩ :=
  accepted_of_selected 13 1176 ⟨10214, by decide⟩ ⟨13, 2, 0, 10214, 1176, 1829, 16384⟩
    (by decide) selected_cut_00168

theorem selected_cut_00169 : selected 8 ⟨10269, by decide⟩
    (prefixPartial 13 1177) = some ⟨13, 2, 0, 10269, 1177, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_1177_10269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1177 ⟨10269, by decide⟩ :=
  accepted_of_selected 13 1177 ⟨10269, by decide⟩ ⟨13, 2, 0, 10269, 1177, 3141, 16384⟩
    (by decide) selected_cut_00169

theorem selected_cut_00170 : selected 8 ⟨10317, by decide⟩
    (prefixPartial 13 1178) = some ⟨13, 2, 0, 10317, 1178, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_1178_10317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1178 ⟨10317, by decide⟩ :=
  accepted_of_selected 13 1178 ⟨10317, by decide⟩ ⟨13, 2, 0, 10317, 1178, 2357, 16384⟩
    (by decide) selected_cut_00170

theorem selected_cut_00171 : selected 8 ⟨10347, by decide⟩
    (prefixPartial 13 1179) = some ⟨13, 2, 0, 10347, 1179, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_1179_10347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1179 ⟨10347, by decide⟩ :=
  accepted_of_selected 13 1179 ⟨10347, by decide⟩ ⟨13, 2, 0, 10347, 1179, 1433, 16384⟩
    (by decide) selected_cut_00171

theorem unmarked_context_12_294_10348 : frontier 9 ⟨10348, by decide⟩
    (prefixCache 12 294) (prefixPartial 12 294) = false := by
  decide +kernel

theorem node_context_12_294_10348 : EJMOriginalGlobalDAGData.nodes 9 ⟨10348, by decide⟩ =
    .split (coordinate 12) (![⟨10214, by decide⟩,⟨10269, by decide⟩,⟨10317, by decide⟩,⟨10347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_294_10348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 294 ⟨10348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 294
    ⟨10348, by decide⟩ (by decide) (![⟨10214, by decide⟩,⟨10269, by decide⟩,⟨10317, by decide⟩,⟨10347, by decide⟩]) unmarked_context_12_294_10348 node_context_12_294_10348
  intro a
  fin_cases a
  · exact context_13_1176_10214
  · exact context_13_1177_10269
  · exact context_13_1178_10317
  · exact context_13_1179_10347

theorem selected_cut_00172 : selected 8 ⟨10385, by decide⟩
    (prefixPartial 13 1180) = some ⟨13, 2, 0, 10385, 1180, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_1180_10385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1180 ⟨10385, by decide⟩ :=
  accepted_of_selected 13 1180 ⟨10385, by decide⟩ ⟨13, 2, 0, 10385, 1180, 1549, 16384⟩
    (by decide) selected_cut_00172

theorem selected_cut_00173 : selected 8 ⟨10431, by decide⟩
    (prefixPartial 13 1181) = some ⟨13, 2, 0, 10431, 1181, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_1181_10431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1181 ⟨10431, by decide⟩ :=
  accepted_of_selected 13 1181 ⟨10431, by decide⟩ ⟨13, 2, 0, 10431, 1181, 2921, 16384⟩
    (by decide) selected_cut_00173

theorem selected_cut_00174 : selected 8 ⟨10474, by decide⟩
    (prefixPartial 13 1182) = some ⟨13, 2, 0, 10474, 1182, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_1182_10474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1182 ⟨10474, by decide⟩ :=
  accepted_of_selected 13 1182 ⟨10474, by decide⟩ ⟨13, 2, 0, 10474, 1182, 2121, 16384⟩
    (by decide) selected_cut_00174

theorem selected_cut_00175 : selected 8 ⟨10496, by decide⟩
    (prefixPartial 13 1183) = some ⟨13, 2, 0, 10496, 1183, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_1183_10496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1183 ⟨10496, by decide⟩ :=
  accepted_of_selected 13 1183 ⟨10496, by decide⟩ ⟨13, 2, 0, 10496, 1183, 1225, 16384⟩
    (by decide) selected_cut_00175

theorem unmarked_context_12_295_10497 : frontier 9 ⟨10497, by decide⟩
    (prefixCache 12 295) (prefixPartial 12 295) = false := by
  decide +kernel

theorem node_context_12_295_10497 : EJMOriginalGlobalDAGData.nodes 9 ⟨10497, by decide⟩ =
    .split (coordinate 12) (![⟨10385, by decide⟩,⟨10431, by decide⟩,⟨10474, by decide⟩,⟨10496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_295_10497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 295 ⟨10497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 295
    ⟨10497, by decide⟩ (by decide) (![⟨10385, by decide⟩,⟨10431, by decide⟩,⟨10474, by decide⟩,⟨10496, by decide⟩]) unmarked_context_12_295_10497 node_context_12_295_10497
  intro a
  fin_cases a
  · exact context_13_1180_10385
  · exact context_13_1181_10431
  · exact context_13_1182_10474
  · exact context_13_1183_10496

theorem unmarked_context_11_73_10498 : frontier 10 ⟨10498, by decide⟩
    (prefixCache 11 73) (prefixPartial 11 73) = false := by
  decide +kernel

theorem node_context_11_73_10498 : EJMOriginalGlobalDAGData.nodes 10 ⟨10498, by decide⟩ =
    .split (coordinate 11) (![⟨9865, by decide⟩,⟨10161, by decide⟩,⟨10348, by decide⟩,⟨10497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_73_10498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 73 ⟨10498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 73
    ⟨10498, by decide⟩ (by decide) (![⟨9865, by decide⟩,⟨10161, by decide⟩,⟨10348, by decide⟩,⟨10497, by decide⟩]) unmarked_context_11_73_10498 node_context_11_73_10498
  intro a
  fin_cases a
  · exact context_12_292_9865
  · exact context_12_293_10161
  · exact context_12_294_10348
  · exact context_12_295_10497

theorem selected_cut_00176 : selected 8 ⟨10539, by decide⟩
    (prefixPartial 13 1184) = some ⟨13, 2, 0, 10539, 1184, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_1184_10539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1184 ⟨10539, by decide⟩ :=
  accepted_of_selected 13 1184 ⟨10539, by decide⟩ ⟨13, 2, 0, 10539, 1184, 1373, 16384⟩
    (by decide) selected_cut_00176

theorem selected_cut_00177 : selected 8 ⟨10629, by decide⟩
    (prefixPartial 13 1185) = some ⟨13, 2, 0, 10629, 1185, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_1185_10629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1185 ⟨10629, by decide⟩ :=
  accepted_of_selected 13 1185 ⟨10629, by decide⟩ ⟨13, 2, 0, 10629, 1185, 3421, 16384⟩
    (by decide) selected_cut_00177

theorem selected_cut_00178 : selected 8 ⟨10697, by decide⟩
    (prefixPartial 13 1186) = some ⟨13, 2, 0, 10697, 1186, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_1186_10697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1186 ⟨10697, by decide⟩ :=
  accepted_of_selected 13 1186 ⟨10697, by decide⟩ ⟨13, 2, 0, 10697, 1186, 2293, 16384⟩
    (by decide) selected_cut_00178

theorem selected_cut_00179 : selected 8 ⟨10743, by decide⟩
    (prefixPartial 13 1187) = some ⟨13, 2, 0, 10743, 1187, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_1187_10743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1187 ⟨10743, by decide⟩ :=
  accepted_of_selected 13 1187 ⟨10743, by decide⟩ ⟨13, 2, 0, 10743, 1187, 1401, 16384⟩
    (by decide) selected_cut_00179

theorem unmarked_context_12_296_10744 : frontier 9 ⟨10744, by decide⟩
    (prefixCache 12 296) (prefixPartial 12 296) = false := by
  decide +kernel

theorem node_context_12_296_10744 : EJMOriginalGlobalDAGData.nodes 9 ⟨10744, by decide⟩ =
    .split (coordinate 12) (![⟨10539, by decide⟩,⟨10629, by decide⟩,⟨10697, by decide⟩,⟨10743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_296_10744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 296 ⟨10744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 296
    ⟨10744, by decide⟩ (by decide) (![⟨10539, by decide⟩,⟨10629, by decide⟩,⟨10697, by decide⟩,⟨10743, by decide⟩]) unmarked_context_12_296_10744 node_context_12_296_10744
  intro a
  fin_cases a
  · exact context_13_1184_10539
  · exact context_13_1185_10629
  · exact context_13_1186_10697
  · exact context_13_1187_10743

theorem selected_cut_00180 : selected 8 ⟨10767, by decide⟩
    (prefixPartial 13 1188) = some ⟨13, 2, 0, 10767, 1188, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_1188_10767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1188 ⟨10767, by decide⟩ :=
  accepted_of_selected 13 1188 ⟨10767, by decide⟩ ⟨13, 2, 0, 10767, 1188, 1037, 16384⟩
    (by decide) selected_cut_00180

theorem selected_cut_00181 : selected 8 ⟨10814, by decide⟩
    (prefixPartial 13 1189) = some ⟨13, 2, 0, 10814, 1189, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_1189_10814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1189 ⟨10814, by decide⟩ :=
  accepted_of_selected 13 1189 ⟨10814, by decide⟩ ⟨13, 2, 0, 10814, 1189, 2293, 16384⟩
    (by decide) selected_cut_00181

theorem selected_cut_00182 : selected 8 ⟨10842, by decide⟩
    (prefixPartial 13 1190) = some ⟨13, 2, 0, 10842, 1190, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_1190_10842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1190 ⟨10842, by decide⟩ :=
  accepted_of_selected 13 1190 ⟨10842, by decide⟩ ⟨13, 2, 0, 10842, 1190, 1657, 16384⟩
    (by decide) selected_cut_00182

theorem selected_cut_00183 : selected 8 ⟨10871, by decide⟩
    (prefixPartial 13 1191) = some ⟨13, 2, 0, 10871, 1191, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_1191_10871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1191 ⟨10871, by decide⟩ :=
  accepted_of_selected 13 1191 ⟨10871, by decide⟩ ⟨13, 2, 0, 10871, 1191, 1213, 16384⟩
    (by decide) selected_cut_00183

theorem unmarked_context_12_297_10872 : frontier 9 ⟨10872, by decide⟩
    (prefixCache 12 297) (prefixPartial 12 297) = false := by
  decide +kernel

theorem node_context_12_297_10872 : EJMOriginalGlobalDAGData.nodes 9 ⟨10872, by decide⟩ =
    .split (coordinate 12) (![⟨10767, by decide⟩,⟨10814, by decide⟩,⟨10842, by decide⟩,⟨10871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_297_10872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297 ⟨10872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 297
    ⟨10872, by decide⟩ (by decide) (![⟨10767, by decide⟩,⟨10814, by decide⟩,⟨10842, by decide⟩,⟨10871, by decide⟩]) unmarked_context_12_297_10872 node_context_12_297_10872
  intro a
  fin_cases a
  · exact context_13_1188_10767
  · exact context_13_1189_10814
  · exact context_13_1190_10842
  · exact context_13_1191_10871

theorem selected_cut_00184 : selected 8 ⟨10896, by decide⟩
    (prefixPartial 13 1192) = some ⟨13, 2, 0, 10896, 1192, 917, 16384⟩ := by
  decide +kernel

theorem context_13_1192_10896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1192 ⟨10896, by decide⟩ :=
  accepted_of_selected 13 1192 ⟨10896, by decide⟩ ⟨13, 2, 0, 10896, 1192, 917, 16384⟩
    (by decide) selected_cut_00184

theorem selected_cut_00185 : selected 8 ⟨10946, by decide⟩
    (prefixPartial 13 1193) = some ⟨13, 2, 0, 10946, 1193, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_1193_10946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1193 ⟨10946, by decide⟩ :=
  accepted_of_selected 13 1193 ⟨10946, by decide⟩ ⟨13, 2, 0, 10946, 1193, 2657, 16384⟩
    (by decide) selected_cut_00185

theorem selected_cut_00186 : selected 8 ⟨10978, by decide⟩
    (prefixPartial 13 1194) = some ⟨13, 2, 0, 10978, 1194, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_1194_10978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1194 ⟨10978, by decide⟩ :=
  accepted_of_selected 13 1194 ⟨10978, by decide⟩ ⟨13, 2, 0, 10978, 1194, 1673, 16384⟩
    (by decide) selected_cut_00186

theorem selected_cut_00187 : selected 8 ⟨11001, by decide⟩
    (prefixPartial 13 1195) = some ⟨13, 2, 0, 11001, 1195, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_1195_11001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1195 ⟨11001, by decide⟩ :=
  accepted_of_selected 13 1195 ⟨11001, by decide⟩ ⟨13, 2, 0, 11001, 1195, 1189, 16384⟩
    (by decide) selected_cut_00187

theorem unmarked_context_12_298_11002 : frontier 9 ⟨11002, by decide⟩
    (prefixCache 12 298) (prefixPartial 12 298) = false := by
  decide +kernel

theorem node_context_12_298_11002 : EJMOriginalGlobalDAGData.nodes 9 ⟨11002, by decide⟩ =
    .split (coordinate 12) (![⟨10896, by decide⟩,⟨10946, by decide⟩,⟨10978, by decide⟩,⟨11001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_298_11002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 298 ⟨11002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 298
    ⟨11002, by decide⟩ (by decide) (![⟨10896, by decide⟩,⟨10946, by decide⟩,⟨10978, by decide⟩,⟨11001, by decide⟩]) unmarked_context_12_298_11002 node_context_12_298_11002
  intro a
  fin_cases a
  · exact context_13_1192_10896
  · exact context_13_1193_10946
  · exact context_13_1194_10978
  · exact context_13_1195_11001

theorem selected_cut_00188 : selected 8 ⟨11028, by decide⟩
    (prefixPartial 13 1196) = some ⟨13, 2, 0, 11028, 1196, 825, 16384⟩ := by
  decide +kernel

theorem context_13_1196_11028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1196 ⟨11028, by decide⟩ :=
  accepted_of_selected 13 1196 ⟨11028, by decide⟩ ⟨13, 2, 0, 11028, 1196, 825, 16384⟩
    (by decide) selected_cut_00188

theorem selected_cut_00189 : selected 8 ⟨11069, by decide⟩
    (prefixPartial 13 1197) = some ⟨13, 2, 0, 11069, 1197, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_1197_11069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197 ⟨11069, by decide⟩ :=
  accepted_of_selected 13 1197 ⟨11069, by decide⟩ ⟨13, 2, 0, 11069, 1197, 2805, 16384⟩
    (by decide) selected_cut_00189

theorem selected_cut_00190 : selected 8 ⟨11100, by decide⟩
    (prefixPartial 13 1198) = some ⟨13, 2, 0, 11100, 1198, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_1198_11100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198 ⟨11100, by decide⟩ :=
  accepted_of_selected 13 1198 ⟨11100, by decide⟩ ⟨13, 2, 0, 11100, 1198, 1593, 16384⟩
    (by decide) selected_cut_00190

theorem selected_cut_00191 : selected 8 ⟨11124, by decide⟩
    (prefixPartial 13 1199) = some ⟨13, 2, 0, 11124, 1199, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_1199_11124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199 ⟨11124, by decide⟩ :=
  accepted_of_selected 13 1199 ⟨11124, by decide⟩ ⟨13, 2, 0, 11124, 1199, 1161, 16384⟩
    (by decide) selected_cut_00191

theorem unmarked_context_12_299_11125 : frontier 9 ⟨11125, by decide⟩
    (prefixCache 12 299) (prefixPartial 12 299) = false := by
  decide +kernel

theorem node_context_12_299_11125 : EJMOriginalGlobalDAGData.nodes 9 ⟨11125, by decide⟩ =
    .split (coordinate 12) (![⟨11028, by decide⟩,⟨11069, by decide⟩,⟨11100, by decide⟩,⟨11124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299_11125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299 ⟨11125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299
    ⟨11125, by decide⟩ (by decide) (![⟨11028, by decide⟩,⟨11069, by decide⟩,⟨11100, by decide⟩,⟨11124, by decide⟩]) unmarked_context_12_299_11125 node_context_12_299_11125
  intro a
  fin_cases a
  · exact context_13_1196_11028
  · exact context_13_1197_11069
  · exact context_13_1198_11100
  · exact context_13_1199_11124

theorem unmarked_context_11_74_11126 : frontier 10 ⟨11126, by decide⟩
    (prefixCache 11 74) (prefixPartial 11 74) = false := by
  decide +kernel

theorem node_context_11_74_11126 : EJMOriginalGlobalDAGData.nodes 10 ⟨11126, by decide⟩ =
    .split (coordinate 11) (![⟨10744, by decide⟩,⟨10872, by decide⟩,⟨11002, by decide⟩,⟨11125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74_11126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74 ⟨11126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74
    ⟨11126, by decide⟩ (by decide) (![⟨10744, by decide⟩,⟨10872, by decide⟩,⟨11002, by decide⟩,⟨11125, by decide⟩]) unmarked_context_11_74_11126 node_context_11_74_11126
  intro a
  fin_cases a
  · exact context_12_296_10744
  · exact context_12_297_10872
  · exact context_12_298_11002
  · exact context_12_299_11125

theorem selected_cut_00192 : selected 8 ⟨11156, by decide⟩
    (prefixPartial 13 1200) = some ⟨13, 2, 0, 11156, 1200, 817, 16384⟩ := by
  decide +kernel

theorem context_13_1200_11156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200 ⟨11156, by decide⟩ :=
  accepted_of_selected 13 1200 ⟨11156, by decide⟩ ⟨13, 2, 0, 11156, 1200, 817, 16384⟩
    (by decide) selected_cut_00192

theorem selected_cut_00193 : selected 8 ⟨11251, by decide⟩
    (prefixPartial 13 1201) = some ⟨13, 2, 0, 11251, 1201, 3829, 16384⟩ := by
  decide +kernel

theorem context_13_1201_11251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201 ⟨11251, by decide⟩ :=
  accepted_of_selected 13 1201 ⟨11251, by decide⟩ ⟨13, 2, 0, 11251, 1201, 3829, 16384⟩
    (by decide) selected_cut_00193

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
