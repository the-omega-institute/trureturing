/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover375
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36098 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18005) = some ⟨10, 1, 0, 893098, 18005, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18005_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18005 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18005 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18005, 1, 1048576⟩
    (by decide) selected_cut_36098

theorem selected_cut_36099 : selected 10 ⟨952878, by decide⟩
    (prefixPartial 11 72024) = some ⟨11, 2, 0, 952878, 72024, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_72024_952878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72024 ⟨952878, by decide⟩ :=
  accepted_of_selected 11 72024 ⟨952878, by decide⟩ ⟨11, 2, 0, 952878, 72024, 3545, 262144⟩
    (by decide) selected_cut_36099

theorem selected_cut_36100 : selected 10 ⟨952939, by decide⟩
    (prefixPartial 11 72025) = some ⟨11, 2, 0, 952939, 72025, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_72025_952939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72025 ⟨952939, by decide⟩ :=
  accepted_of_selected 11 72025 ⟨952939, by decide⟩ ⟨11, 2, 0, 952939, 72025, 2313, 262144⟩
    (by decide) selected_cut_36100

theorem selected_cut_36101 : selected 10 ⟨952989, by decide⟩
    (prefixPartial 11 72026) = some ⟨11, 2, 0, 952989, 72026, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_72026_952989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72026 ⟨952989, by decide⟩ :=
  accepted_of_selected 11 72026 ⟨952989, by decide⟩ ⟨11, 2, 0, 952989, 72026, 1941, 262144⟩
    (by decide) selected_cut_36101

theorem selected_cut_36102 : selected 10 ⟨953079, by decide⟩
    (prefixPartial 11 72027) = some ⟨11, 2, 0, 953079, 72027, 3241, 262144⟩ := by
  decide +kernel

theorem context_11_72027_953079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72027 ⟨953079, by decide⟩ :=
  accepted_of_selected 11 72027 ⟨953079, by decide⟩ ⟨11, 2, 0, 953079, 72027, 3241, 262144⟩
    (by decide) selected_cut_36102

theorem unmarked_context_10_18006_953080 : frontier 11 ⟨953080, by decide⟩
    (prefixCache 10 18006) (prefixPartial 10 18006) = false := by
  decide +kernel

theorem node_context_10_18006_953080 : EJMOriginalGlobalDAGData.nodes 11 ⟨953080, by decide⟩ =
    .split (coordinate 10) (![⟨952878, by decide⟩,⟨952939, by decide⟩,⟨952989, by decide⟩,⟨953079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18006_953080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18006 ⟨953080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18006
    ⟨953080, by decide⟩ (by decide) (![⟨952878, by decide⟩,⟨952939, by decide⟩,⟨952989, by decide⟩,⟨953079, by decide⟩]) unmarked_context_10_18006_953080 node_context_10_18006_953080
  intro a
  fin_cases a
  · exact context_11_72024_952878
  · exact context_11_72025_952939
  · exact context_11_72026_952989
  · exact context_11_72027_953079

theorem selected_cut_36103 : selected 11 ⟨953204, by decide⟩
    (prefixPartial 10 18007) = some ⟨10, 2, 0, 953204, 18007, 3653, 1048576⟩ := by
  decide +kernel

theorem context_10_18007_953204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18007 ⟨953204, by decide⟩ :=
  accepted_of_selected 10 18007 ⟨953204, by decide⟩ ⟨10, 2, 0, 953204, 18007, 3653, 1048576⟩
    (by decide) selected_cut_36103

theorem unmarked_context_9_4501_953205 : frontier 12 ⟨953205, by decide⟩
    (prefixCache 9 4501) (prefixPartial 9 4501) = false := by
  decide +kernel

theorem node_context_9_4501_953205 : EJMOriginalGlobalDAGData.nodes 12 ⟨953205, by decide⟩ =
    .split (coordinate 9) (![⟨952781, by decide⟩,⟨893098, by decide⟩,⟨953080, by decide⟩,⟨953204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4501_953205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4501 ⟨953205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4501
    ⟨953205, by decide⟩ (by decide) (![⟨952781, by decide⟩,⟨893098, by decide⟩,⟨953080, by decide⟩,⟨953204, by decide⟩]) unmarked_context_9_4501_953205 node_context_9_4501_953205
  intro a
  fin_cases a
  · exact context_10_18004_952781
  · exact context_10_18005_893098
  · exact context_10_18006_953080
  · exact context_10_18007_953204

theorem selected_cut_36104 : selected 9 ⟨953274, by decide⟩
    (prefixPartial 12 288128) = some ⟨12, 2, 0, 953274, 288128, 829, 65536⟩ := by
  decide +kernel

theorem context_12_288128_953274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288128 ⟨953274, by decide⟩ :=
  accepted_of_selected 12 288128 ⟨953274, by decide⟩ ⟨12, 2, 0, 953274, 288128, 829, 65536⟩
    (by decide) selected_cut_36104

theorem selected_cut_36105 : selected 9 ⟨953306, by decide⟩
    (prefixPartial 12 288129) = some ⟨12, 2, 0, 953306, 288129, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_288129_953306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288129 ⟨953306, by decide⟩ :=
  accepted_of_selected 12 288129 ⟨953306, by decide⟩ ⟨12, 2, 0, 953306, 288129, 1581, 65536⟩
    (by decide) selected_cut_36105

theorem selected_cut_36106 : selected 9 ⟨953339, by decide⟩
    (prefixPartial 12 288130) = some ⟨12, 2, 0, 953339, 288130, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_288130_953339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288130 ⟨953339, by decide⟩ :=
  accepted_of_selected 12 288130 ⟨953339, by decide⟩ ⟨12, 2, 0, 953339, 288130, 1597, 65536⟩
    (by decide) selected_cut_36106

theorem selected_cut_36107 : selected 9 ⟨953382, by decide⟩
    (prefixPartial 12 288131) = some ⟨12, 2, 0, 953382, 288131, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_288131_953382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288131 ⟨953382, by decide⟩ :=
  accepted_of_selected 12 288131 ⟨953382, by decide⟩ ⟨12, 2, 0, 953382, 288131, 1869, 65536⟩
    (by decide) selected_cut_36107

theorem unmarked_context_11_72032_953383 : frontier 10 ⟨953383, by decide⟩
    (prefixCache 11 72032) (prefixPartial 11 72032) = false := by
  decide +kernel

theorem node_context_11_72032_953383 : EJMOriginalGlobalDAGData.nodes 10 ⟨953383, by decide⟩ =
    .split (coordinate 11) (![⟨953274, by decide⟩,⟨953306, by decide⟩,⟨953339, by decide⟩,⟨953382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72032_953383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72032 ⟨953383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72032
    ⟨953383, by decide⟩ (by decide) (![⟨953274, by decide⟩,⟨953306, by decide⟩,⟨953339, by decide⟩,⟨953382, by decide⟩]) unmarked_context_11_72032_953383 node_context_11_72032_953383
  intro a
  fin_cases a
  · exact context_12_288128_953274
  · exact context_12_288129_953306
  · exact context_12_288130_953339
  · exact context_12_288131_953382

theorem selected_cut_36108 : selected 9 ⟨953426, by decide⟩
    (prefixPartial 12 288132) = some ⟨12, 2, 0, 953426, 288132, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_288132_953426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288132 ⟨953426, by decide⟩ :=
  accepted_of_selected 12 288132 ⟨953426, by decide⟩ ⟨12, 2, 0, 953426, 288132, 1341, 65536⟩
    (by decide) selected_cut_36108

theorem selected_cut_36109 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 288133) = some ⟨12, 1, 0, 891951, 288133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288133_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288133 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 288133 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 288133, 1, 65536⟩
    (by decide) selected_cut_36109

theorem selected_cut_36110 : selected 9 ⟨953451, by decide⟩
    (prefixPartial 12 288134) = some ⟨12, 2, 0, 953451, 288134, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_288134_953451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288134 ⟨953451, by decide⟩ :=
  accepted_of_selected 12 288134 ⟨953451, by decide⟩ ⟨12, 2, 0, 953451, 288134, 1393, 65536⟩
    (by decide) selected_cut_36110

theorem selected_cut_36111 : selected 9 ⟨953479, by decide⟩
    (prefixPartial 12 288135) = some ⟨12, 2, 0, 953479, 288135, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_288135_953479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288135 ⟨953479, by decide⟩ :=
  accepted_of_selected 12 288135 ⟨953479, by decide⟩ ⟨12, 2, 0, 953479, 288135, 1505, 65536⟩
    (by decide) selected_cut_36111

theorem unmarked_context_11_72033_953480 : frontier 10 ⟨953480, by decide⟩
    (prefixCache 11 72033) (prefixPartial 11 72033) = false := by
  decide +kernel

theorem node_context_11_72033_953480 : EJMOriginalGlobalDAGData.nodes 10 ⟨953480, by decide⟩ =
    .split (coordinate 11) (![⟨953426, by decide⟩,⟨891951, by decide⟩,⟨953451, by decide⟩,⟨953479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72033_953480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72033 ⟨953480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72033
    ⟨953480, by decide⟩ (by decide) (![⟨953426, by decide⟩,⟨891951, by decide⟩,⟨953451, by decide⟩,⟨953479, by decide⟩]) unmarked_context_11_72033_953480 node_context_11_72033_953480
  intro a
  fin_cases a
  · exact context_12_288132_953426
  · exact context_12_288133_891951
  · exact context_12_288134_953451
  · exact context_12_288135_953479

theorem selected_cut_36112 : selected 9 ⟨953553, by decide⟩
    (prefixPartial 12 288136) = some ⟨12, 2, 0, 953553, 288136, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_288136_953553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288136 ⟨953553, by decide⟩ :=
  accepted_of_selected 12 288136 ⟨953553, by decide⟩ ⟨12, 2, 0, 953553, 288136, 1449, 65536⟩
    (by decide) selected_cut_36112

theorem selected_cut_36113 : selected 9 ⟨953593, by decide⟩
    (prefixPartial 12 288137) = some ⟨12, 2, 0, 953593, 288137, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_288137_953593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288137 ⟨953593, by decide⟩ :=
  accepted_of_selected 12 288137 ⟨953593, by decide⟩ ⟨12, 2, 0, 953593, 288137, 1269, 65536⟩
    (by decide) selected_cut_36113

theorem selected_cut_36114 : selected 9 ⟨953637, by decide⟩
    (prefixPartial 12 288138) = some ⟨12, 2, 0, 953637, 288138, 521, 65536⟩ := by
  decide +kernel

theorem context_12_288138_953637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288138 ⟨953637, by decide⟩ :=
  accepted_of_selected 12 288138 ⟨953637, by decide⟩ ⟨12, 2, 0, 953637, 288138, 521, 65536⟩
    (by decide) selected_cut_36114

theorem selected_cut_36115 : selected 9 ⟨953675, by decide⟩
    (prefixPartial 12 288139) = some ⟨12, 2, 0, 953675, 288139, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_288139_953675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288139 ⟨953675, by decide⟩ :=
  accepted_of_selected 12 288139 ⟨953675, by decide⟩ ⟨12, 2, 0, 953675, 288139, 1513, 65536⟩
    (by decide) selected_cut_36115

theorem unmarked_context_11_72034_953676 : frontier 10 ⟨953676, by decide⟩
    (prefixCache 11 72034) (prefixPartial 11 72034) = false := by
  decide +kernel

theorem node_context_11_72034_953676 : EJMOriginalGlobalDAGData.nodes 10 ⟨953676, by decide⟩ =
    .split (coordinate 11) (![⟨953553, by decide⟩,⟨953593, by decide⟩,⟨953637, by decide⟩,⟨953675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72034_953676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72034 ⟨953676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72034
    ⟨953676, by decide⟩ (by decide) (![⟨953553, by decide⟩,⟨953593, by decide⟩,⟨953637, by decide⟩,⟨953675, by decide⟩]) unmarked_context_11_72034_953676 node_context_11_72034_953676
  intro a
  fin_cases a
  · exact context_12_288136_953553
  · exact context_12_288137_953593
  · exact context_12_288138_953637
  · exact context_12_288139_953675

theorem selected_cut_36116 : selected 9 ⟨953714, by decide⟩
    (prefixPartial 12 288140) = some ⟨12, 2, 0, 953714, 288140, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_288140_953714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288140 ⟨953714, by decide⟩ :=
  accepted_of_selected 12 288140 ⟨953714, by decide⟩ ⟨12, 2, 0, 953714, 288140, 1025, 65536⟩
    (by decide) selected_cut_36116

theorem selected_cut_36117 : selected 9 ⟨953735, by decide⟩
    (prefixPartial 12 288141) = some ⟨12, 2, 0, 953735, 288141, 957, 65536⟩ := by
  decide +kernel

theorem context_12_288141_953735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288141 ⟨953735, by decide⟩ :=
  accepted_of_selected 12 288141 ⟨953735, by decide⟩ ⟨12, 2, 0, 953735, 288141, 957, 65536⟩
    (by decide) selected_cut_36117

theorem selected_cut_36118 : selected 9 ⟨953760, by decide⟩
    (prefixPartial 12 288142) = some ⟨12, 2, 0, 953760, 288142, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_288142_953760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288142 ⟨953760, by decide⟩ :=
  accepted_of_selected 12 288142 ⟨953760, by decide⟩ ⟨12, 2, 0, 953760, 288142, 1189, 65536⟩
    (by decide) selected_cut_36118

theorem selected_cut_36119 : selected 9 ⟨953783, by decide⟩
    (prefixPartial 12 288143) = some ⟨12, 2, 0, 953783, 288143, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_288143_953783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288143 ⟨953783, by decide⟩ :=
  accepted_of_selected 12 288143 ⟨953783, by decide⟩ ⟨12, 2, 0, 953783, 288143, 1105, 65536⟩
    (by decide) selected_cut_36119

theorem unmarked_context_11_72035_953784 : frontier 10 ⟨953784, by decide⟩
    (prefixCache 11 72035) (prefixPartial 11 72035) = false := by
  decide +kernel

theorem node_context_11_72035_953784 : EJMOriginalGlobalDAGData.nodes 10 ⟨953784, by decide⟩ =
    .split (coordinate 11) (![⟨953714, by decide⟩,⟨953735, by decide⟩,⟨953760, by decide⟩,⟨953783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72035_953784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72035 ⟨953784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72035
    ⟨953784, by decide⟩ (by decide) (![⟨953714, by decide⟩,⟨953735, by decide⟩,⟨953760, by decide⟩,⟨953783, by decide⟩]) unmarked_context_11_72035_953784 node_context_11_72035_953784
  intro a
  fin_cases a
  · exact context_12_288140_953714
  · exact context_12_288141_953735
  · exact context_12_288142_953760
  · exact context_12_288143_953783

theorem unmarked_context_10_18008_953785 : frontier 11 ⟨953785, by decide⟩
    (prefixCache 10 18008) (prefixPartial 10 18008) = false := by
  decide +kernel

theorem node_context_10_18008_953785 : EJMOriginalGlobalDAGData.nodes 11 ⟨953785, by decide⟩ =
    .split (coordinate 10) (![⟨953383, by decide⟩,⟨953480, by decide⟩,⟨953676, by decide⟩,⟨953784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18008_953785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18008 ⟨953785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18008
    ⟨953785, by decide⟩ (by decide) (![⟨953383, by decide⟩,⟨953480, by decide⟩,⟨953676, by decide⟩,⟨953784, by decide⟩]) unmarked_context_10_18008_953785 node_context_10_18008_953785
  intro a
  fin_cases a
  · exact context_11_72032_953383
  · exact context_11_72033_953480
  · exact context_11_72034_953676
  · exact context_11_72035_953784

theorem selected_cut_36120 : selected 10 ⟨953847, by decide⟩
    (prefixPartial 11 72036) = some ⟨11, 2, 0, 953847, 72036, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_72036_953847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72036 ⟨953847, by decide⟩ :=
  accepted_of_selected 11 72036 ⟨953847, by decide⟩ ⟨11, 2, 0, 953847, 72036, 2401, 262144⟩
    (by decide) selected_cut_36120

theorem selected_cut_36121 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 72037) = some ⟨11, 1, 0, 892405, 72037, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72037_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72037 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 72037 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 72037, 1, 262144⟩
    (by decide) selected_cut_36121

theorem selected_cut_36122 : selected 10 ⟨953884, by decide⟩
    (prefixPartial 11 72038) = some ⟨11, 2, 0, 953884, 72038, 1273, 262144⟩ := by
  decide +kernel

theorem context_11_72038_953884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72038 ⟨953884, by decide⟩ :=
  accepted_of_selected 11 72038 ⟨953884, by decide⟩ ⟨11, 2, 0, 953884, 72038, 1273, 262144⟩
    (by decide) selected_cut_36122

theorem selected_cut_36123 : selected 10 ⟨953921, by decide⟩
    (prefixPartial 11 72039) = some ⟨11, 2, 0, 953921, 72039, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_72039_953921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72039 ⟨953921, by decide⟩ :=
  accepted_of_selected 11 72039 ⟨953921, by decide⟩ ⟨11, 2, 0, 953921, 72039, 1749, 262144⟩
    (by decide) selected_cut_36123

theorem unmarked_context_10_18009_953922 : frontier 11 ⟨953922, by decide⟩
    (prefixCache 10 18009) (prefixPartial 10 18009) = false := by
  decide +kernel

theorem node_context_10_18009_953922 : EJMOriginalGlobalDAGData.nodes 11 ⟨953922, by decide⟩ =
    .split (coordinate 10) (![⟨953847, by decide⟩,⟨892405, by decide⟩,⟨953884, by decide⟩,⟨953921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18009_953922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18009 ⟨953922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18009
    ⟨953922, by decide⟩ (by decide) (![⟨953847, by decide⟩,⟨892405, by decide⟩,⟨953884, by decide⟩,⟨953921, by decide⟩]) unmarked_context_10_18009_953922 node_context_10_18009_953922
  intro a
  fin_cases a
  · exact context_11_72036_953847
  · exact context_11_72037_892405
  · exact context_11_72038_953884
  · exact context_11_72039_953921

theorem selected_cut_36124 : selected 11 ⟨954076, by decide⟩
    (prefixPartial 10 18010) = some ⟨10, 2, 0, 954076, 18010, 2781, 1048576⟩ := by
  decide +kernel

theorem context_10_18010_954076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18010 ⟨954076, by decide⟩ :=
  accepted_of_selected 10 18010 ⟨954076, by decide⟩ ⟨10, 2, 0, 954076, 18010, 2781, 1048576⟩
    (by decide) selected_cut_36124

theorem selected_cut_36125 : selected 11 ⟨954136, by decide⟩
    (prefixPartial 10 18011) = some ⟨10, 2, 0, 954136, 18011, 1749, 1048576⟩ := by
  decide +kernel

theorem context_10_18011_954136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18011 ⟨954136, by decide⟩ :=
  accepted_of_selected 10 18011 ⟨954136, by decide⟩ ⟨10, 2, 0, 954136, 18011, 1749, 1048576⟩
    (by decide) selected_cut_36125

theorem unmarked_context_9_4502_954137 : frontier 12 ⟨954137, by decide⟩
    (prefixCache 9 4502) (prefixPartial 9 4502) = false := by
  decide +kernel

theorem node_context_9_4502_954137 : EJMOriginalGlobalDAGData.nodes 12 ⟨954137, by decide⟩ =
    .split (coordinate 9) (![⟨953785, by decide⟩,⟨953922, by decide⟩,⟨954076, by decide⟩,⟨954136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4502_954137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4502 ⟨954137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4502
    ⟨954137, by decide⟩ (by decide) (![⟨953785, by decide⟩,⟨953922, by decide⟩,⟨954076, by decide⟩,⟨954136, by decide⟩]) unmarked_context_9_4502_954137 node_context_9_4502_954137
  intro a
  fin_cases a
  · exact context_10_18008_953785
  · exact context_10_18009_953922
  · exact context_10_18010_954076
  · exact context_10_18011_954136

theorem selected_cut_36126 : selected 10 ⟨954200, by decide⟩
    (prefixPartial 11 72048) = some ⟨11, 2, 0, 954200, 72048, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_72048_954200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72048 ⟨954200, by decide⟩ :=
  accepted_of_selected 11 72048 ⟨954200, by decide⟩ ⟨11, 2, 0, 954200, 72048, 1917, 262144⟩
    (by decide) selected_cut_36126

theorem selected_cut_36127 : selected 10 ⟨954243, by decide⟩
    (prefixPartial 11 72049) = some ⟨11, 2, 0, 954243, 72049, 1389, 262144⟩ := by
  decide +kernel

theorem context_11_72049_954243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72049 ⟨954243, by decide⟩ :=
  accepted_of_selected 11 72049 ⟨954243, by decide⟩ ⟨11, 2, 0, 954243, 72049, 1389, 262144⟩
    (by decide) selected_cut_36127

theorem selected_cut_36128 : selected 10 ⟨954328, by decide⟩
    (prefixPartial 11 72050) = some ⟨11, 2, 0, 954328, 72050, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_72050_954328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72050 ⟨954328, by decide⟩ :=
  accepted_of_selected 11 72050 ⟨954328, by decide⟩ ⟨11, 2, 0, 954328, 72050, 1749, 262144⟩
    (by decide) selected_cut_36128

theorem selected_cut_36129 : selected 10 ⟨954378, by decide⟩
    (prefixPartial 11 72051) = some ⟨11, 2, 0, 954378, 72051, 1021, 262144⟩ := by
  decide +kernel

theorem context_11_72051_954378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72051 ⟨954378, by decide⟩ :=
  accepted_of_selected 11 72051 ⟨954378, by decide⟩ ⟨11, 2, 0, 954378, 72051, 1021, 262144⟩
    (by decide) selected_cut_36129

theorem unmarked_context_10_18012_954379 : frontier 11 ⟨954379, by decide⟩
    (prefixCache 10 18012) (prefixPartial 10 18012) = false := by
  decide +kernel

theorem node_context_10_18012_954379 : EJMOriginalGlobalDAGData.nodes 11 ⟨954379, by decide⟩ =
    .split (coordinate 10) (![⟨954200, by decide⟩,⟨954243, by decide⟩,⟨954328, by decide⟩,⟨954378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18012_954379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18012 ⟨954379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18012
    ⟨954379, by decide⟩ (by decide) (![⟨954200, by decide⟩,⟨954243, by decide⟩,⟨954328, by decide⟩,⟨954378, by decide⟩]) unmarked_context_10_18012_954379 node_context_10_18012_954379
  intro a
  fin_cases a
  · exact context_11_72048_954200
  · exact context_11_72049_954243
  · exact context_11_72050_954328
  · exact context_11_72051_954378

theorem selected_cut_36130 : selected 11 ⟨954439, by decide⟩
    (prefixPartial 10 18013) = some ⟨10, 2, 0, 954439, 18013, 1497, 1048576⟩ := by
  decide +kernel

theorem context_10_18013_954439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18013 ⟨954439, by decide⟩ :=
  accepted_of_selected 10 18013 ⟨954439, by decide⟩ ⟨10, 2, 0, 954439, 18013, 1497, 1048576⟩
    (by decide) selected_cut_36130

theorem selected_cut_36131 : selected 11 ⟨954484, by decide⟩
    (prefixPartial 10 18014) = some ⟨10, 2, 0, 954484, 18014, 593, 1048576⟩ := by
  decide +kernel

theorem context_10_18014_954484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18014 ⟨954484, by decide⟩ :=
  accepted_of_selected 10 18014 ⟨954484, by decide⟩ ⟨10, 2, 0, 954484, 18014, 593, 1048576⟩
    (by decide) selected_cut_36131

theorem selected_cut_36132 : selected 11 ⟨954487, by decide⟩
    (prefixPartial 10 18015) = some ⟨10, 2, 0, 954487, 18015, 25, 1048576⟩ := by
  decide +kernel

theorem context_10_18015_954487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18015 ⟨954487, by decide⟩ :=
  accepted_of_selected 10 18015 ⟨954487, by decide⟩ ⟨10, 2, 0, 954487, 18015, 25, 1048576⟩
    (by decide) selected_cut_36132

theorem unmarked_context_9_4503_954488 : frontier 12 ⟨954488, by decide⟩
    (prefixCache 9 4503) (prefixPartial 9 4503) = false := by
  decide +kernel

theorem node_context_9_4503_954488 : EJMOriginalGlobalDAGData.nodes 12 ⟨954488, by decide⟩ =
    .split (coordinate 9) (![⟨954379, by decide⟩,⟨954439, by decide⟩,⟨954484, by decide⟩,⟨954487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4503_954488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4503 ⟨954488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4503
    ⟨954488, by decide⟩ (by decide) (![⟨954379, by decide⟩,⟨954439, by decide⟩,⟨954484, by decide⟩,⟨954487, by decide⟩]) unmarked_context_9_4503_954488 node_context_9_4503_954488
  intro a
  fin_cases a
  · exact context_10_18012_954379
  · exact context_10_18013_954439
  · exact context_10_18014_954484
  · exact context_10_18015_954487

theorem unmarked_context_8_1125_954489 : frontier 13 ⟨954489, by decide⟩
    (prefixCache 8 1125) (prefixPartial 8 1125) = false := by
  decide +kernel

theorem node_context_8_1125_954489 : EJMOriginalGlobalDAGData.nodes 13 ⟨954489, by decide⟩ =
    .split (coordinate 8) (![⟨952129, by decide⟩,⟨953205, by decide⟩,⟨954137, by decide⟩,⟨954488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1125_954489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1125 ⟨954489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1125
    ⟨954489, by decide⟩ (by decide) (![⟨952129, by decide⟩,⟨953205, by decide⟩,⟨954137, by decide⟩,⟨954488, by decide⟩]) unmarked_context_8_1125_954489 node_context_8_1125_954489
  intro a
  fin_cases a
  · exact context_9_4500_952129
  · exact context_9_4501_953205
  · exact context_9_4502_954137
  · exact context_9_4503_954488

theorem selected_cut_36133 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 288256) = some ⟨12, 1, 0, 34034, 288256, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288256_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288256 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 288256 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 288256, 1, 65536⟩
    (by decide) selected_cut_36133

theorem selected_cut_36134 : selected 9 ⟨301653, by decide⟩
    (prefixPartial 12 288257) = some ⟨12, 1, 0, 301653, 288257, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288257_301653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288257 ⟨301653, by decide⟩ :=
  accepted_of_selected 12 288257 ⟨301653, by decide⟩ ⟨12, 1, 0, 301653, 288257, 1, 65536⟩
    (by decide) selected_cut_36134

theorem selected_cut_36135 : selected 9 ⟨954556, by decide⟩
    (prefixPartial 12 288258) = some ⟨12, 2, 0, 954556, 288258, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_288258_954556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288258 ⟨954556, by decide⟩ :=
  accepted_of_selected 12 288258 ⟨954556, by decide⟩ ⟨12, 2, 0, 954556, 288258, 2121, 65536⟩
    (by decide) selected_cut_36135

theorem selected_cut_36136 : selected 8 ⟨954581, by decide⟩
    (prefixPartial 13 1153036) = some ⟨13, 2, 0, 954581, 1153036, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_1153036_954581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153036 ⟨954581, by decide⟩ :=
  accepted_of_selected 13 1153036 ⟨954581, by decide⟩ ⟨13, 2, 0, 954581, 1153036, 1501, 16384⟩
    (by decide) selected_cut_36136

theorem selected_cut_36137 : selected 8 ⟨954597, by decide⟩
    (prefixPartial 13 1153037) = some ⟨13, 2, 0, 954597, 1153037, 873, 16384⟩ := by
  decide +kernel

theorem context_13_1153037_954597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153037 ⟨954597, by decide⟩ :=
  accepted_of_selected 13 1153037 ⟨954597, by decide⟩ ⟨13, 2, 0, 954597, 1153037, 873, 16384⟩
    (by decide) selected_cut_36137

theorem selected_cut_36138 : selected 8 ⟨954619, by decide⟩
    (prefixPartial 13 1153038) = some ⟨13, 2, 0, 954619, 1153038, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_1153038_954619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153038 ⟨954619, by decide⟩ :=
  accepted_of_selected 13 1153038 ⟨954619, by decide⟩ ⟨13, 2, 0, 954619, 1153038, 1145, 16384⟩
    (by decide) selected_cut_36138

theorem selected_cut_36139 : selected 8 ⟨954625, by decide⟩
    (prefixPartial 13 1153039) = some ⟨13, 2, 0, 954625, 1153039, 653, 16384⟩ := by
  decide +kernel

theorem context_13_1153039_954625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153039 ⟨954625, by decide⟩ :=
  accepted_of_selected 13 1153039 ⟨954625, by decide⟩ ⟨13, 2, 0, 954625, 1153039, 653, 16384⟩
    (by decide) selected_cut_36139

theorem unmarked_context_12_288259_954626 : frontier 9 ⟨954626, by decide⟩
    (prefixCache 12 288259) (prefixPartial 12 288259) = false := by
  decide +kernel

theorem node_context_12_288259_954626 : EJMOriginalGlobalDAGData.nodes 9 ⟨954626, by decide⟩ =
    .split (coordinate 12) (![⟨954581, by decide⟩,⟨954597, by decide⟩,⟨954619, by decide⟩,⟨954625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288259_954626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288259 ⟨954626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288259
    ⟨954626, by decide⟩ (by decide) (![⟨954581, by decide⟩,⟨954597, by decide⟩,⟨954619, by decide⟩,⟨954625, by decide⟩]) unmarked_context_12_288259_954626 node_context_12_288259_954626
  intro a
  fin_cases a
  · exact context_13_1153036_954581
  · exact context_13_1153037_954597
  · exact context_13_1153038_954619
  · exact context_13_1153039_954625

theorem unmarked_context_11_72064_954627 : frontier 10 ⟨954627, by decide⟩
    (prefixCache 11 72064) (prefixPartial 11 72064) = false := by
  decide +kernel

theorem node_context_11_72064_954627 : EJMOriginalGlobalDAGData.nodes 10 ⟨954627, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨954556, by decide⟩,⟨954626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72064_954627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72064 ⟨954627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72064
    ⟨954627, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨954556, by decide⟩,⟨954626, by decide⟩]) unmarked_context_11_72064_954627 node_context_11_72064_954627
  intro a
  fin_cases a
  · exact context_12_288256_34034
  · exact context_12_288257_301653
  · exact context_12_288258_954556
  · exact context_12_288259_954626

theorem selected_cut_36140 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 288260) = some ⟨12, 1, 0, 34034, 288260, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288260_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288260 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 288260 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 288260, 1, 65536⟩
    (by decide) selected_cut_36140

theorem selected_cut_36141 : selected 9 ⟨954674, by decide⟩
    (prefixPartial 12 288261) = some ⟨12, 2, 0, 954674, 288261, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_288261_954674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288261 ⟨954674, by decide⟩ :=
  accepted_of_selected 12 288261 ⟨954674, by decide⟩ ⟨12, 2, 0, 954674, 288261, 3121, 65536⟩
    (by decide) selected_cut_36141

theorem selected_cut_36142 : selected 9 ⟨954728, by decide⟩
    (prefixPartial 12 288262) = some ⟨12, 2, 0, 954728, 288262, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_288262_954728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288262 ⟨954728, by decide⟩ :=
  accepted_of_selected 12 288262 ⟨954728, by decide⟩ ⟨12, 2, 0, 954728, 288262, 3369, 65536⟩
    (by decide) selected_cut_36142

theorem selected_cut_36143 : selected 9 ⟨954808, by decide⟩
    (prefixPartial 12 288263) = some ⟨12, 2, 0, 954808, 288263, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_288263_954808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288263 ⟨954808, by decide⟩ :=
  accepted_of_selected 12 288263 ⟨954808, by decide⟩ ⟨12, 2, 0, 954808, 288263, 4033, 65536⟩
    (by decide) selected_cut_36143

theorem unmarked_context_11_72065_954809 : frontier 10 ⟨954809, by decide⟩
    (prefixCache 11 72065) (prefixPartial 11 72065) = false := by
  decide +kernel

theorem node_context_11_72065_954809 : EJMOriginalGlobalDAGData.nodes 10 ⟨954809, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨954674, by decide⟩,⟨954728, by decide⟩,⟨954808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72065_954809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72065 ⟨954809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72065
    ⟨954809, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨954674, by decide⟩,⟨954728, by decide⟩,⟨954808, by decide⟩]) unmarked_context_11_72065_954809 node_context_11_72065_954809
  intro a
  fin_cases a
  · exact context_12_288260_34034
  · exact context_12_288261_954674
  · exact context_12_288262_954728
  · exact context_12_288263_954808

theorem selected_cut_36144 : selected 8 ⟨954846, by decide⟩
    (prefixPartial 13 1153056) = some ⟨13, 2, 0, 954846, 1153056, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_1153056_954846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153056 ⟨954846, by decide⟩ :=
  accepted_of_selected 13 1153056 ⟨954846, by decide⟩ ⟨13, 2, 0, 954846, 1153056, 1305, 16384⟩
    (by decide) selected_cut_36144

theorem selected_cut_36145 : selected 8 ⟨954885, by decide⟩
    (prefixPartial 13 1153057) = some ⟨13, 2, 0, 954885, 1153057, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_1153057_954885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153057 ⟨954885, by decide⟩ :=
  accepted_of_selected 13 1153057 ⟨954885, by decide⟩ ⟨13, 2, 0, 954885, 1153057, 1197, 16384⟩
    (by decide) selected_cut_36145

theorem selected_cut_36146 : selected 8 ⟨954913, by decide⟩
    (prefixPartial 13 1153058) = some ⟨13, 2, 0, 954913, 1153058, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_1153058_954913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153058 ⟨954913, by decide⟩ :=
  accepted_of_selected 13 1153058 ⟨954913, by decide⟩ ⟨13, 2, 0, 954913, 1153058, 1229, 16384⟩
    (by decide) selected_cut_36146

theorem selected_cut_36147 : selected 8 ⟨954926, by decide⟩
    (prefixPartial 13 1153059) = some ⟨13, 2, 0, 954926, 1153059, 841, 16384⟩ := by
  decide +kernel

theorem context_13_1153059_954926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153059 ⟨954926, by decide⟩ :=
  accepted_of_selected 13 1153059 ⟨954926, by decide⟩ ⟨13, 2, 0, 954926, 1153059, 841, 16384⟩
    (by decide) selected_cut_36147

theorem unmarked_context_12_288264_954927 : frontier 9 ⟨954927, by decide⟩
    (prefixCache 12 288264) (prefixPartial 12 288264) = false := by
  decide +kernel

theorem node_context_12_288264_954927 : EJMOriginalGlobalDAGData.nodes 9 ⟨954927, by decide⟩ =
    .split (coordinate 12) (![⟨954846, by decide⟩,⟨954885, by decide⟩,⟨954913, by decide⟩,⟨954926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288264_954927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288264 ⟨954927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288264
    ⟨954927, by decide⟩ (by decide) (![⟨954846, by decide⟩,⟨954885, by decide⟩,⟨954913, by decide⟩,⟨954926, by decide⟩]) unmarked_context_12_288264_954927 node_context_12_288264_954927
  intro a
  fin_cases a
  · exact context_13_1153056_954846
  · exact context_13_1153057_954885
  · exact context_13_1153058_954913
  · exact context_13_1153059_954926

theorem selected_cut_36148 : selected 9 ⟨954994, by decide⟩
    (prefixPartial 12 288265) = some ⟨12, 2, 0, 954994, 288265, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_288265_954994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288265 ⟨954994, by decide⟩ :=
  accepted_of_selected 12 288265 ⟨954994, by decide⟩ ⟨12, 2, 0, 954994, 288265, 3437, 65536⟩
    (by decide) selected_cut_36148

theorem selected_cut_36149 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 288266) = some ⟨12, 1, 0, 893903, 288266, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288266_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288266 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 288266 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 288266, 1, 65536⟩
    (by decide) selected_cut_36149

theorem selected_cut_36150 : selected 8 ⟨955031, by decide⟩
    (prefixPartial 13 1153068) = some ⟨13, 2, 0, 955031, 1153068, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_1153068_955031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153068 ⟨955031, by decide⟩ :=
  accepted_of_selected 13 1153068 ⟨955031, by decide⟩ ⟨13, 2, 0, 955031, 1153068, 1533, 16384⟩
    (by decide) selected_cut_36150

theorem selected_cut_36151 : selected 8 ⟨955067, by decide⟩
    (prefixPartial 13 1153069) = some ⟨13, 2, 0, 955067, 1153069, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_1153069_955067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153069 ⟨955067, by decide⟩ :=
  accepted_of_selected 13 1153069 ⟨955067, by decide⟩ ⟨13, 2, 0, 955067, 1153069, 1173, 16384⟩
    (by decide) selected_cut_36151

theorem selected_cut_36152 : selected 8 ⟨955091, by decide⟩
    (prefixPartial 13 1153070) = some ⟨13, 2, 0, 955091, 1153070, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_1153070_955091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153070 ⟨955091, by decide⟩ :=
  accepted_of_selected 13 1153070 ⟨955091, by decide⟩ ⟨13, 2, 0, 955091, 1153070, 1169, 16384⟩
    (by decide) selected_cut_36152

theorem selected_cut_36153 : selected 8 ⟨955100, by decide⟩
    (prefixPartial 13 1153071) = some ⟨13, 2, 0, 955100, 1153071, 737, 16384⟩ := by
  decide +kernel

theorem context_13_1153071_955100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153071 ⟨955100, by decide⟩ :=
  accepted_of_selected 13 1153071 ⟨955100, by decide⟩ ⟨13, 2, 0, 955100, 1153071, 737, 16384⟩
    (by decide) selected_cut_36153

theorem unmarked_context_12_288267_955101 : frontier 9 ⟨955101, by decide⟩
    (prefixCache 12 288267) (prefixPartial 12 288267) = false := by
  decide +kernel

theorem node_context_12_288267_955101 : EJMOriginalGlobalDAGData.nodes 9 ⟨955101, by decide⟩ =
    .split (coordinate 12) (![⟨955031, by decide⟩,⟨955067, by decide⟩,⟨955091, by decide⟩,⟨955100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288267_955101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288267 ⟨955101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288267
    ⟨955101, by decide⟩ (by decide) (![⟨955031, by decide⟩,⟨955067, by decide⟩,⟨955091, by decide⟩,⟨955100, by decide⟩]) unmarked_context_12_288267_955101 node_context_12_288267_955101
  intro a
  fin_cases a
  · exact context_13_1153068_955031
  · exact context_13_1153069_955067
  · exact context_13_1153070_955091
  · exact context_13_1153071_955100

theorem unmarked_context_11_72066_955102 : frontier 10 ⟨955102, by decide⟩
    (prefixCache 11 72066) (prefixPartial 11 72066) = false := by
  decide +kernel

theorem node_context_11_72066_955102 : EJMOriginalGlobalDAGData.nodes 10 ⟨955102, by decide⟩ =
    .split (coordinate 11) (![⟨954927, by decide⟩,⟨954994, by decide⟩,⟨893903, by decide⟩,⟨955101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72066_955102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72066 ⟨955102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72066
    ⟨955102, by decide⟩ (by decide) (![⟨954927, by decide⟩,⟨954994, by decide⟩,⟨893903, by decide⟩,⟨955101, by decide⟩]) unmarked_context_11_72066_955102 node_context_11_72066_955102
  intro a
  fin_cases a
  · exact context_12_288264_954927
  · exact context_12_288265_954994
  · exact context_12_288266_893903
  · exact context_12_288267_955101

theorem selected_cut_36154 : selected 8 ⟨955133, by decide⟩
    (prefixPartial 13 1153072) = some ⟨13, 2, 0, 955133, 1153072, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_1153072_955133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153072 ⟨955133, by decide⟩ :=
  accepted_of_selected 13 1153072 ⟨955133, by decide⟩ ⟨13, 2, 0, 955133, 1153072, 1237, 16384⟩
    (by decide) selected_cut_36154

theorem selected_cut_36155 : selected 8 ⟨955156, by decide⟩
    (prefixPartial 13 1153073) = some ⟨13, 2, 0, 955156, 1153073, 969, 16384⟩ := by
  decide +kernel

theorem context_13_1153073_955156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153073 ⟨955156, by decide⟩ :=
  accepted_of_selected 13 1153073 ⟨955156, by decide⟩ ⟨13, 2, 0, 955156, 1153073, 969, 16384⟩
    (by decide) selected_cut_36155

theorem selected_cut_36156 : selected 8 ⟨955178, by decide⟩
    (prefixPartial 13 1153074) = some ⟨13, 2, 0, 955178, 1153074, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_1153074_955178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153074 ⟨955178, by decide⟩ :=
  accepted_of_selected 13 1153074 ⟨955178, by decide⟩ ⟨13, 2, 0, 955178, 1153074, 1153, 16384⟩
    (by decide) selected_cut_36156

theorem selected_cut_36157 : selected 8 ⟨955190, by decide⟩
    (prefixPartial 13 1153075) = some ⟨13, 2, 0, 955190, 1153075, 785, 16384⟩ := by
  decide +kernel

theorem context_13_1153075_955190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153075 ⟨955190, by decide⟩ :=
  accepted_of_selected 13 1153075 ⟨955190, by decide⟩ ⟨13, 2, 0, 955190, 1153075, 785, 16384⟩
    (by decide) selected_cut_36157

theorem unmarked_context_12_288268_955191 : frontier 9 ⟨955191, by decide⟩
    (prefixCache 12 288268) (prefixPartial 12 288268) = false := by
  decide +kernel

theorem node_context_12_288268_955191 : EJMOriginalGlobalDAGData.nodes 9 ⟨955191, by decide⟩ =
    .split (coordinate 12) (![⟨955133, by decide⟩,⟨955156, by decide⟩,⟨955178, by decide⟩,⟨955190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288268_955191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288268 ⟨955191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288268
    ⟨955191, by decide⟩ (by decide) (![⟨955133, by decide⟩,⟨955156, by decide⟩,⟨955178, by decide⟩,⟨955190, by decide⟩]) unmarked_context_12_288268_955191 node_context_12_288268_955191
  intro a
  fin_cases a
  · exact context_13_1153072_955133
  · exact context_13_1153073_955156
  · exact context_13_1153074_955178
  · exact context_13_1153075_955190

theorem selected_cut_36158 : selected 9 ⟨955250, by decide⟩
    (prefixPartial 12 288269) = some ⟨12, 2, 0, 955250, 288269, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_288269_955250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288269 ⟨955250, by decide⟩ :=
  accepted_of_selected 12 288269 ⟨955250, by decide⟩ ⟨12, 2, 0, 955250, 288269, 3325, 65536⟩
    (by decide) selected_cut_36158

theorem selected_cut_36159 : selected 9 ⟨955315, by decide⟩
    (prefixPartial 12 288270) = some ⟨12, 2, 0, 955315, 288270, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_288270_955315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288270 ⟨955315, by decide⟩ :=
  accepted_of_selected 12 288270 ⟨955315, by decide⟩ ⟨12, 2, 0, 955315, 288270, 3809, 65536⟩
    (by decide) selected_cut_36159

theorem selected_cut_36160 : selected 8 ⟨955343, by decide⟩
    (prefixPartial 13 1153084) = some ⟨13, 2, 0, 955343, 1153084, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_1153084_955343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153084 ⟨955343, by decide⟩ :=
  accepted_of_selected 13 1153084 ⟨955343, by decide⟩ ⟨13, 2, 0, 955343, 1153084, 1349, 16384⟩
    (by decide) selected_cut_36160

theorem selected_cut_36161 : selected 8 ⟨955368, by decide⟩
    (prefixPartial 13 1153085) = some ⟨13, 2, 0, 955368, 1153085, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_1153085_955368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153085 ⟨955368, by decide⟩ :=
  accepted_of_selected 13 1153085 ⟨955368, by decide⟩ ⟨13, 2, 0, 955368, 1153085, 1029, 16384⟩
    (by decide) selected_cut_36161

theorem selected_cut_36162 : selected 8 ⟨955388, by decide⟩
    (prefixPartial 13 1153086) = some ⟨13, 2, 0, 955388, 1153086, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_1153086_955388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153086 ⟨955388, by decide⟩ :=
  accepted_of_selected 13 1153086 ⟨955388, by decide⟩ ⟨13, 2, 0, 955388, 1153086, 1073, 16384⟩
    (by decide) selected_cut_36162

theorem selected_cut_36163 : selected 8 ⟨955396, by decide⟩
    (prefixPartial 13 1153087) = some ⟨13, 2, 0, 955396, 1153087, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1153087_955396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1153087 ⟨955396, by decide⟩ :=
  accepted_of_selected 13 1153087 ⟨955396, by decide⟩ ⟨13, 2, 0, 955396, 1153087, 725, 16384⟩
    (by decide) selected_cut_36163

theorem unmarked_context_12_288271_955397 : frontier 9 ⟨955397, by decide⟩
    (prefixCache 12 288271) (prefixPartial 12 288271) = false := by
  decide +kernel

theorem node_context_12_288271_955397 : EJMOriginalGlobalDAGData.nodes 9 ⟨955397, by decide⟩ =
    .split (coordinate 12) (![⟨955343, by decide⟩,⟨955368, by decide⟩,⟨955388, by decide⟩,⟨955396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288271_955397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288271 ⟨955397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288271
    ⟨955397, by decide⟩ (by decide) (![⟨955343, by decide⟩,⟨955368, by decide⟩,⟨955388, by decide⟩,⟨955396, by decide⟩]) unmarked_context_12_288271_955397 node_context_12_288271_955397
  intro a
  fin_cases a
  · exact context_13_1153084_955343
  · exact context_13_1153085_955368
  · exact context_13_1153086_955388
  · exact context_13_1153087_955396

theorem unmarked_context_11_72067_955398 : frontier 10 ⟨955398, by decide⟩
    (prefixCache 11 72067) (prefixPartial 11 72067) = false := by
  decide +kernel

theorem node_context_11_72067_955398 : EJMOriginalGlobalDAGData.nodes 10 ⟨955398, by decide⟩ =
    .split (coordinate 11) (![⟨955191, by decide⟩,⟨955250, by decide⟩,⟨955315, by decide⟩,⟨955397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72067_955398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72067 ⟨955398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72067
    ⟨955398, by decide⟩ (by decide) (![⟨955191, by decide⟩,⟨955250, by decide⟩,⟨955315, by decide⟩,⟨955397, by decide⟩]) unmarked_context_11_72067_955398 node_context_11_72067_955398
  intro a
  fin_cases a
  · exact context_12_288268_955191
  · exact context_12_288269_955250
  · exact context_12_288270_955315
  · exact context_12_288271_955397

theorem unmarked_context_10_18016_955399 : frontier 11 ⟨955399, by decide⟩
    (prefixCache 10 18016) (prefixPartial 10 18016) = false := by
  decide +kernel

theorem node_context_10_18016_955399 : EJMOriginalGlobalDAGData.nodes 11 ⟨955399, by decide⟩ =
    .split (coordinate 10) (![⟨954627, by decide⟩,⟨954809, by decide⟩,⟨955102, by decide⟩,⟨955398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18016_955399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18016 ⟨955399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18016
    ⟨955399, by decide⟩ (by decide) (![⟨954627, by decide⟩,⟨954809, by decide⟩,⟨955102, by decide⟩,⟨955398, by decide⟩]) unmarked_context_10_18016_955399 node_context_10_18016_955399
  intro a
  fin_cases a
  · exact context_11_72064_954627
  · exact context_11_72065_954809
  · exact context_11_72066_955102
  · exact context_11_72067_955398

theorem selected_cut_36164 : selected 9 ⟨955436, by decide⟩
    (prefixPartial 12 288272) = some ⟨12, 2, 0, 955436, 288272, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_288272_955436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288272 ⟨955436, by decide⟩ :=
  accepted_of_selected 12 288272 ⟨955436, by decide⟩ ⟨12, 2, 0, 955436, 288272, 2753, 65536⟩
    (by decide) selected_cut_36164

theorem selected_cut_36165 : selected 9 ⟨955479, by decide⟩
    (prefixPartial 12 288273) = some ⟨12, 2, 0, 955479, 288273, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_288273_955479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288273 ⟨955479, by decide⟩ :=
  accepted_of_selected 12 288273 ⟨955479, by decide⟩ ⟨12, 2, 0, 955479, 288273, 2693, 65536⟩
    (by decide) selected_cut_36165

theorem selected_cut_36166 : selected 9 ⟨955524, by decide⟩
    (prefixPartial 12 288274) = some ⟨12, 2, 0, 955524, 288274, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_288274_955524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288274 ⟨955524, by decide⟩ :=
  accepted_of_selected 12 288274 ⟨955524, by decide⟩ ⟨12, 2, 0, 955524, 288274, 2889, 65536⟩
    (by decide) selected_cut_36166

theorem selected_cut_36167 : selected 9 ⟨955586, by decide⟩
    (prefixPartial 12 288275) = some ⟨12, 2, 0, 955586, 288275, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_288275_955586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288275 ⟨955586, by decide⟩ :=
  accepted_of_selected 12 288275 ⟨955586, by decide⟩ ⟨12, 2, 0, 955586, 288275, 3597, 65536⟩
    (by decide) selected_cut_36167

theorem unmarked_context_11_72068_955587 : frontier 10 ⟨955587, by decide⟩
    (prefixCache 11 72068) (prefixPartial 11 72068) = false := by
  decide +kernel

theorem node_context_11_72068_955587 : EJMOriginalGlobalDAGData.nodes 10 ⟨955587, by decide⟩ =
    .split (coordinate 11) (![⟨955436, by decide⟩,⟨955479, by decide⟩,⟨955524, by decide⟩,⟨955586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72068_955587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72068 ⟨955587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72068
    ⟨955587, by decide⟩ (by decide) (![⟨955436, by decide⟩,⟨955479, by decide⟩,⟨955524, by decide⟩,⟨955586, by decide⟩]) unmarked_context_11_72068_955587 node_context_11_72068_955587
  intro a
  fin_cases a
  · exact context_12_288272_955436
  · exact context_12_288273_955479
  · exact context_12_288274_955524
  · exact context_12_288275_955586

theorem selected_cut_36168 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 72069) = some ⟨11, 1, 0, 892405, 72069, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72069_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72069 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 72069 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 72069, 1, 262144⟩
    (by decide) selected_cut_36168

theorem selected_cut_36169 : selected 9 ⟨955642, by decide⟩
    (prefixPartial 12 288280) = some ⟨12, 2, 0, 955642, 288280, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_288280_955642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288280 ⟨955642, by decide⟩ :=
  accepted_of_selected 12 288280 ⟨955642, by decide⟩ ⟨12, 2, 0, 955642, 288280, 3185, 65536⟩
    (by decide) selected_cut_36169

theorem selected_cut_36170 : selected 9 ⟨955681, by decide⟩
    (prefixPartial 12 288281) = some ⟨12, 2, 0, 955681, 288281, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_288281_955681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288281 ⟨955681, by decide⟩ :=
  accepted_of_selected 12 288281 ⟨955681, by decide⟩ ⟨12, 2, 0, 955681, 288281, 2597, 65536⟩
    (by decide) selected_cut_36170

theorem selected_cut_36171 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 288282) = some ⟨12, 1, 0, 893903, 288282, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288282_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288282 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 288282 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 288282, 1, 65536⟩
    (by decide) selected_cut_36171

theorem selected_cut_36172 : selected 9 ⟨955745, by decide⟩
    (prefixPartial 12 288283) = some ⟨12, 2, 0, 955745, 288283, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_288283_955745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288283 ⟨955745, by decide⟩ :=
  accepted_of_selected 12 288283 ⟨955745, by decide⟩ ⟨12, 2, 0, 955745, 288283, 3505, 65536⟩
    (by decide) selected_cut_36172

theorem unmarked_context_11_72070_955746 : frontier 10 ⟨955746, by decide⟩
    (prefixCache 11 72070) (prefixPartial 11 72070) = false := by
  decide +kernel

theorem node_context_11_72070_955746 : EJMOriginalGlobalDAGData.nodes 10 ⟨955746, by decide⟩ =
    .split (coordinate 11) (![⟨955642, by decide⟩,⟨955681, by decide⟩,⟨893903, by decide⟩,⟨955745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72070_955746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72070 ⟨955746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72070
    ⟨955746, by decide⟩ (by decide) (![⟨955642, by decide⟩,⟨955681, by decide⟩,⟨893903, by decide⟩,⟨955745, by decide⟩]) unmarked_context_11_72070_955746 node_context_11_72070_955746
  intro a
  fin_cases a
  · exact context_12_288280_955642
  · exact context_12_288281_955681
  · exact context_12_288282_893903
  · exact context_12_288283_955745

theorem selected_cut_36173 : selected 9 ⟨955788, by decide⟩
    (prefixPartial 12 288284) = some ⟨12, 2, 0, 955788, 288284, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_288284_955788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288284 ⟨955788, by decide⟩ :=
  accepted_of_selected 12 288284 ⟨955788, by decide⟩ ⟨12, 2, 0, 955788, 288284, 3081, 65536⟩
    (by decide) selected_cut_36173

theorem selected_cut_36174 : selected 9 ⟨955826, by decide⟩
    (prefixPartial 12 288285) = some ⟨12, 2, 0, 955826, 288285, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_288285_955826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288285 ⟨955826, by decide⟩ :=
  accepted_of_selected 12 288285 ⟨955826, by decide⟩ ⟨12, 2, 0, 955826, 288285, 2705, 65536⟩
    (by decide) selected_cut_36174

theorem selected_cut_36175 : selected 9 ⟨955873, by decide⟩
    (prefixPartial 12 288286) = some ⟨12, 2, 0, 955873, 288286, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_288286_955873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288286 ⟨955873, by decide⟩ :=
  accepted_of_selected 12 288286 ⟨955873, by decide⟩ ⟨12, 2, 0, 955873, 288286, 2977, 65536⟩
    (by decide) selected_cut_36175

theorem selected_cut_36176 : selected 9 ⟨955929, by decide⟩
    (prefixPartial 12 288287) = some ⟨12, 2, 0, 955929, 288287, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_288287_955929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288287 ⟨955929, by decide⟩ :=
  accepted_of_selected 12 288287 ⟨955929, by decide⟩ ⟨12, 2, 0, 955929, 288287, 3565, 65536⟩
    (by decide) selected_cut_36176

theorem unmarked_context_11_72071_955930 : frontier 10 ⟨955930, by decide⟩
    (prefixCache 11 72071) (prefixPartial 11 72071) = false := by
  decide +kernel

theorem node_context_11_72071_955930 : EJMOriginalGlobalDAGData.nodes 10 ⟨955930, by decide⟩ =
    .split (coordinate 11) (![⟨955788, by decide⟩,⟨955826, by decide⟩,⟨955873, by decide⟩,⟨955929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72071_955930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72071 ⟨955930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72071
    ⟨955930, by decide⟩ (by decide) (![⟨955788, by decide⟩,⟨955826, by decide⟩,⟨955873, by decide⟩,⟨955929, by decide⟩]) unmarked_context_11_72071_955930 node_context_11_72071_955930
  intro a
  fin_cases a
  · exact context_12_288284_955788
  · exact context_12_288285_955826
  · exact context_12_288286_955873
  · exact context_12_288287_955929

theorem unmarked_context_10_18017_955931 : frontier 11 ⟨955931, by decide⟩
    (prefixCache 10 18017) (prefixPartial 10 18017) = false := by
  decide +kernel

theorem node_context_10_18017_955931 : EJMOriginalGlobalDAGData.nodes 11 ⟨955931, by decide⟩ =
    .split (coordinate 10) (![⟨955587, by decide⟩,⟨892405, by decide⟩,⟨955746, by decide⟩,⟨955930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18017_955931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18017 ⟨955931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18017
    ⟨955931, by decide⟩ (by decide) (![⟨955587, by decide⟩,⟨892405, by decide⟩,⟨955746, by decide⟩,⟨955930, by decide⟩]) unmarked_context_10_18017_955931 node_context_10_18017_955931
  intro a
  fin_cases a
  · exact context_11_72068_955587
  · exact context_11_72069_892405
  · exact context_11_72070_955746
  · exact context_11_72071_955930

theorem selected_cut_36177 : selected 9 ⟨955972, by decide⟩
    (prefixPartial 12 288288) = some ⟨12, 2, 0, 955972, 288288, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_288288_955972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288288 ⟨955972, by decide⟩ :=
  accepted_of_selected 12 288288 ⟨955972, by decide⟩ ⟨12, 2, 0, 955972, 288288, 2817, 65536⟩
    (by decide) selected_cut_36177

theorem selected_cut_36178 : selected 9 ⟨956010, by decide⟩
    (prefixPartial 12 288289) = some ⟨12, 2, 0, 956010, 288289, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_288289_956010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288289 ⟨956010, by decide⟩ :=
  accepted_of_selected 12 288289 ⟨956010, by decide⟩ ⟨12, 2, 0, 956010, 288289, 2761, 65536⟩
    (by decide) selected_cut_36178

theorem selected_cut_36179 : selected 9 ⟨956059, by decide⟩
    (prefixPartial 12 288290) = some ⟨12, 2, 0, 956059, 288290, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_288290_956059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288290 ⟨956059, by decide⟩ :=
  accepted_of_selected 12 288290 ⟨956059, by decide⟩ ⟨12, 2, 0, 956059, 288290, 3029, 65536⟩
    (by decide) selected_cut_36179

theorem selected_cut_36180 : selected 9 ⟨956125, by decide⟩
    (prefixPartial 12 288291) = some ⟨12, 2, 0, 956125, 288291, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_288291_956125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288291 ⟨956125, by decide⟩ :=
  accepted_of_selected 12 288291 ⟨956125, by decide⟩ ⟨12, 2, 0, 956125, 288291, 3597, 65536⟩
    (by decide) selected_cut_36180

theorem unmarked_context_11_72072_956126 : frontier 10 ⟨956126, by decide⟩
    (prefixCache 11 72072) (prefixPartial 11 72072) = false := by
  decide +kernel

theorem node_context_11_72072_956126 : EJMOriginalGlobalDAGData.nodes 10 ⟨956126, by decide⟩ =
    .split (coordinate 11) (![⟨955972, by decide⟩,⟨956010, by decide⟩,⟨956059, by decide⟩,⟨956125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72072_956126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72072 ⟨956126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72072
    ⟨956126, by decide⟩ (by decide) (![⟨955972, by decide⟩,⟨956010, by decide⟩,⟨956059, by decide⟩,⟨956125, by decide⟩]) unmarked_context_11_72072_956126 node_context_11_72072_956126
  intro a
  fin_cases a
  · exact context_12_288288_955972
  · exact context_12_288289_956010
  · exact context_12_288290_956059
  · exact context_12_288291_956125

theorem selected_cut_36181 : selected 9 ⟨956165, by decide⟩
    (prefixPartial 12 288292) = some ⟨12, 2, 0, 956165, 288292, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_288292_956165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288292 ⟨956165, by decide⟩ :=
  accepted_of_selected 12 288292 ⟨956165, by decide⟩ ⟨12, 2, 0, 956165, 288292, 2833, 65536⟩
    (by decide) selected_cut_36181

theorem selected_cut_36182 : selected 9 ⟨956203, by decide⟩
    (prefixPartial 12 288293) = some ⟨12, 2, 0, 956203, 288293, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_288293_956203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288293 ⟨956203, by decide⟩ :=
  accepted_of_selected 12 288293 ⟨956203, by decide⟩ ⟨12, 2, 0, 956203, 288293, 2545, 65536⟩
    (by decide) selected_cut_36182

theorem selected_cut_36183 : selected 9 ⟨956249, by decide⟩
    (prefixPartial 12 288294) = some ⟨12, 2, 0, 956249, 288294, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_288294_956249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288294 ⟨956249, by decide⟩ :=
  accepted_of_selected 12 288294 ⟨956249, by decide⟩ ⟨12, 2, 0, 956249, 288294, 2873, 65536⟩
    (by decide) selected_cut_36183

theorem selected_cut_36184 : selected 9 ⟨956296, by decide⟩
    (prefixPartial 12 288295) = some ⟨12, 2, 0, 956296, 288295, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_288295_956296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288295 ⟨956296, by decide⟩ :=
  accepted_of_selected 12 288295 ⟨956296, by decide⟩ ⟨12, 2, 0, 956296, 288295, 3205, 65536⟩
    (by decide) selected_cut_36184

theorem unmarked_context_11_72073_956297 : frontier 10 ⟨956297, by decide⟩
    (prefixCache 11 72073) (prefixPartial 11 72073) = false := by
  decide +kernel

theorem node_context_11_72073_956297 : EJMOriginalGlobalDAGData.nodes 10 ⟨956297, by decide⟩ =
    .split (coordinate 11) (![⟨956165, by decide⟩,⟨956203, by decide⟩,⟨956249, by decide⟩,⟨956296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72073_956297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72073 ⟨956297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72073
    ⟨956297, by decide⟩ (by decide) (![⟨956165, by decide⟩,⟨956203, by decide⟩,⟨956249, by decide⟩,⟨956296, by decide⟩]) unmarked_context_11_72073_956297 node_context_11_72073_956297
  intro a
  fin_cases a
  · exact context_12_288292_956165
  · exact context_12_288293_956203
  · exact context_12_288294_956249
  · exact context_12_288295_956296

theorem selected_cut_36185 : selected 9 ⟨956366, by decide⟩
    (prefixPartial 12 288296) = some ⟨12, 2, 0, 956366, 288296, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_288296_956366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288296 ⟨956366, by decide⟩ :=
  accepted_of_selected 12 288296 ⟨956366, by decide⟩ ⟨12, 2, 0, 956366, 288296, 3157, 65536⟩
    (by decide) selected_cut_36185

theorem selected_cut_36186 : selected 9 ⟨956410, by decide⟩
    (prefixPartial 12 288297) = some ⟨12, 2, 0, 956410, 288297, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_288297_956410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288297 ⟨956410, by decide⟩ :=
  accepted_of_selected 12 288297 ⟨956410, by decide⟩ ⟨12, 2, 0, 956410, 288297, 2753, 65536⟩
    (by decide) selected_cut_36186

theorem selected_cut_36187 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 288298) = some ⟨12, 1, 0, 661671, 288298, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288298_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288298 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 288298 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 288298, 1, 65536⟩
    (by decide) selected_cut_36187

theorem selected_cut_36188 : selected 9 ⟨956483, by decide⟩
    (prefixPartial 12 288299) = some ⟨12, 2, 0, 956483, 288299, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_288299_956483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288299 ⟨956483, by decide⟩ :=
  accepted_of_selected 12 288299 ⟨956483, by decide⟩ ⟨12, 2, 0, 956483, 288299, 3441, 65536⟩
    (by decide) selected_cut_36188

theorem unmarked_context_11_72074_956484 : frontier 10 ⟨956484, by decide⟩
    (prefixCache 11 72074) (prefixPartial 11 72074) = false := by
  decide +kernel

theorem node_context_11_72074_956484 : EJMOriginalGlobalDAGData.nodes 10 ⟨956484, by decide⟩ =
    .split (coordinate 11) (![⟨956366, by decide⟩,⟨956410, by decide⟩,⟨661671, by decide⟩,⟨956483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72074_956484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72074 ⟨956484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72074
    ⟨956484, by decide⟩ (by decide) (![⟨956366, by decide⟩,⟨956410, by decide⟩,⟨661671, by decide⟩,⟨956483, by decide⟩]) unmarked_context_11_72074_956484 node_context_11_72074_956484
  intro a
  fin_cases a
  · exact context_12_288296_956366
  · exact context_12_288297_956410
  · exact context_12_288298_661671
  · exact context_12_288299_956483

theorem selected_cut_36189 : selected 9 ⟨956539, by decide⟩
    (prefixPartial 12 288300) = some ⟨12, 2, 0, 956539, 288300, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_288300_956539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288300 ⟨956539, by decide⟩ :=
  accepted_of_selected 12 288300 ⟨956539, by decide⟩ ⟨12, 2, 0, 956539, 288300, 3097, 65536⟩
    (by decide) selected_cut_36189

theorem selected_cut_36190 : selected 9 ⟨956584, by decide⟩
    (prefixPartial 12 288301) = some ⟨12, 2, 0, 956584, 288301, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_288301_956584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288301 ⟨956584, by decide⟩ :=
  accepted_of_selected 12 288301 ⟨956584, by decide⟩ ⟨12, 2, 0, 956584, 288301, 2773, 65536⟩
    (by decide) selected_cut_36190

theorem selected_cut_36191 : selected 9 ⟨956644, by decide⟩
    (prefixPartial 12 288302) = some ⟨12, 2, 0, 956644, 288302, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_288302_956644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288302 ⟨956644, by decide⟩ :=
  accepted_of_selected 12 288302 ⟨956644, by decide⟩ ⟨12, 2, 0, 956644, 288302, 3241, 65536⟩
    (by decide) selected_cut_36191

theorem selected_cut_36192 : selected 9 ⟨956711, by decide⟩
    (prefixPartial 12 288303) = some ⟨12, 2, 0, 956711, 288303, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_288303_956711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288303 ⟨956711, by decide⟩ :=
  accepted_of_selected 12 288303 ⟨956711, by decide⟩ ⟨12, 2, 0, 956711, 288303, 3369, 65536⟩
    (by decide) selected_cut_36192

theorem unmarked_context_11_72075_956712 : frontier 10 ⟨956712, by decide⟩
    (prefixCache 11 72075) (prefixPartial 11 72075) = false := by
  decide +kernel

theorem node_context_11_72075_956712 : EJMOriginalGlobalDAGData.nodes 10 ⟨956712, by decide⟩ =
    .split (coordinate 11) (![⟨956539, by decide⟩,⟨956584, by decide⟩,⟨956644, by decide⟩,⟨956711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72075_956712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72075 ⟨956712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72075
    ⟨956712, by decide⟩ (by decide) (![⟨956539, by decide⟩,⟨956584, by decide⟩,⟨956644, by decide⟩,⟨956711, by decide⟩]) unmarked_context_11_72075_956712 node_context_11_72075_956712
  intro a
  fin_cases a
  · exact context_12_288300_956539
  · exact context_12_288301_956584
  · exact context_12_288302_956644
  · exact context_12_288303_956711

theorem unmarked_context_10_18018_956713 : frontier 11 ⟨956713, by decide⟩
    (prefixCache 10 18018) (prefixPartial 10 18018) = false := by
  decide +kernel

theorem node_context_10_18018_956713 : EJMOriginalGlobalDAGData.nodes 11 ⟨956713, by decide⟩ =
    .split (coordinate 10) (![⟨956126, by decide⟩,⟨956297, by decide⟩,⟨956484, by decide⟩,⟨956712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18018_956713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18018 ⟨956713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18018
    ⟨956713, by decide⟩ (by decide) (![⟨956126, by decide⟩,⟨956297, by decide⟩,⟨956484, by decide⟩,⟨956712, by decide⟩]) unmarked_context_10_18018_956713 node_context_10_18018_956713
  intro a
  fin_cases a
  · exact context_11_72072_956126
  · exact context_11_72073_956297
  · exact context_11_72074_956484
  · exact context_11_72075_956712

theorem selected_cut_36193 : selected 9 ⟨956751, by decide⟩
    (prefixPartial 12 288304) = some ⟨12, 2, 0, 956751, 288304, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_288304_956751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288304 ⟨956751, by decide⟩ :=
  accepted_of_selected 12 288304 ⟨956751, by decide⟩ ⟨12, 2, 0, 956751, 288304, 2525, 65536⟩
    (by decide) selected_cut_36193

theorem selected_cut_36194 : selected 9 ⟨956786, by decide⟩
    (prefixPartial 12 288305) = some ⟨12, 2, 0, 956786, 288305, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_288305_956786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288305 ⟨956786, by decide⟩ :=
  accepted_of_selected 12 288305 ⟨956786, by decide⟩ ⟨12, 2, 0, 956786, 288305, 2409, 65536⟩
    (by decide) selected_cut_36194

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
