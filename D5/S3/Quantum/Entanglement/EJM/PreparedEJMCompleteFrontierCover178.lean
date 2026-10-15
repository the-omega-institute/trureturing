/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover177
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17092 : selected 9 ⟨434371, by decide⟩
    (prefixPartial 12 28600) = some ⟨12, 2, 0, 434371, 28600, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_28600_434371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28600 ⟨434371, by decide⟩ :=
  accepted_of_selected 12 28600 ⟨434371, by decide⟩ ⟨12, 2, 0, 434371, 28600, 1201, 65536⟩
    (by decide) selected_cut_17092

theorem selected_cut_17093 : selected 9 ⟨434384, by decide⟩
    (prefixPartial 12 28601) = some ⟨12, 2, 0, 434384, 28601, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_28601_434384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28601 ⟨434384, by decide⟩ :=
  accepted_of_selected 12 28601 ⟨434384, by decide⟩ ⟨12, 2, 0, 434384, 28601, 1177, 65536⟩
    (by decide) selected_cut_17093

theorem selected_cut_17094 : selected 9 ⟨434394, by decide⟩
    (prefixPartial 12 28602) = some ⟨12, 2, 0, 434394, 28602, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_28602_434394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28602 ⟨434394, by decide⟩ :=
  accepted_of_selected 12 28602 ⟨434394, by decide⟩ ⟨12, 2, 0, 434394, 28602, 1073, 65536⟩
    (by decide) selected_cut_17094

theorem selected_cut_17095 : selected 9 ⟨434408, by decide⟩
    (prefixPartial 12 28603) = some ⟨12, 2, 0, 434408, 28603, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_28603_434408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28603 ⟨434408, by decide⟩ :=
  accepted_of_selected 12 28603 ⟨434408, by decide⟩ ⟨12, 2, 0, 434408, 28603, 1037, 65536⟩
    (by decide) selected_cut_17095

theorem unmarked_context_11_7150_434409 : frontier 10 ⟨434409, by decide⟩
    (prefixCache 11 7150) (prefixPartial 11 7150) = false := by
  decide +kernel

theorem node_context_11_7150_434409 : EJMOriginalGlobalDAGData.nodes 10 ⟨434409, by decide⟩ =
    .split (coordinate 11) (![⟨434371, by decide⟩,⟨434384, by decide⟩,⟨434394, by decide⟩,⟨434408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7150_434409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7150 ⟨434409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7150
    ⟨434409, by decide⟩ (by decide) (![⟨434371, by decide⟩,⟨434384, by decide⟩,⟨434394, by decide⟩,⟨434408, by decide⟩]) unmarked_context_11_7150_434409 node_context_11_7150_434409
  intro a
  fin_cases a
  · exact context_12_28600_434371
  · exact context_12_28601_434384
  · exact context_12_28602_434394
  · exact context_12_28603_434408

theorem selected_cut_17096 : selected 10 ⟨434451, by decide⟩
    (prefixPartial 11 7151) = some ⟨11, 2, 0, 434451, 7151, 3353, 262144⟩ := by
  decide +kernel

theorem context_11_7151_434451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7151 ⟨434451, by decide⟩ :=
  accepted_of_selected 11 7151 ⟨434451, by decide⟩ ⟨11, 2, 0, 434451, 7151, 3353, 262144⟩
    (by decide) selected_cut_17096

theorem unmarked_context_10_1787_434452 : frontier 11 ⟨434452, by decide⟩
    (prefixCache 10 1787) (prefixPartial 10 1787) = false := by
  decide +kernel

theorem node_context_10_1787_434452 : EJMOriginalGlobalDAGData.nodes 11 ⟨434452, by decide⟩ =
    .split (coordinate 10) (![⟨434298, by decide⟩,⟨434355, by decide⟩,⟨434409, by decide⟩,⟨434451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1787_434452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1787 ⟨434452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1787
    ⟨434452, by decide⟩ (by decide) (![⟨434298, by decide⟩,⟨434355, by decide⟩,⟨434409, by decide⟩,⟨434451, by decide⟩]) unmarked_context_10_1787_434452 node_context_10_1787_434452
  intro a
  fin_cases a
  · exact context_11_7148_434298
  · exact context_11_7149_434355
  · exact context_11_7150_434409
  · exact context_11_7151_434451

theorem unmarked_context_9_446_434453 : frontier 12 ⟨434453, by decide⟩
    (prefixCache 9 446) (prefixPartial 9 446) = false := by
  decide +kernel

theorem node_context_9_446_434453 : EJMOriginalGlobalDAGData.nodes 12 ⟨434453, by decide⟩ =
    .split (coordinate 9) (![⟨433560, by decide⟩,⟨433964, by decide⟩,⟨434245, by decide⟩,⟨434452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_446_434453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 446 ⟨434453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 446
    ⟨434453, by decide⟩ (by decide) (![⟨433560, by decide⟩,⟨433964, by decide⟩,⟨434245, by decide⟩,⟨434452, by decide⟩]) unmarked_context_9_446_434453 node_context_9_446_434453
  intro a
  fin_cases a
  · exact context_10_1784_433560
  · exact context_10_1785_433964
  · exact context_10_1786_434245
  · exact context_10_1787_434452

theorem selected_cut_17097 : selected 10 ⟨434484, by decide⟩
    (prefixPartial 11 7152) = some ⟨11, 2, 0, 434484, 7152, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_7152_434484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7152 ⟨434484, by decide⟩ :=
  accepted_of_selected 11 7152 ⟨434484, by decide⟩ ⟨11, 2, 0, 434484, 7152, 2173, 262144⟩
    (by decide) selected_cut_17097

theorem selected_cut_17098 : selected 10 ⟨434513, by decide⟩
    (prefixPartial 11 7153) = some ⟨11, 2, 0, 434513, 7153, 2437, 262144⟩ := by
  decide +kernel

theorem context_11_7153_434513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7153 ⟨434513, by decide⟩ :=
  accepted_of_selected 11 7153 ⟨434513, by decide⟩ ⟨11, 2, 0, 434513, 7153, 2437, 262144⟩
    (by decide) selected_cut_17098

theorem selected_cut_17099 : selected 10 ⟨434539, by decide⟩
    (prefixPartial 11 7154) = some ⟨11, 2, 0, 434539, 7154, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_7154_434539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7154 ⟨434539, by decide⟩ :=
  accepted_of_selected 11 7154 ⟨434539, by decide⟩ ⟨11, 2, 0, 434539, 7154, 2445, 262144⟩
    (by decide) selected_cut_17099

theorem selected_cut_17100 : selected 10 ⟨434557, by decide⟩
    (prefixPartial 11 7155) = some ⟨11, 2, 0, 434557, 7155, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_7155_434557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7155 ⟨434557, by decide⟩ :=
  accepted_of_selected 11 7155 ⟨434557, by decide⟩ ⟨11, 2, 0, 434557, 7155, 1369, 262144⟩
    (by decide) selected_cut_17100

theorem unmarked_context_10_1788_434558 : frontier 11 ⟨434558, by decide⟩
    (prefixCache 10 1788) (prefixPartial 10 1788) = false := by
  decide +kernel

theorem node_context_10_1788_434558 : EJMOriginalGlobalDAGData.nodes 11 ⟨434558, by decide⟩ =
    .split (coordinate 10) (![⟨434484, by decide⟩,⟨434513, by decide⟩,⟨434539, by decide⟩,⟨434557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1788_434558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1788 ⟨434558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1788
    ⟨434558, by decide⟩ (by decide) (![⟨434484, by decide⟩,⟨434513, by decide⟩,⟨434539, by decide⟩,⟨434557, by decide⟩]) unmarked_context_10_1788_434558 node_context_10_1788_434558
  intro a
  fin_cases a
  · exact context_11_7152_434484
  · exact context_11_7153_434513
  · exact context_11_7154_434539
  · exact context_11_7155_434557

theorem selected_cut_17101 : selected 10 ⟨434583, by decide⟩
    (prefixPartial 11 7156) = some ⟨11, 2, 0, 434583, 7156, 2029, 262144⟩ := by
  decide +kernel

theorem context_11_7156_434583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7156 ⟨434583, by decide⟩ :=
  accepted_of_selected 11 7156 ⟨434583, by decide⟩ ⟨11, 2, 0, 434583, 7156, 2029, 262144⟩
    (by decide) selected_cut_17101

theorem selected_cut_17102 : selected 10 ⟨434604, by decide⟩
    (prefixPartial 11 7157) = some ⟨11, 2, 0, 434604, 7157, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_7157_434604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7157 ⟨434604, by decide⟩ :=
  accepted_of_selected 11 7157 ⟨434604, by decide⟩ ⟨11, 2, 0, 434604, 7157, 1893, 262144⟩
    (by decide) selected_cut_17102

theorem selected_cut_17103 : selected 10 ⟨434623, by decide⟩
    (prefixPartial 11 7158) = some ⟨11, 2, 0, 434623, 7158, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_7158_434623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7158 ⟨434623, by decide⟩ :=
  accepted_of_selected 11 7158 ⟨434623, by decide⟩ ⟨11, 2, 0, 434623, 7158, 1653, 262144⟩
    (by decide) selected_cut_17103

theorem selected_cut_17104 : selected 10 ⟨434637, by decide⟩
    (prefixPartial 11 7159) = some ⟨11, 2, 0, 434637, 7159, 1029, 262144⟩ := by
  decide +kernel

theorem context_11_7159_434637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7159 ⟨434637, by decide⟩ :=
  accepted_of_selected 11 7159 ⟨434637, by decide⟩ ⟨11, 2, 0, 434637, 7159, 1029, 262144⟩
    (by decide) selected_cut_17104

theorem unmarked_context_10_1789_434638 : frontier 11 ⟨434638, by decide⟩
    (prefixCache 10 1789) (prefixPartial 10 1789) = false := by
  decide +kernel

theorem node_context_10_1789_434638 : EJMOriginalGlobalDAGData.nodes 11 ⟨434638, by decide⟩ =
    .split (coordinate 10) (![⟨434583, by decide⟩,⟨434604, by decide⟩,⟨434623, by decide⟩,⟨434637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1789_434638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1789 ⟨434638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1789
    ⟨434638, by decide⟩ (by decide) (![⟨434583, by decide⟩,⟨434604, by decide⟩,⟨434623, by decide⟩,⟨434637, by decide⟩]) unmarked_context_10_1789_434638 node_context_10_1789_434638
  intro a
  fin_cases a
  · exact context_11_7156_434583
  · exact context_11_7157_434604
  · exact context_11_7158_434623
  · exact context_11_7159_434637

theorem selected_cut_17105 : selected 11 ⟨434706, by decide⟩
    (prefixPartial 10 1790) = some ⟨10, 2, 0, 434706, 1790, 4081, 1048576⟩ := by
  decide +kernel

theorem context_10_1790_434706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1790 ⟨434706, by decide⟩ :=
  accepted_of_selected 10 1790 ⟨434706, by decide⟩ ⟨10, 2, 0, 434706, 1790, 4081, 1048576⟩
    (by decide) selected_cut_17105

theorem selected_cut_17106 : selected 11 ⟨434735, by decide⟩
    (prefixPartial 10 1791) = some ⟨10, 2, 0, 434735, 1791, 1069, 1048576⟩ := by
  decide +kernel

theorem context_10_1791_434735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1791 ⟨434735, by decide⟩ :=
  accepted_of_selected 10 1791 ⟨434735, by decide⟩ ⟨10, 2, 0, 434735, 1791, 1069, 1048576⟩
    (by decide) selected_cut_17106

theorem unmarked_context_9_447_434736 : frontier 12 ⟨434736, by decide⟩
    (prefixCache 9 447) (prefixPartial 9 447) = false := by
  decide +kernel

theorem node_context_9_447_434736 : EJMOriginalGlobalDAGData.nodes 12 ⟨434736, by decide⟩ =
    .split (coordinate 9) (![⟨434558, by decide⟩,⟨434638, by decide⟩,⟨434706, by decide⟩,⟨434735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_447_434736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 447 ⟨434736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 447
    ⟨434736, by decide⟩ (by decide) (![⟨434558, by decide⟩,⟨434638, by decide⟩,⟨434706, by decide⟩,⟨434735, by decide⟩]) unmarked_context_9_447_434736 node_context_9_447_434736
  intro a
  fin_cases a
  · exact context_10_1788_434558
  · exact context_10_1789_434638
  · exact context_10_1790_434706
  · exact context_10_1791_434735

theorem unmarked_context_8_111_434737 : frontier 13 ⟨434737, by decide⟩
    (prefixCache 8 111) (prefixPartial 8 111) = false := by
  decide +kernel

theorem node_context_8_111_434737 : EJMOriginalGlobalDAGData.nodes 13 ⟨434737, by decide⟩ =
    .split (coordinate 8) (![⟨429288, by decide⟩,⟨433018, by decide⟩,⟨434453, by decide⟩,⟨434736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_111_434737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 111 ⟨434737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 111
    ⟨434737, by decide⟩ (by decide) (![⟨429288, by decide⟩,⟨433018, by decide⟩,⟨434453, by decide⟩,⟨434736, by decide⟩]) unmarked_context_8_111_434737 node_context_8_111_434737
  intro a
  fin_cases a
  · exact context_9_444_429288
  · exact context_9_445_433018
  · exact context_9_446_434453
  · exact context_9_447_434736

theorem unmarked_context_7_27_434738 : frontier 14 ⟨434738, by decide⟩
    (prefixCache 7 27) (prefixPartial 7 27) = false := by
  decide +kernel

theorem node_context_7_27_434738 : EJMOriginalGlobalDAGData.nodes 14 ⟨434738, by decide⟩ =
    .split (coordinate 7) (![⟨399389, by decide⟩,⟨410768, by decide⟩,⟨421999, by decide⟩,⟨434737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_27_434738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 27 ⟨434738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 27
    ⟨434738, by decide⟩ (by decide) (![⟨399389, by decide⟩,⟨410768, by decide⟩,⟨421999, by decide⟩,⟨434737, by decide⟩]) unmarked_context_7_27_434738 node_context_7_27_434738
  intro a
  fin_cases a
  · exact context_8_108_399389
  · exact context_8_109_410768
  · exact context_8_110_421999
  · exact context_8_111_434737

theorem unmarked_context_6_6_434739 : frontier 15 ⟨434739, by decide⟩
    (prefixCache 6 6) (prefixPartial 6 6) = false := by
  decide +kernel

theorem node_context_6_6_434739 : EJMOriginalGlobalDAGData.nodes 15 ⟨434739, by decide⟩ =
    .split (coordinate 6) (![⟨301652, by decide⟩,⟨347461, by decide⟩,⟨388828, by decide⟩,⟨434738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_6_434739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 6 ⟨434739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 6
    ⟨434739, by decide⟩ (by decide) (![⟨301652, by decide⟩,⟨347461, by decide⟩,⟨388828, by decide⟩,⟨434738, by decide⟩]) unmarked_context_6_6_434739 node_context_6_6_434739
  intro a
  fin_cases a
  · exact context_7_24_301652
  · exact context_7_25_347461
  · exact context_7_26_388828
  · exact context_7_27_434738

theorem selected_cut_17107 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 7) = some ⟨6, 1, 0, 116314, 7, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_7_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 7 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 7 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 7, 1, 268435456⟩
    (by decide) selected_cut_17107

theorem unmarked_context_5_1_434740 : frontier 16 ⟨434740, by decide⟩
    (prefixCache 5 1) (prefixPartial 5 1) = false := by
  decide +kernel

theorem node_context_5_1_434740 : EJMOriginalGlobalDAGData.nodes 16 ⟨434740, by decide⟩ =
    .split (coordinate 5) (![⟨167447, by decide⟩,⟨265058, by decide⟩,⟨434739, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_1_434740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 1 ⟨434740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 1
    ⟨434740, by decide⟩ (by decide) (![⟨167447, by decide⟩,⟨265058, by decide⟩,⟨434739, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_1_434740 node_context_5_1_434740
  intro a
  fin_cases a
  · exact context_6_4_167447
  · exact context_6_5_265058
  · exact context_6_6_434739
  · exact context_6_7_116314

theorem selected_cut_17108 : selected 16 ⟨434741, by decide⟩
    (prefixPartial 5 2) = some ⟨5, 1, 0, 434741, 2, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_2_434741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 2 ⟨434741, by decide⟩ :=
  accepted_of_selected 5 2 ⟨434741, by decide⟩ ⟨5, 1, 0, 434741, 2, 1, 1073741824⟩
    (by decide) selected_cut_17108

theorem selected_cut_17109 : selected 16 ⟨434742, by decide⟩
    (prefixPartial 5 3) = some ⟨5, 1, 0, 434742, 3, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_3_434742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 3 ⟨434742, by decide⟩ :=
  accepted_of_selected 5 3 ⟨434742, by decide⟩ ⟨5, 1, 0, 434742, 3, 1, 1073741824⟩
    (by decide) selected_cut_17109

theorem unmarked_context_4_0_434743 : frontier 17 ⟨434743, by decide⟩
    (prefixCache 4 0) (prefixPartial 4 0) = false := by
  decide +kernel

theorem node_context_4_0_434743 : EJMOriginalGlobalDAGData.nodes 17 ⟨434743, by decide⟩ =
    .split (coordinate 4) (![⟨116315, by decide⟩,⟨434740, by decide⟩,⟨434741, by decide⟩,⟨434742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_0_434743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 0 ⟨434743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 0
    ⟨434743, by decide⟩ (by decide) (![⟨116315, by decide⟩,⟨434740, by decide⟩,⟨434741, by decide⟩,⟨434742, by decide⟩]) unmarked_context_4_0_434743 node_context_4_0_434743
  intro a
  fin_cases a
  · exact context_5_0_116315
  · exact context_5_1_434740
  · exact context_5_2_434741
  · exact context_5_3_434742

theorem selected_cut_17110 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 16) = some ⟨6, 1, 0, 434744, 16, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_16_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 16 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 16 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 16, 1, 268435456⟩
    (by decide) selected_cut_17110

theorem selected_cut_17111 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17408) = some ⟨11, 1, 0, 434745, 17408, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17408_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17408 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17408 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17408, 1, 262144⟩
    (by decide) selected_cut_17111

theorem selected_cut_17112 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69636) = some ⟨12, 1, 0, 895, 69636, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69636_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69636 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69636 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69636, 1, 65536⟩
    (by decide) selected_cut_17112

theorem selected_cut_17113 : selected 9 ⟨434810, by decide⟩
    (prefixPartial 12 69637) = some ⟨12, 2, 0, 434810, 69637, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_69637_434810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69637 ⟨434810, by decide⟩ :=
  accepted_of_selected 12 69637 ⟨434810, by decide⟩ ⟨12, 2, 0, 434810, 69637, 1837, 65536⟩
    (by decide) selected_cut_17113

theorem selected_cut_17114 : selected 8 ⟨434854, by decide⟩
    (prefixPartial 13 278552) = some ⟨13, 2, 0, 434854, 278552, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_278552_434854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278552 ⟨434854, by decide⟩ :=
  accepted_of_selected 13 278552 ⟨434854, by decide⟩ ⟨13, 2, 0, 434854, 278552, 1633, 16384⟩
    (by decide) selected_cut_17114

theorem selected_cut_17115 : selected 8 ⟨434879, by decide⟩
    (prefixPartial 13 278553) = some ⟨13, 2, 0, 434879, 278553, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_278553_434879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278553 ⟨434879, by decide⟩ :=
  accepted_of_selected 13 278553 ⟨434879, by decide⟩ ⟨13, 2, 0, 434879, 278553, 2189, 16384⟩
    (by decide) selected_cut_17115

theorem selected_cut_17116 : selected 8 ⟨434904, by decide⟩
    (prefixPartial 13 278554) = some ⟨13, 2, 0, 434904, 278554, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_278554_434904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278554 ⟨434904, by decide⟩ :=
  accepted_of_selected 13 278554 ⟨434904, by decide⟩ ⟨13, 2, 0, 434904, 278554, 1545, 16384⟩
    (by decide) selected_cut_17116

theorem selected_cut_17117 : selected 8 ⟨434926, by decide⟩
    (prefixPartial 13 278555) = some ⟨13, 2, 0, 434926, 278555, 869, 16384⟩ := by
  decide +kernel

theorem context_13_278555_434926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278555 ⟨434926, by decide⟩ :=
  accepted_of_selected 13 278555 ⟨434926, by decide⟩ ⟨13, 2, 0, 434926, 278555, 869, 16384⟩
    (by decide) selected_cut_17117

theorem unmarked_context_12_69638_434927 : frontier 9 ⟨434927, by decide⟩
    (prefixCache 12 69638) (prefixPartial 12 69638) = false := by
  decide +kernel

theorem node_context_12_69638_434927 : EJMOriginalGlobalDAGData.nodes 9 ⟨434927, by decide⟩ =
    .split (coordinate 12) (![⟨434854, by decide⟩,⟨434879, by decide⟩,⟨434904, by decide⟩,⟨434926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69638_434927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69638 ⟨434927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69638
    ⟨434927, by decide⟩ (by decide) (![⟨434854, by decide⟩,⟨434879, by decide⟩,⟨434904, by decide⟩,⟨434926, by decide⟩]) unmarked_context_12_69638_434927 node_context_12_69638_434927
  intro a
  fin_cases a
  · exact context_13_278552_434854
  · exact context_13_278553_434879
  · exact context_13_278554_434904
  · exact context_13_278555_434926

theorem selected_cut_17118 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69639) = some ⟨12, 1, 0, 893, 69639, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69639_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69639 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69639 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69639, 1, 65536⟩
    (by decide) selected_cut_17118

theorem unmarked_context_11_17409_434928 : frontier 10 ⟨434928, by decide⟩
    (prefixCache 11 17409) (prefixPartial 11 17409) = false := by
  decide +kernel

theorem node_context_11_17409_434928 : EJMOriginalGlobalDAGData.nodes 10 ⟨434928, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨434810, by decide⟩,⟨434927, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17409_434928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17409 ⟨434928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17409
    ⟨434928, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨434810, by decide⟩,⟨434927, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17409_434928 node_context_11_17409_434928
  intro a
  fin_cases a
  · exact context_12_69636_895
  · exact context_12_69637_434810
  · exact context_12_69638_434927
  · exact context_12_69639_893

theorem selected_cut_17119 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69640) = some ⟨12, 1, 0, 895, 69640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69640_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69640 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69640 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69640, 1, 65536⟩
    (by decide) selected_cut_17119

theorem selected_cut_17120 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69641) = some ⟨12, 1, 0, 895, 69641, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69641_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69641 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69641 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69641, 1, 65536⟩
    (by decide) selected_cut_17120

theorem selected_cut_17121 : selected 9 ⟨435031, by decide⟩
    (prefixPartial 12 69642) = some ⟨12, 2, 0, 435031, 69642, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_69642_435031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69642 ⟨435031, by decide⟩ :=
  accepted_of_selected 12 69642 ⟨435031, by decide⟩ ⟨12, 2, 0, 435031, 69642, 1973, 65536⟩
    (by decide) selected_cut_17121

theorem selected_cut_17122 : selected 9 ⟨435157, by decide⟩
    (prefixPartial 12 69643) = some ⟨12, 2, 0, 435157, 69643, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_69643_435157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69643 ⟨435157, by decide⟩ :=
  accepted_of_selected 12 69643 ⟨435157, by decide⟩ ⟨12, 2, 0, 435157, 69643, 3725, 65536⟩
    (by decide) selected_cut_17122

theorem unmarked_context_11_17410_435158 : frontier 10 ⟨435158, by decide⟩
    (prefixCache 11 17410) (prefixPartial 11 17410) = false := by
  decide +kernel

theorem node_context_11_17410_435158 : EJMOriginalGlobalDAGData.nodes 10 ⟨435158, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨435031, by decide⟩,⟨435157, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17410_435158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17410 ⟨435158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17410
    ⟨435158, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨435031, by decide⟩,⟨435157, by decide⟩]) unmarked_context_11_17410_435158 node_context_11_17410_435158
  intro a
  fin_cases a
  · exact context_12_69640_895
  · exact context_12_69641_895
  · exact context_12_69642_435031
  · exact context_12_69643_435157

theorem selected_cut_17123 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17411) = some ⟨11, 1, 0, 1736, 17411, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17411_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17411 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17411 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17411, 1, 262144⟩
    (by decide) selected_cut_17123

theorem unmarked_context_10_4352_435159 : frontier 11 ⟨435159, by decide⟩
    (prefixCache 10 4352) (prefixPartial 10 4352) = false := by
  decide +kernel

theorem node_context_10_4352_435159 : EJMOriginalGlobalDAGData.nodes 11 ⟨435159, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434928, by decide⟩,⟨435158, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4352_435159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4352 ⟨435159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4352
    ⟨435159, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434928, by decide⟩,⟨435158, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4352_435159 node_context_10_4352_435159
  intro a
  fin_cases a
  · exact context_11_17408_434745
  · exact context_11_17409_434928
  · exact context_11_17410_435158
  · exact context_11_17411_1736

theorem selected_cut_17124 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 69648) = some ⟨12, 1, 0, 435160, 69648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69648_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69648 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 69648 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 69648, 1, 65536⟩
    (by decide) selected_cut_17124

theorem selected_cut_17125 : selected 9 ⟨435208, by decide⟩
    (prefixPartial 12 69649) = some ⟨12, 2, 0, 435208, 69649, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_69649_435208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69649 ⟨435208, by decide⟩ :=
  accepted_of_selected 12 69649 ⟨435208, by decide⟩ ⟨12, 2, 0, 435208, 69649, 1981, 65536⟩
    (by decide) selected_cut_17125

theorem selected_cut_17126 : selected 9 ⟨435263, by decide⟩
    (prefixPartial 12 69650) = some ⟨12, 2, 0, 435263, 69650, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_69650_435263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69650 ⟨435263, by decide⟩ :=
  accepted_of_selected 12 69650 ⟨435263, by decide⟩ ⟨12, 2, 0, 435263, 69650, 3577, 65536⟩
    (by decide) selected_cut_17126

theorem selected_cut_17127 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69651) = some ⟨12, 1, 0, 893, 69651, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69651_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69651 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69651 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69651, 1, 65536⟩
    (by decide) selected_cut_17127

theorem unmarked_context_11_17412_435264 : frontier 10 ⟨435264, by decide⟩
    (prefixCache 11 17412) (prefixPartial 11 17412) = false := by
  decide +kernel

theorem node_context_11_17412_435264 : EJMOriginalGlobalDAGData.nodes 10 ⟨435264, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨435208, by decide⟩,⟨435263, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17412_435264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17412 ⟨435264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17412
    ⟨435264, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨435208, by decide⟩,⟨435263, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17412_435264 node_context_11_17412_435264
  intro a
  fin_cases a
  · exact context_12_69648_435160
  · exact context_12_69649_435208
  · exact context_12_69650_435263
  · exact context_12_69651_893

theorem selected_cut_17128 : selected 9 ⟨435339, by decide⟩
    (prefixPartial 12 69652) = some ⟨12, 2, 0, 435339, 69652, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_69652_435339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69652 ⟨435339, by decide⟩ :=
  accepted_of_selected 12 69652 ⟨435339, by decide⟩ ⟨12, 2, 0, 435339, 69652, 2109, 65536⟩
    (by decide) selected_cut_17128

theorem selected_cut_17129 : selected 9 ⟨435397, by decide⟩
    (prefixPartial 12 69653) = some ⟨12, 2, 0, 435397, 69653, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_69653_435397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69653 ⟨435397, by decide⟩ :=
  accepted_of_selected 12 69653 ⟨435397, by decide⟩ ⟨12, 2, 0, 435397, 69653, 2453, 65536⟩
    (by decide) selected_cut_17129

theorem selected_cut_17130 : selected 8 ⟨435420, by decide⟩
    (prefixPartial 13 278616) = some ⟨13, 2, 0, 435420, 278616, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_278616_435420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278616 ⟨435420, by decide⟩ :=
  accepted_of_selected 13 278616 ⟨435420, by decide⟩ ⟨13, 2, 0, 435420, 278616, 1081, 16384⟩
    (by decide) selected_cut_17130

theorem selected_cut_17131 : selected 8 ⟨435448, by decide⟩
    (prefixPartial 13 278617) = some ⟨13, 2, 0, 435448, 278617, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_278617_435448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278617 ⟨435448, by decide⟩ :=
  accepted_of_selected 13 278617 ⟨435448, by decide⟩ ⟨13, 2, 0, 435448, 278617, 1721, 16384⟩
    (by decide) selected_cut_17131

theorem selected_cut_17132 : selected 8 ⟨435467, by decide⟩
    (prefixPartial 13 278618) = some ⟨13, 2, 0, 435467, 278618, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_278618_435467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278618 ⟨435467, by decide⟩ :=
  accepted_of_selected 13 278618 ⟨435467, by decide⟩ ⟨13, 2, 0, 435467, 278618, 1377, 16384⟩
    (by decide) selected_cut_17132

theorem selected_cut_17133 : selected 8 ⟨435480, by decide⟩
    (prefixPartial 13 278619) = some ⟨13, 2, 0, 435480, 278619, 785, 16384⟩ := by
  decide +kernel

theorem context_13_278619_435480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278619 ⟨435480, by decide⟩ :=
  accepted_of_selected 13 278619 ⟨435480, by decide⟩ ⟨13, 2, 0, 435480, 278619, 785, 16384⟩
    (by decide) selected_cut_17133

theorem unmarked_context_12_69654_435481 : frontier 9 ⟨435481, by decide⟩
    (prefixCache 12 69654) (prefixPartial 12 69654) = false := by
  decide +kernel

theorem node_context_12_69654_435481 : EJMOriginalGlobalDAGData.nodes 9 ⟨435481, by decide⟩ =
    .split (coordinate 12) (![⟨435420, by decide⟩,⟨435448, by decide⟩,⟨435467, by decide⟩,⟨435480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69654_435481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69654 ⟨435481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69654
    ⟨435481, by decide⟩ (by decide) (![⟨435420, by decide⟩,⟨435448, by decide⟩,⟨435467, by decide⟩,⟨435480, by decide⟩]) unmarked_context_12_69654_435481 node_context_12_69654_435481
  intro a
  fin_cases a
  · exact context_13_278616_435420
  · exact context_13_278617_435448
  · exact context_13_278618_435467
  · exact context_13_278619_435480

theorem selected_cut_17134 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69655) = some ⟨12, 1, 0, 893, 69655, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69655_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69655 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69655 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69655, 1, 65536⟩
    (by decide) selected_cut_17134

theorem unmarked_context_11_17413_435482 : frontier 10 ⟨435482, by decide⟩
    (prefixCache 11 17413) (prefixPartial 11 17413) = false := by
  decide +kernel

theorem node_context_11_17413_435482 : EJMOriginalGlobalDAGData.nodes 10 ⟨435482, by decide⟩ =
    .split (coordinate 11) (![⟨435339, by decide⟩,⟨435397, by decide⟩,⟨435481, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17413_435482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17413 ⟨435482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17413
    ⟨435482, by decide⟩ (by decide) (![⟨435339, by decide⟩,⟨435397, by decide⟩,⟨435481, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17413_435482 node_context_11_17413_435482
  intro a
  fin_cases a
  · exact context_12_69652_435339
  · exact context_12_69653_435397
  · exact context_12_69654_435481
  · exact context_12_69655_893

theorem selected_cut_17135 : selected 8 ⟨435503, by decide⟩
    (prefixPartial 13 278624) = some ⟨13, 2, 0, 435503, 278624, 977, 16384⟩ := by
  decide +kernel

theorem context_13_278624_435503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278624 ⟨435503, by decide⟩ :=
  accepted_of_selected 13 278624 ⟨435503, by decide⟩ ⟨13, 2, 0, 435503, 278624, 977, 16384⟩
    (by decide) selected_cut_17135

theorem selected_cut_17136 : selected 8 ⟨435542, by decide⟩
    (prefixPartial 13 278625) = some ⟨13, 2, 0, 435542, 278625, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_278625_435542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278625 ⟨435542, by decide⟩ :=
  accepted_of_selected 13 278625 ⟨435542, by decide⟩ ⟨13, 2, 0, 435542, 278625, 2485, 16384⟩
    (by decide) selected_cut_17136

theorem selected_cut_17137 : selected 8 ⟨435575, by decide⟩
    (prefixPartial 13 278626) = some ⟨13, 2, 0, 435575, 278626, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_278626_435575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278626 ⟨435575, by decide⟩ :=
  accepted_of_selected 13 278626 ⟨435575, by decide⟩ ⟨13, 2, 0, 435575, 278626, 1849, 16384⟩
    (by decide) selected_cut_17137

theorem selected_cut_17138 : selected 8 ⟨435581, by decide⟩
    (prefixPartial 13 278627) = some ⟨13, 2, 0, 435581, 278627, 789, 16384⟩ := by
  decide +kernel

theorem context_13_278627_435581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278627 ⟨435581, by decide⟩ :=
  accepted_of_selected 13 278627 ⟨435581, by decide⟩ ⟨13, 2, 0, 435581, 278627, 789, 16384⟩
    (by decide) selected_cut_17138

theorem unmarked_context_12_69656_435582 : frontier 9 ⟨435582, by decide⟩
    (prefixCache 12 69656) (prefixPartial 12 69656) = false := by
  decide +kernel

theorem node_context_12_69656_435582 : EJMOriginalGlobalDAGData.nodes 9 ⟨435582, by decide⟩ =
    .split (coordinate 12) (![⟨435503, by decide⟩,⟨435542, by decide⟩,⟨435575, by decide⟩,⟨435581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69656_435582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69656 ⟨435582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69656
    ⟨435582, by decide⟩ (by decide) (![⟨435503, by decide⟩,⟨435542, by decide⟩,⟨435575, by decide⟩,⟨435581, by decide⟩]) unmarked_context_12_69656_435582 node_context_12_69656_435582
  intro a
  fin_cases a
  · exact context_13_278624_435503
  · exact context_13_278625_435542
  · exact context_13_278626_435575
  · exact context_13_278627_435581

theorem selected_cut_17139 : selected 8 ⟨435607, by decide⟩
    (prefixPartial 13 278628) = some ⟨13, 2, 0, 435607, 278628, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_278628_435607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278628 ⟨435607, by decide⟩ :=
  accepted_of_selected 13 278628 ⟨435607, by decide⟩ ⟨13, 2, 0, 435607, 278628, 1137, 16384⟩
    (by decide) selected_cut_17139

theorem selected_cut_17140 : selected 8 ⟨435627, by decide⟩
    (prefixPartial 13 278629) = some ⟨13, 2, 0, 435627, 278629, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_278629_435627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278629 ⟨435627, by decide⟩ :=
  accepted_of_selected 13 278629 ⟨435627, by decide⟩ ⟨13, 2, 0, 435627, 278629, 1305, 16384⟩
    (by decide) selected_cut_17140

theorem selected_cut_17141 : selected 8 ⟨435652, by decide⟩
    (prefixPartial 13 278630) = some ⟨13, 2, 0, 435652, 278630, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_278630_435652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278630 ⟨435652, by decide⟩ :=
  accepted_of_selected 13 278630 ⟨435652, by decide⟩ ⟨13, 2, 0, 435652, 278630, 1717, 16384⟩
    (by decide) selected_cut_17141

theorem selected_cut_17142 : selected 8 ⟨435659, by decide⟩
    (prefixPartial 13 278631) = some ⟨13, 2, 0, 435659, 278631, 777, 16384⟩ := by
  decide +kernel

theorem context_13_278631_435659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278631 ⟨435659, by decide⟩ :=
  accepted_of_selected 13 278631 ⟨435659, by decide⟩ ⟨13, 2, 0, 435659, 278631, 777, 16384⟩
    (by decide) selected_cut_17142

theorem unmarked_context_12_69657_435660 : frontier 9 ⟨435660, by decide⟩
    (prefixCache 12 69657) (prefixPartial 12 69657) = false := by
  decide +kernel

theorem node_context_12_69657_435660 : EJMOriginalGlobalDAGData.nodes 9 ⟨435660, by decide⟩ =
    .split (coordinate 12) (![⟨435607, by decide⟩,⟨435627, by decide⟩,⟨435652, by decide⟩,⟨435659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69657_435660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69657 ⟨435660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69657
    ⟨435660, by decide⟩ (by decide) (![⟨435607, by decide⟩,⟨435627, by decide⟩,⟨435652, by decide⟩,⟨435659, by decide⟩]) unmarked_context_12_69657_435660 node_context_12_69657_435660
  intro a
  fin_cases a
  · exact context_13_278628_435607
  · exact context_13_278629_435627
  · exact context_13_278630_435652
  · exact context_13_278631_435659

theorem selected_cut_17143 : selected 8 ⟨435677, by decide⟩
    (prefixPartial 13 278632) = some ⟨13, 2, 0, 435677, 278632, 889, 16384⟩ := by
  decide +kernel

theorem context_13_278632_435677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278632 ⟨435677, by decide⟩ :=
  accepted_of_selected 13 278632 ⟨435677, by decide⟩ ⟨13, 2, 0, 435677, 278632, 889, 16384⟩
    (by decide) selected_cut_17143

theorem selected_cut_17144 : selected 8 ⟨435698, by decide⟩
    (prefixPartial 13 278633) = some ⟨13, 2, 0, 435698, 278633, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_278633_435698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278633 ⟨435698, by decide⟩ :=
  accepted_of_selected 13 278633 ⟨435698, by decide⟩ ⟨13, 2, 0, 435698, 278633, 1541, 16384⟩
    (by decide) selected_cut_17144

theorem selected_cut_17145 : selected 8 ⟨435713, by decide⟩
    (prefixPartial 13 278634) = some ⟨13, 2, 0, 435713, 278634, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_278634_435713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278634 ⟨435713, by decide⟩ :=
  accepted_of_selected 13 278634 ⟨435713, by decide⟩ ⟨13, 2, 0, 435713, 278634, 1141, 16384⟩
    (by decide) selected_cut_17145

theorem selected_cut_17146 : selected 8 ⟨435720, by decide⟩
    (prefixPartial 13 278635) = some ⟨13, 2, 0, 435720, 278635, 761, 16384⟩ := by
  decide +kernel

theorem context_13_278635_435720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278635 ⟨435720, by decide⟩ :=
  accepted_of_selected 13 278635 ⟨435720, by decide⟩ ⟨13, 2, 0, 435720, 278635, 761, 16384⟩
    (by decide) selected_cut_17146

theorem unmarked_context_12_69658_435721 : frontier 9 ⟨435721, by decide⟩
    (prefixCache 12 69658) (prefixPartial 12 69658) = false := by
  decide +kernel

theorem node_context_12_69658_435721 : EJMOriginalGlobalDAGData.nodes 9 ⟨435721, by decide⟩ =
    .split (coordinate 12) (![⟨435677, by decide⟩,⟨435698, by decide⟩,⟨435713, by decide⟩,⟨435720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69658_435721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69658 ⟨435721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69658
    ⟨435721, by decide⟩ (by decide) (![⟨435677, by decide⟩,⟨435698, by decide⟩,⟨435713, by decide⟩,⟨435720, by decide⟩]) unmarked_context_12_69658_435721 node_context_12_69658_435721
  intro a
  fin_cases a
  · exact context_13_278632_435677
  · exact context_13_278633_435698
  · exact context_13_278634_435713
  · exact context_13_278635_435720

theorem selected_cut_17147 : selected 8 ⟨435740, by decide⟩
    (prefixPartial 13 278636) = some ⟨13, 2, 0, 435740, 278636, 853, 16384⟩ := by
  decide +kernel

theorem context_13_278636_435740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278636 ⟨435740, by decide⟩ :=
  accepted_of_selected 13 278636 ⟨435740, by decide⟩ ⟨13, 2, 0, 435740, 278636, 853, 16384⟩
    (by decide) selected_cut_17147

theorem selected_cut_17148 : selected 8 ⟨435762, by decide⟩
    (prefixPartial 13 278637) = some ⟨13, 2, 0, 435762, 278637, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_278637_435762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278637 ⟨435762, by decide⟩ :=
  accepted_of_selected 13 278637 ⟨435762, by decide⟩ ⟨13, 2, 0, 435762, 278637, 1713, 16384⟩
    (by decide) selected_cut_17148

theorem selected_cut_17149 : selected 8 ⟨435781, by decide⟩
    (prefixPartial 13 278638) = some ⟨13, 2, 0, 435781, 278638, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_278638_435781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278638 ⟨435781, by decide⟩ :=
  accepted_of_selected 13 278638 ⟨435781, by decide⟩ ⟨13, 2, 0, 435781, 278638, 1497, 16384⟩
    (by decide) selected_cut_17149

theorem selected_cut_17150 : selected 8 ⟨435786, by decide⟩
    (prefixPartial 13 278639) = some ⟨13, 2, 0, 435786, 278639, 653, 16384⟩ := by
  decide +kernel

theorem context_13_278639_435786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278639 ⟨435786, by decide⟩ :=
  accepted_of_selected 13 278639 ⟨435786, by decide⟩ ⟨13, 2, 0, 435786, 278639, 653, 16384⟩
    (by decide) selected_cut_17150

theorem unmarked_context_12_69659_435787 : frontier 9 ⟨435787, by decide⟩
    (prefixCache 12 69659) (prefixPartial 12 69659) = false := by
  decide +kernel

theorem node_context_12_69659_435787 : EJMOriginalGlobalDAGData.nodes 9 ⟨435787, by decide⟩ =
    .split (coordinate 12) (![⟨435740, by decide⟩,⟨435762, by decide⟩,⟨435781, by decide⟩,⟨435786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69659_435787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69659 ⟨435787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69659
    ⟨435787, by decide⟩ (by decide) (![⟨435740, by decide⟩,⟨435762, by decide⟩,⟨435781, by decide⟩,⟨435786, by decide⟩]) unmarked_context_12_69659_435787 node_context_12_69659_435787
  intro a
  fin_cases a
  · exact context_13_278636_435740
  · exact context_13_278637_435762
  · exact context_13_278638_435781
  · exact context_13_278639_435786

theorem unmarked_context_11_17414_435788 : frontier 10 ⟨435788, by decide⟩
    (prefixCache 11 17414) (prefixPartial 11 17414) = false := by
  decide +kernel

theorem node_context_11_17414_435788 : EJMOriginalGlobalDAGData.nodes 10 ⟨435788, by decide⟩ =
    .split (coordinate 11) (![⟨435582, by decide⟩,⟨435660, by decide⟩,⟨435721, by decide⟩,⟨435787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17414_435788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17414 ⟨435788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17414
    ⟨435788, by decide⟩ (by decide) (![⟨435582, by decide⟩,⟨435660, by decide⟩,⟨435721, by decide⟩,⟨435787, by decide⟩]) unmarked_context_11_17414_435788 node_context_11_17414_435788
  intro a
  fin_cases a
  · exact context_12_69656_435582
  · exact context_12_69657_435660
  · exact context_12_69658_435721
  · exact context_12_69659_435787

theorem selected_cut_17151 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17415) = some ⟨11, 1, 0, 1736, 17415, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17415_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17415 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17415 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17415, 1, 262144⟩
    (by decide) selected_cut_17151

theorem unmarked_context_10_4353_435789 : frontier 11 ⟨435789, by decide⟩
    (prefixCache 10 4353) (prefixPartial 10 4353) = false := by
  decide +kernel

theorem node_context_10_4353_435789 : EJMOriginalGlobalDAGData.nodes 11 ⟨435789, by decide⟩ =
    .split (coordinate 10) (![⟨435264, by decide⟩,⟨435482, by decide⟩,⟨435788, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4353_435789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4353 ⟨435789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4353
    ⟨435789, by decide⟩ (by decide) (![⟨435264, by decide⟩,⟨435482, by decide⟩,⟨435788, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4353_435789 node_context_10_4353_435789
  intro a
  fin_cases a
  · exact context_11_17412_435264
  · exact context_11_17413_435482
  · exact context_11_17414_435788
  · exact context_11_17415_1736

theorem selected_cut_17152 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 69664) = some ⟨12, 1, 0, 435790, 69664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69664_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69664 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 69664 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 69664, 1, 65536⟩
    (by decide) selected_cut_17152

theorem selected_cut_17153 : selected 9 ⟨435844, by decide⟩
    (prefixPartial 12 69665) = some ⟨12, 2, 0, 435844, 69665, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_69665_435844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69665 ⟨435844, by decide⟩ :=
  accepted_of_selected 12 69665 ⟨435844, by decide⟩ ⟨12, 2, 0, 435844, 69665, 3165, 65536⟩
    (by decide) selected_cut_17153

theorem selected_cut_17154 : selected 9 ⟨435893, by decide⟩
    (prefixPartial 12 69666) = some ⟨12, 2, 0, 435893, 69666, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_69666_435893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69666 ⟨435893, by decide⟩ :=
  accepted_of_selected 12 69666 ⟨435893, by decide⟩ ⟨12, 2, 0, 435893, 69666, 3097, 65536⟩
    (by decide) selected_cut_17154

theorem selected_cut_17155 : selected 9 ⟨435943, by decide⟩
    (prefixPartial 12 69667) = some ⟨12, 2, 0, 435943, 69667, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_69667_435943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69667 ⟨435943, by decide⟩ :=
  accepted_of_selected 12 69667 ⟨435943, by decide⟩ ⟨12, 2, 0, 435943, 69667, 3057, 65536⟩
    (by decide) selected_cut_17155

theorem unmarked_context_11_17416_435944 : frontier 10 ⟨435944, by decide⟩
    (prefixCache 11 17416) (prefixPartial 11 17416) = false := by
  decide +kernel

theorem node_context_11_17416_435944 : EJMOriginalGlobalDAGData.nodes 10 ⟨435944, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨435844, by decide⟩,⟨435893, by decide⟩,⟨435943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17416_435944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17416 ⟨435944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17416
    ⟨435944, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨435844, by decide⟩,⟨435893, by decide⟩,⟨435943, by decide⟩]) unmarked_context_11_17416_435944 node_context_11_17416_435944
  intro a
  fin_cases a
  · exact context_12_69664_435790
  · exact context_12_69665_435844
  · exact context_12_69666_435893
  · exact context_12_69667_435943

theorem selected_cut_17156 : selected 8 ⟨435966, by decide⟩
    (prefixPartial 13 278672) = some ⟨13, 2, 0, 435966, 278672, 597, 16384⟩ := by
  decide +kernel

theorem context_13_278672_435966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278672 ⟨435966, by decide⟩ :=
  accepted_of_selected 13 278672 ⟨435966, by decide⟩ ⟨13, 2, 0, 435966, 278672, 597, 16384⟩
    (by decide) selected_cut_17156

theorem selected_cut_17157 : selected 8 ⟨435994, by decide⟩
    (prefixPartial 13 278673) = some ⟨13, 2, 0, 435994, 278673, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_278673_435994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278673 ⟨435994, by decide⟩ :=
  accepted_of_selected 13 278673 ⟨435994, by decide⟩ ⟨13, 2, 0, 435994, 278673, 2145, 16384⟩
    (by decide) selected_cut_17157

theorem selected_cut_17158 : selected 8 ⟨436034, by decide⟩
    (prefixPartial 13 278674) = some ⟨13, 2, 0, 436034, 278674, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_278674_436034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278674 ⟨436034, by decide⟩ :=
  accepted_of_selected 13 278674 ⟨436034, by decide⟩ ⟨13, 2, 0, 436034, 278674, 1625, 16384⟩
    (by decide) selected_cut_17158

theorem selected_cut_17159 : selected 8 ⟨436046, by decide⟩
    (prefixPartial 13 278675) = some ⟨13, 2, 0, 436046, 278675, 685, 16384⟩ := by
  decide +kernel

theorem context_13_278675_436046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278675 ⟨436046, by decide⟩ :=
  accepted_of_selected 13 278675 ⟨436046, by decide⟩ ⟨13, 2, 0, 436046, 278675, 685, 16384⟩
    (by decide) selected_cut_17159

theorem unmarked_context_12_69668_436047 : frontier 9 ⟨436047, by decide⟩
    (prefixCache 12 69668) (prefixPartial 12 69668) = false := by
  decide +kernel

theorem node_context_12_69668_436047 : EJMOriginalGlobalDAGData.nodes 9 ⟨436047, by decide⟩ =
    .split (coordinate 12) (![⟨435966, by decide⟩,⟨435994, by decide⟩,⟨436034, by decide⟩,⟨436046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69668_436047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69668 ⟨436047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69668
    ⟨436047, by decide⟩ (by decide) (![⟨435966, by decide⟩,⟨435994, by decide⟩,⟨436034, by decide⟩,⟨436046, by decide⟩]) unmarked_context_12_69668_436047 node_context_12_69668_436047
  intro a
  fin_cases a
  · exact context_13_278672_435966
  · exact context_13_278673_435994
  · exact context_13_278674_436034
  · exact context_13_278675_436046

theorem selected_cut_17160 : selected 9 ⟨436107, by decide⟩
    (prefixPartial 12 69669) = some ⟨12, 2, 0, 436107, 69669, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_69669_436107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69669 ⟨436107, by decide⟩ :=
  accepted_of_selected 12 69669 ⟨436107, by decide⟩ ⟨12, 2, 0, 436107, 69669, 3525, 65536⟩
    (by decide) selected_cut_17160

theorem selected_cut_17161 : selected 9 ⟨436172, by decide⟩
    (prefixPartial 12 69670) = some ⟨12, 2, 0, 436172, 69670, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_69670_436172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69670 ⟨436172, by decide⟩ :=
  accepted_of_selected 12 69670 ⟨436172, by decide⟩ ⟨12, 2, 0, 436172, 69670, 3913, 65536⟩
    (by decide) selected_cut_17161

theorem selected_cut_17162 : selected 9 ⟨436227, by decide⟩
    (prefixPartial 12 69671) = some ⟨12, 2, 0, 436227, 69671, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_69671_436227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69671 ⟨436227, by decide⟩ :=
  accepted_of_selected 12 69671 ⟨436227, by decide⟩ ⟨12, 2, 0, 436227, 69671, 3821, 65536⟩
    (by decide) selected_cut_17162

theorem unmarked_context_11_17417_436228 : frontier 10 ⟨436228, by decide⟩
    (prefixCache 11 17417) (prefixPartial 11 17417) = false := by
  decide +kernel

theorem node_context_11_17417_436228 : EJMOriginalGlobalDAGData.nodes 10 ⟨436228, by decide⟩ =
    .split (coordinate 11) (![⟨436047, by decide⟩,⟨436107, by decide⟩,⟨436172, by decide⟩,⟨436227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17417_436228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17417 ⟨436228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17417
    ⟨436228, by decide⟩ (by decide) (![⟨436047, by decide⟩,⟨436107, by decide⟩,⟨436172, by decide⟩,⟨436227, by decide⟩]) unmarked_context_11_17417_436228 node_context_11_17417_436228
  intro a
  fin_cases a
  · exact context_12_69668_436047
  · exact context_12_69669_436107
  · exact context_12_69670_436172
  · exact context_12_69671_436227

theorem selected_cut_17163 : selected 9 ⟨436304, by decide⟩
    (prefixPartial 12 69672) = some ⟨12, 2, 0, 436304, 69672, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_69672_436304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69672 ⟨436304, by decide⟩ :=
  accepted_of_selected 12 69672 ⟨436304, by decide⟩ ⟨12, 2, 0, 436304, 69672, 2885, 65536⟩
    (by decide) selected_cut_17163

theorem selected_cut_17164 : selected 8 ⟨436318, by decide⟩
    (prefixPartial 13 278692) = some ⟨13, 2, 0, 436318, 278692, 437, 16384⟩ := by
  decide +kernel

theorem context_13_278692_436318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278692 ⟨436318, by decide⟩ :=
  accepted_of_selected 13 278692 ⟨436318, by decide⟩ ⟨13, 2, 0, 436318, 278692, 437, 16384⟩
    (by decide) selected_cut_17164

theorem selected_cut_17165 : selected 8 ⟨436335, by decide⟩
    (prefixPartial 13 278693) = some ⟨13, 2, 0, 436335, 278693, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_278693_436335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278693 ⟨436335, by decide⟩ :=
  accepted_of_selected 13 278693 ⟨436335, by decide⟩ ⟨13, 2, 0, 436335, 278693, 1533, 16384⟩
    (by decide) selected_cut_17165

theorem selected_cut_17166 : selected 8 ⟨436353, by decide⟩
    (prefixPartial 13 278694) = some ⟨13, 2, 0, 436353, 278694, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_278694_436353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278694 ⟨436353, by decide⟩ :=
  accepted_of_selected 13 278694 ⟨436353, by decide⟩ ⟨13, 2, 0, 436353, 278694, 1537, 16384⟩
    (by decide) selected_cut_17166

theorem selected_cut_17167 : selected 8 ⟨436363, by decide⟩
    (prefixPartial 13 278695) = some ⟨13, 2, 0, 436363, 278695, 649, 16384⟩ := by
  decide +kernel

theorem context_13_278695_436363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278695 ⟨436363, by decide⟩ :=
  accepted_of_selected 13 278695 ⟨436363, by decide⟩ ⟨13, 2, 0, 436363, 278695, 649, 16384⟩
    (by decide) selected_cut_17167

theorem unmarked_context_12_69673_436364 : frontier 9 ⟨436364, by decide⟩
    (prefixCache 12 69673) (prefixPartial 12 69673) = false := by
  decide +kernel

theorem node_context_12_69673_436364 : EJMOriginalGlobalDAGData.nodes 9 ⟨436364, by decide⟩ =
    .split (coordinate 12) (![⟨436318, by decide⟩,⟨436335, by decide⟩,⟨436353, by decide⟩,⟨436363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69673_436364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69673 ⟨436364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69673
    ⟨436364, by decide⟩ (by decide) (![⟨436318, by decide⟩,⟨436335, by decide⟩,⟨436353, by decide⟩,⟨436363, by decide⟩]) unmarked_context_12_69673_436364 node_context_12_69673_436364
  intro a
  fin_cases a
  · exact context_13_278692_436318
  · exact context_13_278693_436335
  · exact context_13_278694_436353
  · exact context_13_278695_436363

theorem selected_cut_17168 : selected 9 ⟨436412, by decide⟩
    (prefixPartial 12 69674) = some ⟨12, 2, 0, 436412, 69674, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_69674_436412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69674 ⟨436412, by decide⟩ :=
  accepted_of_selected 12 69674 ⟨436412, by decide⟩ ⟨12, 2, 0, 436412, 69674, 3501, 65536⟩
    (by decide) selected_cut_17168

theorem selected_cut_17169 : selected 9 ⟨436462, by decide⟩
    (prefixPartial 12 69675) = some ⟨12, 2, 0, 436462, 69675, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_69675_436462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69675 ⟨436462, by decide⟩ :=
  accepted_of_selected 12 69675 ⟨436462, by decide⟩ ⟨12, 2, 0, 436462, 69675, 3853, 65536⟩
    (by decide) selected_cut_17169

theorem unmarked_context_11_17418_436463 : frontier 10 ⟨436463, by decide⟩
    (prefixCache 11 17418) (prefixPartial 11 17418) = false := by
  decide +kernel

theorem node_context_11_17418_436463 : EJMOriginalGlobalDAGData.nodes 10 ⟨436463, by decide⟩ =
    .split (coordinate 11) (![⟨436304, by decide⟩,⟨436364, by decide⟩,⟨436412, by decide⟩,⟨436462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17418_436463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17418 ⟨436463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17418
    ⟨436463, by decide⟩ (by decide) (![⟨436304, by decide⟩,⟨436364, by decide⟩,⟨436412, by decide⟩,⟨436462, by decide⟩]) unmarked_context_11_17418_436463 node_context_11_17418_436463
  intro a
  fin_cases a
  · exact context_12_69672_436304
  · exact context_12_69673_436364
  · exact context_12_69674_436412
  · exact context_12_69675_436462

theorem selected_cut_17170 : selected 8 ⟨436470, by decide⟩
    (prefixPartial 13 278704) = some ⟨13, 2, 0, 436470, 278704, 217, 16384⟩ := by
  decide +kernel

theorem context_13_278704_436470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278704 ⟨436470, by decide⟩ :=
  accepted_of_selected 13 278704 ⟨436470, by decide⟩ ⟨13, 2, 0, 436470, 278704, 217, 16384⟩
    (by decide) selected_cut_17170

theorem selected_cut_17171 : selected 8 ⟨436511, by decide⟩
    (prefixPartial 13 278705) = some ⟨13, 2, 0, 436511, 278705, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_278705_436511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278705 ⟨436511, by decide⟩ :=
  accepted_of_selected 13 278705 ⟨436511, by decide⟩ ⟨13, 2, 0, 436511, 278705, 2625, 16384⟩
    (by decide) selected_cut_17171

theorem selected_cut_17172 : selected 8 ⟨436542, by decide⟩
    (prefixPartial 13 278706) = some ⟨13, 2, 0, 436542, 278706, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_278706_436542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278706 ⟨436542, by decide⟩ :=
  accepted_of_selected 13 278706 ⟨436542, by decide⟩ ⟨13, 2, 0, 436542, 278706, 1537, 16384⟩
    (by decide) selected_cut_17172

theorem selected_cut_17173 : selected 8 ⟨436549, by decide⟩
    (prefixPartial 13 278707) = some ⟨13, 2, 0, 436549, 278707, 625, 16384⟩ := by
  decide +kernel

theorem context_13_278707_436549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 278707 ⟨436549, by decide⟩ :=
  accepted_of_selected 13 278707 ⟨436549, by decide⟩ ⟨13, 2, 0, 436549, 278707, 625, 16384⟩
    (by decide) selected_cut_17173

theorem unmarked_context_12_69676_436550 : frontier 9 ⟨436550, by decide⟩
    (prefixCache 12 69676) (prefixPartial 12 69676) = false := by
  decide +kernel

theorem node_context_12_69676_436550 : EJMOriginalGlobalDAGData.nodes 9 ⟨436550, by decide⟩ =
    .split (coordinate 12) (![⟨436470, by decide⟩,⟨436511, by decide⟩,⟨436542, by decide⟩,⟨436549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69676_436550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69676 ⟨436550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69676
    ⟨436550, by decide⟩ (by decide) (![⟨436470, by decide⟩,⟨436511, by decide⟩,⟨436542, by decide⟩,⟨436549, by decide⟩]) unmarked_context_12_69676_436550 node_context_12_69676_436550
  intro a
  fin_cases a
  · exact context_13_278704_436470
  · exact context_13_278705_436511
  · exact context_13_278706_436542
  · exact context_13_278707_436549

theorem selected_cut_17174 : selected 9 ⟨436600, by decide⟩
    (prefixPartial 12 69677) = some ⟨12, 2, 0, 436600, 69677, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_69677_436600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69677 ⟨436600, by decide⟩ :=
  accepted_of_selected 12 69677 ⟨436600, by decide⟩ ⟨12, 2, 0, 436600, 69677, 3833, 65536⟩
    (by decide) selected_cut_17174

theorem selected_cut_17175 : selected 9 ⟨436646, by decide⟩
    (prefixPartial 12 69678) = some ⟨12, 2, 0, 436646, 69678, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_69678_436646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69678 ⟨436646, by decide⟩ :=
  accepted_of_selected 12 69678 ⟨436646, by decide⟩ ⟨12, 2, 0, 436646, 69678, 3617, 65536⟩
    (by decide) selected_cut_17175

theorem selected_cut_17176 : selected 9 ⟨436688, by decide⟩
    (prefixPartial 12 69679) = some ⟨12, 2, 0, 436688, 69679, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_69679_436688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69679 ⟨436688, by decide⟩ :=
  accepted_of_selected 12 69679 ⟨436688, by decide⟩ ⟨12, 2, 0, 436688, 69679, 3341, 65536⟩
    (by decide) selected_cut_17176

theorem unmarked_context_11_17419_436689 : frontier 10 ⟨436689, by decide⟩
    (prefixCache 11 17419) (prefixPartial 11 17419) = false := by
  decide +kernel

theorem node_context_11_17419_436689 : EJMOriginalGlobalDAGData.nodes 10 ⟨436689, by decide⟩ =
    .split (coordinate 11) (![⟨436550, by decide⟩,⟨436600, by decide⟩,⟨436646, by decide⟩,⟨436688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17419_436689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17419 ⟨436689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17419
    ⟨436689, by decide⟩ (by decide) (![⟨436550, by decide⟩,⟨436600, by decide⟩,⟨436646, by decide⟩,⟨436688, by decide⟩]) unmarked_context_11_17419_436689 node_context_11_17419_436689
  intro a
  fin_cases a
  · exact context_12_69676_436550
  · exact context_12_69677_436600
  · exact context_12_69678_436646
  · exact context_12_69679_436688

theorem unmarked_context_10_4354_436690 : frontier 11 ⟨436690, by decide⟩
    (prefixCache 10 4354) (prefixPartial 10 4354) = false := by
  decide +kernel

theorem node_context_10_4354_436690 : EJMOriginalGlobalDAGData.nodes 11 ⟨436690, by decide⟩ =
    .split (coordinate 10) (![⟨435944, by decide⟩,⟨436228, by decide⟩,⟨436463, by decide⟩,⟨436689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4354_436690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4354 ⟨436690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4354
    ⟨436690, by decide⟩ (by decide) (![⟨435944, by decide⟩,⟨436228, by decide⟩,⟨436463, by decide⟩,⟨436689, by decide⟩]) unmarked_context_10_4354_436690 node_context_10_4354_436690
  intro a
  fin_cases a
  · exact context_11_17416_435944
  · exact context_11_17417_436228
  · exact context_11_17418_436463
  · exact context_11_17419_436689

theorem selected_cut_17177 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4355) = some ⟨10, 1, 0, 3440, 4355, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4355_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4355 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4355 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4355, 1, 1048576⟩
    (by decide) selected_cut_17177

theorem unmarked_context_9_1088_436691 : frontier 12 ⟨436691, by decide⟩
    (prefixCache 9 1088) (prefixPartial 9 1088) = false := by
  decide +kernel

theorem node_context_9_1088_436691 : EJMOriginalGlobalDAGData.nodes 12 ⟨436691, by decide⟩ =
    .split (coordinate 9) (![⟨435159, by decide⟩,⟨435789, by decide⟩,⟨436690, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1088_436691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1088 ⟨436691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1088
    ⟨436691, by decide⟩ (by decide) (![⟨435159, by decide⟩,⟨435789, by decide⟩,⟨436690, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1088_436691 node_context_9_1088_436691
  intro a
  fin_cases a
  · exact context_10_4352_435159
  · exact context_10_4353_435789
  · exact context_10_4354_436690
  · exact context_10_4355_3440

theorem selected_cut_17178 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4356) = some ⟨10, 1, 0, 3442, 4356, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4356_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4356 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4356 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4356, 1, 1048576⟩
    (by decide) selected_cut_17178

theorem selected_cut_17179 : selected 9 ⟨436749, by decide⟩
    (prefixPartial 12 69712) = some ⟨12, 2, 0, 436749, 69712, 741, 65536⟩ := by
  decide +kernel

theorem context_12_69712_436749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69712 ⟨436749, by decide⟩ :=
  accepted_of_selected 12 69712 ⟨436749, by decide⟩ ⟨12, 2, 0, 436749, 69712, 741, 65536⟩
    (by decide) selected_cut_17179

theorem selected_cut_17180 : selected 9 ⟨436792, by decide⟩
    (prefixPartial 12 69713) = some ⟨12, 2, 0, 436792, 69713, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_69713_436792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69713 ⟨436792, by decide⟩ :=
  accepted_of_selected 12 69713 ⟨436792, by decide⟩ ⟨12, 2, 0, 436792, 69713, 1825, 65536⟩
    (by decide) selected_cut_17180

theorem selected_cut_17181 : selected 9 ⟨436855, by decide⟩
    (prefixPartial 12 69714) = some ⟨12, 2, 0, 436855, 69714, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_69714_436855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69714 ⟨436855, by decide⟩ :=
  accepted_of_selected 12 69714 ⟨436855, by decide⟩ ⟨12, 2, 0, 436855, 69714, 3565, 65536⟩
    (by decide) selected_cut_17181

theorem selected_cut_17182 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69715) = some ⟨12, 1, 0, 893, 69715, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69715_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69715 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69715 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69715, 1, 65536⟩
    (by decide) selected_cut_17182

theorem unmarked_context_11_17428_436856 : frontier 10 ⟨436856, by decide⟩
    (prefixCache 11 17428) (prefixPartial 11 17428) = false := by
  decide +kernel

theorem node_context_11_17428_436856 : EJMOriginalGlobalDAGData.nodes 10 ⟨436856, by decide⟩ =
    .split (coordinate 11) (![⟨436749, by decide⟩,⟨436792, by decide⟩,⟨436855, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17428_436856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17428 ⟨436856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17428
    ⟨436856, by decide⟩ (by decide) (![⟨436749, by decide⟩,⟨436792, by decide⟩,⟨436855, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17428_436856 node_context_11_17428_436856
  intro a
  fin_cases a
  · exact context_12_69712_436749
  · exact context_12_69713_436792
  · exact context_12_69714_436855
  · exact context_12_69715_893

theorem selected_cut_17183 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69716) = some ⟨12, 1, 0, 895, 69716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69716_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69716 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69716 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69716, 1, 65536⟩
    (by decide) selected_cut_17183

theorem selected_cut_17184 : selected 9 ⟨436890, by decide⟩
    (prefixPartial 12 69717) = some ⟨12, 2, 0, 436890, 69717, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_69717_436890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69717 ⟨436890, by decide⟩ :=
  accepted_of_selected 12 69717 ⟨436890, by decide⟩ ⟨12, 2, 0, 436890, 69717, 1077, 65536⟩
    (by decide) selected_cut_17184

theorem selected_cut_17185 : selected 9 ⟨436955, by decide⟩
    (prefixPartial 12 69718) = some ⟨12, 2, 0, 436955, 69718, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_69718_436955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69718 ⟨436955, by decide⟩ :=
  accepted_of_selected 12 69718 ⟨436955, by decide⟩ ⟨12, 2, 0, 436955, 69718, 3821, 65536⟩
    (by decide) selected_cut_17185

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
