/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover458
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_22071_1209511 : frontier 11 ⟨1209511, by decide⟩
    (prefixCache 10 22071) (prefixPartial 10 22071) = false := by
  decide +kernel

theorem node_context_10_22071_1209511 : EJMOriginalGlobalDAGData.nodes 11 ⟨1209511, by decide⟩ =
    .split (coordinate 10) (![⟨1209341, by decide⟩,⟨1209408, by decide⟩,⟨1209483, by decide⟩,⟨1209510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22071_1209511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22071 ⟨1209511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22071
    ⟨1209511, by decide⟩ (by decide) (![⟨1209341, by decide⟩,⟨1209408, by decide⟩,⟨1209483, by decide⟩,⟨1209510, by decide⟩]) unmarked_context_10_22071_1209511 node_context_10_22071_1209511
  intro a
  fin_cases a
  · exact context_11_88284_1209341
  · exact context_11_88285_1209408
  · exact context_11_88286_1209483
  · exact context_11_88287_1209510

theorem unmarked_context_9_5517_1209512 : frontier 12 ⟨1209512, by decide⟩
    (prefixCache 9 5517) (prefixPartial 9 5517) = false := by
  decide +kernel

theorem node_context_9_5517_1209512 : EJMOriginalGlobalDAGData.nodes 12 ⟨1209512, by decide⟩ =
    .split (coordinate 9) (![⟨1209090, by decide⟩,⟨893098, by decide⟩,⟨1209292, by decide⟩,⟨1209511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5517_1209512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5517 ⟨1209512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5517
    ⟨1209512, by decide⟩ (by decide) (![⟨1209090, by decide⟩,⟨893098, by decide⟩,⟨1209292, by decide⟩,⟨1209511, by decide⟩]) unmarked_context_9_5517_1209512 node_context_9_5517_1209512
  intro a
  fin_cases a
  · exact context_10_22068_1209090
  · exact context_10_22069_893098
  · exact context_10_22070_1209292
  · exact context_10_22071_1209511

theorem selected_cut_44068 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88288) = some ⟨11, 1, 0, 907917, 88288, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88288_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88288 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88288 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88288, 1, 262144⟩
    (by decide) selected_cut_44068

theorem selected_cut_44069 : selected 9 ⟨1209533, by decide⟩
    (prefixPartial 12 353156) = some ⟨12, 2, 0, 1209533, 353156, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_353156_1209533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353156 ⟨1209533, by decide⟩ :=
  accepted_of_selected 12 353156 ⟨1209533, by decide⟩ ⟨12, 2, 0, 1209533, 353156, 1285, 65536⟩
    (by decide) selected_cut_44069

theorem selected_cut_44070 : selected 9 ⟨1209551, by decide⟩
    (prefixPartial 12 353157) = some ⟨12, 2, 0, 1209551, 353157, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_353157_1209551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353157 ⟨1209551, by decide⟩ :=
  accepted_of_selected 12 353157 ⟨1209551, by decide⟩ ⟨12, 2, 0, 1209551, 353157, 1045, 65536⟩
    (by decide) selected_cut_44070

theorem selected_cut_44071 : selected 9 ⟨1209568, by decide⟩
    (prefixPartial 12 353158) = some ⟨12, 2, 0, 1209568, 353158, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_353158_1209568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353158 ⟨1209568, by decide⟩ :=
  accepted_of_selected 12 353158 ⟨1209568, by decide⟩ ⟨12, 2, 0, 1209568, 353158, 1265, 65536⟩
    (by decide) selected_cut_44071

theorem selected_cut_44072 : selected 9 ⟨1209584, by decide⟩
    (prefixPartial 12 353159) = some ⟨12, 2, 0, 1209584, 353159, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_353159_1209584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353159 ⟨1209584, by decide⟩ :=
  accepted_of_selected 12 353159 ⟨1209584, by decide⟩ ⟨12, 2, 0, 1209584, 353159, 1193, 65536⟩
    (by decide) selected_cut_44072

theorem unmarked_context_11_88289_1209585 : frontier 10 ⟨1209585, by decide⟩
    (prefixCache 11 88289) (prefixPartial 11 88289) = false := by
  decide +kernel

theorem node_context_11_88289_1209585 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209585, by decide⟩ =
    .split (coordinate 11) (![⟨1209533, by decide⟩,⟨1209551, by decide⟩,⟨1209568, by decide⟩,⟨1209584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88289_1209585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88289 ⟨1209585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88289
    ⟨1209585, by decide⟩ (by decide) (![⟨1209533, by decide⟩,⟨1209551, by decide⟩,⟨1209568, by decide⟩,⟨1209584, by decide⟩]) unmarked_context_11_88289_1209585 node_context_11_88289_1209585
  intro a
  fin_cases a
  · exact context_12_353156_1209533
  · exact context_12_353157_1209551
  · exact context_12_353158_1209568
  · exact context_12_353159_1209584

theorem selected_cut_44073 : selected 10 ⟨1209649, by decide⟩
    (prefixPartial 11 88290) = some ⟨11, 2, 0, 1209649, 88290, 3837, 262144⟩ := by
  decide +kernel

theorem context_11_88290_1209649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88290 ⟨1209649, by decide⟩ :=
  accepted_of_selected 11 88290 ⟨1209649, by decide⟩ ⟨11, 2, 0, 1209649, 88290, 3837, 262144⟩
    (by decide) selected_cut_44073

theorem selected_cut_44074 : selected 10 ⟨1209704, by decide⟩
    (prefixPartial 11 88291) = some ⟨11, 2, 0, 1209704, 88291, 3225, 262144⟩ := by
  decide +kernel

theorem context_11_88291_1209704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88291 ⟨1209704, by decide⟩ :=
  accepted_of_selected 11 88291 ⟨1209704, by decide⟩ ⟨11, 2, 0, 1209704, 88291, 3225, 262144⟩
    (by decide) selected_cut_44074

theorem unmarked_context_10_22072_1209705 : frontier 11 ⟨1209705, by decide⟩
    (prefixCache 10 22072) (prefixPartial 10 22072) = false := by
  decide +kernel

theorem node_context_10_22072_1209705 : EJMOriginalGlobalDAGData.nodes 11 ⟨1209705, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1209585, by decide⟩,⟨1209649, by decide⟩,⟨1209704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22072_1209705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22072 ⟨1209705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22072
    ⟨1209705, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1209585, by decide⟩,⟨1209649, by decide⟩,⟨1209704, by decide⟩]) unmarked_context_10_22072_1209705 node_context_10_22072_1209705
  intro a
  fin_cases a
  · exact context_11_88288_907917
  · exact context_11_88289_1209585
  · exact context_11_88290_1209649
  · exact context_11_88291_1209704

theorem selected_cut_44075 : selected 9 ⟨1209724, by decide⟩
    (prefixPartial 12 353168) = some ⟨12, 2, 0, 1209724, 353168, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_353168_1209724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353168 ⟨1209724, by decide⟩ :=
  accepted_of_selected 12 353168 ⟨1209724, by decide⟩ ⟨12, 2, 0, 1209724, 353168, 1117, 65536⟩
    (by decide) selected_cut_44075

theorem selected_cut_44076 : selected 9 ⟨1209740, by decide⟩
    (prefixPartial 12 353169) = some ⟨12, 2, 0, 1209740, 353169, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_353169_1209740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353169 ⟨1209740, by decide⟩ :=
  accepted_of_selected 12 353169 ⟨1209740, by decide⟩ ⟨12, 2, 0, 1209740, 353169, 1069, 65536⟩
    (by decide) selected_cut_44076

theorem selected_cut_44077 : selected 9 ⟨1209763, by decide⟩
    (prefixPartial 12 353170) = some ⟨12, 2, 0, 1209763, 353170, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_353170_1209763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353170 ⟨1209763, by decide⟩ :=
  accepted_of_selected 12 353170 ⟨1209763, by decide⟩ ⟨12, 2, 0, 1209763, 353170, 1261, 65536⟩
    (by decide) selected_cut_44077

theorem selected_cut_44078 : selected 9 ⟨1209779, by decide⟩
    (prefixPartial 12 353171) = some ⟨12, 2, 0, 1209779, 353171, 997, 65536⟩ := by
  decide +kernel

theorem context_12_353171_1209779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353171 ⟨1209779, by decide⟩ :=
  accepted_of_selected 12 353171 ⟨1209779, by decide⟩ ⟨12, 2, 0, 1209779, 353171, 997, 65536⟩
    (by decide) selected_cut_44078

theorem unmarked_context_11_88292_1209780 : frontier 10 ⟨1209780, by decide⟩
    (prefixCache 11 88292) (prefixPartial 11 88292) = false := by
  decide +kernel

theorem node_context_11_88292_1209780 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209780, by decide⟩ =
    .split (coordinate 11) (![⟨1209724, by decide⟩,⟨1209740, by decide⟩,⟨1209763, by decide⟩,⟨1209779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88292_1209780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88292 ⟨1209780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88292
    ⟨1209780, by decide⟩ (by decide) (![⟨1209724, by decide⟩,⟨1209740, by decide⟩,⟨1209763, by decide⟩,⟨1209779, by decide⟩]) unmarked_context_11_88292_1209780 node_context_11_88292_1209780
  intro a
  fin_cases a
  · exact context_12_353168_1209724
  · exact context_12_353169_1209740
  · exact context_12_353170_1209763
  · exact context_12_353171_1209779

theorem selected_cut_44079 : selected 10 ⟨1209814, by decide⟩
    (prefixPartial 11 88293) = some ⟨11, 2, 0, 1209814, 88293, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_88293_1209814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88293 ⟨1209814, by decide⟩ :=
  accepted_of_selected 11 88293 ⟨1209814, by decide⟩ ⟨11, 2, 0, 1209814, 88293, 2309, 262144⟩
    (by decide) selected_cut_44079

theorem selected_cut_44080 : selected 10 ⟨1209882, by decide⟩
    (prefixPartial 11 88294) = some ⟨11, 2, 0, 1209882, 88294, 3433, 262144⟩ := by
  decide +kernel

theorem context_11_88294_1209882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88294 ⟨1209882, by decide⟩ :=
  accepted_of_selected 11 88294 ⟨1209882, by decide⟩ ⟨11, 2, 0, 1209882, 88294, 3433, 262144⟩
    (by decide) selected_cut_44080

theorem selected_cut_44081 : selected 10 ⟨1209940, by decide⟩
    (prefixPartial 11 88295) = some ⟨11, 2, 0, 1209940, 88295, 3165, 262144⟩ := by
  decide +kernel

theorem context_11_88295_1209940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88295 ⟨1209940, by decide⟩ :=
  accepted_of_selected 11 88295 ⟨1209940, by decide⟩ ⟨11, 2, 0, 1209940, 88295, 3165, 262144⟩
    (by decide) selected_cut_44081

theorem unmarked_context_10_22073_1209941 : frontier 11 ⟨1209941, by decide⟩
    (prefixCache 10 22073) (prefixPartial 10 22073) = false := by
  decide +kernel

theorem node_context_10_22073_1209941 : EJMOriginalGlobalDAGData.nodes 11 ⟨1209941, by decide⟩ =
    .split (coordinate 10) (![⟨1209780, by decide⟩,⟨1209814, by decide⟩,⟨1209882, by decide⟩,⟨1209940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22073_1209941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22073 ⟨1209941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22073
    ⟨1209941, by decide⟩ (by decide) (![⟨1209780, by decide⟩,⟨1209814, by decide⟩,⟨1209882, by decide⟩,⟨1209940, by decide⟩]) unmarked_context_10_22073_1209941 node_context_10_22073_1209941
  intro a
  fin_cases a
  · exact context_11_88292_1209780
  · exact context_11_88293_1209814
  · exact context_11_88294_1209882
  · exact context_11_88295_1209940

theorem selected_cut_44082 : selected 10 ⟨1209976, by decide⟩
    (prefixPartial 11 88296) = some ⟨11, 2, 0, 1209976, 88296, 2365, 262144⟩ := by
  decide +kernel

theorem context_11_88296_1209976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88296 ⟨1209976, by decide⟩ :=
  accepted_of_selected 11 88296 ⟨1209976, by decide⟩ ⟨11, 2, 0, 1209976, 88296, 2365, 262144⟩
    (by decide) selected_cut_44082

theorem selected_cut_44083 : selected 10 ⟨1210006, by decide⟩
    (prefixPartial 11 88297) = some ⟨11, 2, 0, 1210006, 88297, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_88297_1210006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88297 ⟨1210006, by decide⟩ :=
  accepted_of_selected 11 88297 ⟨1210006, by decide⟩ ⟨11, 2, 0, 1210006, 88297, 1669, 262144⟩
    (by decide) selected_cut_44083

theorem selected_cut_44084 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88298) = some ⟨11, 1, 0, 1109453, 88298, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88298_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88298 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88298 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88298, 1, 262144⟩
    (by decide) selected_cut_44084

theorem selected_cut_44085 : selected 10 ⟨1210027, by decide⟩
    (prefixPartial 11 88299) = some ⟨11, 2, 0, 1210027, 88299, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_88299_1210027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88299 ⟨1210027, by decide⟩ :=
  accepted_of_selected 11 88299 ⟨1210027, by decide⟩ ⟨11, 2, 0, 1210027, 88299, 1581, 262144⟩
    (by decide) selected_cut_44085

theorem unmarked_context_10_22074_1210028 : frontier 11 ⟨1210028, by decide⟩
    (prefixCache 10 22074) (prefixPartial 10 22074) = false := by
  decide +kernel

theorem node_context_10_22074_1210028 : EJMOriginalGlobalDAGData.nodes 11 ⟨1210028, by decide⟩ =
    .split (coordinate 10) (![⟨1209976, by decide⟩,⟨1210006, by decide⟩,⟨1109453, by decide⟩,⟨1210027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22074_1210028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22074 ⟨1210028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22074
    ⟨1210028, by decide⟩ (by decide) (![⟨1209976, by decide⟩,⟨1210006, by decide⟩,⟨1109453, by decide⟩,⟨1210027, by decide⟩]) unmarked_context_10_22074_1210028 node_context_10_22074_1210028
  intro a
  fin_cases a
  · exact context_11_88296_1209976
  · exact context_11_88297_1210006
  · exact context_11_88298_1109453
  · exact context_11_88299_1210027

theorem selected_cut_44086 : selected 10 ⟨1210073, by decide⟩
    (prefixPartial 11 88300) = some ⟨11, 2, 0, 1210073, 88300, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_88300_1210073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88300 ⟨1210073, by decide⟩ :=
  accepted_of_selected 11 88300 ⟨1210073, by decide⟩ ⟨11, 2, 0, 1210073, 88300, 2385, 262144⟩
    (by decide) selected_cut_44086

theorem selected_cut_44087 : selected 10 ⟨1210134, by decide⟩
    (prefixPartial 11 88301) = some ⟨11, 2, 0, 1210134, 88301, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_88301_1210134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88301 ⟨1210134, by decide⟩ :=
  accepted_of_selected 11 88301 ⟨1210134, by decide⟩ ⟨11, 2, 0, 1210134, 88301, 2929, 262144⟩
    (by decide) selected_cut_44087

theorem selected_cut_44088 : selected 10 ⟨1210175, by decide⟩
    (prefixPartial 11 88302) = some ⟨11, 2, 0, 1210175, 88302, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_88302_1210175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88302 ⟨1210175, by decide⟩ :=
  accepted_of_selected 11 88302 ⟨1210175, by decide⟩ ⟨11, 2, 0, 1210175, 88302, 2117, 262144⟩
    (by decide) selected_cut_44088

theorem selected_cut_44089 : selected 10 ⟨1210209, by decide⟩
    (prefixPartial 11 88303) = some ⟨11, 2, 0, 1210209, 88303, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_88303_1210209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88303 ⟨1210209, by decide⟩ :=
  accepted_of_selected 11 88303 ⟨1210209, by decide⟩ ⟨11, 2, 0, 1210209, 88303, 1293, 262144⟩
    (by decide) selected_cut_44089

theorem unmarked_context_10_22075_1210210 : frontier 11 ⟨1210210, by decide⟩
    (prefixCache 10 22075) (prefixPartial 10 22075) = false := by
  decide +kernel

theorem node_context_10_22075_1210210 : EJMOriginalGlobalDAGData.nodes 11 ⟨1210210, by decide⟩ =
    .split (coordinate 10) (![⟨1210073, by decide⟩,⟨1210134, by decide⟩,⟨1210175, by decide⟩,⟨1210209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22075_1210210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22075 ⟨1210210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22075
    ⟨1210210, by decide⟩ (by decide) (![⟨1210073, by decide⟩,⟨1210134, by decide⟩,⟨1210175, by decide⟩,⟨1210209, by decide⟩]) unmarked_context_10_22075_1210210 node_context_10_22075_1210210
  intro a
  fin_cases a
  · exact context_11_88300_1210073
  · exact context_11_88301_1210134
  · exact context_11_88302_1210175
  · exact context_11_88303_1210209

theorem unmarked_context_9_5518_1210211 : frontier 12 ⟨1210211, by decide⟩
    (prefixCache 9 5518) (prefixPartial 9 5518) = false := by
  decide +kernel

theorem node_context_9_5518_1210211 : EJMOriginalGlobalDAGData.nodes 12 ⟨1210211, by decide⟩ =
    .split (coordinate 9) (![⟨1209705, by decide⟩,⟨1209941, by decide⟩,⟨1210028, by decide⟩,⟨1210210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5518_1210211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5518 ⟨1210211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5518
    ⟨1210211, by decide⟩ (by decide) (![⟨1209705, by decide⟩,⟨1209941, by decide⟩,⟨1210028, by decide⟩,⟨1210210, by decide⟩]) unmarked_context_9_5518_1210211 node_context_9_5518_1210211
  intro a
  fin_cases a
  · exact context_10_22072_1209705
  · exact context_10_22073_1209941
  · exact context_10_22074_1210028
  · exact context_10_22075_1210210

theorem selected_cut_44090 : selected 11 ⟨1210267, by decide⟩
    (prefixPartial 10 22076) = some ⟨10, 2, 0, 1210267, 22076, 3685, 1048576⟩ := by
  decide +kernel

theorem context_10_22076_1210267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22076 ⟨1210267, by decide⟩ :=
  accepted_of_selected 10 22076 ⟨1210267, by decide⟩ ⟨10, 2, 0, 1210267, 22076, 3685, 1048576⟩
    (by decide) selected_cut_44090

theorem selected_cut_44091 : selected 11 ⟨1210330, by decide⟩
    (prefixPartial 10 22077) = some ⟨10, 2, 0, 1210330, 22077, 3501, 1048576⟩ := by
  decide +kernel

theorem context_10_22077_1210330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22077 ⟨1210330, by decide⟩ :=
  accepted_of_selected 10 22077 ⟨1210330, by decide⟩ ⟨10, 2, 0, 1210330, 22077, 3501, 1048576⟩
    (by decide) selected_cut_44091

theorem selected_cut_44092 : selected 11 ⟨1210375, by decide⟩
    (prefixPartial 10 22078) = some ⟨10, 2, 0, 1210375, 22078, 2337, 1048576⟩ := by
  decide +kernel

theorem context_10_22078_1210375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22078 ⟨1210375, by decide⟩ :=
  accepted_of_selected 10 22078 ⟨1210375, by decide⟩ ⟨10, 2, 0, 1210375, 22078, 2337, 1048576⟩
    (by decide) selected_cut_44092

theorem selected_cut_44093 : selected 11 ⟨1210388, by decide⟩
    (prefixPartial 10 22079) = some ⟨10, 2, 0, 1210388, 22079, 441, 1048576⟩ := by
  decide +kernel

theorem context_10_22079_1210388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22079 ⟨1210388, by decide⟩ :=
  accepted_of_selected 10 22079 ⟨1210388, by decide⟩ ⟨10, 2, 0, 1210388, 22079, 441, 1048576⟩
    (by decide) selected_cut_44093

theorem unmarked_context_9_5519_1210389 : frontier 12 ⟨1210389, by decide⟩
    (prefixCache 9 5519) (prefixPartial 9 5519) = false := by
  decide +kernel

theorem node_context_9_5519_1210389 : EJMOriginalGlobalDAGData.nodes 12 ⟨1210389, by decide⟩ =
    .split (coordinate 9) (![⟨1210267, by decide⟩,⟨1210330, by decide⟩,⟨1210375, by decide⟩,⟨1210388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5519_1210389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5519 ⟨1210389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5519
    ⟨1210389, by decide⟩ (by decide) (![⟨1210267, by decide⟩,⟨1210330, by decide⟩,⟨1210375, by decide⟩,⟨1210388, by decide⟩]) unmarked_context_9_5519_1210389 node_context_9_5519_1210389
  intro a
  fin_cases a
  · exact context_10_22076_1210267
  · exact context_10_22077_1210330
  · exact context_10_22078_1210375
  · exact context_10_22079_1210388

theorem unmarked_context_8_1379_1210390 : frontier 13 ⟨1210390, by decide⟩
    (prefixCache 8 1379) (prefixPartial 8 1379) = false := by
  decide +kernel

theorem node_context_8_1379_1210390 : EJMOriginalGlobalDAGData.nodes 13 ⟨1210390, by decide⟩ =
    .split (coordinate 8) (![⟨1208873, by decide⟩,⟨1209512, by decide⟩,⟨1210211, by decide⟩,⟨1210389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1379_1210390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1379 ⟨1210390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1379
    ⟨1210390, by decide⟩ (by decide) (![⟨1208873, by decide⟩,⟨1209512, by decide⟩,⟨1210211, by decide⟩,⟨1210389, by decide⟩]) unmarked_context_8_1379_1210390 node_context_8_1379_1210390
  intro a
  fin_cases a
  · exact context_9_5516_1208873
  · exact context_9_5517_1209512
  · exact context_9_5518_1210211
  · exact context_9_5519_1210389

theorem unmarked_context_7_344_1210391 : frontier 14 ⟨1210391, by decide⟩
    (prefixCache 7 344) (prefixPartial 7 344) = false := by
  decide +kernel

theorem node_context_7_344_1210391 : EJMOriginalGlobalDAGData.nodes 14 ⟨1210391, by decide⟩ =
    .split (coordinate 7) (![⟨1200220, by decide⟩,⟨1203345, by decide⟩,⟨1206852, by decide⟩,⟨1210390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_344_1210391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 344 ⟨1210391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 344
    ⟨1210391, by decide⟩ (by decide) (![⟨1200220, by decide⟩,⟨1203345, by decide⟩,⟨1206852, by decide⟩,⟨1210390, by decide⟩]) unmarked_context_7_344_1210391 node_context_7_344_1210391
  intro a
  fin_cases a
  · exact context_8_1376_1200220
  · exact context_8_1377_1203345
  · exact context_8_1378_1206852
  · exact context_8_1379_1210390

theorem selected_cut_44094 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88320) = some ⟨11, 1, 0, 434745, 88320, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88320_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88320 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88320 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88320, 1, 262144⟩
    (by decide) selected_cut_44094

theorem selected_cut_44095 : selected 10 ⟨1210515, by decide⟩
    (prefixPartial 11 88321) = some ⟨11, 2, 0, 1210515, 88321, 3305, 262144⟩ := by
  decide +kernel

theorem context_11_88321_1210515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88321 ⟨1210515, by decide⟩ :=
  accepted_of_selected 11 88321 ⟨1210515, by decide⟩ ⟨11, 2, 0, 1210515, 88321, 3305, 262144⟩
    (by decide) selected_cut_44095

theorem selected_cut_44096 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353288) = some ⟨12, 1, 0, 448748, 353288, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353288_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353288 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353288 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353288, 1, 65536⟩
    (by decide) selected_cut_44096

theorem selected_cut_44097 : selected 9 ⟨1210588, by decide⟩
    (prefixPartial 12 353289) = some ⟨12, 2, 0, 1210588, 353289, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_353289_1210588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353289 ⟨1210588, by decide⟩ :=
  accepted_of_selected 12 353289 ⟨1210588, by decide⟩ ⟨12, 2, 0, 1210588, 353289, 2905, 65536⟩
    (by decide) selected_cut_44097

theorem selected_cut_44098 : selected 9 ⟨1210660, by decide⟩
    (prefixPartial 12 353290) = some ⟨12, 2, 0, 1210660, 353290, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_353290_1210660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353290 ⟨1210660, by decide⟩ :=
  accepted_of_selected 12 353290 ⟨1210660, by decide⟩ ⟨12, 2, 0, 1210660, 353290, 3289, 65536⟩
    (by decide) selected_cut_44098

theorem selected_cut_44099 : selected 9 ⟨1210759, by decide⟩
    (prefixPartial 12 353291) = some ⟨12, 2, 0, 1210759, 353291, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_353291_1210759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353291 ⟨1210759, by decide⟩ :=
  accepted_of_selected 12 353291 ⟨1210759, by decide⟩ ⟨12, 2, 0, 1210759, 353291, 3809, 65536⟩
    (by decide) selected_cut_44099

theorem unmarked_context_11_88322_1210760 : frontier 10 ⟨1210760, by decide⟩
    (prefixCache 11 88322) (prefixPartial 11 88322) = false := by
  decide +kernel

theorem node_context_11_88322_1210760 : EJMOriginalGlobalDAGData.nodes 10 ⟨1210760, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1210588, by decide⟩,⟨1210660, by decide⟩,⟨1210759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88322_1210760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88322 ⟨1210760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88322
    ⟨1210760, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1210588, by decide⟩,⟨1210660, by decide⟩,⟨1210759, by decide⟩]) unmarked_context_11_88322_1210760 node_context_11_88322_1210760
  intro a
  fin_cases a
  · exact context_12_353288_448748
  · exact context_12_353289_1210588
  · exact context_12_353290_1210660
  · exact context_12_353291_1210759

theorem selected_cut_44100 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353292) = some ⟨12, 1, 0, 448748, 353292, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353292_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353292 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353292 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353292, 1, 65536⟩
    (by decide) selected_cut_44100

theorem selected_cut_44101 : selected 9 ⟨1210801, by decide⟩
    (prefixPartial 12 353293) = some ⟨12, 2, 0, 1210801, 353293, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_353293_1210801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353293 ⟨1210801, by decide⟩ :=
  accepted_of_selected 12 353293 ⟨1210801, by decide⟩ ⟨12, 2, 0, 1210801, 353293, 1401, 65536⟩
    (by decide) selected_cut_44101

theorem selected_cut_44102 : selected 9 ⟨1210874, by decide⟩
    (prefixPartial 12 353294) = some ⟨12, 2, 0, 1210874, 353294, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_353294_1210874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353294 ⟨1210874, by decide⟩ :=
  accepted_of_selected 12 353294 ⟨1210874, by decide⟩ ⟨12, 2, 0, 1210874, 353294, 3285, 65536⟩
    (by decide) selected_cut_44102

theorem selected_cut_44103 : selected 9 ⟨1210940, by decide⟩
    (prefixPartial 12 353295) = some ⟨12, 2, 0, 1210940, 353295, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_353295_1210940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353295 ⟨1210940, by decide⟩ :=
  accepted_of_selected 12 353295 ⟨1210940, by decide⟩ ⟨12, 2, 0, 1210940, 353295, 3193, 65536⟩
    (by decide) selected_cut_44103

theorem unmarked_context_11_88323_1210941 : frontier 10 ⟨1210941, by decide⟩
    (prefixCache 11 88323) (prefixPartial 11 88323) = false := by
  decide +kernel

theorem node_context_11_88323_1210941 : EJMOriginalGlobalDAGData.nodes 10 ⟨1210941, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1210801, by decide⟩,⟨1210874, by decide⟩,⟨1210940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88323_1210941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88323 ⟨1210941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88323
    ⟨1210941, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1210801, by decide⟩,⟨1210874, by decide⟩,⟨1210940, by decide⟩]) unmarked_context_11_88323_1210941 node_context_11_88323_1210941
  intro a
  fin_cases a
  · exact context_12_353292_448748
  · exact context_12_353293_1210801
  · exact context_12_353294_1210874
  · exact context_12_353295_1210940

theorem unmarked_context_10_22080_1210942 : frontier 11 ⟨1210942, by decide⟩
    (prefixCache 10 22080) (prefixPartial 10 22080) = false := by
  decide +kernel

theorem node_context_10_22080_1210942 : EJMOriginalGlobalDAGData.nodes 11 ⟨1210942, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1210515, by decide⟩,⟨1210760, by decide⟩,⟨1210941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22080_1210942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22080 ⟨1210942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22080
    ⟨1210942, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1210515, by decide⟩,⟨1210760, by decide⟩,⟨1210941, by decide⟩]) unmarked_context_10_22080_1210942 node_context_10_22080_1210942
  intro a
  fin_cases a
  · exact context_11_88320_434745
  · exact context_11_88321_1210515
  · exact context_11_88322_1210760
  · exact context_11_88323_1210941

theorem selected_cut_44104 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 353296) = some ⟨12, 1, 0, 435160, 353296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353296_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353296 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 353296 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 353296, 1, 65536⟩
    (by decide) selected_cut_44104

theorem selected_cut_44105 : selected 9 ⟨1210977, by decide⟩
    (prefixPartial 12 353297) = some ⟨12, 2, 0, 1210977, 353297, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_353297_1210977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353297 ⟨1210977, by decide⟩ :=
  accepted_of_selected 12 353297 ⟨1210977, by decide⟩ ⟨12, 2, 0, 1210977, 353297, 2041, 65536⟩
    (by decide) selected_cut_44105

theorem selected_cut_44106 : selected 9 ⟨1211025, by decide⟩
    (prefixPartial 12 353298) = some ⟨12, 2, 0, 1211025, 353298, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_353298_1211025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353298 ⟨1211025, by decide⟩ :=
  accepted_of_selected 12 353298 ⟨1211025, by decide⟩ ⟨12, 2, 0, 1211025, 353298, 2581, 65536⟩
    (by decide) selected_cut_44106

theorem selected_cut_44107 : selected 9 ⟨1211071, by decide⟩
    (prefixPartial 12 353299) = some ⟨12, 2, 0, 1211071, 353299, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_353299_1211071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353299 ⟨1211071, by decide⟩ :=
  accepted_of_selected 12 353299 ⟨1211071, by decide⟩ ⟨12, 2, 0, 1211071, 353299, 2657, 65536⟩
    (by decide) selected_cut_44107

theorem unmarked_context_11_88324_1211072 : frontier 10 ⟨1211072, by decide⟩
    (prefixCache 11 88324) (prefixPartial 11 88324) = false := by
  decide +kernel

theorem node_context_11_88324_1211072 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211072, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1210977, by decide⟩,⟨1211025, by decide⟩,⟨1211071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88324_1211072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88324 ⟨1211072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88324
    ⟨1211072, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1210977, by decide⟩,⟨1211025, by decide⟩,⟨1211071, by decide⟩]) unmarked_context_11_88324_1211072 node_context_11_88324_1211072
  intro a
  fin_cases a
  · exact context_12_353296_435160
  · exact context_12_353297_1210977
  · exact context_12_353298_1211025
  · exact context_12_353299_1211071

theorem selected_cut_44108 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88325) = some ⟨11, 1, 0, 892405, 88325, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88325_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88325 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88325 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88325, 1, 262144⟩
    (by decide) selected_cut_44108

theorem selected_cut_44109 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 353304) = some ⟨12, 1, 0, 449505, 353304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353304_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353304 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 353304 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 353304, 1, 65536⟩
    (by decide) selected_cut_44109

theorem selected_cut_44110 : selected 9 ⟨1211109, by decide⟩
    (prefixPartial 12 353305) = some ⟨12, 2, 0, 1211109, 353305, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_353305_1211109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353305 ⟨1211109, by decide⟩ :=
  accepted_of_selected 12 353305 ⟨1211109, by decide⟩ ⟨12, 2, 0, 1211109, 353305, 2249, 65536⟩
    (by decide) selected_cut_44110

theorem selected_cut_44111 : selected 9 ⟨1211156, by decide⟩
    (prefixPartial 12 353306) = some ⟨12, 2, 0, 1211156, 353306, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_353306_1211156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353306 ⟨1211156, by decide⟩ :=
  accepted_of_selected 12 353306 ⟨1211156, by decide⟩ ⟨12, 2, 0, 1211156, 353306, 2757, 65536⟩
    (by decide) selected_cut_44111

theorem selected_cut_44112 : selected 9 ⟨1211222, by decide⟩
    (prefixPartial 12 353307) = some ⟨12, 2, 0, 1211222, 353307, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_353307_1211222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353307 ⟨1211222, by decide⟩ :=
  accepted_of_selected 12 353307 ⟨1211222, by decide⟩ ⟨12, 2, 0, 1211222, 353307, 3181, 65536⟩
    (by decide) selected_cut_44112

theorem unmarked_context_11_88326_1211223 : frontier 10 ⟨1211223, by decide⟩
    (prefixCache 11 88326) (prefixPartial 11 88326) = false := by
  decide +kernel

theorem node_context_11_88326_1211223 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211223, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨1211109, by decide⟩,⟨1211156, by decide⟩,⟨1211222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88326_1211223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88326 ⟨1211223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88326
    ⟨1211223, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨1211109, by decide⟩,⟨1211156, by decide⟩,⟨1211222, by decide⟩]) unmarked_context_11_88326_1211223 node_context_11_88326_1211223
  intro a
  fin_cases a
  · exact context_12_353304_449505
  · exact context_12_353305_1211109
  · exact context_12_353306_1211156
  · exact context_12_353307_1211222

theorem selected_cut_44113 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 353308) = some ⟨12, 1, 0, 539296, 353308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353308_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353308 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 353308 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 353308, 1, 65536⟩
    (by decide) selected_cut_44113

theorem selected_cut_44114 : selected 9 ⟨1211258, by decide⟩
    (prefixPartial 12 353309) = some ⟨12, 2, 0, 1211258, 353309, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_353309_1211258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353309 ⟨1211258, by decide⟩ :=
  accepted_of_selected 12 353309 ⟨1211258, by decide⟩ ⟨12, 2, 0, 1211258, 353309, 2081, 65536⟩
    (by decide) selected_cut_44114

theorem selected_cut_44115 : selected 9 ⟨1211314, by decide⟩
    (prefixPartial 12 353310) = some ⟨12, 2, 0, 1211314, 353310, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_353310_1211314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353310 ⟨1211314, by decide⟩ :=
  accepted_of_selected 12 353310 ⟨1211314, by decide⟩ ⟨12, 2, 0, 1211314, 353310, 2845, 65536⟩
    (by decide) selected_cut_44115

theorem selected_cut_44116 : selected 9 ⟨1211360, by decide⟩
    (prefixPartial 12 353311) = some ⟨12, 2, 0, 1211360, 353311, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_353311_1211360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353311 ⟨1211360, by decide⟩ :=
  accepted_of_selected 12 353311 ⟨1211360, by decide⟩ ⟨12, 2, 0, 1211360, 353311, 2789, 65536⟩
    (by decide) selected_cut_44116

theorem unmarked_context_11_88327_1211361 : frontier 10 ⟨1211361, by decide⟩
    (prefixCache 11 88327) (prefixPartial 11 88327) = false := by
  decide +kernel

theorem node_context_11_88327_1211361 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211361, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨1211258, by decide⟩,⟨1211314, by decide⟩,⟨1211360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88327_1211361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88327 ⟨1211361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88327
    ⟨1211361, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨1211258, by decide⟩,⟨1211314, by decide⟩,⟨1211360, by decide⟩]) unmarked_context_11_88327_1211361 node_context_11_88327_1211361
  intro a
  fin_cases a
  · exact context_12_353308_539296
  · exact context_12_353309_1211258
  · exact context_12_353310_1211314
  · exact context_12_353311_1211360

theorem unmarked_context_10_22081_1211362 : frontier 11 ⟨1211362, by decide⟩
    (prefixCache 10 22081) (prefixPartial 10 22081) = false := by
  decide +kernel

theorem node_context_10_22081_1211362 : EJMOriginalGlobalDAGData.nodes 11 ⟨1211362, by decide⟩ =
    .split (coordinate 10) (![⟨1211072, by decide⟩,⟨892405, by decide⟩,⟨1211223, by decide⟩,⟨1211361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22081_1211362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22081 ⟨1211362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22081
    ⟨1211362, by decide⟩ (by decide) (![⟨1211072, by decide⟩,⟨892405, by decide⟩,⟨1211223, by decide⟩,⟨1211361, by decide⟩]) unmarked_context_10_22081_1211362 node_context_10_22081_1211362
  intro a
  fin_cases a
  · exact context_11_88324_1211072
  · exact context_11_88325_892405
  · exact context_11_88326_1211223
  · exact context_11_88327_1211361

theorem selected_cut_44117 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 353312) = some ⟨12, 1, 0, 985390, 353312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353312_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353312 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 353312 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 353312, 1, 65536⟩
    (by decide) selected_cut_44117

theorem selected_cut_44118 : selected 9 ⟨1211404, by decide⟩
    (prefixPartial 12 353313) = some ⟨12, 2, 0, 1211404, 353313, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_353313_1211404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353313 ⟨1211404, by decide⟩ :=
  accepted_of_selected 12 353313 ⟨1211404, by decide⟩ ⟨12, 2, 0, 1211404, 353313, 2281, 65536⟩
    (by decide) selected_cut_44118

theorem selected_cut_44119 : selected 9 ⟨1211455, by decide⟩
    (prefixPartial 12 353314) = some ⟨12, 2, 0, 1211455, 353314, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_353314_1211455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353314 ⟨1211455, by decide⟩ :=
  accepted_of_selected 12 353314 ⟨1211455, by decide⟩ ⟨12, 2, 0, 1211455, 353314, 2701, 65536⟩
    (by decide) selected_cut_44119

theorem selected_cut_44120 : selected 9 ⟨1211514, by decide⟩
    (prefixPartial 12 353315) = some ⟨12, 2, 0, 1211514, 353315, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_353315_1211514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353315 ⟨1211514, by decide⟩ :=
  accepted_of_selected 12 353315 ⟨1211514, by decide⟩ ⟨12, 2, 0, 1211514, 353315, 2981, 65536⟩
    (by decide) selected_cut_44120

theorem unmarked_context_11_88328_1211515 : frontier 10 ⟨1211515, by decide⟩
    (prefixCache 11 88328) (prefixPartial 11 88328) = false := by
  decide +kernel

theorem node_context_11_88328_1211515 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211515, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1211404, by decide⟩,⟨1211455, by decide⟩,⟨1211514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88328_1211515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88328 ⟨1211515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88328
    ⟨1211515, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1211404, by decide⟩,⟨1211455, by decide⟩,⟨1211514, by decide⟩]) unmarked_context_11_88328_1211515 node_context_11_88328_1211515
  intro a
  fin_cases a
  · exact context_12_353312_985390
  · exact context_12_353313_1211404
  · exact context_12_353314_1211455
  · exact context_12_353315_1211514

theorem selected_cut_44121 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 353316) = some ⟨12, 1, 0, 1197509, 353316, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353316_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353316 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 353316 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 353316, 1, 65536⟩
    (by decide) selected_cut_44121

theorem selected_cut_44122 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 353317) = some ⟨12, 1, 0, 719134, 353317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353317_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353317 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 353317 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 353317, 1, 65536⟩
    (by decide) selected_cut_44122

theorem selected_cut_44123 : selected 9 ⟨1211553, by decide⟩
    (prefixPartial 12 353318) = some ⟨12, 2, 0, 1211553, 353318, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_353318_1211553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353318 ⟨1211553, by decide⟩ :=
  accepted_of_selected 12 353318 ⟨1211553, by decide⟩ ⟨12, 2, 0, 1211553, 353318, 2249, 65536⟩
    (by decide) selected_cut_44123

theorem selected_cut_44124 : selected 9 ⟨1211598, by decide⟩
    (prefixPartial 12 353319) = some ⟨12, 2, 0, 1211598, 353319, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_353319_1211598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353319 ⟨1211598, by decide⟩ :=
  accepted_of_selected 12 353319 ⟨1211598, by decide⟩ ⟨12, 2, 0, 1211598, 353319, 2669, 65536⟩
    (by decide) selected_cut_44124

theorem unmarked_context_11_88329_1211599 : frontier 10 ⟨1211599, by decide⟩
    (prefixCache 11 88329) (prefixPartial 11 88329) = false := by
  decide +kernel

theorem node_context_11_88329_1211599 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211599, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1211553, by decide⟩,⟨1211598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88329_1211599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88329 ⟨1211599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88329
    ⟨1211599, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1211553, by decide⟩,⟨1211598, by decide⟩]) unmarked_context_11_88329_1211599 node_context_11_88329_1211599
  intro a
  fin_cases a
  · exact context_12_353316_1197509
  · exact context_12_353317_719134
  · exact context_12_353318_1211553
  · exact context_12_353319_1211598

theorem selected_cut_44125 : selected 9 ⟨1211646, by decide⟩
    (prefixPartial 12 353320) = some ⟨12, 2, 0, 1211646, 353320, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_353320_1211646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353320 ⟨1211646, by decide⟩ :=
  accepted_of_selected 12 353320 ⟨1211646, by decide⟩ ⟨12, 2, 0, 1211646, 353320, 2613, 65536⟩
    (by decide) selected_cut_44125

theorem selected_cut_44126 : selected 9 ⟨1211681, by decide⟩
    (prefixPartial 12 353321) = some ⟨12, 2, 0, 1211681, 353321, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_353321_1211681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353321 ⟨1211681, by decide⟩ :=
  accepted_of_selected 12 353321 ⟨1211681, by decide⟩ ⟨12, 2, 0, 1211681, 353321, 2281, 65536⟩
    (by decide) selected_cut_44126

theorem selected_cut_44127 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 353322) = some ⟨12, 1, 0, 1113261, 353322, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353322_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353322 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 353322 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 353322, 1, 65536⟩
    (by decide) selected_cut_44127

theorem selected_cut_44128 : selected 9 ⟨1211739, by decide⟩
    (prefixPartial 12 353323) = some ⟨12, 2, 0, 1211739, 353323, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_353323_1211739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353323 ⟨1211739, by decide⟩ :=
  accepted_of_selected 12 353323 ⟨1211739, by decide⟩ ⟨12, 2, 0, 1211739, 353323, 3213, 65536⟩
    (by decide) selected_cut_44128

theorem unmarked_context_11_88330_1211740 : frontier 10 ⟨1211740, by decide⟩
    (prefixCache 11 88330) (prefixPartial 11 88330) = false := by
  decide +kernel

theorem node_context_11_88330_1211740 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211740, by decide⟩ =
    .split (coordinate 11) (![⟨1211646, by decide⟩,⟨1211681, by decide⟩,⟨1113261, by decide⟩,⟨1211739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88330_1211740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88330 ⟨1211740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88330
    ⟨1211740, by decide⟩ (by decide) (![⟨1211646, by decide⟩,⟨1211681, by decide⟩,⟨1113261, by decide⟩,⟨1211739, by decide⟩]) unmarked_context_11_88330_1211740 node_context_11_88330_1211740
  intro a
  fin_cases a
  · exact context_12_353320_1211646
  · exact context_12_353321_1211681
  · exact context_12_353322_1113261
  · exact context_12_353323_1211739

theorem selected_cut_44129 : selected 9 ⟨1211786, by decide⟩
    (prefixPartial 12 353324) = some ⟨12, 2, 0, 1211786, 353324, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_353324_1211786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353324 ⟨1211786, by decide⟩ :=
  accepted_of_selected 12 353324 ⟨1211786, by decide⟩ ⟨12, 2, 0, 1211786, 353324, 2553, 65536⟩
    (by decide) selected_cut_44129

theorem selected_cut_44130 : selected 9 ⟨1211816, by decide⟩
    (prefixPartial 12 353325) = some ⟨12, 2, 0, 1211816, 353325, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_353325_1211816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353325 ⟨1211816, by decide⟩ :=
  accepted_of_selected 12 353325 ⟨1211816, by decide⟩ ⟨12, 2, 0, 1211816, 353325, 2193, 65536⟩
    (by decide) selected_cut_44130

theorem selected_cut_44131 : selected 9 ⟨1211864, by decide⟩
    (prefixPartial 12 353326) = some ⟨12, 2, 0, 1211864, 353326, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_353326_1211864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353326 ⟨1211864, by decide⟩ :=
  accepted_of_selected 12 353326 ⟨1211864, by decide⟩ ⟨12, 2, 0, 1211864, 353326, 2693, 65536⟩
    (by decide) selected_cut_44131

theorem selected_cut_44132 : selected 9 ⟨1211912, by decide⟩
    (prefixPartial 12 353327) = some ⟨12, 2, 0, 1211912, 353327, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_353327_1211912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353327 ⟨1211912, by decide⟩ :=
  accepted_of_selected 12 353327 ⟨1211912, by decide⟩ ⟨12, 2, 0, 1211912, 353327, 2861, 65536⟩
    (by decide) selected_cut_44132

theorem unmarked_context_11_88331_1211913 : frontier 10 ⟨1211913, by decide⟩
    (prefixCache 11 88331) (prefixPartial 11 88331) = false := by
  decide +kernel

theorem node_context_11_88331_1211913 : EJMOriginalGlobalDAGData.nodes 10 ⟨1211913, by decide⟩ =
    .split (coordinate 11) (![⟨1211786, by decide⟩,⟨1211816, by decide⟩,⟨1211864, by decide⟩,⟨1211912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88331_1211913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88331 ⟨1211913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88331
    ⟨1211913, by decide⟩ (by decide) (![⟨1211786, by decide⟩,⟨1211816, by decide⟩,⟨1211864, by decide⟩,⟨1211912, by decide⟩]) unmarked_context_11_88331_1211913 node_context_11_88331_1211913
  intro a
  fin_cases a
  · exact context_12_353324_1211786
  · exact context_12_353325_1211816
  · exact context_12_353326_1211864
  · exact context_12_353327_1211912

theorem unmarked_context_10_22082_1211914 : frontier 11 ⟨1211914, by decide⟩
    (prefixCache 10 22082) (prefixPartial 10 22082) = false := by
  decide +kernel

theorem node_context_10_22082_1211914 : EJMOriginalGlobalDAGData.nodes 11 ⟨1211914, by decide⟩ =
    .split (coordinate 10) (![⟨1211515, by decide⟩,⟨1211599, by decide⟩,⟨1211740, by decide⟩,⟨1211913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22082_1211914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22082 ⟨1211914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22082
    ⟨1211914, by decide⟩ (by decide) (![⟨1211515, by decide⟩,⟨1211599, by decide⟩,⟨1211740, by decide⟩,⟨1211913, by decide⟩]) unmarked_context_10_22082_1211914 node_context_10_22082_1211914
  intro a
  fin_cases a
  · exact context_11_88328_1211515
  · exact context_11_88329_1211599
  · exact context_11_88330_1211740
  · exact context_11_88331_1211913

theorem selected_cut_44133 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 353328) = some ⟨12, 1, 0, 985390, 353328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353328_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353328 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 353328 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 353328, 1, 65536⟩
    (by decide) selected_cut_44133

theorem selected_cut_44134 : selected 9 ⟨1211946, by decide⟩
    (prefixPartial 12 353329) = some ⟨12, 2, 0, 1211946, 353329, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_353329_1211946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353329 ⟨1211946, by decide⟩ :=
  accepted_of_selected 12 353329 ⟨1211946, by decide⟩ ⟨12, 2, 0, 1211946, 353329, 1969, 65536⟩
    (by decide) selected_cut_44134

theorem selected_cut_44135 : selected 9 ⟨1211994, by decide⟩
    (prefixPartial 12 353330) = some ⟨12, 2, 0, 1211994, 353330, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_353330_1211994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353330 ⟨1211994, by decide⟩ :=
  accepted_of_selected 12 353330 ⟨1211994, by decide⟩ ⟨12, 2, 0, 1211994, 353330, 2489, 65536⟩
    (by decide) selected_cut_44135

theorem selected_cut_44136 : selected 9 ⟨1212037, by decide⟩
    (prefixPartial 12 353331) = some ⟨12, 2, 0, 1212037, 353331, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_353331_1212037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353331 ⟨1212037, by decide⟩ :=
  accepted_of_selected 12 353331 ⟨1212037, by decide⟩ ⟨12, 2, 0, 1212037, 353331, 2513, 65536⟩
    (by decide) selected_cut_44136

theorem unmarked_context_11_88332_1212038 : frontier 10 ⟨1212038, by decide⟩
    (prefixCache 11 88332) (prefixPartial 11 88332) = false := by
  decide +kernel

theorem node_context_11_88332_1212038 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212038, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1211946, by decide⟩,⟨1211994, by decide⟩,⟨1212037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88332_1212038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88332 ⟨1212038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88332
    ⟨1212038, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1211946, by decide⟩,⟨1211994, by decide⟩,⟨1212037, by decide⟩]) unmarked_context_11_88332_1212038 node_context_11_88332_1212038
  intro a
  fin_cases a
  · exact context_12_353328_985390
  · exact context_12_353329_1211946
  · exact context_12_353330_1211994
  · exact context_12_353331_1212037

theorem selected_cut_44137 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 353332) = some ⟨12, 1, 0, 1197509, 353332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353332_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353332 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 353332 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 353332, 1, 65536⟩
    (by decide) selected_cut_44137

theorem selected_cut_44138 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 353333) = some ⟨12, 1, 0, 719134, 353333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353333_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353333 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 353333 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 353333, 1, 65536⟩
    (by decide) selected_cut_44138

theorem selected_cut_44139 : selected 9 ⟨1212076, by decide⟩
    (prefixPartial 12 353334) = some ⟨12, 2, 0, 1212076, 353334, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_353334_1212076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353334 ⟨1212076, by decide⟩ :=
  accepted_of_selected 12 353334 ⟨1212076, by decide⟩ ⟨12, 2, 0, 1212076, 353334, 2185, 65536⟩
    (by decide) selected_cut_44139

theorem selected_cut_44140 : selected 9 ⟨1212114, by decide⟩
    (prefixPartial 12 353335) = some ⟨12, 2, 0, 1212114, 353335, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_353335_1212114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353335 ⟨1212114, by decide⟩ :=
  accepted_of_selected 12 353335 ⟨1212114, by decide⟩ ⟨12, 2, 0, 1212114, 353335, 2229, 65536⟩
    (by decide) selected_cut_44140

theorem unmarked_context_11_88333_1212115 : frontier 10 ⟨1212115, by decide⟩
    (prefixCache 11 88333) (prefixPartial 11 88333) = false := by
  decide +kernel

theorem node_context_11_88333_1212115 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212115, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1212076, by decide⟩,⟨1212114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88333_1212115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88333 ⟨1212115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88333
    ⟨1212115, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1212076, by decide⟩,⟨1212114, by decide⟩]) unmarked_context_11_88333_1212115 node_context_11_88333_1212115
  intro a
  fin_cases a
  · exact context_12_353332_1197509
  · exact context_12_353333_719134
  · exact context_12_353334_1212076
  · exact context_12_353335_1212114

theorem selected_cut_44141 : selected 9 ⟨1212165, by decide⟩
    (prefixPartial 12 353336) = some ⟨12, 2, 0, 1212165, 353336, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_353336_1212165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353336 ⟨1212165, by decide⟩ :=
  accepted_of_selected 12 353336 ⟨1212165, by decide⟩ ⟨12, 2, 0, 1212165, 353336, 2481, 65536⟩
    (by decide) selected_cut_44141

theorem selected_cut_44142 : selected 9 ⟨1212201, by decide⟩
    (prefixPartial 12 353337) = some ⟨12, 2, 0, 1212201, 353337, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_353337_1212201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353337 ⟨1212201, by decide⟩ :=
  accepted_of_selected 12 353337 ⟨1212201, by decide⟩ ⟨12, 2, 0, 1212201, 353337, 2057, 65536⟩
    (by decide) selected_cut_44142

theorem selected_cut_44143 : selected 9 ⟨1212247, by decide⟩
    (prefixPartial 12 353338) = some ⟨12, 2, 0, 1212247, 353338, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_353338_1212247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353338 ⟨1212247, by decide⟩ :=
  accepted_of_selected 12 353338 ⟨1212247, by decide⟩ ⟨12, 2, 0, 1212247, 353338, 2537, 65536⟩
    (by decide) selected_cut_44143

theorem selected_cut_44144 : selected 9 ⟨1212308, by decide⟩
    (prefixPartial 12 353339) = some ⟨12, 2, 0, 1212308, 353339, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_353339_1212308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353339 ⟨1212308, by decide⟩ :=
  accepted_of_selected 12 353339 ⟨1212308, by decide⟩ ⟨12, 2, 0, 1212308, 353339, 2733, 65536⟩
    (by decide) selected_cut_44144

theorem unmarked_context_11_88334_1212309 : frontier 10 ⟨1212309, by decide⟩
    (prefixCache 11 88334) (prefixPartial 11 88334) = false := by
  decide +kernel

theorem node_context_11_88334_1212309 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212309, by decide⟩ =
    .split (coordinate 11) (![⟨1212165, by decide⟩,⟨1212201, by decide⟩,⟨1212247, by decide⟩,⟨1212308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88334_1212309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88334 ⟨1212309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88334
    ⟨1212309, by decide⟩ (by decide) (![⟨1212165, by decide⟩,⟨1212201, by decide⟩,⟨1212247, by decide⟩,⟨1212308, by decide⟩]) unmarked_context_11_88334_1212309 node_context_11_88334_1212309
  intro a
  fin_cases a
  · exact context_12_353336_1212165
  · exact context_12_353337_1212201
  · exact context_12_353338_1212247
  · exact context_12_353339_1212308

theorem selected_cut_44145 : selected 9 ⟨1212346, by decide⟩
    (prefixPartial 12 353340) = some ⟨12, 2, 0, 1212346, 353340, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_353340_1212346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353340 ⟨1212346, by decide⟩ :=
  accepted_of_selected 12 353340 ⟨1212346, by decide⟩ ⟨12, 2, 0, 1212346, 353340, 2081, 65536⟩
    (by decide) selected_cut_44145

theorem selected_cut_44146 : selected 9 ⟨1212379, by decide⟩
    (prefixPartial 12 353341) = some ⟨12, 2, 0, 1212379, 353341, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_353341_1212379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353341 ⟨1212379, by decide⟩ :=
  accepted_of_selected 12 353341 ⟨1212379, by decide⟩ ⟨12, 2, 0, 1212379, 353341, 1757, 65536⟩
    (by decide) selected_cut_44146

theorem selected_cut_44147 : selected 9 ⟨1212421, by decide⟩
    (prefixPartial 12 353342) = some ⟨12, 2, 0, 1212421, 353342, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_353342_1212421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353342 ⟨1212421, by decide⟩ :=
  accepted_of_selected 12 353342 ⟨1212421, by decide⟩ ⟨12, 2, 0, 1212421, 353342, 2297, 65536⟩
    (by decide) selected_cut_44147

theorem selected_cut_44148 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 353343) = some ⟨12, 1, 0, 1116246, 353343, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353343_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353343 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 353343 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 353343, 1, 65536⟩
    (by decide) selected_cut_44148

theorem unmarked_context_11_88335_1212422 : frontier 10 ⟨1212422, by decide⟩
    (prefixCache 11 88335) (prefixPartial 11 88335) = false := by
  decide +kernel

theorem node_context_11_88335_1212422 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212422, by decide⟩ =
    .split (coordinate 11) (![⟨1212346, by decide⟩,⟨1212379, by decide⟩,⟨1212421, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88335_1212422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88335 ⟨1212422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88335
    ⟨1212422, by decide⟩ (by decide) (![⟨1212346, by decide⟩,⟨1212379, by decide⟩,⟨1212421, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_88335_1212422 node_context_11_88335_1212422
  intro a
  fin_cases a
  · exact context_12_353340_1212346
  · exact context_12_353341_1212379
  · exact context_12_353342_1212421
  · exact context_12_353343_1116246

theorem unmarked_context_10_22083_1212423 : frontier 11 ⟨1212423, by decide⟩
    (prefixCache 10 22083) (prefixPartial 10 22083) = false := by
  decide +kernel

theorem node_context_10_22083_1212423 : EJMOriginalGlobalDAGData.nodes 11 ⟨1212423, by decide⟩ =
    .split (coordinate 10) (![⟨1212038, by decide⟩,⟨1212115, by decide⟩,⟨1212309, by decide⟩,⟨1212422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22083_1212423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22083 ⟨1212423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22083
    ⟨1212423, by decide⟩ (by decide) (![⟨1212038, by decide⟩,⟨1212115, by decide⟩,⟨1212309, by decide⟩,⟨1212422, by decide⟩]) unmarked_context_10_22083_1212423 node_context_10_22083_1212423
  intro a
  fin_cases a
  · exact context_11_88332_1212038
  · exact context_11_88333_1212115
  · exact context_11_88334_1212309
  · exact context_11_88335_1212422

theorem unmarked_context_9_5520_1212424 : frontier 12 ⟨1212424, by decide⟩
    (prefixCache 9 5520) (prefixPartial 9 5520) = false := by
  decide +kernel

theorem node_context_9_5520_1212424 : EJMOriginalGlobalDAGData.nodes 12 ⟨1212424, by decide⟩ =
    .split (coordinate 9) (![⟨1210942, by decide⟩,⟨1211362, by decide⟩,⟨1211914, by decide⟩,⟨1212423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5520_1212424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5520 ⟨1212424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5520
    ⟨1212424, by decide⟩ (by decide) (![⟨1210942, by decide⟩,⟨1211362, by decide⟩,⟨1211914, by decide⟩,⟨1212423, by decide⟩]) unmarked_context_9_5520_1212424 node_context_9_5520_1212424
  intro a
  fin_cases a
  · exact context_10_22080_1210942
  · exact context_10_22081_1211362
  · exact context_10_22082_1211914
  · exact context_10_22083_1212423

theorem selected_cut_44149 : selected 10 ⟨1212427, by decide⟩
    (prefixPartial 11 88336) = some ⟨11, 2, 0, 1212427, 88336, 5, 262144⟩ := by
  decide +kernel

theorem context_11_88336_1212427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88336 ⟨1212427, by decide⟩ :=
  accepted_of_selected 11 88336 ⟨1212427, by decide⟩ ⟨11, 2, 0, 1212427, 88336, 5, 262144⟩
    (by decide) selected_cut_44149

theorem selected_cut_44150 : selected 9 ⟨1212448, by decide⟩
    (prefixPartial 12 353348) = some ⟨12, 2, 0, 1212448, 353348, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_353348_1212448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353348 ⟨1212448, by decide⟩ :=
  accepted_of_selected 12 353348 ⟨1212448, by decide⟩ ⟨12, 2, 0, 1212448, 353348, 1365, 65536⟩
    (by decide) selected_cut_44150

theorem selected_cut_44151 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353349) = some ⟨12, 1, 0, 896706, 353349, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353349_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353349 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353349 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353349, 1, 65536⟩
    (by decide) selected_cut_44151

theorem selected_cut_44152 : selected 9 ⟨1212471, by decide⟩
    (prefixPartial 12 353350) = some ⟨12, 2, 0, 1212471, 353350, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_353350_1212471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353350 ⟨1212471, by decide⟩ :=
  accepted_of_selected 12 353350 ⟨1212471, by decide⟩ ⟨12, 2, 0, 1212471, 353350, 1529, 65536⟩
    (by decide) selected_cut_44152

theorem selected_cut_44153 : selected 9 ⟨1212495, by decide⟩
    (prefixPartial 12 353351) = some ⟨12, 2, 0, 1212495, 353351, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_353351_1212495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353351 ⟨1212495, by decide⟩ :=
  accepted_of_selected 12 353351 ⟨1212495, by decide⟩ ⟨12, 2, 0, 1212495, 353351, 1553, 65536⟩
    (by decide) selected_cut_44153

theorem unmarked_context_11_88337_1212496 : frontier 10 ⟨1212496, by decide⟩
    (prefixCache 11 88337) (prefixPartial 11 88337) = false := by
  decide +kernel

theorem node_context_11_88337_1212496 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212496, by decide⟩ =
    .split (coordinate 11) (![⟨1212448, by decide⟩,⟨896706, by decide⟩,⟨1212471, by decide⟩,⟨1212495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88337_1212496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88337 ⟨1212496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88337
    ⟨1212496, by decide⟩ (by decide) (![⟨1212448, by decide⟩,⟨896706, by decide⟩,⟨1212471, by decide⟩,⟨1212495, by decide⟩]) unmarked_context_11_88337_1212496 node_context_11_88337_1212496
  intro a
  fin_cases a
  · exact context_12_353348_1212448
  · exact context_12_353349_896706
  · exact context_12_353350_1212471
  · exact context_12_353351_1212495

theorem selected_cut_44154 : selected 9 ⟨1212528, by decide⟩
    (prefixPartial 12 353352) = some ⟨12, 2, 0, 1212528, 353352, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_353352_1212528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353352 ⟨1212528, by decide⟩ :=
  accepted_of_selected 12 353352 ⟨1212528, by decide⟩ ⟨12, 2, 0, 1212528, 353352, 1761, 65536⟩
    (by decide) selected_cut_44154

theorem selected_cut_44155 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353353) = some ⟨12, 1, 0, 896706, 353353, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353353_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353353 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353353 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353353, 1, 65536⟩
    (by decide) selected_cut_44155

theorem selected_cut_44156 : selected 9 ⟨1212563, by decide⟩
    (prefixPartial 12 353354) = some ⟨12, 2, 0, 1212563, 353354, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_353354_1212563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353354 ⟨1212563, by decide⟩ :=
  accepted_of_selected 12 353354 ⟨1212563, by decide⟩ ⟨12, 2, 0, 1212563, 353354, 1981, 65536⟩
    (by decide) selected_cut_44156

theorem selected_cut_44157 : selected 9 ⟨1212608, by decide⟩
    (prefixPartial 12 353355) = some ⟨12, 2, 0, 1212608, 353355, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_353355_1212608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353355 ⟨1212608, by decide⟩ :=
  accepted_of_selected 12 353355 ⟨1212608, by decide⟩ ⟨12, 2, 0, 1212608, 353355, 2101, 65536⟩
    (by decide) selected_cut_44157

theorem unmarked_context_11_88338_1212609 : frontier 10 ⟨1212609, by decide⟩
    (prefixCache 11 88338) (prefixPartial 11 88338) = false := by
  decide +kernel

theorem node_context_11_88338_1212609 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212609, by decide⟩ =
    .split (coordinate 11) (![⟨1212528, by decide⟩,⟨896706, by decide⟩,⟨1212563, by decide⟩,⟨1212608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88338_1212609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88338 ⟨1212609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88338
    ⟨1212609, by decide⟩ (by decide) (![⟨1212528, by decide⟩,⟨896706, by decide⟩,⟨1212563, by decide⟩,⟨1212608, by decide⟩]) unmarked_context_11_88338_1212609 node_context_11_88338_1212609
  intro a
  fin_cases a
  · exact context_12_353352_1212528
  · exact context_12_353353_896706
  · exact context_12_353354_1212563
  · exact context_12_353355_1212608

theorem selected_cut_44158 : selected 9 ⟨1212634, by decide⟩
    (prefixPartial 12 353356) = some ⟨12, 2, 0, 1212634, 353356, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_353356_1212634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353356 ⟨1212634, by decide⟩ :=
  accepted_of_selected 12 353356 ⟨1212634, by decide⟩ ⟨12, 2, 0, 1212634, 353356, 1597, 65536⟩
    (by decide) selected_cut_44158

theorem selected_cut_44159 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353357) = some ⟨12, 1, 0, 896706, 353357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353357_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353357 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353357 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353357, 1, 65536⟩
    (by decide) selected_cut_44159

theorem selected_cut_44160 : selected 9 ⟨1212663, by decide⟩
    (prefixPartial 12 353358) = some ⟨12, 2, 0, 1212663, 353358, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_353358_1212663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353358 ⟨1212663, by decide⟩ :=
  accepted_of_selected 12 353358 ⟨1212663, by decide⟩ ⟨12, 2, 0, 1212663, 353358, 1817, 65536⟩
    (by decide) selected_cut_44160

theorem selected_cut_44161 : selected 9 ⟨1212697, by decide⟩
    (prefixPartial 12 353359) = some ⟨12, 2, 0, 1212697, 353359, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_353359_1212697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353359 ⟨1212697, by decide⟩ :=
  accepted_of_selected 12 353359 ⟨1212697, by decide⟩ ⟨12, 2, 0, 1212697, 353359, 1829, 65536⟩
    (by decide) selected_cut_44161

theorem unmarked_context_11_88339_1212698 : frontier 10 ⟨1212698, by decide⟩
    (prefixCache 11 88339) (prefixPartial 11 88339) = false := by
  decide +kernel

theorem node_context_11_88339_1212698 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212698, by decide⟩ =
    .split (coordinate 11) (![⟨1212634, by decide⟩,⟨896706, by decide⟩,⟨1212663, by decide⟩,⟨1212697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88339_1212698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88339 ⟨1212698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88339
    ⟨1212698, by decide⟩ (by decide) (![⟨1212634, by decide⟩,⟨896706, by decide⟩,⟨1212663, by decide⟩,⟨1212697, by decide⟩]) unmarked_context_11_88339_1212698 node_context_11_88339_1212698
  intro a
  fin_cases a
  · exact context_12_353356_1212634
  · exact context_12_353357_896706
  · exact context_12_353358_1212663
  · exact context_12_353359_1212697

theorem unmarked_context_10_22084_1212699 : frontier 11 ⟨1212699, by decide⟩
    (prefixCache 10 22084) (prefixPartial 10 22084) = false := by
  decide +kernel

theorem node_context_10_22084_1212699 : EJMOriginalGlobalDAGData.nodes 11 ⟨1212699, by decide⟩ =
    .split (coordinate 10) (![⟨1212427, by decide⟩,⟨1212496, by decide⟩,⟨1212609, by decide⟩,⟨1212698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22084_1212699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22084 ⟨1212699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22084
    ⟨1212699, by decide⟩ (by decide) (![⟨1212427, by decide⟩,⟨1212496, by decide⟩,⟨1212609, by decide⟩,⟨1212698, by decide⟩]) unmarked_context_10_22084_1212699 node_context_10_22084_1212699
  intro a
  fin_cases a
  · exact context_11_88336_1212427
  · exact context_11_88337_1212496
  · exact context_11_88338_1212609
  · exact context_11_88339_1212698

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
