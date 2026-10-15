/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover469
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_45124 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88975) = some ⟨11, 1, 0, 977886, 88975, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88975_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88975 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88975 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88975, 1, 262144⟩
    (by decide) selected_cut_45124

theorem unmarked_context_10_22243_1246635 : frontier 11 ⟨1246635, by decide⟩
    (prefixCache 10 22243) (prefixPartial 10 22243) = false := by
  decide +kernel

theorem node_context_10_22243_1246635 : EJMOriginalGlobalDAGData.nodes 11 ⟨1246635, by decide⟩ =
    .split (coordinate 10) (![⟨1246381, by decide⟩,⟨1246510, by decide⟩,⟨1246634, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22243_1246635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22243 ⟨1246635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22243
    ⟨1246635, by decide⟩ (by decide) (![⟨1246381, by decide⟩,⟨1246510, by decide⟩,⟨1246634, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22243_1246635 node_context_10_22243_1246635
  intro a
  fin_cases a
  · exact context_11_88972_1246381
  · exact context_11_88973_1246510
  · exact context_11_88974_1246634
  · exact context_11_88975_977886

theorem unmarked_context_9_5560_1246636 : frontier 12 ⟨1246636, by decide⟩
    (prefixCache 9 5560) (prefixPartial 9 5560) = false := by
  decide +kernel

theorem node_context_9_5560_1246636 : EJMOriginalGlobalDAGData.nodes 12 ⟨1246636, by decide⟩ =
    .split (coordinate 9) (![⟨1245032, by decide⟩,⟨1245657, by decide⟩,⟨1246255, by decide⟩,⟨1246635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5560_1246636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5560 ⟨1246636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5560
    ⟨1246636, by decide⟩ (by decide) (![⟨1245032, by decide⟩,⟨1245657, by decide⟩,⟨1246255, by decide⟩,⟨1246635, by decide⟩]) unmarked_context_9_5560_1246636 node_context_9_5560_1246636
  intro a
  fin_cases a
  · exact context_10_22240_1245032
  · exact context_10_22241_1245657
  · exact context_10_22242_1246255
  · exact context_10_22243_1246635

theorem selected_cut_45125 : selected 10 ⟨1246713, by decide⟩
    (prefixPartial 11 88976) = some ⟨11, 2, 0, 1246713, 88976, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_88976_1246713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88976 ⟨1246713, by decide⟩ :=
  accepted_of_selected 11 88976 ⟨1246713, by decide⟩ ⟨11, 2, 0, 1246713, 88976, 3685, 262144⟩
    (by decide) selected_cut_45125

theorem selected_cut_45126 : selected 9 ⟨1246741, by decide⟩
    (prefixPartial 12 355908) = some ⟨12, 2, 0, 1246741, 355908, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_355908_1246741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355908 ⟨1246741, by decide⟩ :=
  accepted_of_selected 12 355908 ⟨1246741, by decide⟩ ⟨12, 2, 0, 1246741, 355908, 1653, 65536⟩
    (by decide) selected_cut_45126

theorem selected_cut_45127 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355909) = some ⟨12, 1, 0, 896706, 355909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355909_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355909 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355909 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355909, 1, 65536⟩
    (by decide) selected_cut_45127

theorem selected_cut_45128 : selected 9 ⟨1246770, by decide⟩
    (prefixPartial 12 355910) = some ⟨12, 2, 0, 1246770, 355910, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_355910_1246770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355910 ⟨1246770, by decide⟩ :=
  accepted_of_selected 12 355910 ⟨1246770, by decide⟩ ⟨12, 2, 0, 1246770, 355910, 1521, 65536⟩
    (by decide) selected_cut_45128

theorem selected_cut_45129 : selected 9 ⟨1246805, by decide⟩
    (prefixPartial 12 355911) = some ⟨12, 2, 0, 1246805, 355911, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_355911_1246805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355911 ⟨1246805, by decide⟩ :=
  accepted_of_selected 12 355911 ⟨1246805, by decide⟩ ⟨12, 2, 0, 1246805, 355911, 1705, 65536⟩
    (by decide) selected_cut_45129

theorem unmarked_context_11_88977_1246806 : frontier 10 ⟨1246806, by decide⟩
    (prefixCache 11 88977) (prefixPartial 11 88977) = false := by
  decide +kernel

theorem node_context_11_88977_1246806 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246806, by decide⟩ =
    .split (coordinate 11) (![⟨1246741, by decide⟩,⟨896706, by decide⟩,⟨1246770, by decide⟩,⟨1246805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88977_1246806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88977 ⟨1246806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88977
    ⟨1246806, by decide⟩ (by decide) (![⟨1246741, by decide⟩,⟨896706, by decide⟩,⟨1246770, by decide⟩,⟨1246805, by decide⟩]) unmarked_context_11_88977_1246806 node_context_11_88977_1246806
  intro a
  fin_cases a
  · exact context_12_355908_1246741
  · exact context_12_355909_896706
  · exact context_12_355910_1246770
  · exact context_12_355911_1246805

theorem selected_cut_45130 : selected 10 ⟨1246876, by decide⟩
    (prefixPartial 11 88978) = some ⟨11, 2, 0, 1246876, 88978, 3413, 262144⟩ := by
  decide +kernel

theorem context_11_88978_1246876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88978 ⟨1246876, by decide⟩ :=
  accepted_of_selected 11 88978 ⟨1246876, by decide⟩ ⟨11, 2, 0, 1246876, 88978, 3413, 262144⟩
    (by decide) selected_cut_45130

theorem selected_cut_45131 : selected 9 ⟨1246899, by decide⟩
    (prefixPartial 12 355916) = some ⟨12, 2, 0, 1246899, 355916, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_355916_1246899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355916 ⟨1246899, by decide⟩ :=
  accepted_of_selected 12 355916 ⟨1246899, by decide⟩ ⟨12, 2, 0, 1246899, 355916, 1409, 65536⟩
    (by decide) selected_cut_45131

theorem selected_cut_45132 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355917) = some ⟨12, 1, 0, 896706, 355917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355917_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355917 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355917 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355917, 1, 65536⟩
    (by decide) selected_cut_45132

theorem selected_cut_45133 : selected 9 ⟨1246924, by decide⟩
    (prefixPartial 12 355918) = some ⟨12, 2, 0, 1246924, 355918, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_355918_1246924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355918 ⟨1246924, by decide⟩ :=
  accepted_of_selected 12 355918 ⟨1246924, by decide⟩ ⟨12, 2, 0, 1246924, 355918, 1393, 65536⟩
    (by decide) selected_cut_45133

theorem selected_cut_45134 : selected 9 ⟨1246950, by decide⟩
    (prefixPartial 12 355919) = some ⟨12, 2, 0, 1246950, 355919, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_355919_1246950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355919 ⟨1246950, by decide⟩ :=
  accepted_of_selected 12 355919 ⟨1246950, by decide⟩ ⟨12, 2, 0, 1246950, 355919, 1565, 65536⟩
    (by decide) selected_cut_45134

theorem unmarked_context_11_88979_1246951 : frontier 10 ⟨1246951, by decide⟩
    (prefixCache 11 88979) (prefixPartial 11 88979) = false := by
  decide +kernel

theorem node_context_11_88979_1246951 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246951, by decide⟩ =
    .split (coordinate 11) (![⟨1246899, by decide⟩,⟨896706, by decide⟩,⟨1246924, by decide⟩,⟨1246950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88979_1246951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88979 ⟨1246951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88979
    ⟨1246951, by decide⟩ (by decide) (![⟨1246899, by decide⟩,⟨896706, by decide⟩,⟨1246924, by decide⟩,⟨1246950, by decide⟩]) unmarked_context_11_88979_1246951 node_context_11_88979_1246951
  intro a
  fin_cases a
  · exact context_12_355916_1246899
  · exact context_12_355917_896706
  · exact context_12_355918_1246924
  · exact context_12_355919_1246950

theorem unmarked_context_10_22244_1246952 : frontier 11 ⟨1246952, by decide⟩
    (prefixCache 10 22244) (prefixPartial 10 22244) = false := by
  decide +kernel

theorem node_context_10_22244_1246952 : EJMOriginalGlobalDAGData.nodes 11 ⟨1246952, by decide⟩ =
    .split (coordinate 10) (![⟨1246713, by decide⟩,⟨1246806, by decide⟩,⟨1246876, by decide⟩,⟨1246951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22244_1246952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22244 ⟨1246952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22244
    ⟨1246952, by decide⟩ (by decide) (![⟨1246713, by decide⟩,⟨1246806, by decide⟩,⟨1246876, by decide⟩,⟨1246951, by decide⟩]) unmarked_context_10_22244_1246952 node_context_10_22244_1246952
  intro a
  fin_cases a
  · exact context_11_88976_1246713
  · exact context_11_88977_1246806
  · exact context_11_88978_1246876
  · exact context_11_88979_1246951

theorem selected_cut_45135 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22245) = some ⟨10, 1, 0, 893098, 22245, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22245_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22245 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22245 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22245, 1, 1048576⟩
    (by decide) selected_cut_45135

theorem selected_cut_45136 : selected 9 ⟨1246980, by decide⟩
    (prefixPartial 12 355936) = some ⟨12, 2, 0, 1246980, 355936, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_355936_1246980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355936 ⟨1246980, by decide⟩ :=
  accepted_of_selected 12 355936 ⟨1246980, by decide⟩ ⟨12, 2, 0, 1246980, 355936, 1585, 65536⟩
    (by decide) selected_cut_45136

theorem selected_cut_45137 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355937) = some ⟨12, 1, 0, 896706, 355937, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355937_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355937 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355937 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355937, 1, 65536⟩
    (by decide) selected_cut_45137

theorem selected_cut_45138 : selected 9 ⟨1247004, by decide⟩
    (prefixPartial 12 355938) = some ⟨12, 2, 0, 1247004, 355938, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_355938_1247004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355938 ⟨1247004, by decide⟩ :=
  accepted_of_selected 12 355938 ⟨1247004, by decide⟩ ⟨12, 2, 0, 1247004, 355938, 1377, 65536⟩
    (by decide) selected_cut_45138

theorem selected_cut_45139 : selected 9 ⟨1247032, by decide⟩
    (prefixPartial 12 355939) = some ⟨12, 2, 0, 1247032, 355939, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_355939_1247032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355939 ⟨1247032, by decide⟩ :=
  accepted_of_selected 12 355939 ⟨1247032, by decide⟩ ⟨12, 2, 0, 1247032, 355939, 1677, 65536⟩
    (by decide) selected_cut_45139

theorem unmarked_context_11_88984_1247033 : frontier 10 ⟨1247033, by decide⟩
    (prefixCache 11 88984) (prefixPartial 11 88984) = false := by
  decide +kernel

theorem node_context_11_88984_1247033 : EJMOriginalGlobalDAGData.nodes 10 ⟨1247033, by decide⟩ =
    .split (coordinate 11) (![⟨1246980, by decide⟩,⟨896706, by decide⟩,⟨1247004, by decide⟩,⟨1247032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88984_1247033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88984 ⟨1247033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88984
    ⟨1247033, by decide⟩ (by decide) (![⟨1246980, by decide⟩,⟨896706, by decide⟩,⟨1247004, by decide⟩,⟨1247032, by decide⟩]) unmarked_context_11_88984_1247033 node_context_11_88984_1247033
  intro a
  fin_cases a
  · exact context_12_355936_1246980
  · exact context_12_355937_896706
  · exact context_12_355938_1247004
  · exact context_12_355939_1247032

theorem selected_cut_45140 : selected 9 ⟨1247054, by decide⟩
    (prefixPartial 12 355940) = some ⟨12, 2, 0, 1247054, 355940, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_355940_1247054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355940 ⟨1247054, by decide⟩ :=
  accepted_of_selected 12 355940 ⟨1247054, by decide⟩ ⟨12, 2, 0, 1247054, 355940, 1445, 65536⟩
    (by decide) selected_cut_45140

theorem selected_cut_45141 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355941) = some ⟨12, 1, 0, 896706, 355941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355941_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355941 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355941 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355941, 1, 65536⟩
    (by decide) selected_cut_45141

theorem selected_cut_45142 : selected 9 ⟨1247073, by decide⟩
    (prefixPartial 12 355942) = some ⟨12, 2, 0, 1247073, 355942, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_355942_1247073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355942 ⟨1247073, by decide⟩ :=
  accepted_of_selected 12 355942 ⟨1247073, by decide⟩ ⟨12, 2, 0, 1247073, 355942, 1261, 65536⟩
    (by decide) selected_cut_45142

theorem selected_cut_45143 : selected 9 ⟨1247097, by decide⟩
    (prefixPartial 12 355943) = some ⟨12, 2, 0, 1247097, 355943, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_355943_1247097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355943 ⟨1247097, by decide⟩ :=
  accepted_of_selected 12 355943 ⟨1247097, by decide⟩ ⟨12, 2, 0, 1247097, 355943, 1489, 65536⟩
    (by decide) selected_cut_45143

theorem unmarked_context_11_88985_1247098 : frontier 10 ⟨1247098, by decide⟩
    (prefixCache 11 88985) (prefixPartial 11 88985) = false := by
  decide +kernel

theorem node_context_11_88985_1247098 : EJMOriginalGlobalDAGData.nodes 10 ⟨1247098, by decide⟩ =
    .split (coordinate 11) (![⟨1247054, by decide⟩,⟨896706, by decide⟩,⟨1247073, by decide⟩,⟨1247097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88985_1247098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88985 ⟨1247098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88985
    ⟨1247098, by decide⟩ (by decide) (![⟨1247054, by decide⟩,⟨896706, by decide⟩,⟨1247073, by decide⟩,⟨1247097, by decide⟩]) unmarked_context_11_88985_1247098 node_context_11_88985_1247098
  intro a
  fin_cases a
  · exact context_12_355940_1247054
  · exact context_12_355941_896706
  · exact context_12_355942_1247073
  · exact context_12_355943_1247097

theorem selected_cut_45144 : selected 10 ⟨1247122, by decide⟩
    (prefixPartial 11 88986) = some ⟨11, 2, 0, 1247122, 88986, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_88986_1247122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88986 ⟨1247122, by decide⟩ :=
  accepted_of_selected 11 88986 ⟨1247122, by decide⟩ ⟨11, 2, 0, 1247122, 88986, 1397, 262144⟩
    (by decide) selected_cut_45144

theorem selected_cut_45145 : selected 10 ⟨1247156, by decide⟩
    (prefixPartial 11 88987) = some ⟨11, 2, 0, 1247156, 88987, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_88987_1247156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88987 ⟨1247156, by decide⟩ :=
  accepted_of_selected 11 88987 ⟨1247156, by decide⟩ ⟨11, 2, 0, 1247156, 88987, 2461, 262144⟩
    (by decide) selected_cut_45145

theorem unmarked_context_10_22246_1247157 : frontier 11 ⟨1247157, by decide⟩
    (prefixCache 10 22246) (prefixPartial 10 22246) = false := by
  decide +kernel

theorem node_context_10_22246_1247157 : EJMOriginalGlobalDAGData.nodes 11 ⟨1247157, by decide⟩ =
    .split (coordinate 10) (![⟨1247033, by decide⟩,⟨1247098, by decide⟩,⟨1247122, by decide⟩,⟨1247156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22246_1247157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22246 ⟨1247157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22246
    ⟨1247157, by decide⟩ (by decide) (![⟨1247033, by decide⟩,⟨1247098, by decide⟩,⟨1247122, by decide⟩,⟨1247156, by decide⟩]) unmarked_context_10_22246_1247157 node_context_10_22246_1247157
  intro a
  fin_cases a
  · exact context_11_88984_1247033
  · exact context_11_88985_1247098
  · exact context_11_88986_1247122
  · exact context_11_88987_1247156

theorem selected_cut_45146 : selected 10 ⟨1247225, by decide⟩
    (prefixPartial 11 88988) = some ⟨11, 2, 0, 1247225, 88988, 3769, 262144⟩ := by
  decide +kernel

theorem context_11_88988_1247225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88988 ⟨1247225, by decide⟩ :=
  accepted_of_selected 11 88988 ⟨1247225, by decide⟩ ⟨11, 2, 0, 1247225, 88988, 3769, 262144⟩
    (by decide) selected_cut_45146

theorem selected_cut_45147 : selected 10 ⟨1247277, by decide⟩
    (prefixPartial 11 88989) = some ⟨11, 2, 0, 1247277, 88989, 3141, 262144⟩ := by
  decide +kernel

theorem context_11_88989_1247277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88989 ⟨1247277, by decide⟩ :=
  accepted_of_selected 11 88989 ⟨1247277, by decide⟩ ⟨11, 2, 0, 1247277, 88989, 3141, 262144⟩
    (by decide) selected_cut_45147

theorem selected_cut_45148 : selected 10 ⟨1247314, by decide⟩
    (prefixPartial 11 88990) = some ⟨11, 2, 0, 1247314, 88990, 2053, 262144⟩ := by
  decide +kernel

theorem context_11_88990_1247314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88990 ⟨1247314, by decide⟩ :=
  accepted_of_selected 11 88990 ⟨1247314, by decide⟩ ⟨11, 2, 0, 1247314, 88990, 2053, 262144⟩
    (by decide) selected_cut_45148

theorem selected_cut_45149 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88991) = some ⟨11, 1, 0, 977886, 88991, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88991_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88991 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88991 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88991, 1, 262144⟩
    (by decide) selected_cut_45149

theorem unmarked_context_10_22247_1247315 : frontier 11 ⟨1247315, by decide⟩
    (prefixCache 10 22247) (prefixPartial 10 22247) = false := by
  decide +kernel

theorem node_context_10_22247_1247315 : EJMOriginalGlobalDAGData.nodes 11 ⟨1247315, by decide⟩ =
    .split (coordinate 10) (![⟨1247225, by decide⟩,⟨1247277, by decide⟩,⟨1247314, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22247_1247315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22247 ⟨1247315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22247
    ⟨1247315, by decide⟩ (by decide) (![⟨1247225, by decide⟩,⟨1247277, by decide⟩,⟨1247314, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22247_1247315 node_context_10_22247_1247315
  intro a
  fin_cases a
  · exact context_11_88988_1247225
  · exact context_11_88989_1247277
  · exact context_11_88990_1247314
  · exact context_11_88991_977886

theorem unmarked_context_9_5561_1247316 : frontier 12 ⟨1247316, by decide⟩
    (prefixCache 9 5561) (prefixPartial 9 5561) = false := by
  decide +kernel

theorem node_context_9_5561_1247316 : EJMOriginalGlobalDAGData.nodes 12 ⟨1247316, by decide⟩ =
    .split (coordinate 9) (![⟨1246952, by decide⟩,⟨893098, by decide⟩,⟨1247157, by decide⟩,⟨1247315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5561_1247316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5561 ⟨1247316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5561
    ⟨1247316, by decide⟩ (by decide) (![⟨1246952, by decide⟩,⟨893098, by decide⟩,⟨1247157, by decide⟩,⟨1247315, by decide⟩]) unmarked_context_9_5561_1247316 node_context_9_5561_1247316
  intro a
  fin_cases a
  · exact context_10_22244_1246952
  · exact context_10_22245_893098
  · exact context_10_22246_1247157
  · exact context_10_22247_1247315

theorem selected_cut_45150 : selected 10 ⟨1247385, by decide⟩
    (prefixPartial 11 88992) = some ⟨11, 2, 0, 1247385, 88992, 3649, 262144⟩ := by
  decide +kernel

theorem context_11_88992_1247385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88992 ⟨1247385, by decide⟩ :=
  accepted_of_selected 11 88992 ⟨1247385, by decide⟩ ⟨11, 2, 0, 1247385, 88992, 3649, 262144⟩
    (by decide) selected_cut_45150

theorem selected_cut_45151 : selected 10 ⟨1247430, by decide⟩
    (prefixPartial 11 88993) = some ⟨11, 2, 0, 1247430, 88993, 2765, 262144⟩ := by
  decide +kernel

theorem context_11_88993_1247430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88993 ⟨1247430, by decide⟩ :=
  accepted_of_selected 11 88993 ⟨1247430, by decide⟩ ⟨11, 2, 0, 1247430, 88993, 2765, 262144⟩
    (by decide) selected_cut_45151

theorem selected_cut_45152 : selected 10 ⟨1247494, by decide⟩
    (prefixPartial 11 88994) = some ⟨11, 2, 0, 1247494, 88994, 3889, 262144⟩ := by
  decide +kernel

theorem context_11_88994_1247494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88994 ⟨1247494, by decide⟩ :=
  accepted_of_selected 11 88994 ⟨1247494, by decide⟩ ⟨11, 2, 0, 1247494, 88994, 3889, 262144⟩
    (by decide) selected_cut_45152

theorem selected_cut_45153 : selected 9 ⟨1247527, by decide⟩
    (prefixPartial 12 355980) = some ⟨12, 2, 0, 1247527, 355980, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_355980_1247527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355980 ⟨1247527, by decide⟩ :=
  accepted_of_selected 12 355980 ⟨1247527, by decide⟩ ⟨12, 2, 0, 1247527, 355980, 1277, 65536⟩
    (by decide) selected_cut_45153

theorem selected_cut_45154 : selected 9 ⟨1247545, by decide⟩
    (prefixPartial 12 355981) = some ⟨12, 2, 0, 1247545, 355981, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_355981_1247545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355981 ⟨1247545, by decide⟩ :=
  accepted_of_selected 12 355981 ⟨1247545, by decide⟩ ⟨12, 2, 0, 1247545, 355981, 1041, 65536⟩
    (by decide) selected_cut_45154

theorem selected_cut_45155 : selected 9 ⟨1247574, by decide⟩
    (prefixPartial 12 355982) = some ⟨12, 2, 0, 1247574, 355982, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_355982_1247574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355982 ⟨1247574, by decide⟩ :=
  accepted_of_selected 12 355982 ⟨1247574, by decide⟩ ⟨12, 2, 0, 1247574, 355982, 1137, 65536⟩
    (by decide) selected_cut_45155

theorem selected_cut_45156 : selected 9 ⟨1247602, by decide⟩
    (prefixPartial 12 355983) = some ⟨12, 2, 0, 1247602, 355983, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_355983_1247602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355983 ⟨1247602, by decide⟩ :=
  accepted_of_selected 12 355983 ⟨1247602, by decide⟩ ⟨12, 2, 0, 1247602, 355983, 1353, 65536⟩
    (by decide) selected_cut_45156

theorem unmarked_context_11_88995_1247603 : frontier 10 ⟨1247603, by decide⟩
    (prefixCache 11 88995) (prefixPartial 11 88995) = false := by
  decide +kernel

theorem node_context_11_88995_1247603 : EJMOriginalGlobalDAGData.nodes 10 ⟨1247603, by decide⟩ =
    .split (coordinate 11) (![⟨1247527, by decide⟩,⟨1247545, by decide⟩,⟨1247574, by decide⟩,⟨1247602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88995_1247603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88995 ⟨1247603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88995
    ⟨1247603, by decide⟩ (by decide) (![⟨1247527, by decide⟩,⟨1247545, by decide⟩,⟨1247574, by decide⟩,⟨1247602, by decide⟩]) unmarked_context_11_88995_1247603 node_context_11_88995_1247603
  intro a
  fin_cases a
  · exact context_12_355980_1247527
  · exact context_12_355981_1247545
  · exact context_12_355982_1247574
  · exact context_12_355983_1247602

theorem unmarked_context_10_22248_1247604 : frontier 11 ⟨1247604, by decide⟩
    (prefixCache 10 22248) (prefixPartial 10 22248) = false := by
  decide +kernel

theorem node_context_10_22248_1247604 : EJMOriginalGlobalDAGData.nodes 11 ⟨1247604, by decide⟩ =
    .split (coordinate 10) (![⟨1247385, by decide⟩,⟨1247430, by decide⟩,⟨1247494, by decide⟩,⟨1247603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22248_1247604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22248 ⟨1247604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22248
    ⟨1247604, by decide⟩ (by decide) (![⟨1247385, by decide⟩,⟨1247430, by decide⟩,⟨1247494, by decide⟩,⟨1247603, by decide⟩]) unmarked_context_10_22248_1247604 node_context_10_22248_1247604
  intro a
  fin_cases a
  · exact context_11_88992_1247385
  · exact context_11_88993_1247430
  · exact context_11_88994_1247494
  · exact context_11_88995_1247603

theorem selected_cut_45157 : selected 10 ⟨1247678, by decide⟩
    (prefixPartial 11 88996) = some ⟨11, 2, 0, 1247678, 88996, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_88996_1247678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88996 ⟨1247678, by decide⟩ :=
  accepted_of_selected 11 88996 ⟨1247678, by decide⟩ ⟨11, 2, 0, 1247678, 88996, 3237, 262144⟩
    (by decide) selected_cut_45157

theorem selected_cut_45158 : selected 10 ⟨1247711, by decide⟩
    (prefixPartial 11 88997) = some ⟨11, 2, 0, 1247711, 88997, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_88997_1247711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88997 ⟨1247711, by decide⟩ :=
  accepted_of_selected 11 88997 ⟨1247711, by decide⟩ ⟨11, 2, 0, 1247711, 88997, 2085, 262144⟩
    (by decide) selected_cut_45158

theorem selected_cut_45159 : selected 10 ⟨1247765, by decide⟩
    (prefixPartial 11 88998) = some ⟨11, 2, 0, 1247765, 88998, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_88998_1247765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88998 ⟨1247765, by decide⟩ :=
  accepted_of_selected 11 88998 ⟨1247765, by decide⟩ ⟨11, 2, 0, 1247765, 88998, 2909, 262144⟩
    (by decide) selected_cut_45159

theorem selected_cut_45160 : selected 10 ⟨1247813, by decide⟩
    (prefixPartial 11 88999) = some ⟨11, 2, 0, 1247813, 88999, 2789, 262144⟩ := by
  decide +kernel

theorem context_11_88999_1247813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88999 ⟨1247813, by decide⟩ :=
  accepted_of_selected 11 88999 ⟨1247813, by decide⟩ ⟨11, 2, 0, 1247813, 88999, 2789, 262144⟩
    (by decide) selected_cut_45160

theorem unmarked_context_10_22249_1247814 : frontier 11 ⟨1247814, by decide⟩
    (prefixCache 10 22249) (prefixPartial 10 22249) = false := by
  decide +kernel

theorem node_context_10_22249_1247814 : EJMOriginalGlobalDAGData.nodes 11 ⟨1247814, by decide⟩ =
    .split (coordinate 10) (![⟨1247678, by decide⟩,⟨1247711, by decide⟩,⟨1247765, by decide⟩,⟨1247813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22249_1247814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22249 ⟨1247814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22249
    ⟨1247814, by decide⟩ (by decide) (![⟨1247678, by decide⟩,⟨1247711, by decide⟩,⟨1247765, by decide⟩,⟨1247813, by decide⟩]) unmarked_context_10_22249_1247814 node_context_10_22249_1247814
  intro a
  fin_cases a
  · exact context_11_88996_1247678
  · exact context_11_88997_1247711
  · exact context_11_88998_1247765
  · exact context_11_88999_1247813

theorem selected_cut_45161 : selected 10 ⟨1247847, by decide⟩
    (prefixPartial 11 89000) = some ⟨11, 2, 0, 1247847, 89000, 1737, 262144⟩ := by
  decide +kernel

theorem context_11_89000_1247847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89000 ⟨1247847, by decide⟩ :=
  accepted_of_selected 11 89000 ⟨1247847, by decide⟩ ⟨11, 2, 0, 1247847, 89000, 1737, 262144⟩
    (by decide) selected_cut_45161

theorem selected_cut_45162 : selected 10 ⟨1247879, by decide⟩
    (prefixPartial 11 89001) = some ⟨11, 2, 0, 1247879, 89001, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_89001_1247879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89001 ⟨1247879, by decide⟩ :=
  accepted_of_selected 11 89001 ⟨1247879, by decide⟩ ⟨11, 2, 0, 1247879, 89001, 1645, 262144⟩
    (by decide) selected_cut_45162

theorem selected_cut_45163 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 89002) = some ⟨11, 1, 0, 1109453, 89002, 1, 262144⟩ := by
  decide +kernel

theorem context_11_89002_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89002 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 89002 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 89002, 1, 262144⟩
    (by decide) selected_cut_45163

theorem selected_cut_45164 : selected 10 ⟨1247895, by decide⟩
    (prefixPartial 11 89003) = some ⟨11, 2, 0, 1247895, 89003, 773, 262144⟩ := by
  decide +kernel

theorem context_11_89003_1247895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89003 ⟨1247895, by decide⟩ :=
  accepted_of_selected 11 89003 ⟨1247895, by decide⟩ ⟨11, 2, 0, 1247895, 89003, 773, 262144⟩
    (by decide) selected_cut_45164

theorem unmarked_context_10_22250_1247896 : frontier 11 ⟨1247896, by decide⟩
    (prefixCache 10 22250) (prefixPartial 10 22250) = false := by
  decide +kernel

theorem node_context_10_22250_1247896 : EJMOriginalGlobalDAGData.nodes 11 ⟨1247896, by decide⟩ =
    .split (coordinate 10) (![⟨1247847, by decide⟩,⟨1247879, by decide⟩,⟨1109453, by decide⟩,⟨1247895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22250_1247896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22250 ⟨1247896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22250
    ⟨1247896, by decide⟩ (by decide) (![⟨1247847, by decide⟩,⟨1247879, by decide⟩,⟨1109453, by decide⟩,⟨1247895, by decide⟩]) unmarked_context_10_22250_1247896 node_context_10_22250_1247896
  intro a
  fin_cases a
  · exact context_11_89000_1247847
  · exact context_11_89001_1247879
  · exact context_11_89002_1109453
  · exact context_11_89003_1247895

theorem selected_cut_45165 : selected 10 ⟨1247936, by decide⟩
    (prefixPartial 11 89004) = some ⟨11, 2, 0, 1247936, 89004, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_89004_1247936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89004 ⟨1247936, by decide⟩ :=
  accepted_of_selected 11 89004 ⟨1247936, by decide⟩ ⟨11, 2, 0, 1247936, 89004, 2433, 262144⟩
    (by decide) selected_cut_45165

theorem selected_cut_45166 : selected 10 ⟨1247955, by decide⟩
    (prefixPartial 11 89005) = some ⟨11, 2, 0, 1247955, 89005, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_89005_1247955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89005 ⟨1247955, by decide⟩ :=
  accepted_of_selected 11 89005 ⟨1247955, by decide⟩ ⟨11, 2, 0, 1247955, 89005, 1105, 262144⟩
    (by decide) selected_cut_45166

theorem selected_cut_45167 : selected 10 ⟨1247981, by decide⟩
    (prefixPartial 11 89006) = some ⟨11, 2, 0, 1247981, 89006, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_89006_1247981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89006 ⟨1247981, by decide⟩ :=
  accepted_of_selected 11 89006 ⟨1247981, by decide⟩ ⟨11, 2, 0, 1247981, 89006, 1489, 262144⟩
    (by decide) selected_cut_45167

theorem selected_cut_45168 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 89007) = some ⟨11, 1, 0, 977886, 89007, 1, 262144⟩ := by
  decide +kernel

theorem context_11_89007_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89007 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 89007 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 89007, 1, 262144⟩
    (by decide) selected_cut_45168

theorem unmarked_context_10_22251_1247982 : frontier 11 ⟨1247982, by decide⟩
    (prefixCache 10 22251) (prefixPartial 10 22251) = false := by
  decide +kernel

theorem node_context_10_22251_1247982 : EJMOriginalGlobalDAGData.nodes 11 ⟨1247982, by decide⟩ =
    .split (coordinate 10) (![⟨1247936, by decide⟩,⟨1247955, by decide⟩,⟨1247981, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22251_1247982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22251 ⟨1247982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22251
    ⟨1247982, by decide⟩ (by decide) (![⟨1247936, by decide⟩,⟨1247955, by decide⟩,⟨1247981, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22251_1247982 node_context_10_22251_1247982
  intro a
  fin_cases a
  · exact context_11_89004_1247936
  · exact context_11_89005_1247955
  · exact context_11_89006_1247981
  · exact context_11_89007_977886

theorem unmarked_context_9_5562_1247983 : frontier 12 ⟨1247983, by decide⟩
    (prefixCache 9 5562) (prefixPartial 9 5562) = false := by
  decide +kernel

theorem node_context_9_5562_1247983 : EJMOriginalGlobalDAGData.nodes 12 ⟨1247983, by decide⟩ =
    .split (coordinate 9) (![⟨1247604, by decide⟩,⟨1247814, by decide⟩,⟨1247896, by decide⟩,⟨1247982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5562_1247983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5562 ⟨1247983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5562
    ⟨1247983, by decide⟩ (by decide) (![⟨1247604, by decide⟩,⟨1247814, by decide⟩,⟨1247896, by decide⟩,⟨1247982, by decide⟩]) unmarked_context_9_5562_1247983 node_context_9_5562_1247983
  intro a
  fin_cases a
  · exact context_10_22248_1247604
  · exact context_10_22249_1247814
  · exact context_10_22250_1247896
  · exact context_10_22251_1247982

theorem selected_cut_45169 : selected 10 ⟨1248015, by decide⟩
    (prefixPartial 11 89008) = some ⟨11, 2, 0, 1248015, 89008, 1505, 262144⟩ := by
  decide +kernel

theorem context_11_89008_1248015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89008 ⟨1248015, by decide⟩ :=
  accepted_of_selected 11 89008 ⟨1248015, by decide⟩ ⟨11, 2, 0, 1248015, 89008, 1505, 262144⟩
    (by decide) selected_cut_45169

theorem selected_cut_45170 : selected 10 ⟨1248044, by decide⟩
    (prefixPartial 11 89009) = some ⟨11, 2, 0, 1248044, 89009, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_89009_1248044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89009 ⟨1248044, by decide⟩ :=
  accepted_of_selected 11 89009 ⟨1248044, by decide⟩ ⟨11, 2, 0, 1248044, 89009, 1709, 262144⟩
    (by decide) selected_cut_45170

theorem selected_cut_45171 : selected 10 ⟨1248067, by decide⟩
    (prefixPartial 11 89010) = some ⟨11, 2, 0, 1248067, 89010, 1297, 262144⟩ := by
  decide +kernel

theorem context_11_89010_1248067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89010 ⟨1248067, by decide⟩ :=
  accepted_of_selected 11 89010 ⟨1248067, by decide⟩ ⟨11, 2, 0, 1248067, 89010, 1297, 262144⟩
    (by decide) selected_cut_45171

theorem selected_cut_45172 : selected 10 ⟨1248084, by decide⟩
    (prefixPartial 11 89011) = some ⟨11, 2, 0, 1248084, 89011, 1017, 262144⟩ := by
  decide +kernel

theorem context_11_89011_1248084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89011 ⟨1248084, by decide⟩ :=
  accepted_of_selected 11 89011 ⟨1248084, by decide⟩ ⟨11, 2, 0, 1248084, 89011, 1017, 262144⟩
    (by decide) selected_cut_45172

theorem unmarked_context_10_22252_1248085 : frontier 11 ⟨1248085, by decide⟩
    (prefixCache 10 22252) (prefixPartial 10 22252) = false := by
  decide +kernel

theorem node_context_10_22252_1248085 : EJMOriginalGlobalDAGData.nodes 11 ⟨1248085, by decide⟩ =
    .split (coordinate 10) (![⟨1248015, by decide⟩,⟨1248044, by decide⟩,⟨1248067, by decide⟩,⟨1248084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22252_1248085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22252 ⟨1248085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22252
    ⟨1248085, by decide⟩ (by decide) (![⟨1248015, by decide⟩,⟨1248044, by decide⟩,⟨1248067, by decide⟩,⟨1248084, by decide⟩]) unmarked_context_10_22252_1248085 node_context_10_22252_1248085
  intro a
  fin_cases a
  · exact context_11_89008_1248015
  · exact context_11_89009_1248044
  · exact context_11_89010_1248067
  · exact context_11_89011_1248084

theorem selected_cut_45173 : selected 11 ⟨1248121, by decide⟩
    (prefixPartial 10 22253) = some ⟨10, 2, 0, 1248121, 22253, 1917, 1048576⟩ := by
  decide +kernel

theorem context_10_22253_1248121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22253 ⟨1248121, by decide⟩ :=
  accepted_of_selected 10 22253 ⟨1248121, by decide⟩ ⟨10, 2, 0, 1248121, 22253, 1917, 1048576⟩
    (by decide) selected_cut_45173

theorem selected_cut_45174 : selected 11 ⟨1248171, by decide⟩
    (prefixPartial 10 22254) = some ⟨10, 2, 0, 1248171, 22254, 1621, 1048576⟩ := by
  decide +kernel

theorem context_10_22254_1248171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22254 ⟨1248171, by decide⟩ :=
  accepted_of_selected 10 22254 ⟨1248171, by decide⟩ ⟨10, 2, 0, 1248171, 22254, 1621, 1048576⟩
    (by decide) selected_cut_45174

theorem selected_cut_45175 : selected 11 ⟨1248182, by decide⟩
    (prefixPartial 10 22255) = some ⟨10, 2, 0, 1248182, 22255, 133, 1048576⟩ := by
  decide +kernel

theorem context_10_22255_1248182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22255 ⟨1248182, by decide⟩ :=
  accepted_of_selected 10 22255 ⟨1248182, by decide⟩ ⟨10, 2, 0, 1248182, 22255, 133, 1048576⟩
    (by decide) selected_cut_45175

theorem unmarked_context_9_5563_1248183 : frontier 12 ⟨1248183, by decide⟩
    (prefixCache 9 5563) (prefixPartial 9 5563) = false := by
  decide +kernel

theorem node_context_9_5563_1248183 : EJMOriginalGlobalDAGData.nodes 12 ⟨1248183, by decide⟩ =
    .split (coordinate 9) (![⟨1248085, by decide⟩,⟨1248121, by decide⟩,⟨1248171, by decide⟩,⟨1248182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5563_1248183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5563 ⟨1248183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5563
    ⟨1248183, by decide⟩ (by decide) (![⟨1248085, by decide⟩,⟨1248121, by decide⟩,⟨1248171, by decide⟩,⟨1248182, by decide⟩]) unmarked_context_9_5563_1248183 node_context_9_5563_1248183
  intro a
  fin_cases a
  · exact context_10_22252_1248085
  · exact context_10_22253_1248121
  · exact context_10_22254_1248171
  · exact context_10_22255_1248182

theorem unmarked_context_8_1390_1248184 : frontier 13 ⟨1248184, by decide⟩
    (prefixCache 8 1390) (prefixPartial 8 1390) = false := by
  decide +kernel

theorem node_context_8_1390_1248184 : EJMOriginalGlobalDAGData.nodes 13 ⟨1248184, by decide⟩ =
    .split (coordinate 8) (![⟨1246636, by decide⟩,⟨1247316, by decide⟩,⟨1247983, by decide⟩,⟨1248183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1390_1248184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1390 ⟨1248184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1390
    ⟨1248184, by decide⟩ (by decide) (![⟨1246636, by decide⟩,⟨1247316, by decide⟩,⟨1247983, by decide⟩,⟨1248183, by decide⟩]) unmarked_context_8_1390_1248184 node_context_8_1390_1248184
  intro a
  fin_cases a
  · exact context_9_5560_1246636
  · exact context_9_5561_1247316
  · exact context_9_5562_1247983
  · exact context_9_5563_1248183

theorem selected_cut_45176 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 89024) = some ⟨11, 1, 0, 434745, 89024, 1, 262144⟩ := by
  decide +kernel

theorem context_11_89024_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89024 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 89024 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 89024, 1, 262144⟩
    (by decide) selected_cut_45176

theorem selected_cut_45177 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 356100) = some ⟨12, 1, 0, 448748, 356100, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356100_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356100 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 356100 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 356100, 1, 65536⟩
    (by decide) selected_cut_45177

theorem selected_cut_45178 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 356101) = some ⟨12, 1, 0, 34034, 356101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356101_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356101 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 356101 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 356101, 1, 65536⟩
    (by decide) selected_cut_45178

theorem selected_cut_45179 : selected 9 ⟨1248269, by decide⟩
    (prefixPartial 12 356102) = some ⟨12, 2, 0, 1248269, 356102, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_356102_1248269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356102 ⟨1248269, by decide⟩ :=
  accepted_of_selected 12 356102 ⟨1248269, by decide⟩ ⟨12, 2, 0, 1248269, 356102, 3161, 65536⟩
    (by decide) selected_cut_45179

theorem selected_cut_45180 : selected 9 ⟨1248347, by decide⟩
    (prefixPartial 12 356103) = some ⟨12, 2, 0, 1248347, 356103, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_356103_1248347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356103 ⟨1248347, by decide⟩ :=
  accepted_of_selected 12 356103 ⟨1248347, by decide⟩ ⟨12, 2, 0, 1248347, 356103, 3417, 65536⟩
    (by decide) selected_cut_45180

theorem unmarked_context_11_89025_1248348 : frontier 10 ⟨1248348, by decide⟩
    (prefixCache 11 89025) (prefixPartial 11 89025) = false := by
  decide +kernel

theorem node_context_11_89025_1248348 : EJMOriginalGlobalDAGData.nodes 10 ⟨1248348, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1248269, by decide⟩,⟨1248347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89025_1248348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89025 ⟨1248348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89025
    ⟨1248348, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1248269, by decide⟩,⟨1248347, by decide⟩]) unmarked_context_11_89025_1248348 node_context_11_89025_1248348
  intro a
  fin_cases a
  · exact context_12_356100_448748
  · exact context_12_356101_34034
  · exact context_12_356102_1248269
  · exact context_12_356103_1248347

theorem selected_cut_45181 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 356104) = some ⟨12, 1, 0, 448748, 356104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356104_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356104 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 356104 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 356104, 1, 65536⟩
    (by decide) selected_cut_45181

theorem selected_cut_45182 : selected 9 ⟨1248429, by decide⟩
    (prefixPartial 12 356105) = some ⟨12, 2, 0, 1248429, 356105, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_356105_1248429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356105 ⟨1248429, by decide⟩ :=
  accepted_of_selected 12 356105 ⟨1248429, by decide⟩ ⟨12, 2, 0, 1248429, 356105, 3449, 65536⟩
    (by decide) selected_cut_45182

theorem selected_cut_45183 : selected 9 ⟨1248501, by decide⟩
    (prefixPartial 12 356106) = some ⟨12, 2, 0, 1248501, 356106, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_356106_1248501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356106 ⟨1248501, by decide⟩ :=
  accepted_of_selected 12 356106 ⟨1248501, by decide⟩ ⟨12, 2, 0, 1248501, 356106, 3285, 65536⟩
    (by decide) selected_cut_45183

theorem selected_cut_45184 : selected 9 ⟨1248586, by decide⟩
    (prefixPartial 12 356107) = some ⟨12, 2, 0, 1248586, 356107, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_356107_1248586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356107 ⟨1248586, by decide⟩ :=
  accepted_of_selected 12 356107 ⟨1248586, by decide⟩ ⟨12, 2, 0, 1248586, 356107, 3621, 65536⟩
    (by decide) selected_cut_45184

theorem unmarked_context_11_89026_1248587 : frontier 10 ⟨1248587, by decide⟩
    (prefixCache 11 89026) (prefixPartial 11 89026) = false := by
  decide +kernel

theorem node_context_11_89026_1248587 : EJMOriginalGlobalDAGData.nodes 10 ⟨1248587, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1248429, by decide⟩,⟨1248501, by decide⟩,⟨1248586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89026_1248587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89026 ⟨1248587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89026
    ⟨1248587, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1248429, by decide⟩,⟨1248501, by decide⟩,⟨1248586, by decide⟩]) unmarked_context_11_89026_1248587 node_context_11_89026_1248587
  intro a
  fin_cases a
  · exact context_12_356104_448748
  · exact context_12_356105_1248429
  · exact context_12_356106_1248501
  · exact context_12_356107_1248586

theorem selected_cut_45185 : selected 10 ⟨1248661, by decide⟩
    (prefixPartial 11 89027) = some ⟨11, 2, 0, 1248661, 89027, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_89027_1248661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89027 ⟨1248661, by decide⟩ :=
  accepted_of_selected 11 89027 ⟨1248661, by decide⟩ ⟨11, 2, 0, 1248661, 89027, 3097, 262144⟩
    (by decide) selected_cut_45185

theorem unmarked_context_10_22256_1248662 : frontier 11 ⟨1248662, by decide⟩
    (prefixCache 10 22256) (prefixPartial 10 22256) = false := by
  decide +kernel

theorem node_context_10_22256_1248662 : EJMOriginalGlobalDAGData.nodes 11 ⟨1248662, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1248348, by decide⟩,⟨1248587, by decide⟩,⟨1248661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22256_1248662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22256 ⟨1248662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22256
    ⟨1248662, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1248348, by decide⟩,⟨1248587, by decide⟩,⟨1248661, by decide⟩]) unmarked_context_10_22256_1248662 node_context_10_22256_1248662
  intro a
  fin_cases a
  · exact context_11_89024_434745
  · exact context_11_89025_1248348
  · exact context_11_89026_1248587
  · exact context_11_89027_1248661

theorem selected_cut_45186 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 356112) = some ⟨12, 1, 0, 435160, 356112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356112_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356112 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 356112 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 356112, 1, 65536⟩
    (by decide) selected_cut_45186

theorem selected_cut_45187 : selected 9 ⟨1248745, by decide⟩
    (prefixPartial 12 356113) = some ⟨12, 2, 0, 1248745, 356113, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_356113_1248745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356113 ⟨1248745, by decide⟩ :=
  accepted_of_selected 12 356113 ⟨1248745, by decide⟩ ⟨12, 2, 0, 1248745, 356113, 3289, 65536⟩
    (by decide) selected_cut_45187

theorem selected_cut_45188 : selected 9 ⟨1248818, by decide⟩
    (prefixPartial 12 356114) = some ⟨12, 2, 0, 1248818, 356114, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_356114_1248818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356114 ⟨1248818, by decide⟩ :=
  accepted_of_selected 12 356114 ⟨1248818, by decide⟩ ⟨12, 2, 0, 1248818, 356114, 3853, 65536⟩
    (by decide) selected_cut_45188

theorem selected_cut_45189 : selected 9 ⟨1248894, by decide⟩
    (prefixPartial 12 356115) = some ⟨12, 2, 0, 1248894, 356115, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_356115_1248894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356115 ⟨1248894, by decide⟩ :=
  accepted_of_selected 12 356115 ⟨1248894, by decide⟩ ⟨12, 2, 0, 1248894, 356115, 3753, 65536⟩
    (by decide) selected_cut_45189

theorem unmarked_context_11_89028_1248895 : frontier 10 ⟨1248895, by decide⟩
    (prefixCache 11 89028) (prefixPartial 11 89028) = false := by
  decide +kernel

theorem node_context_11_89028_1248895 : EJMOriginalGlobalDAGData.nodes 10 ⟨1248895, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1248745, by decide⟩,⟨1248818, by decide⟩,⟨1248894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89028_1248895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89028 ⟨1248895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89028
    ⟨1248895, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1248745, by decide⟩,⟨1248818, by decide⟩,⟨1248894, by decide⟩]) unmarked_context_11_89028_1248895 node_context_11_89028_1248895
  intro a
  fin_cases a
  · exact context_12_356112_435160
  · exact context_12_356113_1248745
  · exact context_12_356114_1248818
  · exact context_12_356115_1248894

theorem selected_cut_45190 : selected 10 ⟨1248968, by decide⟩
    (prefixPartial 11 89029) = some ⟨11, 2, 0, 1248968, 89029, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_89029_1248968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89029 ⟨1248968, by decide⟩ :=
  accepted_of_selected 11 89029 ⟨1248968, by decide⟩ ⟨11, 2, 0, 1248968, 89029, 3605, 262144⟩
    (by decide) selected_cut_45190

theorem selected_cut_45191 : selected 9 ⟨1249046, by decide⟩
    (prefixPartial 12 356120) = some ⟨12, 2, 0, 1249046, 356120, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_356120_1249046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356120 ⟨1249046, by decide⟩ :=
  accepted_of_selected 12 356120 ⟨1249046, by decide⟩ ⟨12, 2, 0, 1249046, 356120, 1981, 65536⟩
    (by decide) selected_cut_45191

theorem selected_cut_45192 : selected 9 ⟨1249117, by decide⟩
    (prefixPartial 12 356121) = some ⟨12, 2, 0, 1249117, 356121, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_356121_1249117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356121 ⟨1249117, by decide⟩ :=
  accepted_of_selected 12 356121 ⟨1249117, by decide⟩ ⟨12, 2, 0, 1249117, 356121, 3257, 65536⟩
    (by decide) selected_cut_45192

theorem selected_cut_45193 : selected 9 ⟨1249184, by decide⟩
    (prefixPartial 12 356122) = some ⟨12, 2, 0, 1249184, 356122, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_356122_1249184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356122 ⟨1249184, by decide⟩ :=
  accepted_of_selected 12 356122 ⟨1249184, by decide⟩ ⟨12, 2, 0, 1249184, 356122, 3453, 65536⟩
    (by decide) selected_cut_45193

theorem selected_cut_45194 : selected 9 ⟨1249254, by decide⟩
    (prefixPartial 12 356123) = some ⟨12, 2, 0, 1249254, 356123, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_356123_1249254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356123 ⟨1249254, by decide⟩ :=
  accepted_of_selected 12 356123 ⟨1249254, by decide⟩ ⟨12, 2, 0, 1249254, 356123, 3601, 65536⟩
    (by decide) selected_cut_45194

theorem unmarked_context_11_89030_1249255 : frontier 10 ⟨1249255, by decide⟩
    (prefixCache 11 89030) (prefixPartial 11 89030) = false := by
  decide +kernel

theorem node_context_11_89030_1249255 : EJMOriginalGlobalDAGData.nodes 10 ⟨1249255, by decide⟩ =
    .split (coordinate 11) (![⟨1249046, by decide⟩,⟨1249117, by decide⟩,⟨1249184, by decide⟩,⟨1249254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89030_1249255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89030 ⟨1249255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89030
    ⟨1249255, by decide⟩ (by decide) (![⟨1249046, by decide⟩,⟨1249117, by decide⟩,⟨1249184, by decide⟩,⟨1249254, by decide⟩]) unmarked_context_11_89030_1249255 node_context_11_89030_1249255
  intro a
  fin_cases a
  · exact context_12_356120_1249046
  · exact context_12_356121_1249117
  · exact context_12_356122_1249184
  · exact context_12_356123_1249254

theorem selected_cut_45195 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 356124) = some ⟨12, 1, 0, 539296, 356124, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356124_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356124 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 356124 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 356124, 1, 65536⟩
    (by decide) selected_cut_45195

theorem selected_cut_45196 : selected 9 ⟨1249308, by decide⟩
    (prefixPartial 12 356125) = some ⟨12, 2, 0, 1249308, 356125, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_356125_1249308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356125 ⟨1249308, by decide⟩ :=
  accepted_of_selected 12 356125 ⟨1249308, by decide⟩ ⟨12, 2, 0, 1249308, 356125, 2677, 65536⟩
    (by decide) selected_cut_45196

theorem selected_cut_45197 : selected 9 ⟨1249365, by decide⟩
    (prefixPartial 12 356126) = some ⟨12, 2, 0, 1249365, 356126, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_356126_1249365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356126 ⟨1249365, by decide⟩ :=
  accepted_of_selected 12 356126 ⟨1249365, by decide⟩ ⟨12, 2, 0, 1249365, 356126, 3301, 65536⟩
    (by decide) selected_cut_45197

theorem selected_cut_45198 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 356127) = some ⟨12, 1, 0, 903806, 356127, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356127_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356127 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 356127 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 356127, 1, 65536⟩
    (by decide) selected_cut_45198

theorem unmarked_context_11_89031_1249366 : frontier 10 ⟨1249366, by decide⟩
    (prefixCache 11 89031) (prefixPartial 11 89031) = false := by
  decide +kernel

theorem node_context_11_89031_1249366 : EJMOriginalGlobalDAGData.nodes 10 ⟨1249366, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨1249308, by decide⟩,⟨1249365, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89031_1249366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89031 ⟨1249366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89031
    ⟨1249366, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨1249308, by decide⟩,⟨1249365, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_89031_1249366 node_context_11_89031_1249366
  intro a
  fin_cases a
  · exact context_12_356124_539296
  · exact context_12_356125_1249308
  · exact context_12_356126_1249365
  · exact context_12_356127_903806

theorem unmarked_context_10_22257_1249367 : frontier 11 ⟨1249367, by decide⟩
    (prefixCache 10 22257) (prefixPartial 10 22257) = false := by
  decide +kernel

theorem node_context_10_22257_1249367 : EJMOriginalGlobalDAGData.nodes 11 ⟨1249367, by decide⟩ =
    .split (coordinate 10) (![⟨1248895, by decide⟩,⟨1248968, by decide⟩,⟨1249255, by decide⟩,⟨1249366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22257_1249367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22257 ⟨1249367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22257
    ⟨1249367, by decide⟩ (by decide) (![⟨1248895, by decide⟩,⟨1248968, by decide⟩,⟨1249255, by decide⟩,⟨1249366, by decide⟩]) unmarked_context_10_22257_1249367 node_context_10_22257_1249367
  intro a
  fin_cases a
  · exact context_11_89028_1248895
  · exact context_11_89029_1248968
  · exact context_11_89030_1249255
  · exact context_11_89031_1249366

theorem selected_cut_45199 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 356128) = some ⟨12, 1, 0, 1187656, 356128, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356128_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356128 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 356128 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 356128, 1, 65536⟩
    (by decide) selected_cut_45199

theorem selected_cut_45200 : selected 9 ⟨1249426, by decide⟩
    (prefixPartial 12 356129) = some ⟨12, 2, 0, 1249426, 356129, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_356129_1249426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356129 ⟨1249426, by decide⟩ :=
  accepted_of_selected 12 356129 ⟨1249426, by decide⟩ ⟨12, 2, 0, 1249426, 356129, 2809, 65536⟩
    (by decide) selected_cut_45200

theorem selected_cut_45201 : selected 9 ⟨1249490, by decide⟩
    (prefixPartial 12 356130) = some ⟨12, 2, 0, 1249490, 356130, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_356130_1249490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356130 ⟨1249490, by decide⟩ :=
  accepted_of_selected 12 356130 ⟨1249490, by decide⟩ ⟨12, 2, 0, 1249490, 356130, 3157, 65536⟩
    (by decide) selected_cut_45201

theorem selected_cut_45202 : selected 9 ⟨1249556, by decide⟩
    (prefixPartial 12 356131) = some ⟨12, 2, 0, 1249556, 356131, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_356131_1249556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356131 ⟨1249556, by decide⟩ :=
  accepted_of_selected 12 356131 ⟨1249556, by decide⟩ ⟨12, 2, 0, 1249556, 356131, 3245, 65536⟩
    (by decide) selected_cut_45202

theorem unmarked_context_11_89032_1249557 : frontier 10 ⟨1249557, by decide⟩
    (prefixCache 11 89032) (prefixPartial 11 89032) = false := by
  decide +kernel

theorem node_context_11_89032_1249557 : EJMOriginalGlobalDAGData.nodes 10 ⟨1249557, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1249426, by decide⟩,⟨1249490, by decide⟩,⟨1249556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89032_1249557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89032 ⟨1249557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89032
    ⟨1249557, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1249426, by decide⟩,⟨1249490, by decide⟩,⟨1249556, by decide⟩]) unmarked_context_11_89032_1249557 node_context_11_89032_1249557
  intro a
  fin_cases a
  · exact context_12_356128_1187656
  · exact context_12_356129_1249426
  · exact context_12_356130_1249490
  · exact context_12_356131_1249556

theorem selected_cut_45203 : selected 9 ⟨1249623, by decide⟩
    (prefixPartial 12 356132) = some ⟨12, 2, 0, 1249623, 356132, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_356132_1249623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356132 ⟨1249623, by decide⟩ :=
  accepted_of_selected 12 356132 ⟨1249623, by decide⟩ ⟨12, 2, 0, 1249623, 356132, 2973, 65536⟩
    (by decide) selected_cut_45203

theorem selected_cut_45204 : selected 9 ⟨1249682, by decide⟩
    (prefixPartial 12 356133) = some ⟨12, 2, 0, 1249682, 356133, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_356133_1249682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356133 ⟨1249682, by decide⟩ :=
  accepted_of_selected 12 356133 ⟨1249682, by decide⟩ ⟨12, 2, 0, 1249682, 356133, 2629, 65536⟩
    (by decide) selected_cut_45204

theorem selected_cut_45205 : selected 9 ⟨1249735, by decide⟩
    (prefixPartial 12 356134) = some ⟨12, 2, 0, 1249735, 356134, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_356134_1249735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356134 ⟨1249735, by decide⟩ :=
  accepted_of_selected 12 356134 ⟨1249735, by decide⟩ ⟨12, 2, 0, 1249735, 356134, 2657, 65536⟩
    (by decide) selected_cut_45205

theorem selected_cut_45206 : selected 9 ⟨1249805, by decide⟩
    (prefixPartial 12 356135) = some ⟨12, 2, 0, 1249805, 356135, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_356135_1249805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356135 ⟨1249805, by decide⟩ :=
  accepted_of_selected 12 356135 ⟨1249805, by decide⟩ ⟨12, 2, 0, 1249805, 356135, 2989, 65536⟩
    (by decide) selected_cut_45206

theorem unmarked_context_11_89033_1249806 : frontier 10 ⟨1249806, by decide⟩
    (prefixCache 11 89033) (prefixPartial 11 89033) = false := by
  decide +kernel

theorem node_context_11_89033_1249806 : EJMOriginalGlobalDAGData.nodes 10 ⟨1249806, by decide⟩ =
    .split (coordinate 11) (![⟨1249623, by decide⟩,⟨1249682, by decide⟩,⟨1249735, by decide⟩,⟨1249805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89033_1249806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89033 ⟨1249806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89033
    ⟨1249806, by decide⟩ (by decide) (![⟨1249623, by decide⟩,⟨1249682, by decide⟩,⟨1249735, by decide⟩,⟨1249805, by decide⟩]) unmarked_context_11_89033_1249806 node_context_11_89033_1249806
  intro a
  fin_cases a
  · exact context_12_356132_1249623
  · exact context_12_356133_1249682
  · exact context_12_356134_1249735
  · exact context_12_356135_1249805

theorem selected_cut_45207 : selected 9 ⟨1249870, by decide⟩
    (prefixPartial 12 356136) = some ⟨12, 2, 0, 1249870, 356136, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_356136_1249870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356136 ⟨1249870, by decide⟩ :=
  accepted_of_selected 12 356136 ⟨1249870, by decide⟩ ⟨12, 2, 0, 1249870, 356136, 2785, 65536⟩
    (by decide) selected_cut_45207

theorem selected_cut_45208 : selected 9 ⟨1249928, by decide⟩
    (prefixPartial 12 356137) = some ⟨12, 2, 0, 1249928, 356137, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_356137_1249928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356137 ⟨1249928, by decide⟩ :=
  accepted_of_selected 12 356137 ⟨1249928, by decide⟩ ⟨12, 2, 0, 1249928, 356137, 2633, 65536⟩
    (by decide) selected_cut_45208

theorem selected_cut_45209 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 356138) = some ⟨12, 1, 0, 1172910, 356138, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356138_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356138 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 356138 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 356138, 1, 65536⟩
    (by decide) selected_cut_45209

theorem selected_cut_45210 : selected 9 ⟨1250050, by decide⟩
    (prefixPartial 12 356139) = some ⟨12, 2, 0, 1250050, 356139, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_356139_1250050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356139 ⟨1250050, by decide⟩ :=
  accepted_of_selected 12 356139 ⟨1250050, by decide⟩ ⟨12, 2, 0, 1250050, 356139, 1585, 65536⟩
    (by decide) selected_cut_45210

theorem unmarked_context_11_89034_1250051 : frontier 10 ⟨1250051, by decide⟩
    (prefixCache 11 89034) (prefixPartial 11 89034) = false := by
  decide +kernel

theorem node_context_11_89034_1250051 : EJMOriginalGlobalDAGData.nodes 10 ⟨1250051, by decide⟩ =
    .split (coordinate 11) (![⟨1249870, by decide⟩,⟨1249928, by decide⟩,⟨1172910, by decide⟩,⟨1250050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89034_1250051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89034 ⟨1250051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89034
    ⟨1250051, by decide⟩ (by decide) (![⟨1249870, by decide⟩,⟨1249928, by decide⟩,⟨1172910, by decide⟩,⟨1250050, by decide⟩]) unmarked_context_11_89034_1250051 node_context_11_89034_1250051
  intro a
  fin_cases a
  · exact context_12_356136_1249870
  · exact context_12_356137_1249928
  · exact context_12_356138_1172910
  · exact context_12_356139_1250050

theorem selected_cut_45211 : selected 9 ⟨1250098, by decide⟩
    (prefixPartial 12 356140) = some ⟨12, 2, 0, 1250098, 356140, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_356140_1250098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356140 ⟨1250098, by decide⟩ :=
  accepted_of_selected 12 356140 ⟨1250098, by decide⟩ ⟨12, 2, 0, 1250098, 356140, 2373, 65536⟩
    (by decide) selected_cut_45211

theorem selected_cut_45212 : selected 9 ⟨1250135, by decide⟩
    (prefixPartial 12 356141) = some ⟨12, 2, 0, 1250135, 356141, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_356141_1250135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356141 ⟨1250135, by decide⟩ :=
  accepted_of_selected 12 356141 ⟨1250135, by decide⟩ ⟨12, 2, 0, 1250135, 356141, 2189, 65536⟩
    (by decide) selected_cut_45212

theorem selected_cut_45213 : selected 9 ⟨1250191, by decide⟩
    (prefixPartial 12 356142) = some ⟨12, 2, 0, 1250191, 356142, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_356142_1250191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356142 ⟨1250191, by decide⟩ :=
  accepted_of_selected 12 356142 ⟨1250191, by decide⟩ ⟨12, 2, 0, 1250191, 356142, 2541, 65536⟩
    (by decide) selected_cut_45213

theorem selected_cut_45214 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 356143) = some ⟨12, 1, 0, 903806, 356143, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356143_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356143 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 356143 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 356143, 1, 65536⟩
    (by decide) selected_cut_45214

theorem unmarked_context_11_89035_1250192 : frontier 10 ⟨1250192, by decide⟩
    (prefixCache 11 89035) (prefixPartial 11 89035) = false := by
  decide +kernel

theorem node_context_11_89035_1250192 : EJMOriginalGlobalDAGData.nodes 10 ⟨1250192, by decide⟩ =
    .split (coordinate 11) (![⟨1250098, by decide⟩,⟨1250135, by decide⟩,⟨1250191, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89035_1250192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89035 ⟨1250192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89035
    ⟨1250192, by decide⟩ (by decide) (![⟨1250098, by decide⟩,⟨1250135, by decide⟩,⟨1250191, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_89035_1250192 node_context_11_89035_1250192
  intro a
  fin_cases a
  · exact context_12_356140_1250098
  · exact context_12_356141_1250135
  · exact context_12_356142_1250191
  · exact context_12_356143_903806

theorem unmarked_context_10_22258_1250193 : frontier 11 ⟨1250193, by decide⟩
    (prefixCache 10 22258) (prefixPartial 10 22258) = false := by
  decide +kernel

theorem node_context_10_22258_1250193 : EJMOriginalGlobalDAGData.nodes 11 ⟨1250193, by decide⟩ =
    .split (coordinate 10) (![⟨1249557, by decide⟩,⟨1249806, by decide⟩,⟨1250051, by decide⟩,⟨1250192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22258_1250193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22258 ⟨1250193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22258
    ⟨1250193, by decide⟩ (by decide) (![⟨1249557, by decide⟩,⟨1249806, by decide⟩,⟨1250051, by decide⟩,⟨1250192, by decide⟩]) unmarked_context_10_22258_1250193 node_context_10_22258_1250193
  intro a
  fin_cases a
  · exact context_11_89032_1249557
  · exact context_11_89033_1249806
  · exact context_11_89034_1250051
  · exact context_11_89035_1250192

theorem selected_cut_45215 : selected 9 ⟨399079, by decide⟩
    (prefixPartial 12 356144) = some ⟨12, 1, 0, 399079, 356144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356144_399079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356144 ⟨399079, by decide⟩ :=
  accepted_of_selected 12 356144 ⟨399079, by decide⟩ ⟨12, 1, 0, 399079, 356144, 1, 65536⟩
    (by decide) selected_cut_45215

theorem selected_cut_45216 : selected 9 ⟨1250242, by decide⟩
    (prefixPartial 12 356145) = some ⟨12, 2, 0, 1250242, 356145, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_356145_1250242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356145 ⟨1250242, by decide⟩ :=
  accepted_of_selected 12 356145 ⟨1250242, by decide⟩ ⟨12, 2, 0, 1250242, 356145, 2197, 65536⟩
    (by decide) selected_cut_45216

theorem selected_cut_45217 : selected 9 ⟨1250301, by decide⟩
    (prefixPartial 12 356146) = some ⟨12, 2, 0, 1250301, 356146, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_356146_1250301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356146 ⟨1250301, by decide⟩ :=
  accepted_of_selected 12 356146 ⟨1250301, by decide⟩ ⟨12, 2, 0, 1250301, 356146, 2521, 65536⟩
    (by decide) selected_cut_45217

theorem selected_cut_45218 : selected 9 ⟨1250356, by decide⟩
    (prefixPartial 12 356147) = some ⟨12, 2, 0, 1250356, 356147, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_356147_1250356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356147 ⟨1250356, by decide⟩ :=
  accepted_of_selected 12 356147 ⟨1250356, by decide⟩ ⟨12, 2, 0, 1250356, 356147, 2373, 65536⟩
    (by decide) selected_cut_45218

theorem unmarked_context_11_89036_1250357 : frontier 10 ⟨1250357, by decide⟩
    (prefixCache 11 89036) (prefixPartial 11 89036) = false := by
  decide +kernel

theorem node_context_11_89036_1250357 : EJMOriginalGlobalDAGData.nodes 10 ⟨1250357, by decide⟩ =
    .split (coordinate 11) (![⟨399079, by decide⟩,⟨1250242, by decide⟩,⟨1250301, by decide⟩,⟨1250356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89036_1250357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89036 ⟨1250357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89036
    ⟨1250357, by decide⟩ (by decide) (![⟨399079, by decide⟩,⟨1250242, by decide⟩,⟨1250301, by decide⟩,⟨1250356, by decide⟩]) unmarked_context_11_89036_1250357 node_context_11_89036_1250357
  intro a
  fin_cases a
  · exact context_12_356144_399079
  · exact context_12_356145_1250242
  · exact context_12_356146_1250301
  · exact context_12_356147_1250356

theorem selected_cut_45219 : selected 9 ⟨1250420, by decide⟩
    (prefixPartial 12 356148) = some ⟨12, 2, 0, 1250420, 356148, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_356148_1250420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356148 ⟨1250420, by decide⟩ :=
  accepted_of_selected 12 356148 ⟨1250420, by decide⟩ ⟨12, 2, 0, 1250420, 356148, 2429, 65536⟩
    (by decide) selected_cut_45219

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
