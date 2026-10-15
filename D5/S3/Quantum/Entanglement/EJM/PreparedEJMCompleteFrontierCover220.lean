/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover219
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21123 : selected 8 ⟨540911, by decide⟩
    (prefixPartial 13 299244) = some ⟨13, 2, 0, 540911, 299244, 213, 16384⟩ := by
  decide +kernel

theorem context_13_299244_540911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299244 ⟨540911, by decide⟩ :=
  accepted_of_selected 13 299244 ⟨540911, by decide⟩ ⟨13, 2, 0, 540911, 299244, 213, 16384⟩
    (by decide) selected_cut_21123

theorem selected_cut_21124 : selected 8 ⟨540940, by decide⟩
    (prefixPartial 13 299245) = some ⟨13, 2, 0, 540940, 299245, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_299245_540940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299245 ⟨540940, by decide⟩ :=
  accepted_of_selected 13 299245 ⟨540940, by decide⟩ ⟨13, 2, 0, 540940, 299245, 2801, 16384⟩
    (by decide) selected_cut_21124

theorem selected_cut_21125 : selected 8 ⟨540966, by decide⟩
    (prefixPartial 13 299246) = some ⟨13, 2, 0, 540966, 299246, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_299246_540966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299246 ⟨540966, by decide⟩ :=
  accepted_of_selected 13 299246 ⟨540966, by decide⟩ ⟨13, 2, 0, 540966, 299246, 1829, 16384⟩
    (by decide) selected_cut_21125

theorem selected_cut_21126 : selected 8 ⟨540976, by decide⟩
    (prefixPartial 13 299247) = some ⟨13, 2, 0, 540976, 299247, 885, 16384⟩ := by
  decide +kernel

theorem context_13_299247_540976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299247 ⟨540976, by decide⟩ :=
  accepted_of_selected 13 299247 ⟨540976, by decide⟩ ⟨13, 2, 0, 540976, 299247, 885, 16384⟩
    (by decide) selected_cut_21126

theorem unmarked_context_12_74811_540977 : frontier 9 ⟨540977, by decide⟩
    (prefixCache 12 74811) (prefixPartial 12 74811) = false := by
  decide +kernel

theorem node_context_12_74811_540977 : EJMOriginalGlobalDAGData.nodes 9 ⟨540977, by decide⟩ =
    .split (coordinate 12) (![⟨540911, by decide⟩,⟨540940, by decide⟩,⟨540966, by decide⟩,⟨540976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74811_540977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74811 ⟨540977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74811
    ⟨540977, by decide⟩ (by decide) (![⟨540911, by decide⟩,⟨540940, by decide⟩,⟨540966, by decide⟩,⟨540976, by decide⟩]) unmarked_context_12_74811_540977 node_context_12_74811_540977
  intro a
  fin_cases a
  · exact context_13_299244_540911
  · exact context_13_299245_540940
  · exact context_13_299246_540966
  · exact context_13_299247_540976

theorem unmarked_context_11_18702_540978 : frontier 10 ⟨540978, by decide⟩
    (prefixCache 11 18702) (prefixPartial 11 18702) = false := by
  decide +kernel

theorem node_context_11_18702_540978 : EJMOriginalGlobalDAGData.nodes 10 ⟨540978, by decide⟩ =
    .split (coordinate 11) (![⟨540780, by decide⟩,⟨540852, by decide⟩,⟨540906, by decide⟩,⟨540977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18702_540978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18702 ⟨540978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18702
    ⟨540978, by decide⟩ (by decide) (![⟨540780, by decide⟩,⟨540852, by decide⟩,⟨540906, by decide⟩,⟨540977, by decide⟩]) unmarked_context_11_18702_540978 node_context_11_18702_540978
  intro a
  fin_cases a
  · exact context_12_74808_540780
  · exact context_12_74809_540852
  · exact context_12_74810_540906
  · exact context_12_74811_540977

theorem selected_cut_21127 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 74812) = some ⟨12, 1, 0, 445562, 74812, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74812_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74812 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 74812 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 74812, 1, 65536⟩
    (by decide) selected_cut_21127

theorem selected_cut_21128 : selected 8 ⟨540981, by decide⟩
    (prefixPartial 13 299252) = some ⟨13, 2, 0, 540981, 299252, 129, 16384⟩ := by
  decide +kernel

theorem context_13_299252_540981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299252 ⟨540981, by decide⟩ :=
  accepted_of_selected 13 299252 ⟨540981, by decide⟩ ⟨13, 2, 0, 540981, 299252, 129, 16384⟩
    (by decide) selected_cut_21128

theorem selected_cut_21129 : selected 8 ⟨541013, by decide⟩
    (prefixPartial 13 299253) = some ⟨13, 2, 0, 541013, 299253, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_299253_541013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299253 ⟨541013, by decide⟩ :=
  accepted_of_selected 13 299253 ⟨541013, by decide⟩ ⟨13, 2, 0, 541013, 299253, 2545, 16384⟩
    (by decide) selected_cut_21129

theorem selected_cut_21130 : selected 8 ⟨541032, by decide⟩
    (prefixPartial 13 299254) = some ⟨13, 2, 0, 541032, 299254, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_299254_541032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299254 ⟨541032, by decide⟩ :=
  accepted_of_selected 13 299254 ⟨541032, by decide⟩ ⟨13, 2, 0, 541032, 299254, 1593, 16384⟩
    (by decide) selected_cut_21130

theorem selected_cut_21131 : selected 8 ⟨541036, by decide⟩
    (prefixPartial 13 299255) = some ⟨13, 2, 0, 541036, 299255, 705, 16384⟩ := by
  decide +kernel

theorem context_13_299255_541036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299255 ⟨541036, by decide⟩ :=
  accepted_of_selected 13 299255 ⟨541036, by decide⟩ ⟨13, 2, 0, 541036, 299255, 705, 16384⟩
    (by decide) selected_cut_21131

theorem unmarked_context_12_74813_541037 : frontier 9 ⟨541037, by decide⟩
    (prefixCache 12 74813) (prefixPartial 12 74813) = false := by
  decide +kernel

theorem node_context_12_74813_541037 : EJMOriginalGlobalDAGData.nodes 9 ⟨541037, by decide⟩ =
    .split (coordinate 12) (![⟨540981, by decide⟩,⟨541013, by decide⟩,⟨541032, by decide⟩,⟨541036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74813_541037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74813 ⟨541037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74813
    ⟨541037, by decide⟩ (by decide) (![⟨540981, by decide⟩,⟨541013, by decide⟩,⟨541032, by decide⟩,⟨541036, by decide⟩]) unmarked_context_12_74813_541037 node_context_12_74813_541037
  intro a
  fin_cases a
  · exact context_13_299252_540981
  · exact context_13_299253_541013
  · exact context_13_299254_541032
  · exact context_13_299255_541036

theorem selected_cut_21132 : selected 8 ⟨541041, by decide⟩
    (prefixPartial 13 299256) = some ⟨13, 2, 0, 541041, 299256, 85, 16384⟩ := by
  decide +kernel

theorem context_13_299256_541041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299256 ⟨541041, by decide⟩ :=
  accepted_of_selected 13 299256 ⟨541041, by decide⟩ ⟨13, 2, 0, 541041, 299256, 85, 16384⟩
    (by decide) selected_cut_21132

theorem selected_cut_21133 : selected 8 ⟨541069, by decide⟩
    (prefixPartial 13 299257) = some ⟨13, 2, 0, 541069, 299257, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_299257_541069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299257 ⟨541069, by decide⟩ :=
  accepted_of_selected 13 299257 ⟨541069, by decide⟩ ⟨13, 2, 0, 541069, 299257, 2601, 16384⟩
    (by decide) selected_cut_21133

theorem selected_cut_21134 : selected 8 ⟨541087, by decide⟩
    (prefixPartial 13 299258) = some ⟨13, 2, 0, 541087, 299258, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_299258_541087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299258 ⟨541087, by decide⟩ :=
  accepted_of_selected 13 299258 ⟨541087, by decide⟩ ⟨13, 2, 0, 541087, 299258, 1481, 16384⟩
    (by decide) selected_cut_21134

theorem selected_cut_21135 : selected 8 ⟨541093, by decide⟩
    (prefixPartial 13 299259) = some ⟨13, 2, 0, 541093, 299259, 817, 16384⟩ := by
  decide +kernel

theorem context_13_299259_541093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299259 ⟨541093, by decide⟩ :=
  accepted_of_selected 13 299259 ⟨541093, by decide⟩ ⟨13, 2, 0, 541093, 299259, 817, 16384⟩
    (by decide) selected_cut_21135

theorem unmarked_context_12_74814_541094 : frontier 9 ⟨541094, by decide⟩
    (prefixCache 12 74814) (prefixPartial 12 74814) = false := by
  decide +kernel

theorem node_context_12_74814_541094 : EJMOriginalGlobalDAGData.nodes 9 ⟨541094, by decide⟩ =
    .split (coordinate 12) (![⟨541041, by decide⟩,⟨541069, by decide⟩,⟨541087, by decide⟩,⟨541093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74814_541094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74814 ⟨541094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74814
    ⟨541094, by decide⟩ (by decide) (![⟨541041, by decide⟩,⟨541069, by decide⟩,⟨541087, by decide⟩,⟨541093, by decide⟩]) unmarked_context_12_74814_541094 node_context_12_74814_541094
  intro a
  fin_cases a
  · exact context_13_299256_541041
  · exact context_13_299257_541069
  · exact context_13_299258_541087
  · exact context_13_299259_541093

theorem selected_cut_21136 : selected 8 ⟨541097, by decide⟩
    (prefixPartial 13 299260) = some ⟨13, 2, 0, 541097, 299260, 49, 16384⟩ := by
  decide +kernel

theorem context_13_299260_541097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299260 ⟨541097, by decide⟩ :=
  accepted_of_selected 13 299260 ⟨541097, by decide⟩ ⟨13, 2, 0, 541097, 299260, 49, 16384⟩
    (by decide) selected_cut_21136

theorem selected_cut_21137 : selected 8 ⟨541130, by decide⟩
    (prefixPartial 13 299261) = some ⟨13, 2, 0, 541130, 299261, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_299261_541130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299261 ⟨541130, by decide⟩ :=
  accepted_of_selected 13 299261 ⟨541130, by decide⟩ ⟨13, 2, 0, 541130, 299261, 2665, 16384⟩
    (by decide) selected_cut_21137

theorem selected_cut_21138 : selected 8 ⟨541153, by decide⟩
    (prefixPartial 13 299262) = some ⟨13, 2, 0, 541153, 299262, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_299262_541153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299262 ⟨541153, by decide⟩ :=
  accepted_of_selected 13 299262 ⟨541153, by decide⟩ ⟨13, 2, 0, 541153, 299262, 1717, 16384⟩
    (by decide) selected_cut_21138

theorem selected_cut_21139 : selected 8 ⟨541161, by decide⟩
    (prefixPartial 13 299263) = some ⟨13, 2, 0, 541161, 299263, 761, 16384⟩ := by
  decide +kernel

theorem context_13_299263_541161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299263 ⟨541161, by decide⟩ :=
  accepted_of_selected 13 299263 ⟨541161, by decide⟩ ⟨13, 2, 0, 541161, 299263, 761, 16384⟩
    (by decide) selected_cut_21139

theorem unmarked_context_12_74815_541162 : frontier 9 ⟨541162, by decide⟩
    (prefixCache 12 74815) (prefixPartial 12 74815) = false := by
  decide +kernel

theorem node_context_12_74815_541162 : EJMOriginalGlobalDAGData.nodes 9 ⟨541162, by decide⟩ =
    .split (coordinate 12) (![⟨541097, by decide⟩,⟨541130, by decide⟩,⟨541153, by decide⟩,⟨541161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74815_541162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74815 ⟨541162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74815
    ⟨541162, by decide⟩ (by decide) (![⟨541097, by decide⟩,⟨541130, by decide⟩,⟨541153, by decide⟩,⟨541161, by decide⟩]) unmarked_context_12_74815_541162 node_context_12_74815_541162
  intro a
  fin_cases a
  · exact context_13_299260_541097
  · exact context_13_299261_541130
  · exact context_13_299262_541153
  · exact context_13_299263_541161

theorem unmarked_context_11_18703_541163 : frontier 10 ⟨541163, by decide⟩
    (prefixCache 11 18703) (prefixPartial 11 18703) = false := by
  decide +kernel

theorem node_context_11_18703_541163 : EJMOriginalGlobalDAGData.nodes 10 ⟨541163, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨541037, by decide⟩,⟨541094, by decide⟩,⟨541162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18703_541163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18703 ⟨541163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18703
    ⟨541163, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨541037, by decide⟩,⟨541094, by decide⟩,⟨541162, by decide⟩]) unmarked_context_11_18703_541163 node_context_11_18703_541163
  intro a
  fin_cases a
  · exact context_12_74812_445562
  · exact context_12_74813_541037
  · exact context_12_74814_541094
  · exact context_12_74815_541162

theorem unmarked_context_10_4675_541164 : frontier 11 ⟨541164, by decide⟩
    (prefixCache 10 4675) (prefixPartial 10 4675) = false := by
  decide +kernel

theorem node_context_10_4675_541164 : EJMOriginalGlobalDAGData.nodes 11 ⟨541164, by decide⟩ =
    .split (coordinate 10) (![⟨540577, by decide⟩,⟨540779, by decide⟩,⟨540978, by decide⟩,⟨541163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4675_541164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4675 ⟨541164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4675
    ⟨541164, by decide⟩ (by decide) (![⟨540577, by decide⟩,⟨540779, by decide⟩,⟨540978, by decide⟩,⟨541163, by decide⟩]) unmarked_context_10_4675_541164 node_context_10_4675_541164
  intro a
  fin_cases a
  · exact context_11_18700_540577
  · exact context_11_18701_540779
  · exact context_11_18702_540978
  · exact context_11_18703_541163

theorem unmarked_context_9_1168_541165 : frontier 12 ⟨541165, by decide⟩
    (prefixCache 9 1168) (prefixPartial 9 1168) = false := by
  decide +kernel

theorem node_context_9_1168_541165 : EJMOriginalGlobalDAGData.nodes 12 ⟨541165, by decide⟩ =
    .split (coordinate 9) (![⟨538560, by decide⟩,⟨539548, by decide⟩,⟨540410, by decide⟩,⟨541164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1168_541165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1168 ⟨541165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1168
    ⟨541165, by decide⟩ (by decide) (![⟨538560, by decide⟩,⟨539548, by decide⟩,⟨540410, by decide⟩,⟨541164, by decide⟩]) unmarked_context_9_1168_541165 node_context_9_1168_541165
  intro a
  fin_cases a
  · exact context_10_4672_538560
  · exact context_10_4673_539548
  · exact context_10_4674_540410
  · exact context_10_4675_541164

theorem selected_cut_21140 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 74816) = some ⟨12, 1, 0, 450982, 74816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74816_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74816 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 74816 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 74816, 1, 65536⟩
    (by decide) selected_cut_21140

theorem selected_cut_21141 : selected 9 ⟨541209, by decide⟩
    (prefixPartial 12 74817) = some ⟨12, 2, 0, 541209, 74817, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_74817_541209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74817 ⟨541209, by decide⟩ :=
  accepted_of_selected 12 74817 ⟨541209, by decide⟩ ⟨12, 2, 0, 541209, 74817, 3533, 65536⟩
    (by decide) selected_cut_21141

theorem selected_cut_21142 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299272) = some ⟨13, 1, 0, 3444, 299272, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299272_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299272 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299272 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299272, 1, 16384⟩
    (by decide) selected_cut_21142

theorem selected_cut_21143 : selected 8 ⟨541238, by decide⟩
    (prefixPartial 13 299273) = some ⟨13, 2, 0, 541238, 299273, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_299273_541238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299273 ⟨541238, by decide⟩ :=
  accepted_of_selected 13 299273 ⟨541238, by decide⟩ ⟨13, 2, 0, 541238, 299273, 2089, 16384⟩
    (by decide) selected_cut_21143

theorem selected_cut_21144 : selected 8 ⟨541254, by decide⟩
    (prefixPartial 13 299274) = some ⟨13, 2, 0, 541254, 299274, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_299274_541254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299274 ⟨541254, by decide⟩ :=
  accepted_of_selected 13 299274 ⟨541254, by decide⟩ ⟨13, 2, 0, 541254, 299274, 1277, 16384⟩
    (by decide) selected_cut_21144

theorem selected_cut_21145 : selected 8 ⟨541262, by decide⟩
    (prefixPartial 13 299275) = some ⟨13, 2, 0, 541262, 299275, 741, 16384⟩ := by
  decide +kernel

theorem context_13_299275_541262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299275 ⟨541262, by decide⟩ :=
  accepted_of_selected 13 299275 ⟨541262, by decide⟩ ⟨13, 2, 0, 541262, 299275, 741, 16384⟩
    (by decide) selected_cut_21145

theorem unmarked_context_12_74818_541263 : frontier 9 ⟨541263, by decide⟩
    (prefixCache 12 74818) (prefixPartial 12 74818) = false := by
  decide +kernel

theorem node_context_12_74818_541263 : EJMOriginalGlobalDAGData.nodes 9 ⟨541263, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541238, by decide⟩,⟨541254, by decide⟩,⟨541262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74818_541263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74818 ⟨541263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74818
    ⟨541263, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541238, by decide⟩,⟨541254, by decide⟩,⟨541262, by decide⟩]) unmarked_context_12_74818_541263 node_context_12_74818_541263
  intro a
  fin_cases a
  · exact context_13_299272_3444
  · exact context_13_299273_541238
  · exact context_13_299274_541254
  · exact context_13_299275_541262

theorem selected_cut_21146 : selected 9 ⟨541311, by decide⟩
    (prefixPartial 12 74819) = some ⟨12, 2, 0, 541311, 74819, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_74819_541311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74819 ⟨541311, by decide⟩ :=
  accepted_of_selected 12 74819 ⟨541311, by decide⟩ ⟨12, 2, 0, 541311, 74819, 3881, 65536⟩
    (by decide) selected_cut_21146

theorem unmarked_context_11_18704_541312 : frontier 10 ⟨541312, by decide⟩
    (prefixCache 11 18704) (prefixPartial 11 18704) = false := by
  decide +kernel

theorem node_context_11_18704_541312 : EJMOriginalGlobalDAGData.nodes 10 ⟨541312, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨541209, by decide⟩,⟨541263, by decide⟩,⟨541311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18704_541312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18704 ⟨541312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18704
    ⟨541312, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨541209, by decide⟩,⟨541263, by decide⟩,⟨541311, by decide⟩]) unmarked_context_11_18704_541312 node_context_11_18704_541312
  intro a
  fin_cases a
  · exact context_12_74816_450982
  · exact context_12_74817_541209
  · exact context_12_74818_541263
  · exact context_12_74819_541311

theorem selected_cut_21147 : selected 9 ⟨541353, by decide⟩
    (prefixPartial 12 74820) = some ⟨12, 2, 0, 541353, 74820, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_74820_541353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74820 ⟨541353, by decide⟩ :=
  accepted_of_selected 12 74820 ⟨541353, by decide⟩ ⟨12, 2, 0, 541353, 74820, 2889, 65536⟩
    (by decide) selected_cut_21147

theorem selected_cut_21148 : selected 9 ⟨541396, by decide⟩
    (prefixPartial 12 74821) = some ⟨12, 2, 0, 541396, 74821, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_74821_541396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74821 ⟨541396, by decide⟩ :=
  accepted_of_selected 12 74821 ⟨541396, by decide⟩ ⟨12, 2, 0, 541396, 74821, 3465, 65536⟩
    (by decide) selected_cut_21148

theorem selected_cut_21149 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299288) = some ⟨13, 1, 0, 3444, 299288, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299288_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299288 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299288 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299288, 1, 16384⟩
    (by decide) selected_cut_21149

theorem selected_cut_21150 : selected 8 ⟨541429, by decide⟩
    (prefixPartial 13 299289) = some ⟨13, 2, 0, 541429, 299289, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_299289_541429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299289 ⟨541429, by decide⟩ :=
  accepted_of_selected 13 299289 ⟨541429, by decide⟩ ⟨13, 2, 0, 541429, 299289, 2001, 16384⟩
    (by decide) selected_cut_21150

theorem selected_cut_21151 : selected 8 ⟨541447, by decide⟩
    (prefixPartial 13 299290) = some ⟨13, 2, 0, 541447, 299290, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_299290_541447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299290 ⟨541447, by decide⟩ :=
  accepted_of_selected 13 299290 ⟨541447, by decide⟩ ⟨13, 2, 0, 541447, 299290, 1361, 16384⟩
    (by decide) selected_cut_21151

theorem selected_cut_21152 : selected 8 ⟨541457, by decide⟩
    (prefixPartial 13 299291) = some ⟨13, 2, 0, 541457, 299291, 853, 16384⟩ := by
  decide +kernel

theorem context_13_299291_541457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299291 ⟨541457, by decide⟩ :=
  accepted_of_selected 13 299291 ⟨541457, by decide⟩ ⟨13, 2, 0, 541457, 299291, 853, 16384⟩
    (by decide) selected_cut_21152

theorem unmarked_context_12_74822_541458 : frontier 9 ⟨541458, by decide⟩
    (prefixCache 12 74822) (prefixPartial 12 74822) = false := by
  decide +kernel

theorem node_context_12_74822_541458 : EJMOriginalGlobalDAGData.nodes 9 ⟨541458, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541429, by decide⟩,⟨541447, by decide⟩,⟨541457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74822_541458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74822 ⟨541458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74822
    ⟨541458, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541429, by decide⟩,⟨541447, by decide⟩,⟨541457, by decide⟩]) unmarked_context_12_74822_541458 node_context_12_74822_541458
  intro a
  fin_cases a
  · exact context_13_299288_3444
  · exact context_13_299289_541429
  · exact context_13_299290_541447
  · exact context_13_299291_541457

theorem selected_cut_21153 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299292) = some ⟨13, 1, 0, 3444, 299292, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299292_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299292 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299292 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299292, 1, 16384⟩
    (by decide) selected_cut_21153

theorem selected_cut_21154 : selected 8 ⟨541484, by decide⟩
    (prefixPartial 13 299293) = some ⟨13, 2, 0, 541484, 299293, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_299293_541484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299293 ⟨541484, by decide⟩ :=
  accepted_of_selected 13 299293 ⟨541484, by decide⟩ ⟨13, 2, 0, 541484, 299293, 1873, 16384⟩
    (by decide) selected_cut_21154

theorem selected_cut_21155 : selected 8 ⟨541503, by decide⟩
    (prefixPartial 13 299294) = some ⟨13, 2, 0, 541503, 299294, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_299294_541503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299294 ⟨541503, by decide⟩ :=
  accepted_of_selected 13 299294 ⟨541503, by decide⟩ ⟨13, 2, 0, 541503, 299294, 1613, 16384⟩
    (by decide) selected_cut_21155

theorem selected_cut_21156 : selected 8 ⟨541507, by decide⟩
    (prefixPartial 13 299295) = some ⟨13, 2, 0, 541507, 299295, 657, 16384⟩ := by
  decide +kernel

theorem context_13_299295_541507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299295 ⟨541507, by decide⟩ :=
  accepted_of_selected 13 299295 ⟨541507, by decide⟩ ⟨13, 2, 0, 541507, 299295, 657, 16384⟩
    (by decide) selected_cut_21156

theorem unmarked_context_12_74823_541508 : frontier 9 ⟨541508, by decide⟩
    (prefixCache 12 74823) (prefixPartial 12 74823) = false := by
  decide +kernel

theorem node_context_12_74823_541508 : EJMOriginalGlobalDAGData.nodes 9 ⟨541508, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541484, by decide⟩,⟨541503, by decide⟩,⟨541507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74823_541508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74823 ⟨541508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74823
    ⟨541508, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541484, by decide⟩,⟨541503, by decide⟩,⟨541507, by decide⟩]) unmarked_context_12_74823_541508 node_context_12_74823_541508
  intro a
  fin_cases a
  · exact context_13_299292_3444
  · exact context_13_299293_541484
  · exact context_13_299294_541503
  · exact context_13_299295_541507

theorem unmarked_context_11_18705_541509 : frontier 10 ⟨541509, by decide⟩
    (prefixCache 11 18705) (prefixPartial 11 18705) = false := by
  decide +kernel

theorem node_context_11_18705_541509 : EJMOriginalGlobalDAGData.nodes 10 ⟨541509, by decide⟩ =
    .split (coordinate 11) (![⟨541353, by decide⟩,⟨541396, by decide⟩,⟨541458, by decide⟩,⟨541508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18705_541509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18705 ⟨541509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18705
    ⟨541509, by decide⟩ (by decide) (![⟨541353, by decide⟩,⟨541396, by decide⟩,⟨541458, by decide⟩,⟨541508, by decide⟩]) unmarked_context_11_18705_541509 node_context_11_18705_541509
  intro a
  fin_cases a
  · exact context_12_74820_541353
  · exact context_12_74821_541396
  · exact context_12_74822_541458
  · exact context_12_74823_541508

theorem selected_cut_21157 : selected 9 ⟨541548, by decide⟩
    (prefixPartial 12 74824) = some ⟨12, 2, 0, 541548, 74824, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_74824_541548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74824 ⟨541548, by decide⟩ :=
  accepted_of_selected 12 74824 ⟨541548, by decide⟩ ⟨12, 2, 0, 541548, 74824, 3369, 65536⟩
    (by decide) selected_cut_21157

theorem selected_cut_21158 : selected 9 ⟨541601, by decide⟩
    (prefixPartial 12 74825) = some ⟨12, 2, 0, 541601, 74825, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_74825_541601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74825 ⟨541601, by decide⟩ :=
  accepted_of_selected 12 74825 ⟨541601, by decide⟩ ⟨12, 2, 0, 541601, 74825, 4021, 65536⟩
    (by decide) selected_cut_21158

theorem selected_cut_21159 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299304) = some ⟨13, 1, 0, 3444, 299304, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299304_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299304 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299304 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299304, 1, 16384⟩
    (by decide) selected_cut_21159

theorem selected_cut_21160 : selected 8 ⟨541624, by decide⟩
    (prefixPartial 13 299305) = some ⟨13, 2, 0, 541624, 299305, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_299305_541624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299305 ⟨541624, by decide⟩ :=
  accepted_of_selected 13 299305 ⟨541624, by decide⟩ ⟨13, 2, 0, 541624, 299305, 1881, 16384⟩
    (by decide) selected_cut_21160

theorem selected_cut_21161 : selected 8 ⟨541645, by decide⟩
    (prefixPartial 13 299306) = some ⟨13, 2, 0, 541645, 299306, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_299306_541645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299306 ⟨541645, by decide⟩ :=
  accepted_of_selected 13 299306 ⟨541645, by decide⟩ ⟨13, 2, 0, 541645, 299306, 1485, 16384⟩
    (by decide) selected_cut_21161

theorem selected_cut_21162 : selected 8 ⟨541657, by decide⟩
    (prefixPartial 13 299307) = some ⟨13, 2, 0, 541657, 299307, 909, 16384⟩ := by
  decide +kernel

theorem context_13_299307_541657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299307 ⟨541657, by decide⟩ :=
  accepted_of_selected 13 299307 ⟨541657, by decide⟩ ⟨13, 2, 0, 541657, 299307, 909, 16384⟩
    (by decide) selected_cut_21162

theorem unmarked_context_12_74826_541658 : frontier 9 ⟨541658, by decide⟩
    (prefixCache 12 74826) (prefixPartial 12 74826) = false := by
  decide +kernel

theorem node_context_12_74826_541658 : EJMOriginalGlobalDAGData.nodes 9 ⟨541658, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541624, by decide⟩,⟨541645, by decide⟩,⟨541657, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74826_541658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74826 ⟨541658, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74826
    ⟨541658, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541624, by decide⟩,⟨541645, by decide⟩,⟨541657, by decide⟩]) unmarked_context_12_74826_541658 node_context_12_74826_541658
  intro a
  fin_cases a
  · exact context_13_299304_3444
  · exact context_13_299305_541624
  · exact context_13_299306_541645
  · exact context_13_299307_541657

theorem selected_cut_21163 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299308) = some ⟨13, 1, 0, 3444, 299308, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299308_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299308 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299308 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299308, 1, 16384⟩
    (by decide) selected_cut_21163

theorem selected_cut_21164 : selected 8 ⟨541685, by decide⟩
    (prefixPartial 13 299309) = some ⟨13, 2, 0, 541685, 299309, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_299309_541685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299309 ⟨541685, by decide⟩ :=
  accepted_of_selected 13 299309 ⟨541685, by decide⟩ ⟨13, 2, 0, 541685, 299309, 2065, 16384⟩
    (by decide) selected_cut_21164

theorem selected_cut_21165 : selected 8 ⟨541709, by decide⟩
    (prefixPartial 13 299310) = some ⟨13, 2, 0, 541709, 299310, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_299310_541709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299310 ⟨541709, by decide⟩ :=
  accepted_of_selected 13 299310 ⟨541709, by decide⟩ ⟨13, 2, 0, 541709, 299310, 1641, 16384⟩
    (by decide) selected_cut_21165

theorem selected_cut_21166 : selected 8 ⟨541715, by decide⟩
    (prefixPartial 13 299311) = some ⟨13, 2, 0, 541715, 299311, 697, 16384⟩ := by
  decide +kernel

theorem context_13_299311_541715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299311 ⟨541715, by decide⟩ :=
  accepted_of_selected 13 299311 ⟨541715, by decide⟩ ⟨13, 2, 0, 541715, 299311, 697, 16384⟩
    (by decide) selected_cut_21166

theorem unmarked_context_12_74827_541716 : frontier 9 ⟨541716, by decide⟩
    (prefixCache 12 74827) (prefixPartial 12 74827) = false := by
  decide +kernel

theorem node_context_12_74827_541716 : EJMOriginalGlobalDAGData.nodes 9 ⟨541716, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541685, by decide⟩,⟨541709, by decide⟩,⟨541715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74827_541716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74827 ⟨541716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74827
    ⟨541716, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541685, by decide⟩,⟨541709, by decide⟩,⟨541715, by decide⟩]) unmarked_context_12_74827_541716 node_context_12_74827_541716
  intro a
  fin_cases a
  · exact context_13_299308_3444
  · exact context_13_299309_541685
  · exact context_13_299310_541709
  · exact context_13_299311_541715

theorem unmarked_context_11_18706_541717 : frontier 10 ⟨541717, by decide⟩
    (prefixCache 11 18706) (prefixPartial 11 18706) = false := by
  decide +kernel

theorem node_context_11_18706_541717 : EJMOriginalGlobalDAGData.nodes 10 ⟨541717, by decide⟩ =
    .split (coordinate 11) (![⟨541548, by decide⟩,⟨541601, by decide⟩,⟨541658, by decide⟩,⟨541716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18706_541717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18706 ⟨541717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18706
    ⟨541717, by decide⟩ (by decide) (![⟨541548, by decide⟩,⟨541601, by decide⟩,⟨541658, by decide⟩,⟨541716, by decide⟩]) unmarked_context_11_18706_541717 node_context_11_18706_541717
  intro a
  fin_cases a
  · exact context_12_74824_541548
  · exact context_12_74825_541601
  · exact context_12_74826_541658
  · exact context_12_74827_541716

theorem selected_cut_21167 : selected 9 ⟨541757, by decide⟩
    (prefixPartial 12 74828) = some ⟨12, 2, 0, 541757, 74828, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_74828_541757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74828 ⟨541757, by decide⟩ :=
  accepted_of_selected 12 74828 ⟨541757, by decide⟩ ⟨12, 2, 0, 541757, 74828, 3137, 65536⟩
    (by decide) selected_cut_21167

theorem selected_cut_21168 : selected 9 ⟨541805, by decide⟩
    (prefixPartial 12 74829) = some ⟨12, 2, 0, 541805, 74829, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_74829_541805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74829 ⟨541805, by decide⟩ :=
  accepted_of_selected 12 74829 ⟨541805, by decide⟩ ⟨12, 2, 0, 541805, 74829, 3957, 65536⟩
    (by decide) selected_cut_21168

theorem selected_cut_21169 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299320) = some ⟨13, 1, 0, 3444, 299320, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299320_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299320 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299320 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299320, 1, 16384⟩
    (by decide) selected_cut_21169

theorem selected_cut_21170 : selected 8 ⟨541832, by decide⟩
    (prefixPartial 13 299321) = some ⟨13, 2, 0, 541832, 299321, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_299321_541832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299321 ⟨541832, by decide⟩ :=
  accepted_of_selected 13 299321 ⟨541832, by decide⟩ ⟨13, 2, 0, 541832, 299321, 2033, 16384⟩
    (by decide) selected_cut_21170

theorem selected_cut_21171 : selected 8 ⟨541847, by decide⟩
    (prefixPartial 13 299322) = some ⟨13, 2, 0, 541847, 299322, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_299322_541847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299322 ⟨541847, by decide⟩ :=
  accepted_of_selected 13 299322 ⟨541847, by decide⟩ ⟨13, 2, 0, 541847, 299322, 1457, 16384⟩
    (by decide) selected_cut_21171

theorem selected_cut_21172 : selected 8 ⟨541857, by decide⟩
    (prefixPartial 13 299323) = some ⟨13, 2, 0, 541857, 299323, 889, 16384⟩ := by
  decide +kernel

theorem context_13_299323_541857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299323 ⟨541857, by decide⟩ :=
  accepted_of_selected 13 299323 ⟨541857, by decide⟩ ⟨13, 2, 0, 541857, 299323, 889, 16384⟩
    (by decide) selected_cut_21172

theorem unmarked_context_12_74830_541858 : frontier 9 ⟨541858, by decide⟩
    (prefixCache 12 74830) (prefixPartial 12 74830) = false := by
  decide +kernel

theorem node_context_12_74830_541858 : EJMOriginalGlobalDAGData.nodes 9 ⟨541858, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541832, by decide⟩,⟨541847, by decide⟩,⟨541857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74830_541858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74830 ⟨541858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74830
    ⟨541858, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541832, by decide⟩,⟨541847, by decide⟩,⟨541857, by decide⟩]) unmarked_context_12_74830_541858 node_context_12_74830_541858
  intro a
  fin_cases a
  · exact context_13_299320_3444
  · exact context_13_299321_541832
  · exact context_13_299322_541847
  · exact context_13_299323_541857

theorem selected_cut_21173 : selected 9 ⟨541905, by decide⟩
    (prefixPartial 12 74831) = some ⟨12, 2, 0, 541905, 74831, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_74831_541905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74831 ⟨541905, by decide⟩ :=
  accepted_of_selected 12 74831 ⟨541905, by decide⟩ ⟨12, 2, 0, 541905, 74831, 4077, 65536⟩
    (by decide) selected_cut_21173

theorem unmarked_context_11_18707_541906 : frontier 10 ⟨541906, by decide⟩
    (prefixCache 11 18707) (prefixPartial 11 18707) = false := by
  decide +kernel

theorem node_context_11_18707_541906 : EJMOriginalGlobalDAGData.nodes 10 ⟨541906, by decide⟩ =
    .split (coordinate 11) (![⟨541757, by decide⟩,⟨541805, by decide⟩,⟨541858, by decide⟩,⟨541905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18707_541906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18707 ⟨541906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18707
    ⟨541906, by decide⟩ (by decide) (![⟨541757, by decide⟩,⟨541805, by decide⟩,⟨541858, by decide⟩,⟨541905, by decide⟩]) unmarked_context_11_18707_541906 node_context_11_18707_541906
  intro a
  fin_cases a
  · exact context_12_74828_541757
  · exact context_12_74829_541805
  · exact context_12_74830_541858
  · exact context_12_74831_541905

theorem unmarked_context_10_4676_541907 : frontier 11 ⟨541907, by decide⟩
    (prefixCache 10 4676) (prefixPartial 10 4676) = false := by
  decide +kernel

theorem node_context_10_4676_541907 : EJMOriginalGlobalDAGData.nodes 11 ⟨541907, by decide⟩ =
    .split (coordinate 10) (![⟨541312, by decide⟩,⟨541509, by decide⟩,⟨541717, by decide⟩,⟨541906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4676_541907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4676 ⟨541907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4676
    ⟨541907, by decide⟩ (by decide) (![⟨541312, by decide⟩,⟨541509, by decide⟩,⟨541717, by decide⟩,⟨541906, by decide⟩]) unmarked_context_10_4676_541907 node_context_10_4676_541907
  intro a
  fin_cases a
  · exact context_11_18704_541312
  · exact context_11_18705_541509
  · exact context_11_18706_541717
  · exact context_11_18707_541906

theorem selected_cut_21174 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 74832) = some ⟨12, 1, 0, 266170, 74832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74832_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74832 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 74832 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 74832, 1, 65536⟩
    (by decide) selected_cut_21174

theorem selected_cut_21175 : selected 9 ⟨541947, by decide⟩
    (prefixPartial 12 74833) = some ⟨12, 2, 0, 541947, 74833, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_74833_541947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74833 ⟨541947, by decide⟩ :=
  accepted_of_selected 12 74833 ⟨541947, by decide⟩ ⟨12, 2, 0, 541947, 74833, 3813, 65536⟩
    (by decide) selected_cut_21175

theorem selected_cut_21176 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299336) = some ⟨13, 1, 0, 3444, 299336, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299336_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299336 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299336 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299336, 1, 16384⟩
    (by decide) selected_cut_21176

theorem selected_cut_21177 : selected 8 ⟨541971, by decide⟩
    (prefixPartial 13 299337) = some ⟨13, 2, 0, 541971, 299337, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_299337_541971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299337 ⟨541971, by decide⟩ :=
  accepted_of_selected 13 299337 ⟨541971, by decide⟩ ⟨13, 2, 0, 541971, 299337, 2009, 16384⟩
    (by decide) selected_cut_21177

theorem selected_cut_21178 : selected 8 ⟨541990, by decide⟩
    (prefixPartial 13 299338) = some ⟨13, 2, 0, 541990, 299338, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_299338_541990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299338 ⟨541990, by decide⟩ :=
  accepted_of_selected 13 299338 ⟨541990, by decide⟩ ⟨13, 2, 0, 541990, 299338, 1645, 16384⟩
    (by decide) selected_cut_21178

theorem selected_cut_21179 : selected 8 ⟨541997, by decide⟩
    (prefixPartial 13 299339) = some ⟨13, 2, 0, 541997, 299339, 861, 16384⟩ := by
  decide +kernel

theorem context_13_299339_541997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299339 ⟨541997, by decide⟩ :=
  accepted_of_selected 13 299339 ⟨541997, by decide⟩ ⟨13, 2, 0, 541997, 299339, 861, 16384⟩
    (by decide) selected_cut_21179

theorem unmarked_context_12_74834_541998 : frontier 9 ⟨541998, by decide⟩
    (prefixCache 12 74834) (prefixPartial 12 74834) = false := by
  decide +kernel

theorem node_context_12_74834_541998 : EJMOriginalGlobalDAGData.nodes 9 ⟨541998, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨541971, by decide⟩,⟨541990, by decide⟩,⟨541997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74834_541998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74834 ⟨541998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74834
    ⟨541998, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨541971, by decide⟩,⟨541990, by decide⟩,⟨541997, by decide⟩]) unmarked_context_12_74834_541998 node_context_12_74834_541998
  intro a
  fin_cases a
  · exact context_13_299336_3444
  · exact context_13_299337_541971
  · exact context_13_299338_541990
  · exact context_13_299339_541997

theorem selected_cut_21180 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299340) = some ⟨13, 1, 0, 3444, 299340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299340, 1, 16384⟩
    (by decide) selected_cut_21180

theorem selected_cut_21181 : selected 8 ⟨542015, by decide⟩
    (prefixPartial 13 299341) = some ⟨13, 2, 0, 542015, 299341, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_299341_542015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299341 ⟨542015, by decide⟩ :=
  accepted_of_selected 13 299341 ⟨542015, by decide⟩ ⟨13, 2, 0, 542015, 299341, 1961, 16384⟩
    (by decide) selected_cut_21181

theorem selected_cut_21182 : selected 8 ⟨542032, by decide⟩
    (prefixPartial 13 299342) = some ⟨13, 2, 0, 542032, 299342, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_299342_542032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299342 ⟨542032, by decide⟩ :=
  accepted_of_selected 13 299342 ⟨542032, by decide⟩ ⟨13, 2, 0, 542032, 299342, 1905, 16384⟩
    (by decide) selected_cut_21182

theorem selected_cut_21183 : selected 8 ⟨542037, by decide⟩
    (prefixPartial 13 299343) = some ⟨13, 2, 0, 542037, 299343, 605, 16384⟩ := by
  decide +kernel

theorem context_13_299343_542037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299343 ⟨542037, by decide⟩ :=
  accepted_of_selected 13 299343 ⟨542037, by decide⟩ ⟨13, 2, 0, 542037, 299343, 605, 16384⟩
    (by decide) selected_cut_21183

theorem unmarked_context_12_74835_542038 : frontier 9 ⟨542038, by decide⟩
    (prefixCache 12 74835) (prefixPartial 12 74835) = false := by
  decide +kernel

theorem node_context_12_74835_542038 : EJMOriginalGlobalDAGData.nodes 9 ⟨542038, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542015, by decide⟩,⟨542032, by decide⟩,⟨542037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74835_542038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74835 ⟨542038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74835
    ⟨542038, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542015, by decide⟩,⟨542032, by decide⟩,⟨542037, by decide⟩]) unmarked_context_12_74835_542038 node_context_12_74835_542038
  intro a
  fin_cases a
  · exact context_13_299340_3444
  · exact context_13_299341_542015
  · exact context_13_299342_542032
  · exact context_13_299343_542037

theorem unmarked_context_11_18708_542039 : frontier 10 ⟨542039, by decide⟩
    (prefixCache 11 18708) (prefixPartial 11 18708) = false := by
  decide +kernel

theorem node_context_11_18708_542039 : EJMOriginalGlobalDAGData.nodes 10 ⟨542039, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨541947, by decide⟩,⟨541998, by decide⟩,⟨542038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18708_542039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18708 ⟨542039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18708
    ⟨542039, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨541947, by decide⟩,⟨541998, by decide⟩,⟨542038, by decide⟩]) unmarked_context_11_18708_542039 node_context_11_18708_542039
  intro a
  fin_cases a
  · exact context_12_74832_266170
  · exact context_12_74833_541947
  · exact context_12_74834_541998
  · exact context_12_74835_542038

theorem selected_cut_21184 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 18709) = some ⟨11, 1, 0, 451541, 18709, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18709_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18709 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 18709 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 18709, 1, 262144⟩
    (by decide) selected_cut_21184

theorem selected_cut_21185 : selected 9 ⟨542083, by decide⟩
    (prefixPartial 12 74840) = some ⟨12, 2, 0, 542083, 74840, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_74840_542083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74840 ⟨542083, by decide⟩ :=
  accepted_of_selected 12 74840 ⟨542083, by decide⟩ ⟨12, 2, 0, 542083, 74840, 3877, 65536⟩
    (by decide) selected_cut_21185

theorem selected_cut_21186 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299364) = some ⟨13, 1, 0, 3444, 299364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299364, 1, 16384⟩
    (by decide) selected_cut_21186

theorem selected_cut_21187 : selected 8 ⟨542098, by decide⟩
    (prefixPartial 13 299365) = some ⟨13, 2, 0, 542098, 299365, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_299365_542098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299365 ⟨542098, by decide⟩ :=
  accepted_of_selected 13 299365 ⟨542098, by decide⟩ ⟨13, 2, 0, 542098, 299365, 1425, 16384⟩
    (by decide) selected_cut_21187

theorem selected_cut_21188 : selected 8 ⟨542119, by decide⟩
    (prefixPartial 13 299366) = some ⟨13, 2, 0, 542119, 299366, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_299366_542119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299366 ⟨542119, by decide⟩ :=
  accepted_of_selected 13 299366 ⟨542119, by decide⟩ ⟨13, 2, 0, 542119, 299366, 1805, 16384⟩
    (by decide) selected_cut_21188

theorem selected_cut_21189 : selected 8 ⟨542127, by decide⟩
    (prefixPartial 13 299367) = some ⟨13, 2, 0, 542127, 299367, 945, 16384⟩ := by
  decide +kernel

theorem context_13_299367_542127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299367 ⟨542127, by decide⟩ :=
  accepted_of_selected 13 299367 ⟨542127, by decide⟩ ⟨13, 2, 0, 542127, 299367, 945, 16384⟩
    (by decide) selected_cut_21189

theorem unmarked_context_12_74841_542128 : frontier 9 ⟨542128, by decide⟩
    (prefixCache 12 74841) (prefixPartial 12 74841) = false := by
  decide +kernel

theorem node_context_12_74841_542128 : EJMOriginalGlobalDAGData.nodes 9 ⟨542128, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542098, by decide⟩,⟨542119, by decide⟩,⟨542127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74841_542128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74841 ⟨542128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74841
    ⟨542128, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542098, by decide⟩,⟨542119, by decide⟩,⟨542127, by decide⟩]) unmarked_context_12_74841_542128 node_context_12_74841_542128
  intro a
  fin_cases a
  · exact context_13_299364_3444
  · exact context_13_299365_542098
  · exact context_13_299366_542119
  · exact context_13_299367_542127

theorem selected_cut_21190 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299368) = some ⟨13, 1, 0, 3444, 299368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299368, 1, 16384⟩
    (by decide) selected_cut_21190

theorem selected_cut_21191 : selected 8 ⟨542142, by decide⟩
    (prefixPartial 13 299369) = some ⟨13, 2, 0, 542142, 299369, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_299369_542142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299369 ⟨542142, by decide⟩ :=
  accepted_of_selected 13 299369 ⟨542142, by decide⟩ ⟨13, 2, 0, 542142, 299369, 1673, 16384⟩
    (by decide) selected_cut_21191

theorem selected_cut_21192 : selected 8 ⟨542163, by decide⟩
    (prefixPartial 13 299370) = some ⟨13, 2, 0, 542163, 299370, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_299370_542163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299370 ⟨542163, by decide⟩ :=
  accepted_of_selected 13 299370 ⟨542163, by decide⟩ ⟨13, 2, 0, 542163, 299370, 1841, 16384⟩
    (by decide) selected_cut_21192

theorem selected_cut_21193 : selected 8 ⟨542172, by decide⟩
    (prefixPartial 13 299371) = some ⟨13, 2, 0, 542172, 299371, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_299371_542172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299371 ⟨542172, by decide⟩ :=
  accepted_of_selected 13 299371 ⟨542172, by decide⟩ ⟨13, 2, 0, 542172, 299371, 1069, 16384⟩
    (by decide) selected_cut_21193

theorem unmarked_context_12_74842_542173 : frontier 9 ⟨542173, by decide⟩
    (prefixCache 12 74842) (prefixPartial 12 74842) = false := by
  decide +kernel

theorem node_context_12_74842_542173 : EJMOriginalGlobalDAGData.nodes 9 ⟨542173, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542142, by decide⟩,⟨542163, by decide⟩,⟨542172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74842_542173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74842 ⟨542173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74842
    ⟨542173, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542142, by decide⟩,⟨542163, by decide⟩,⟨542172, by decide⟩]) unmarked_context_12_74842_542173 node_context_12_74842_542173
  intro a
  fin_cases a
  · exact context_13_299368_3444
  · exact context_13_299369_542142
  · exact context_13_299370_542163
  · exact context_13_299371_542172

theorem selected_cut_21194 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299372) = some ⟨13, 1, 0, 3444, 299372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299372, 1, 16384⟩
    (by decide) selected_cut_21194

theorem selected_cut_21195 : selected 8 ⟨542191, by decide⟩
    (prefixPartial 13 299373) = some ⟨13, 2, 0, 542191, 299373, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_299373_542191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299373 ⟨542191, by decide⟩ :=
  accepted_of_selected 13 299373 ⟨542191, by decide⟩ ⟨13, 2, 0, 542191, 299373, 1837, 16384⟩
    (by decide) selected_cut_21195

theorem selected_cut_21196 : selected 8 ⟨542215, by decide⟩
    (prefixPartial 13 299374) = some ⟨13, 2, 0, 542215, 299374, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_299374_542215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299374 ⟨542215, by decide⟩ :=
  accepted_of_selected 13 299374 ⟨542215, by decide⟩ ⟨13, 2, 0, 542215, 299374, 2117, 16384⟩
    (by decide) selected_cut_21196

theorem selected_cut_21197 : selected 8 ⟨542221, by decide⟩
    (prefixPartial 13 299375) = some ⟨13, 2, 0, 542221, 299375, 917, 16384⟩ := by
  decide +kernel

theorem context_13_299375_542221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299375 ⟨542221, by decide⟩ :=
  accepted_of_selected 13 299375 ⟨542221, by decide⟩ ⟨13, 2, 0, 542221, 299375, 917, 16384⟩
    (by decide) selected_cut_21197

theorem unmarked_context_12_74843_542222 : frontier 9 ⟨542222, by decide⟩
    (prefixCache 12 74843) (prefixPartial 12 74843) = false := by
  decide +kernel

theorem node_context_12_74843_542222 : EJMOriginalGlobalDAGData.nodes 9 ⟨542222, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542191, by decide⟩,⟨542215, by decide⟩,⟨542221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74843_542222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74843 ⟨542222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74843
    ⟨542222, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542191, by decide⟩,⟨542215, by decide⟩,⟨542221, by decide⟩]) unmarked_context_12_74843_542222 node_context_12_74843_542222
  intro a
  fin_cases a
  · exact context_13_299372_3444
  · exact context_13_299373_542191
  · exact context_13_299374_542215
  · exact context_13_299375_542221

theorem unmarked_context_11_18710_542223 : frontier 10 ⟨542223, by decide⟩
    (prefixCache 11 18710) (prefixPartial 11 18710) = false := by
  decide +kernel

theorem node_context_11_18710_542223 : EJMOriginalGlobalDAGData.nodes 10 ⟨542223, by decide⟩ =
    .split (coordinate 11) (![⟨542083, by decide⟩,⟨542128, by decide⟩,⟨542173, by decide⟩,⟨542222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18710_542223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18710 ⟨542223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18710
    ⟨542223, by decide⟩ (by decide) (![⟨542083, by decide⟩,⟨542128, by decide⟩,⟨542173, by decide⟩,⟨542222, by decide⟩]) unmarked_context_11_18710_542223 node_context_11_18710_542223
  intro a
  fin_cases a
  · exact context_12_74840_542083
  · exact context_12_74841_542128
  · exact context_12_74842_542173
  · exact context_12_74843_542222

theorem selected_cut_21198 : selected 9 ⟨542264, by decide⟩
    (prefixPartial 12 74844) = some ⟨12, 2, 0, 542264, 74844, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_74844_542264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74844 ⟨542264, by decide⟩ :=
  accepted_of_selected 12 74844 ⟨542264, by decide⟩ ⟨12, 2, 0, 542264, 74844, 3773, 65536⟩
    (by decide) selected_cut_21198

theorem selected_cut_21199 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299380) = some ⟨13, 1, 0, 3444, 299380, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299380_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299380 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299380 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299380, 1, 16384⟩
    (by decide) selected_cut_21199

theorem selected_cut_21200 : selected 8 ⟨542282, by decide⟩
    (prefixPartial 13 299381) = some ⟨13, 2, 0, 542282, 299381, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_299381_542282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299381 ⟨542282, by decide⟩ :=
  accepted_of_selected 13 299381 ⟨542282, by decide⟩ ⟨13, 2, 0, 542282, 299381, 1609, 16384⟩
    (by decide) selected_cut_21200

theorem selected_cut_21201 : selected 8 ⟨542302, by decide⟩
    (prefixPartial 13 299382) = some ⟨13, 2, 0, 542302, 299382, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_299382_542302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299382 ⟨542302, by decide⟩ :=
  accepted_of_selected 13 299382 ⟨542302, by decide⟩ ⟨13, 2, 0, 542302, 299382, 1825, 16384⟩
    (by decide) selected_cut_21201

theorem selected_cut_21202 : selected 8 ⟨542307, by decide⟩
    (prefixPartial 13 299383) = some ⟨13, 2, 0, 542307, 299383, 829, 16384⟩ := by
  decide +kernel

theorem context_13_299383_542307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299383 ⟨542307, by decide⟩ :=
  accepted_of_selected 13 299383 ⟨542307, by decide⟩ ⟨13, 2, 0, 542307, 299383, 829, 16384⟩
    (by decide) selected_cut_21202

theorem unmarked_context_12_74845_542308 : frontier 9 ⟨542308, by decide⟩
    (prefixCache 12 74845) (prefixPartial 12 74845) = false := by
  decide +kernel

theorem node_context_12_74845_542308 : EJMOriginalGlobalDAGData.nodes 9 ⟨542308, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542282, by decide⟩,⟨542302, by decide⟩,⟨542307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74845_542308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74845 ⟨542308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74845
    ⟨542308, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542282, by decide⟩,⟨542302, by decide⟩,⟨542307, by decide⟩]) unmarked_context_12_74845_542308 node_context_12_74845_542308
  intro a
  fin_cases a
  · exact context_13_299380_3444
  · exact context_13_299381_542282
  · exact context_13_299382_542302
  · exact context_13_299383_542307

theorem selected_cut_21203 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299384) = some ⟨13, 1, 0, 3444, 299384, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299384_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299384 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299384 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299384, 1, 16384⟩
    (by decide) selected_cut_21203

theorem selected_cut_21204 : selected 8 ⟨542329, by decide⟩
    (prefixPartial 13 299385) = some ⟨13, 2, 0, 542329, 299385, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_299385_542329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299385 ⟨542329, by decide⟩ :=
  accepted_of_selected 13 299385 ⟨542329, by decide⟩ ⟨13, 2, 0, 542329, 299385, 1841, 16384⟩
    (by decide) selected_cut_21204

theorem selected_cut_21205 : selected 8 ⟨542348, by decide⟩
    (prefixPartial 13 299386) = some ⟨13, 2, 0, 542348, 299386, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_299386_542348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299386 ⟨542348, by decide⟩ :=
  accepted_of_selected 13 299386 ⟨542348, by decide⟩ ⟨13, 2, 0, 542348, 299386, 2069, 16384⟩
    (by decide) selected_cut_21205

theorem selected_cut_21206 : selected 8 ⟨542354, by decide⟩
    (prefixPartial 13 299387) = some ⟨13, 2, 0, 542354, 299387, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_299387_542354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299387 ⟨542354, by decide⟩ :=
  accepted_of_selected 13 299387 ⟨542354, by decide⟩ ⟨13, 2, 0, 542354, 299387, 1109, 16384⟩
    (by decide) selected_cut_21206

theorem unmarked_context_12_74846_542355 : frontier 9 ⟨542355, by decide⟩
    (prefixCache 12 74846) (prefixPartial 12 74846) = false := by
  decide +kernel

theorem node_context_12_74846_542355 : EJMOriginalGlobalDAGData.nodes 9 ⟨542355, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542329, by decide⟩,⟨542348, by decide⟩,⟨542354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74846_542355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74846 ⟨542355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74846
    ⟨542355, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542329, by decide⟩,⟨542348, by decide⟩,⟨542354, by decide⟩]) unmarked_context_12_74846_542355 node_context_12_74846_542355
  intro a
  fin_cases a
  · exact context_13_299384_3444
  · exact context_13_299385_542329
  · exact context_13_299386_542348
  · exact context_13_299387_542354

theorem selected_cut_21207 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299388) = some ⟨13, 1, 0, 3444, 299388, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299388_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299388 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299388 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299388, 1, 16384⟩
    (by decide) selected_cut_21207

theorem selected_cut_21208 : selected 8 ⟨542368, by decide⟩
    (prefixPartial 13 299389) = some ⟨13, 2, 0, 542368, 299389, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_299389_542368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299389 ⟨542368, by decide⟩ :=
  accepted_of_selected 13 299389 ⟨542368, by decide⟩ ⟨13, 2, 0, 542368, 299389, 1689, 16384⟩
    (by decide) selected_cut_21208

theorem selected_cut_21209 : selected 8 ⟨542392, by decide⟩
    (prefixPartial 13 299390) = some ⟨13, 2, 0, 542392, 299390, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_299390_542392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299390 ⟨542392, by decide⟩ :=
  accepted_of_selected 13 299390 ⟨542392, by decide⟩ ⟨13, 2, 0, 542392, 299390, 2073, 16384⟩
    (by decide) selected_cut_21209

theorem selected_cut_21210 : selected 8 ⟨542397, by decide⟩
    (prefixPartial 13 299391) = some ⟨13, 2, 0, 542397, 299391, 797, 16384⟩ := by
  decide +kernel

theorem context_13_299391_542397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299391 ⟨542397, by decide⟩ :=
  accepted_of_selected 13 299391 ⟨542397, by decide⟩ ⟨13, 2, 0, 542397, 299391, 797, 16384⟩
    (by decide) selected_cut_21210

theorem unmarked_context_12_74847_542398 : frontier 9 ⟨542398, by decide⟩
    (prefixCache 12 74847) (prefixPartial 12 74847) = false := by
  decide +kernel

theorem node_context_12_74847_542398 : EJMOriginalGlobalDAGData.nodes 9 ⟨542398, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542368, by decide⟩,⟨542392, by decide⟩,⟨542397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74847_542398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74847 ⟨542398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74847
    ⟨542398, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542368, by decide⟩,⟨542392, by decide⟩,⟨542397, by decide⟩]) unmarked_context_12_74847_542398 node_context_12_74847_542398
  intro a
  fin_cases a
  · exact context_13_299388_3444
  · exact context_13_299389_542368
  · exact context_13_299390_542392
  · exact context_13_299391_542397

theorem unmarked_context_11_18711_542399 : frontier 10 ⟨542399, by decide⟩
    (prefixCache 11 18711) (prefixPartial 11 18711) = false := by
  decide +kernel

theorem node_context_11_18711_542399 : EJMOriginalGlobalDAGData.nodes 10 ⟨542399, by decide⟩ =
    .split (coordinate 11) (![⟨542264, by decide⟩,⟨542308, by decide⟩,⟨542355, by decide⟩,⟨542398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18711_542399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18711 ⟨542399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18711
    ⟨542399, by decide⟩ (by decide) (![⟨542264, by decide⟩,⟨542308, by decide⟩,⟨542355, by decide⟩,⟨542398, by decide⟩]) unmarked_context_11_18711_542399 node_context_11_18711_542399
  intro a
  fin_cases a
  · exact context_12_74844_542264
  · exact context_12_74845_542308
  · exact context_12_74846_542355
  · exact context_12_74847_542398

theorem unmarked_context_10_4677_542400 : frontier 11 ⟨542400, by decide⟩
    (prefixCache 10 4677) (prefixPartial 10 4677) = false := by
  decide +kernel

theorem node_context_10_4677_542400 : EJMOriginalGlobalDAGData.nodes 11 ⟨542400, by decide⟩ =
    .split (coordinate 10) (![⟨542039, by decide⟩,⟨451541, by decide⟩,⟨542223, by decide⟩,⟨542399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4677_542400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4677 ⟨542400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4677
    ⟨542400, by decide⟩ (by decide) (![⟨542039, by decide⟩,⟨451541, by decide⟩,⟨542223, by decide⟩,⟨542399, by decide⟩]) unmarked_context_10_4677_542400 node_context_10_4677_542400
  intro a
  fin_cases a
  · exact context_11_18708_542039
  · exact context_11_18709_451541
  · exact context_11_18710_542223
  · exact context_11_18711_542399

theorem selected_cut_21211 : selected 9 ⟨542488, by decide⟩
    (prefixPartial 12 74848) = some ⟨12, 2, 0, 542488, 74848, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_74848_542488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74848 ⟨542488, by decide⟩ :=
  accepted_of_selected 12 74848 ⟨542488, by decide⟩ ⟨12, 2, 0, 542488, 74848, 2625, 65536⟩
    (by decide) selected_cut_21211

theorem selected_cut_21212 : selected 9 ⟨542528, by decide⟩
    (prefixPartial 12 74849) = some ⟨12, 2, 0, 542528, 74849, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_74849_542528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74849 ⟨542528, by decide⟩ :=
  accepted_of_selected 12 74849 ⟨542528, by decide⟩ ⟨12, 2, 0, 542528, 74849, 3465, 65536⟩
    (by decide) selected_cut_21212

theorem selected_cut_21213 : selected 9 ⟨542573, by decide⟩
    (prefixPartial 12 74850) = some ⟨12, 2, 0, 542573, 74850, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_74850_542573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74850 ⟨542573, by decide⟩ :=
  accepted_of_selected 12 74850 ⟨542573, by decide⟩ ⟨12, 2, 0, 542573, 74850, 3857, 65536⟩
    (by decide) selected_cut_21213

theorem selected_cut_21214 : selected 9 ⟨542612, by decide⟩
    (prefixPartial 12 74851) = some ⟨12, 2, 0, 542612, 74851, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_74851_542612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74851 ⟨542612, by decide⟩ :=
  accepted_of_selected 12 74851 ⟨542612, by decide⟩ ⟨12, 2, 0, 542612, 74851, 3853, 65536⟩
    (by decide) selected_cut_21214

theorem unmarked_context_11_18712_542613 : frontier 10 ⟨542613, by decide⟩
    (prefixCache 11 18712) (prefixPartial 11 18712) = false := by
  decide +kernel

theorem node_context_11_18712_542613 : EJMOriginalGlobalDAGData.nodes 10 ⟨542613, by decide⟩ =
    .split (coordinate 11) (![⟨542488, by decide⟩,⟨542528, by decide⟩,⟨542573, by decide⟩,⟨542612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18712_542613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18712 ⟨542613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18712
    ⟨542613, by decide⟩ (by decide) (![⟨542488, by decide⟩,⟨542528, by decide⟩,⟨542573, by decide⟩,⟨542612, by decide⟩]) unmarked_context_11_18712_542613 node_context_11_18712_542613
  intro a
  fin_cases a
  · exact context_12_74848_542488
  · exact context_12_74849_542528
  · exact context_12_74850_542573
  · exact context_12_74851_542612

theorem selected_cut_21215 : selected 9 ⟨542658, by decide⟩
    (prefixPartial 12 74852) = some ⟨12, 2, 0, 542658, 74852, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_74852_542658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74852 ⟨542658, by decide⟩ :=
  accepted_of_selected 12 74852 ⟨542658, by decide⟩ ⟨12, 2, 0, 542658, 74852, 3573, 65536⟩
    (by decide) selected_cut_21215

theorem selected_cut_21216 : selected 9 ⟨542700, by decide⟩
    (prefixPartial 12 74853) = some ⟨12, 2, 0, 542700, 74853, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_74853_542700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74853 ⟨542700, by decide⟩ :=
  accepted_of_selected 12 74853 ⟨542700, by decide⟩ ⟨12, 2, 0, 542700, 74853, 3533, 65536⟩
    (by decide) selected_cut_21216

theorem selected_cut_21217 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299416) = some ⟨13, 1, 0, 3444, 299416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299416, 1, 16384⟩
    (by decide) selected_cut_21217

theorem selected_cut_21218 : selected 8 ⟨542731, by decide⟩
    (prefixPartial 13 299417) = some ⟨13, 2, 0, 542731, 299417, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_299417_542731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299417 ⟨542731, by decide⟩ :=
  accepted_of_selected 13 299417 ⟨542731, by decide⟩ ⟨13, 2, 0, 542731, 299417, 1389, 16384⟩
    (by decide) selected_cut_21218

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
