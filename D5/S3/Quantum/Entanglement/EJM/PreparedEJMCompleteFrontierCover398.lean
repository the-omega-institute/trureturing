/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover397
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38210 : selected 9 ⟨1028381, by decide⟩
    (prefixPartial 12 301073) = some ⟨12, 2, 0, 1028381, 301073, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_301073_1028381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301073 ⟨1028381, by decide⟩ :=
  accepted_of_selected 12 301073 ⟨1028381, by decide⟩ ⟨12, 2, 0, 1028381, 301073, 2813, 65536⟩
    (by decide) selected_cut_38210

theorem selected_cut_38211 : selected 9 ⟨1028426, by decide⟩
    (prefixPartial 12 301074) = some ⟨12, 2, 0, 1028426, 301074, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_301074_1028426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301074 ⟨1028426, by decide⟩ :=
  accepted_of_selected 12 301074 ⟨1028426, by decide⟩ ⟨12, 2, 0, 1028426, 301074, 2377, 65536⟩
    (by decide) selected_cut_38211

theorem selected_cut_38212 : selected 9 ⟨1028470, by decide⟩
    (prefixPartial 12 301075) = some ⟨12, 2, 0, 1028470, 301075, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_301075_1028470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301075 ⟨1028470, by decide⟩ :=
  accepted_of_selected 12 301075 ⟨1028470, by decide⟩ ⟨12, 2, 0, 1028470, 301075, 2689, 65536⟩
    (by decide) selected_cut_38212

theorem unmarked_context_11_75268_1028471 : frontier 10 ⟨1028471, by decide⟩
    (prefixCache 11 75268) (prefixPartial 11 75268) = false := by
  decide +kernel

theorem node_context_11_75268_1028471 : EJMOriginalGlobalDAGData.nodes 10 ⟨1028471, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1028381, by decide⟩,⟨1028426, by decide⟩,⟨1028470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75268_1028471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75268 ⟨1028471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75268
    ⟨1028471, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1028381, by decide⟩,⟨1028426, by decide⟩,⟨1028470, by decide⟩]) unmarked_context_11_75268_1028471 node_context_11_75268_1028471
  intro a
  fin_cases a
  · exact context_12_301072_985390
  · exact context_12_301073_1028381
  · exact context_12_301074_1028426
  · exact context_12_301075_1028470

theorem selected_cut_38213 : selected 9 ⟨1028514, by decide⟩
    (prefixPartial 12 301076) = some ⟨12, 2, 0, 1028514, 301076, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_301076_1028514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301076 ⟨1028514, by decide⟩ :=
  accepted_of_selected 12 301076 ⟨1028514, by decide⟩ ⟨12, 2, 0, 1028514, 301076, 2757, 65536⟩
    (by decide) selected_cut_38213

theorem selected_cut_38214 : selected 9 ⟨1028617, by decide⟩
    (prefixPartial 12 301077) = some ⟨12, 2, 0, 1028617, 301077, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_301077_1028617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301077 ⟨1028617, by decide⟩ :=
  accepted_of_selected 12 301077 ⟨1028617, by decide⟩ ⟨12, 2, 0, 1028617, 301077, 1865, 65536⟩
    (by decide) selected_cut_38214

theorem selected_cut_38215 : selected 9 ⟨1028659, by decide⟩
    (prefixPartial 12 301078) = some ⟨12, 2, 0, 1028659, 301078, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_301078_1028659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301078 ⟨1028659, by decide⟩ :=
  accepted_of_selected 12 301078 ⟨1028659, by decide⟩ ⟨12, 2, 0, 1028659, 301078, 2893, 65536⟩
    (by decide) selected_cut_38215

theorem selected_cut_38216 : selected 9 ⟨1028711, by decide⟩
    (prefixPartial 12 301079) = some ⟨12, 2, 0, 1028711, 301079, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_301079_1028711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301079 ⟨1028711, by decide⟩ :=
  accepted_of_selected 12 301079 ⟨1028711, by decide⟩ ⟨12, 2, 0, 1028711, 301079, 3089, 65536⟩
    (by decide) selected_cut_38216

theorem unmarked_context_11_75269_1028712 : frontier 10 ⟨1028712, by decide⟩
    (prefixCache 11 75269) (prefixPartial 11 75269) = false := by
  decide +kernel

theorem node_context_11_75269_1028712 : EJMOriginalGlobalDAGData.nodes 10 ⟨1028712, by decide⟩ =
    .split (coordinate 11) (![⟨1028514, by decide⟩,⟨1028617, by decide⟩,⟨1028659, by decide⟩,⟨1028711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75269_1028712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75269 ⟨1028712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75269
    ⟨1028712, by decide⟩ (by decide) (![⟨1028514, by decide⟩,⟨1028617, by decide⟩,⟨1028659, by decide⟩,⟨1028711, by decide⟩]) unmarked_context_11_75269_1028712 node_context_11_75269_1028712
  intro a
  fin_cases a
  · exact context_12_301076_1028514
  · exact context_12_301077_1028617
  · exact context_12_301078_1028659
  · exact context_12_301079_1028711

theorem selected_cut_38217 : selected 9 ⟨1028749, by decide⟩
    (prefixPartial 12 301080) = some ⟨12, 2, 0, 1028749, 301080, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_301080_1028749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301080 ⟨1028749, by decide⟩ :=
  accepted_of_selected 12 301080 ⟨1028749, by decide⟩ ⟨12, 2, 0, 1028749, 301080, 2621, 65536⟩
    (by decide) selected_cut_38217

theorem selected_cut_38218 : selected 9 ⟨1028800, by decide⟩
    (prefixPartial 12 301081) = some ⟨12, 2, 0, 1028800, 301081, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_301081_1028800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301081 ⟨1028800, by decide⟩ :=
  accepted_of_selected 12 301081 ⟨1028800, by decide⟩ ⟨12, 2, 0, 1028800, 301081, 3265, 65536⟩
    (by decide) selected_cut_38218

theorem selected_cut_38219 : selected 9 ⟨1028844, by decide⟩
    (prefixPartial 12 301082) = some ⟨12, 2, 0, 1028844, 301082, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_301082_1028844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301082 ⟨1028844, by decide⟩ :=
  accepted_of_selected 12 301082 ⟨1028844, by decide⟩ ⟨12, 2, 0, 1028844, 301082, 2825, 65536⟩
    (by decide) selected_cut_38219

theorem selected_cut_38220 : selected 9 ⟨1028897, by decide⟩
    (prefixPartial 12 301083) = some ⟨12, 2, 0, 1028897, 301083, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_301083_1028897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301083 ⟨1028897, by decide⟩ :=
  accepted_of_selected 12 301083 ⟨1028897, by decide⟩ ⟨12, 2, 0, 1028897, 301083, 3289, 65536⟩
    (by decide) selected_cut_38220

theorem unmarked_context_11_75270_1028898 : frontier 10 ⟨1028898, by decide⟩
    (prefixCache 11 75270) (prefixPartial 11 75270) = false := by
  decide +kernel

theorem node_context_11_75270_1028898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1028898, by decide⟩ =
    .split (coordinate 11) (![⟨1028749, by decide⟩,⟨1028800, by decide⟩,⟨1028844, by decide⟩,⟨1028897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75270_1028898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75270 ⟨1028898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75270
    ⟨1028898, by decide⟩ (by decide) (![⟨1028749, by decide⟩,⟨1028800, by decide⟩,⟨1028844, by decide⟩,⟨1028897, by decide⟩]) unmarked_context_11_75270_1028898 node_context_11_75270_1028898
  intro a
  fin_cases a
  · exact context_12_301080_1028749
  · exact context_12_301081_1028800
  · exact context_12_301082_1028844
  · exact context_12_301083_1028897

theorem selected_cut_38221 : selected 9 ⟨1028936, by decide⟩
    (prefixPartial 12 301084) = some ⟨12, 2, 0, 1028936, 301084, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_301084_1028936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301084 ⟨1028936, by decide⟩ :=
  accepted_of_selected 12 301084 ⟨1028936, by decide⟩ ⟨12, 2, 0, 1028936, 301084, 2753, 65536⟩
    (by decide) selected_cut_38221

theorem selected_cut_38222 : selected 9 ⟨1028989, by decide⟩
    (prefixPartial 12 301085) = some ⟨12, 2, 0, 1028989, 301085, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_301085_1028989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301085 ⟨1028989, by decide⟩ :=
  accepted_of_selected 12 301085 ⟨1028989, by decide⟩ ⟨12, 2, 0, 1028989, 301085, 3377, 65536⟩
    (by decide) selected_cut_38222

theorem selected_cut_38223 : selected 9 ⟨1029034, by decide⟩
    (prefixPartial 12 301086) = some ⟨12, 2, 0, 1029034, 301086, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_301086_1029034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301086 ⟨1029034, by decide⟩ :=
  accepted_of_selected 12 301086 ⟨1029034, by decide⟩ ⟨12, 2, 0, 1029034, 301086, 3177, 65536⟩
    (by decide) selected_cut_38223

theorem selected_cut_38224 : selected 9 ⟨1029079, by decide⟩
    (prefixPartial 12 301087) = some ⟨12, 2, 0, 1029079, 301087, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_301087_1029079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301087 ⟨1029079, by decide⟩ :=
  accepted_of_selected 12 301087 ⟨1029079, by decide⟩ ⟨12, 2, 0, 1029079, 301087, 3009, 65536⟩
    (by decide) selected_cut_38224

theorem unmarked_context_11_75271_1029080 : frontier 10 ⟨1029080, by decide⟩
    (prefixCache 11 75271) (prefixPartial 11 75271) = false := by
  decide +kernel

theorem node_context_11_75271_1029080 : EJMOriginalGlobalDAGData.nodes 10 ⟨1029080, by decide⟩ =
    .split (coordinate 11) (![⟨1028936, by decide⟩,⟨1028989, by decide⟩,⟨1029034, by decide⟩,⟨1029079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75271_1029080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75271 ⟨1029080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75271
    ⟨1029080, by decide⟩ (by decide) (![⟨1028936, by decide⟩,⟨1028989, by decide⟩,⟨1029034, by decide⟩,⟨1029079, by decide⟩]) unmarked_context_11_75271_1029080 node_context_11_75271_1029080
  intro a
  fin_cases a
  · exact context_12_301084_1028936
  · exact context_12_301085_1028989
  · exact context_12_301086_1029034
  · exact context_12_301087_1029079

theorem unmarked_context_10_18817_1029081 : frontier 11 ⟨1029081, by decide⟩
    (prefixCache 10 18817) (prefixPartial 10 18817) = false := by
  decide +kernel

theorem node_context_10_18817_1029081 : EJMOriginalGlobalDAGData.nodes 11 ⟨1029081, by decide⟩ =
    .split (coordinate 10) (![⟨1028471, by decide⟩,⟨1028712, by decide⟩,⟨1028898, by decide⟩,⟨1029080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18817_1029081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18817 ⟨1029081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18817
    ⟨1029081, by decide⟩ (by decide) (![⟨1028471, by decide⟩,⟨1028712, by decide⟩,⟨1028898, by decide⟩,⟨1029080, by decide⟩]) unmarked_context_10_18817_1029081 node_context_10_18817_1029081
  intro a
  fin_cases a
  · exact context_11_75268_1028471
  · exact context_11_75269_1028712
  · exact context_11_75270_1028898
  · exact context_11_75271_1029080

theorem selected_cut_38225 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 301088) = some ⟨12, 1, 0, 985390, 301088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301088_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301088 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 301088 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 301088, 1, 65536⟩
    (by decide) selected_cut_38225

theorem selected_cut_38226 : selected 9 ⟨1029125, by decide⟩
    (prefixPartial 12 301089) = some ⟨12, 2, 0, 1029125, 301089, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_301089_1029125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301089 ⟨1029125, by decide⟩ :=
  accepted_of_selected 12 301089 ⟨1029125, by decide⟩ ⟨12, 2, 0, 1029125, 301089, 2637, 65536⟩
    (by decide) selected_cut_38226

theorem selected_cut_38227 : selected 9 ⟨1029160, by decide⟩
    (prefixPartial 12 301090) = some ⟨12, 2, 0, 1029160, 301090, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_301090_1029160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301090 ⟨1029160, by decide⟩ :=
  accepted_of_selected 12 301090 ⟨1029160, by decide⟩ ⟨12, 2, 0, 1029160, 301090, 2169, 65536⟩
    (by decide) selected_cut_38227

theorem selected_cut_38228 : selected 9 ⟨1029186, by decide⟩
    (prefixPartial 12 301091) = some ⟨12, 2, 0, 1029186, 301091, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_301091_1029186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301091 ⟨1029186, by decide⟩ :=
  accepted_of_selected 12 301091 ⟨1029186, by decide⟩ ⟨12, 2, 0, 1029186, 301091, 2413, 65536⟩
    (by decide) selected_cut_38228

theorem unmarked_context_11_75272_1029187 : frontier 10 ⟨1029187, by decide⟩
    (prefixCache 11 75272) (prefixPartial 11 75272) = false := by
  decide +kernel

theorem node_context_11_75272_1029187 : EJMOriginalGlobalDAGData.nodes 10 ⟨1029187, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1029125, by decide⟩,⟨1029160, by decide⟩,⟨1029186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75272_1029187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75272 ⟨1029187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75272
    ⟨1029187, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1029125, by decide⟩,⟨1029160, by decide⟩,⟨1029186, by decide⟩]) unmarked_context_11_75272_1029187 node_context_11_75272_1029187
  intro a
  fin_cases a
  · exact context_12_301088_985390
  · exact context_12_301089_1029125
  · exact context_12_301090_1029160
  · exact context_12_301091_1029186

theorem selected_cut_38229 : selected 9 ⟨1029231, by decide⟩
    (prefixPartial 12 301092) = some ⟨12, 2, 0, 1029231, 301092, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_301092_1029231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301092 ⟨1029231, by decide⟩ :=
  accepted_of_selected 12 301092 ⟨1029231, by decide⟩ ⟨12, 2, 0, 1029231, 301092, 2837, 65536⟩
    (by decide) selected_cut_38229

theorem selected_cut_38230 : selected 9 ⟨1029278, by decide⟩
    (prefixPartial 12 301093) = some ⟨12, 2, 0, 1029278, 301093, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_301093_1029278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301093 ⟨1029278, by decide⟩ :=
  accepted_of_selected 12 301093 ⟨1029278, by decide⟩ ⟨12, 2, 0, 1029278, 301093, 3085, 65536⟩
    (by decide) selected_cut_38230

theorem selected_cut_38231 : selected 9 ⟨1029321, by decide⟩
    (prefixPartial 12 301094) = some ⟨12, 2, 0, 1029321, 301094, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_301094_1029321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301094 ⟨1029321, by decide⟩ :=
  accepted_of_selected 12 301094 ⟨1029321, by decide⟩ ⟨12, 2, 0, 1029321, 301094, 2765, 65536⟩
    (by decide) selected_cut_38231

theorem selected_cut_38232 : selected 9 ⟨1029365, by decide⟩
    (prefixPartial 12 301095) = some ⟨12, 2, 0, 1029365, 301095, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_301095_1029365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301095 ⟨1029365, by decide⟩ :=
  accepted_of_selected 12 301095 ⟨1029365, by decide⟩ ⟨12, 2, 0, 1029365, 301095, 3045, 65536⟩
    (by decide) selected_cut_38232

theorem unmarked_context_11_75273_1029366 : frontier 10 ⟨1029366, by decide⟩
    (prefixCache 11 75273) (prefixPartial 11 75273) = false := by
  decide +kernel

theorem node_context_11_75273_1029366 : EJMOriginalGlobalDAGData.nodes 10 ⟨1029366, by decide⟩ =
    .split (coordinate 11) (![⟨1029231, by decide⟩,⟨1029278, by decide⟩,⟨1029321, by decide⟩,⟨1029365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75273_1029366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75273 ⟨1029366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75273
    ⟨1029366, by decide⟩ (by decide) (![⟨1029231, by decide⟩,⟨1029278, by decide⟩,⟨1029321, by decide⟩,⟨1029365, by decide⟩]) unmarked_context_11_75273_1029366 node_context_11_75273_1029366
  intro a
  fin_cases a
  · exact context_12_301092_1029231
  · exact context_12_301093_1029278
  · exact context_12_301094_1029321
  · exact context_12_301095_1029365

theorem selected_cut_38233 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75274) = some ⟨11, 1, 0, 900587, 75274, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75274_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75274 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75274 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75274, 1, 262144⟩
    (by decide) selected_cut_38233

theorem selected_cut_38234 : selected 9 ⟨1029404, by decide⟩
    (prefixPartial 12 301100) = some ⟨12, 2, 0, 1029404, 301100, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_301100_1029404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301100 ⟨1029404, by decide⟩ :=
  accepted_of_selected 12 301100 ⟨1029404, by decide⟩ ⟨12, 2, 0, 1029404, 301100, 2521, 65536⟩
    (by decide) selected_cut_38234

theorem selected_cut_38235 : selected 9 ⟨1029457, by decide⟩
    (prefixPartial 12 301101) = some ⟨12, 2, 0, 1029457, 301101, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_301101_1029457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301101 ⟨1029457, by decide⟩ :=
  accepted_of_selected 12 301101 ⟨1029457, by decide⟩ ⟨12, 2, 0, 1029457, 301101, 3289, 65536⟩
    (by decide) selected_cut_38235

theorem selected_cut_38236 : selected 9 ⟨1029514, by decide⟩
    (prefixPartial 12 301102) = some ⟨12, 2, 0, 1029514, 301102, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_301102_1029514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301102 ⟨1029514, by decide⟩ :=
  accepted_of_selected 12 301102 ⟨1029514, by decide⟩ ⟨12, 2, 0, 1029514, 301102, 2857, 65536⟩
    (by decide) selected_cut_38236

theorem selected_cut_38237 : selected 9 ⟨1029564, by decide⟩
    (prefixPartial 12 301103) = some ⟨12, 2, 0, 1029564, 301103, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_301103_1029564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301103 ⟨1029564, by decide⟩ :=
  accepted_of_selected 12 301103 ⟨1029564, by decide⟩ ⟨12, 2, 0, 1029564, 301103, 2929, 65536⟩
    (by decide) selected_cut_38237

theorem unmarked_context_11_75275_1029565 : frontier 10 ⟨1029565, by decide⟩
    (prefixCache 11 75275) (prefixPartial 11 75275) = false := by
  decide +kernel

theorem node_context_11_75275_1029565 : EJMOriginalGlobalDAGData.nodes 10 ⟨1029565, by decide⟩ =
    .split (coordinate 11) (![⟨1029404, by decide⟩,⟨1029457, by decide⟩,⟨1029514, by decide⟩,⟨1029564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75275_1029565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75275 ⟨1029565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75275
    ⟨1029565, by decide⟩ (by decide) (![⟨1029404, by decide⟩,⟨1029457, by decide⟩,⟨1029514, by decide⟩,⟨1029564, by decide⟩]) unmarked_context_11_75275_1029565 node_context_11_75275_1029565
  intro a
  fin_cases a
  · exact context_12_301100_1029404
  · exact context_12_301101_1029457
  · exact context_12_301102_1029514
  · exact context_12_301103_1029564

theorem unmarked_context_10_18818_1029566 : frontier 11 ⟨1029566, by decide⟩
    (prefixCache 10 18818) (prefixPartial 10 18818) = false := by
  decide +kernel

theorem node_context_10_18818_1029566 : EJMOriginalGlobalDAGData.nodes 11 ⟨1029566, by decide⟩ =
    .split (coordinate 10) (![⟨1029187, by decide⟩,⟨1029366, by decide⟩,⟨900587, by decide⟩,⟨1029565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18818_1029566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18818 ⟨1029566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18818
    ⟨1029566, by decide⟩ (by decide) (![⟨1029187, by decide⟩,⟨1029366, by decide⟩,⟨900587, by decide⟩,⟨1029565, by decide⟩]) unmarked_context_10_18818_1029566 node_context_10_18818_1029566
  intro a
  fin_cases a
  · exact context_11_75272_1029187
  · exact context_11_75273_1029366
  · exact context_11_75274_900587
  · exact context_11_75275_1029565

theorem selected_cut_38238 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 301104) = some ⟨12, 1, 0, 985390, 301104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301104_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301104 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 301104 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 301104, 1, 65536⟩
    (by decide) selected_cut_38238

theorem selected_cut_38239 : selected 9 ⟨1029613, by decide⟩
    (prefixPartial 12 301105) = some ⟨12, 2, 0, 1029613, 301105, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_301105_1029613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301105 ⟨1029613, by decide⟩ :=
  accepted_of_selected 12 301105 ⟨1029613, by decide⟩ ⟨12, 2, 0, 1029613, 301105, 2813, 65536⟩
    (by decide) selected_cut_38239

theorem selected_cut_38240 : selected 9 ⟨1029647, by decide⟩
    (prefixPartial 12 301106) = some ⟨12, 2, 0, 1029647, 301106, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_301106_1029647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301106 ⟨1029647, by decide⟩ :=
  accepted_of_selected 12 301106 ⟨1029647, by decide⟩ ⟨12, 2, 0, 1029647, 301106, 2353, 65536⟩
    (by decide) selected_cut_38240

theorem selected_cut_38241 : selected 9 ⟨1029688, by decide⟩
    (prefixPartial 12 301107) = some ⟨12, 2, 0, 1029688, 301107, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_301107_1029688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301107 ⟨1029688, by decide⟩ :=
  accepted_of_selected 12 301107 ⟨1029688, by decide⟩ ⟨12, 2, 0, 1029688, 301107, 2565, 65536⟩
    (by decide) selected_cut_38241

theorem unmarked_context_11_75276_1029689 : frontier 10 ⟨1029689, by decide⟩
    (prefixCache 11 75276) (prefixPartial 11 75276) = false := by
  decide +kernel

theorem node_context_11_75276_1029689 : EJMOriginalGlobalDAGData.nodes 10 ⟨1029689, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1029613, by decide⟩,⟨1029647, by decide⟩,⟨1029688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75276_1029689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75276 ⟨1029689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75276
    ⟨1029689, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1029613, by decide⟩,⟨1029647, by decide⟩,⟨1029688, by decide⟩]) unmarked_context_11_75276_1029689 node_context_11_75276_1029689
  intro a
  fin_cases a
  · exact context_12_301104_985390
  · exact context_12_301105_1029613
  · exact context_12_301106_1029647
  · exact context_12_301107_1029688

theorem selected_cut_38242 : selected 9 ⟨1029734, by decide⟩
    (prefixPartial 12 301108) = some ⟨12, 2, 0, 1029734, 301108, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_301108_1029734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301108 ⟨1029734, by decide⟩ :=
  accepted_of_selected 12 301108 ⟨1029734, by decide⟩ ⟨12, 2, 0, 1029734, 301108, 2773, 65536⟩
    (by decide) selected_cut_38242

theorem selected_cut_38243 : selected 9 ⟨1029784, by decide⟩
    (prefixPartial 12 301109) = some ⟨12, 2, 0, 1029784, 301109, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_301109_1029784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301109 ⟨1029784, by decide⟩ :=
  accepted_of_selected 12 301109 ⟨1029784, by decide⟩ ⟨12, 2, 0, 1029784, 301109, 3089, 65536⟩
    (by decide) selected_cut_38243

theorem selected_cut_38244 : selected 9 ⟨1029834, by decide⟩
    (prefixPartial 12 301110) = some ⟨12, 2, 0, 1029834, 301110, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_301110_1029834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301110 ⟨1029834, by decide⟩ :=
  accepted_of_selected 12 301110 ⟨1029834, by decide⟩ ⟨12, 2, 0, 1029834, 301110, 2857, 65536⟩
    (by decide) selected_cut_38244

theorem selected_cut_38245 : selected 9 ⟨1029887, by decide⟩
    (prefixPartial 12 301111) = some ⟨12, 2, 0, 1029887, 301111, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_301111_1029887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301111 ⟨1029887, by decide⟩ :=
  accepted_of_selected 12 301111 ⟨1029887, by decide⟩ ⟨12, 2, 0, 1029887, 301111, 3149, 65536⟩
    (by decide) selected_cut_38245

theorem unmarked_context_11_75277_1029888 : frontier 10 ⟨1029888, by decide⟩
    (prefixCache 11 75277) (prefixPartial 11 75277) = false := by
  decide +kernel

theorem node_context_11_75277_1029888 : EJMOriginalGlobalDAGData.nodes 10 ⟨1029888, by decide⟩ =
    .split (coordinate 11) (![⟨1029734, by decide⟩,⟨1029784, by decide⟩,⟨1029834, by decide⟩,⟨1029887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75277_1029888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75277 ⟨1029888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75277
    ⟨1029888, by decide⟩ (by decide) (![⟨1029734, by decide⟩,⟨1029784, by decide⟩,⟨1029834, by decide⟩,⟨1029887, by decide⟩]) unmarked_context_11_75277_1029888 node_context_11_75277_1029888
  intro a
  fin_cases a
  · exact context_12_301108_1029734
  · exact context_12_301109_1029784
  · exact context_12_301110_1029834
  · exact context_12_301111_1029887

theorem selected_cut_38246 : selected 9 ⟨1029929, by decide⟩
    (prefixPartial 12 301112) = some ⟨12, 2, 0, 1029929, 301112, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_301112_1029929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301112 ⟨1029929, by decide⟩ :=
  accepted_of_selected 12 301112 ⟨1029929, by decide⟩ ⟨12, 2, 0, 1029929, 301112, 2477, 65536⟩
    (by decide) selected_cut_38246

theorem selected_cut_38247 : selected 9 ⟨1029978, by decide⟩
    (prefixPartial 12 301113) = some ⟨12, 2, 0, 1029978, 301113, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_301113_1029978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301113 ⟨1029978, by decide⟩ :=
  accepted_of_selected 12 301113 ⟨1029978, by decide⟩ ⟨12, 2, 0, 1029978, 301113, 3017, 65536⟩
    (by decide) selected_cut_38247

theorem selected_cut_38248 : selected 9 ⟨1030021, by decide⟩
    (prefixPartial 12 301114) = some ⟨12, 2, 0, 1030021, 301114, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_301114_1030021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301114 ⟨1030021, by decide⟩ :=
  accepted_of_selected 12 301114 ⟨1030021, by decide⟩ ⟨12, 2, 0, 1030021, 301114, 2597, 65536⟩
    (by decide) selected_cut_38248

theorem selected_cut_38249 : selected 9 ⟨1030073, by decide⟩
    (prefixPartial 12 301115) = some ⟨12, 2, 0, 1030073, 301115, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_301115_1030073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301115 ⟨1030073, by decide⟩ :=
  accepted_of_selected 12 301115 ⟨1030073, by decide⟩ ⟨12, 2, 0, 1030073, 301115, 3129, 65536⟩
    (by decide) selected_cut_38249

theorem unmarked_context_11_75278_1030074 : frontier 10 ⟨1030074, by decide⟩
    (prefixCache 11 75278) (prefixPartial 11 75278) = false := by
  decide +kernel

theorem node_context_11_75278_1030074 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030074, by decide⟩ =
    .split (coordinate 11) (![⟨1029929, by decide⟩,⟨1029978, by decide⟩,⟨1030021, by decide⟩,⟨1030073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75278_1030074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75278 ⟨1030074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75278
    ⟨1030074, by decide⟩ (by decide) (![⟨1029929, by decide⟩,⟨1029978, by decide⟩,⟨1030021, by decide⟩,⟨1030073, by decide⟩]) unmarked_context_11_75278_1030074 node_context_11_75278_1030074
  intro a
  fin_cases a
  · exact context_12_301112_1029929
  · exact context_12_301113_1029978
  · exact context_12_301114_1030021
  · exact context_12_301115_1030073

theorem selected_cut_38250 : selected 9 ⟨1030112, by decide⟩
    (prefixPartial 12 301116) = some ⟨12, 2, 0, 1030112, 301116, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_301116_1030112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301116 ⟨1030112, by decide⟩ :=
  accepted_of_selected 12 301116 ⟨1030112, by decide⟩ ⟨12, 2, 0, 1030112, 301116, 2281, 65536⟩
    (by decide) selected_cut_38250

theorem selected_cut_38251 : selected 9 ⟨1030154, by decide⟩
    (prefixPartial 12 301117) = some ⟨12, 2, 0, 1030154, 301117, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_301117_1030154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301117 ⟨1030154, by decide⟩ :=
  accepted_of_selected 12 301117 ⟨1030154, by decide⟩ ⟨12, 2, 0, 1030154, 301117, 2905, 65536⟩
    (by decide) selected_cut_38251

theorem selected_cut_38252 : selected 9 ⟨1030199, by decide⟩
    (prefixPartial 12 301118) = some ⟨12, 2, 0, 1030199, 301118, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_301118_1030199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301118 ⟨1030199, by decide⟩ :=
  accepted_of_selected 12 301118 ⟨1030199, by decide⟩ ⟨12, 2, 0, 1030199, 301118, 2653, 65536⟩
    (by decide) selected_cut_38252

theorem selected_cut_38253 : selected 9 ⟨1030241, by decide⟩
    (prefixPartial 12 301119) = some ⟨12, 2, 0, 1030241, 301119, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_301119_1030241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301119 ⟨1030241, by decide⟩ :=
  accepted_of_selected 12 301119 ⟨1030241, by decide⟩ ⟨12, 2, 0, 1030241, 301119, 2633, 65536⟩
    (by decide) selected_cut_38253

theorem unmarked_context_11_75279_1030242 : frontier 10 ⟨1030242, by decide⟩
    (prefixCache 11 75279) (prefixPartial 11 75279) = false := by
  decide +kernel

theorem node_context_11_75279_1030242 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030242, by decide⟩ =
    .split (coordinate 11) (![⟨1030112, by decide⟩,⟨1030154, by decide⟩,⟨1030199, by decide⟩,⟨1030241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75279_1030242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75279 ⟨1030242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75279
    ⟨1030242, by decide⟩ (by decide) (![⟨1030112, by decide⟩,⟨1030154, by decide⟩,⟨1030199, by decide⟩,⟨1030241, by decide⟩]) unmarked_context_11_75279_1030242 node_context_11_75279_1030242
  intro a
  fin_cases a
  · exact context_12_301116_1030112
  · exact context_12_301117_1030154
  · exact context_12_301118_1030199
  · exact context_12_301119_1030241

theorem unmarked_context_10_18819_1030243 : frontier 11 ⟨1030243, by decide⟩
    (prefixCache 10 18819) (prefixPartial 10 18819) = false := by
  decide +kernel

theorem node_context_10_18819_1030243 : EJMOriginalGlobalDAGData.nodes 11 ⟨1030243, by decide⟩ =
    .split (coordinate 10) (![⟨1029689, by decide⟩,⟨1029888, by decide⟩,⟨1030074, by decide⟩,⟨1030242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18819_1030243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18819 ⟨1030243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18819
    ⟨1030243, by decide⟩ (by decide) (![⟨1029689, by decide⟩,⟨1029888, by decide⟩,⟨1030074, by decide⟩,⟨1030242, by decide⟩]) unmarked_context_10_18819_1030243 node_context_10_18819_1030243
  intro a
  fin_cases a
  · exact context_11_75276_1029689
  · exact context_11_75277_1029888
  · exact context_11_75278_1030074
  · exact context_11_75279_1030242

theorem unmarked_context_9_4704_1030244 : frontier 12 ⟨1030244, by decide⟩
    (prefixCache 9 4704) (prefixPartial 9 4704) = false := by
  decide +kernel

theorem node_context_9_4704_1030244 : EJMOriginalGlobalDAGData.nodes 12 ⟨1030244, by decide⟩ =
    .split (coordinate 9) (![⟨1028334, by decide⟩,⟨1029081, by decide⟩,⟨1029566, by decide⟩,⟨1030243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4704_1030244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4704 ⟨1030244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4704
    ⟨1030244, by decide⟩ (by decide) (![⟨1028334, by decide⟩,⟨1029081, by decide⟩,⟨1029566, by decide⟩,⟨1030243, by decide⟩]) unmarked_context_9_4704_1030244 node_context_9_4704_1030244
  intro a
  fin_cases a
  · exact context_10_18816_1028334
  · exact context_10_18817_1029081
  · exact context_10_18818_1029566
  · exact context_10_18819_1030243

theorem selected_cut_38254 : selected 9 ⟨1030245, by decide⟩
    (prefixPartial 12 301120) = some ⟨12, 1, 0, 1030245, 301120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301120_1030245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301120 ⟨1030245, by decide⟩ :=
  accepted_of_selected 12 301120 ⟨1030245, by decide⟩ ⟨12, 1, 0, 1030245, 301120, 1, 65536⟩
    (by decide) selected_cut_38254

theorem selected_cut_38255 : selected 9 ⟨1030274, by decide⟩
    (prefixPartial 12 301121) = some ⟨12, 2, 0, 1030274, 301121, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_301121_1030274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301121 ⟨1030274, by decide⟩ :=
  accepted_of_selected 12 301121 ⟨1030274, by decide⟩ ⟨12, 2, 0, 1030274, 301121, 1953, 65536⟩
    (by decide) selected_cut_38255

theorem selected_cut_38256 : selected 9 ⟨1030300, by decide⟩
    (prefixPartial 12 301122) = some ⟨12, 2, 0, 1030300, 301122, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_301122_1030300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301122 ⟨1030300, by decide⟩ :=
  accepted_of_selected 12 301122 ⟨1030300, by decide⟩ ⟨12, 2, 0, 1030300, 301122, 1733, 65536⟩
    (by decide) selected_cut_38256

theorem selected_cut_38257 : selected 9 ⟨1030324, by decide⟩
    (prefixPartial 12 301123) = some ⟨12, 2, 0, 1030324, 301123, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_301123_1030324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301123 ⟨1030324, by decide⟩ :=
  accepted_of_selected 12 301123 ⟨1030324, by decide⟩ ⟨12, 2, 0, 1030324, 301123, 1781, 65536⟩
    (by decide) selected_cut_38257

theorem unmarked_context_11_75280_1030325 : frontier 10 ⟨1030325, by decide⟩
    (prefixCache 11 75280) (prefixPartial 11 75280) = false := by
  decide +kernel

theorem node_context_11_75280_1030325 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030325, by decide⟩ =
    .split (coordinate 11) (![⟨1030245, by decide⟩,⟨1030274, by decide⟩,⟨1030300, by decide⟩,⟨1030324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75280_1030325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75280 ⟨1030325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75280
    ⟨1030325, by decide⟩ (by decide) (![⟨1030245, by decide⟩,⟨1030274, by decide⟩,⟨1030300, by decide⟩,⟨1030324, by decide⟩]) unmarked_context_11_75280_1030325 node_context_11_75280_1030325
  intro a
  fin_cases a
  · exact context_12_301120_1030245
  · exact context_12_301121_1030274
  · exact context_12_301122_1030300
  · exact context_12_301123_1030324

theorem selected_cut_38258 : selected 9 ⟨1030363, by decide⟩
    (prefixPartial 12 301124) = some ⟨12, 2, 0, 1030363, 301124, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_301124_1030363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301124 ⟨1030363, by decide⟩ :=
  accepted_of_selected 12 301124 ⟨1030363, by decide⟩ ⟨12, 2, 0, 1030363, 301124, 2437, 65536⟩
    (by decide) selected_cut_38258

theorem selected_cut_38259 : selected 9 ⟨1030411, by decide⟩
    (prefixPartial 12 301125) = some ⟨12, 2, 0, 1030411, 301125, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_301125_1030411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301125 ⟨1030411, by decide⟩ :=
  accepted_of_selected 12 301125 ⟨1030411, by decide⟩ ⟨12, 2, 0, 1030411, 301125, 1113, 65536⟩
    (by decide) selected_cut_38259

theorem selected_cut_38260 : selected 9 ⟨1030450, by decide⟩
    (prefixPartial 12 301126) = some ⟨12, 2, 0, 1030450, 301126, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_301126_1030450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301126 ⟨1030450, by decide⟩ :=
  accepted_of_selected 12 301126 ⟨1030450, by decide⟩ ⟨12, 2, 0, 1030450, 301126, 2261, 65536⟩
    (by decide) selected_cut_38260

theorem selected_cut_38261 : selected 9 ⟨1030481, by decide⟩
    (prefixPartial 12 301127) = some ⟨12, 2, 0, 1030481, 301127, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_301127_1030481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301127 ⟨1030481, by decide⟩ :=
  accepted_of_selected 12 301127 ⟨1030481, by decide⟩ ⟨12, 2, 0, 1030481, 301127, 2169, 65536⟩
    (by decide) selected_cut_38261

theorem unmarked_context_11_75281_1030482 : frontier 10 ⟨1030482, by decide⟩
    (prefixCache 11 75281) (prefixPartial 11 75281) = false := by
  decide +kernel

theorem node_context_11_75281_1030482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030482, by decide⟩ =
    .split (coordinate 11) (![⟨1030363, by decide⟩,⟨1030411, by decide⟩,⟨1030450, by decide⟩,⟨1030481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75281_1030482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75281 ⟨1030482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75281
    ⟨1030482, by decide⟩ (by decide) (![⟨1030363, by decide⟩,⟨1030411, by decide⟩,⟨1030450, by decide⟩,⟨1030481, by decide⟩]) unmarked_context_11_75281_1030482 node_context_11_75281_1030482
  intro a
  fin_cases a
  · exact context_12_301124_1030363
  · exact context_12_301125_1030411
  · exact context_12_301126_1030450
  · exact context_12_301127_1030481

theorem selected_cut_38262 : selected 9 ⟨1030513, by decide⟩
    (prefixPartial 12 301128) = some ⟨12, 2, 0, 1030513, 301128, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_301128_1030513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301128 ⟨1030513, by decide⟩ :=
  accepted_of_selected 12 301128 ⟨1030513, by decide⟩ ⟨12, 2, 0, 1030513, 301128, 2149, 65536⟩
    (by decide) selected_cut_38262

theorem selected_cut_38263 : selected 9 ⟨1030542, by decide⟩
    (prefixPartial 12 301129) = some ⟨12, 2, 0, 1030542, 301129, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_301129_1030542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301129 ⟨1030542, by decide⟩ :=
  accepted_of_selected 12 301129 ⟨1030542, by decide⟩ ⟨12, 2, 0, 1030542, 301129, 2073, 65536⟩
    (by decide) selected_cut_38263

theorem selected_cut_38264 : selected 9 ⟨1030571, by decide⟩
    (prefixPartial 12 301130) = some ⟨12, 2, 0, 1030571, 301130, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_301130_1030571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301130 ⟨1030571, by decide⟩ :=
  accepted_of_selected 12 301130 ⟨1030571, by decide⟩ ⟨12, 2, 0, 1030571, 301130, 1993, 65536⟩
    (by decide) selected_cut_38264

theorem selected_cut_38265 : selected 9 ⟨1030600, by decide⟩
    (prefixPartial 12 301131) = some ⟨12, 2, 0, 1030600, 301131, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_301131_1030600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301131 ⟨1030600, by decide⟩ :=
  accepted_of_selected 12 301131 ⟨1030600, by decide⟩ ⟨12, 2, 0, 1030600, 301131, 2101, 65536⟩
    (by decide) selected_cut_38265

theorem unmarked_context_11_75282_1030601 : frontier 10 ⟨1030601, by decide⟩
    (prefixCache 11 75282) (prefixPartial 11 75282) = false := by
  decide +kernel

theorem node_context_11_75282_1030601 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030601, by decide⟩ =
    .split (coordinate 11) (![⟨1030513, by decide⟩,⟨1030542, by decide⟩,⟨1030571, by decide⟩,⟨1030600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75282_1030601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75282 ⟨1030601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75282
    ⟨1030601, by decide⟩ (by decide) (![⟨1030513, by decide⟩,⟨1030542, by decide⟩,⟨1030571, by decide⟩,⟨1030600, by decide⟩]) unmarked_context_11_75282_1030601 node_context_11_75282_1030601
  intro a
  fin_cases a
  · exact context_12_301128_1030513
  · exact context_12_301129_1030542
  · exact context_12_301130_1030571
  · exact context_12_301131_1030600

theorem selected_cut_38266 : selected 9 ⟨1030639, by decide⟩
    (prefixPartial 12 301132) = some ⟨12, 2, 0, 1030639, 301132, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_301132_1030639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301132 ⟨1030639, by decide⟩ :=
  accepted_of_selected 12 301132 ⟨1030639, by decide⟩ ⟨12, 2, 0, 1030639, 301132, 2261, 65536⟩
    (by decide) selected_cut_38266

theorem selected_cut_38267 : selected 9 ⟨1030675, by decide⟩
    (prefixPartial 12 301133) = some ⟨12, 2, 0, 1030675, 301133, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_301133_1030675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301133 ⟨1030675, by decide⟩ :=
  accepted_of_selected 12 301133 ⟨1030675, by decide⟩ ⟨12, 2, 0, 1030675, 301133, 2141, 65536⟩
    (by decide) selected_cut_38267

theorem selected_cut_38268 : selected 9 ⟨1030724, by decide⟩
    (prefixPartial 12 301134) = some ⟨12, 2, 0, 1030724, 301134, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_301134_1030724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301134 ⟨1030724, by decide⟩ :=
  accepted_of_selected 12 301134 ⟨1030724, by decide⟩ ⟨12, 2, 0, 1030724, 301134, 2285, 65536⟩
    (by decide) selected_cut_38268

theorem selected_cut_38269 : selected 9 ⟨1030753, by decide⟩
    (prefixPartial 12 301135) = some ⟨12, 2, 0, 1030753, 301135, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_301135_1030753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301135 ⟨1030753, by decide⟩ :=
  accepted_of_selected 12 301135 ⟨1030753, by decide⟩ ⟨12, 2, 0, 1030753, 301135, 1985, 65536⟩
    (by decide) selected_cut_38269

theorem unmarked_context_11_75283_1030754 : frontier 10 ⟨1030754, by decide⟩
    (prefixCache 11 75283) (prefixPartial 11 75283) = false := by
  decide +kernel

theorem node_context_11_75283_1030754 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030754, by decide⟩ =
    .split (coordinate 11) (![⟨1030639, by decide⟩,⟨1030675, by decide⟩,⟨1030724, by decide⟩,⟨1030753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75283_1030754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75283 ⟨1030754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75283
    ⟨1030754, by decide⟩ (by decide) (![⟨1030639, by decide⟩,⟨1030675, by decide⟩,⟨1030724, by decide⟩,⟨1030753, by decide⟩]) unmarked_context_11_75283_1030754 node_context_11_75283_1030754
  intro a
  fin_cases a
  · exact context_12_301132_1030639
  · exact context_12_301133_1030675
  · exact context_12_301134_1030724
  · exact context_12_301135_1030753

theorem unmarked_context_10_18820_1030755 : frontier 11 ⟨1030755, by decide⟩
    (prefixCache 10 18820) (prefixPartial 10 18820) = false := by
  decide +kernel

theorem node_context_10_18820_1030755 : EJMOriginalGlobalDAGData.nodes 11 ⟨1030755, by decide⟩ =
    .split (coordinate 10) (![⟨1030325, by decide⟩,⟨1030482, by decide⟩,⟨1030601, by decide⟩,⟨1030754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18820_1030755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18820 ⟨1030755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18820
    ⟨1030755, by decide⟩ (by decide) (![⟨1030325, by decide⟩,⟨1030482, by decide⟩,⟨1030601, by decide⟩,⟨1030754, by decide⟩]) unmarked_context_10_18820_1030755 node_context_10_18820_1030755
  intro a
  fin_cases a
  · exact context_11_75280_1030325
  · exact context_11_75281_1030482
  · exact context_11_75282_1030601
  · exact context_11_75283_1030754

theorem selected_cut_38270 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18821) = some ⟨10, 1, 0, 893098, 18821, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18821_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18821 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18821 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18821, 1, 1048576⟩
    (by decide) selected_cut_38270

theorem selected_cut_38271 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 301152) = some ⟨12, 1, 0, 985390, 301152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301152_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301152 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 301152 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 301152, 1, 65536⟩
    (by decide) selected_cut_38271

theorem selected_cut_38272 : selected 9 ⟨1030769, by decide⟩
    (prefixPartial 12 301153) = some ⟨12, 2, 0, 1030769, 301153, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_301153_1030769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301153 ⟨1030769, by decide⟩ :=
  accepted_of_selected 12 301153 ⟨1030769, by decide⟩ ⟨12, 2, 0, 1030769, 301153, 1501, 65536⟩
    (by decide) selected_cut_38272

theorem selected_cut_38273 : selected 9 ⟨1030792, by decide⟩
    (prefixPartial 12 301154) = some ⟨12, 2, 0, 1030792, 301154, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_301154_1030792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301154 ⟨1030792, by decide⟩ :=
  accepted_of_selected 12 301154 ⟨1030792, by decide⟩ ⟨12, 2, 0, 1030792, 301154, 1277, 65536⟩
    (by decide) selected_cut_38273

theorem selected_cut_38274 : selected 9 ⟨1030805, by decide⟩
    (prefixPartial 12 301155) = some ⟨12, 2, 0, 1030805, 301155, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_301155_1030805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301155 ⟨1030805, by decide⟩ :=
  accepted_of_selected 12 301155 ⟨1030805, by decide⟩ ⟨12, 2, 0, 1030805, 301155, 1397, 65536⟩
    (by decide) selected_cut_38274

theorem unmarked_context_11_75288_1030806 : frontier 10 ⟨1030806, by decide⟩
    (prefixCache 11 75288) (prefixPartial 11 75288) = false := by
  decide +kernel

theorem node_context_11_75288_1030806 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030806, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1030769, by decide⟩,⟨1030792, by decide⟩,⟨1030805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75288_1030806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75288 ⟨1030806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75288
    ⟨1030806, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1030769, by decide⟩,⟨1030792, by decide⟩,⟨1030805, by decide⟩]) unmarked_context_11_75288_1030806 node_context_11_75288_1030806
  intro a
  fin_cases a
  · exact context_12_301152_985390
  · exact context_12_301153_1030769
  · exact context_12_301154_1030792
  · exact context_12_301155_1030805

theorem selected_cut_38275 : selected 9 ⟨1030832, by decide⟩
    (prefixPartial 12 301156) = some ⟨12, 2, 0, 1030832, 301156, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_301156_1030832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301156 ⟨1030832, by decide⟩ :=
  accepted_of_selected 12 301156 ⟨1030832, by decide⟩ ⟨12, 2, 0, 1030832, 301156, 1725, 65536⟩
    (by decide) selected_cut_38275

theorem selected_cut_38276 : selected 9 ⟨417109, by decide⟩
    (prefixPartial 12 301157) = some ⟨12, 1, 0, 417109, 301157, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301157_417109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301157 ⟨417109, by decide⟩ :=
  accepted_of_selected 12 301157 ⟨417109, by decide⟩ ⟨12, 1, 0, 417109, 301157, 1, 65536⟩
    (by decide) selected_cut_38276

theorem selected_cut_38277 : selected 9 ⟨1030854, by decide⟩
    (prefixPartial 12 301158) = some ⟨12, 2, 0, 1030854, 301158, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_301158_1030854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301158 ⟨1030854, by decide⟩ :=
  accepted_of_selected 12 301158 ⟨1030854, by decide⟩ ⟨12, 2, 0, 1030854, 301158, 1541, 65536⟩
    (by decide) selected_cut_38277

theorem selected_cut_38278 : selected 9 ⟨1030875, by decide⟩
    (prefixPartial 12 301159) = some ⟨12, 2, 0, 1030875, 301159, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_301159_1030875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301159 ⟨1030875, by decide⟩ :=
  accepted_of_selected 12 301159 ⟨1030875, by decide⟩ ⟨12, 2, 0, 1030875, 301159, 1645, 65536⟩
    (by decide) selected_cut_38278

theorem unmarked_context_11_75289_1030876 : frontier 10 ⟨1030876, by decide⟩
    (prefixCache 11 75289) (prefixPartial 11 75289) = false := by
  decide +kernel

theorem node_context_11_75289_1030876 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030876, by decide⟩ =
    .split (coordinate 11) (![⟨1030832, by decide⟩,⟨417109, by decide⟩,⟨1030854, by decide⟩,⟨1030875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75289_1030876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75289 ⟨1030876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75289
    ⟨1030876, by decide⟩ (by decide) (![⟨1030832, by decide⟩,⟨417109, by decide⟩,⟨1030854, by decide⟩,⟨1030875, by decide⟩]) unmarked_context_11_75289_1030876 node_context_11_75289_1030876
  intro a
  fin_cases a
  · exact context_12_301156_1030832
  · exact context_12_301157_417109
  · exact context_12_301158_1030854
  · exact context_12_301159_1030875

theorem selected_cut_38279 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75290) = some ⟨11, 1, 0, 900587, 75290, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75290_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75290 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75290 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75290, 1, 262144⟩
    (by decide) selected_cut_38279

theorem selected_cut_38280 : selected 9 ⟨1030898, by decide⟩
    (prefixPartial 12 301164) = some ⟨12, 2, 0, 1030898, 301164, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_301164_1030898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301164 ⟨1030898, by decide⟩ :=
  accepted_of_selected 12 301164 ⟨1030898, by decide⟩ ⟨12, 2, 0, 1030898, 301164, 1629, 65536⟩
    (by decide) selected_cut_38280

theorem selected_cut_38281 : selected 9 ⟨1030924, by decide⟩
    (prefixPartial 12 301165) = some ⟨12, 2, 0, 1030924, 301165, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_301165_1030924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301165 ⟨1030924, by decide⟩ :=
  accepted_of_selected 12 301165 ⟨1030924, by decide⟩ ⟨12, 2, 0, 1030924, 301165, 1753, 65536⟩
    (by decide) selected_cut_38281

theorem selected_cut_38282 : selected 9 ⟨1030945, by decide⟩
    (prefixPartial 12 301166) = some ⟨12, 2, 0, 1030945, 301166, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_301166_1030945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301166 ⟨1030945, by decide⟩ :=
  accepted_of_selected 12 301166 ⟨1030945, by decide⟩ ⟨12, 2, 0, 1030945, 301166, 1641, 65536⟩
    (by decide) selected_cut_38282

theorem selected_cut_38283 : selected 9 ⟨1030959, by decide⟩
    (prefixPartial 12 301167) = some ⟨12, 2, 0, 1030959, 301167, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_301167_1030959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301167 ⟨1030959, by decide⟩ :=
  accepted_of_selected 12 301167 ⟨1030959, by decide⟩ ⟨12, 2, 0, 1030959, 301167, 1557, 65536⟩
    (by decide) selected_cut_38283

theorem unmarked_context_11_75291_1030960 : frontier 10 ⟨1030960, by decide⟩
    (prefixCache 11 75291) (prefixPartial 11 75291) = false := by
  decide +kernel

theorem node_context_11_75291_1030960 : EJMOriginalGlobalDAGData.nodes 10 ⟨1030960, by decide⟩ =
    .split (coordinate 11) (![⟨1030898, by decide⟩,⟨1030924, by decide⟩,⟨1030945, by decide⟩,⟨1030959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75291_1030960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75291 ⟨1030960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75291
    ⟨1030960, by decide⟩ (by decide) (![⟨1030898, by decide⟩,⟨1030924, by decide⟩,⟨1030945, by decide⟩,⟨1030959, by decide⟩]) unmarked_context_11_75291_1030960 node_context_11_75291_1030960
  intro a
  fin_cases a
  · exact context_12_301164_1030898
  · exact context_12_301165_1030924
  · exact context_12_301166_1030945
  · exact context_12_301167_1030959

theorem unmarked_context_10_18822_1030961 : frontier 11 ⟨1030961, by decide⟩
    (prefixCache 10 18822) (prefixPartial 10 18822) = false := by
  decide +kernel

theorem node_context_10_18822_1030961 : EJMOriginalGlobalDAGData.nodes 11 ⟨1030961, by decide⟩ =
    .split (coordinate 10) (![⟨1030806, by decide⟩,⟨1030876, by decide⟩,⟨900587, by decide⟩,⟨1030960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18822_1030961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18822 ⟨1030961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18822
    ⟨1030961, by decide⟩ (by decide) (![⟨1030806, by decide⟩,⟨1030876, by decide⟩,⟨900587, by decide⟩,⟨1030960, by decide⟩]) unmarked_context_10_18822_1030961 node_context_10_18822_1030961
  intro a
  fin_cases a
  · exact context_11_75288_1030806
  · exact context_11_75289_1030876
  · exact context_11_75290_900587
  · exact context_11_75291_1030960

theorem selected_cut_38284 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 301168) = some ⟨12, 1, 0, 985390, 301168, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301168_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301168 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 301168 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 301168, 1, 65536⟩
    (by decide) selected_cut_38284

theorem selected_cut_38285 : selected 9 ⟨1030983, by decide⟩
    (prefixPartial 12 301169) = some ⟨12, 2, 0, 1030983, 301169, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_301169_1030983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301169 ⟨1030983, by decide⟩ :=
  accepted_of_selected 12 301169 ⟨1030983, by decide⟩ ⟨12, 2, 0, 1030983, 301169, 1505, 65536⟩
    (by decide) selected_cut_38285

theorem selected_cut_38286 : selected 9 ⟨1030999, by decide⟩
    (prefixPartial 12 301170) = some ⟨12, 2, 0, 1030999, 301170, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_301170_1030999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301170 ⟨1030999, by decide⟩ :=
  accepted_of_selected 12 301170 ⟨1030999, by decide⟩ ⟨12, 2, 0, 1030999, 301170, 1269, 65536⟩
    (by decide) selected_cut_38286

theorem selected_cut_38287 : selected 9 ⟨1031020, by decide⟩
    (prefixPartial 12 301171) = some ⟨12, 2, 0, 1031020, 301171, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_301171_1031020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301171 ⟨1031020, by decide⟩ :=
  accepted_of_selected 12 301171 ⟨1031020, by decide⟩ ⟨12, 2, 0, 1031020, 301171, 1377, 65536⟩
    (by decide) selected_cut_38287

theorem unmarked_context_11_75292_1031021 : frontier 10 ⟨1031021, by decide⟩
    (prefixCache 11 75292) (prefixPartial 11 75292) = false := by
  decide +kernel

theorem node_context_11_75292_1031021 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031021, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1030983, by decide⟩,⟨1030999, by decide⟩,⟨1031020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75292_1031021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75292 ⟨1031021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75292
    ⟨1031021, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1030983, by decide⟩,⟨1030999, by decide⟩,⟨1031020, by decide⟩]) unmarked_context_11_75292_1031021 node_context_11_75292_1031021
  intro a
  fin_cases a
  · exact context_12_301168_985390
  · exact context_12_301169_1030983
  · exact context_12_301170_1030999
  · exact context_12_301171_1031020

theorem selected_cut_38288 : selected 9 ⟨1031045, by decide⟩
    (prefixPartial 12 301172) = some ⟨12, 2, 0, 1031045, 301172, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_301172_1031045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301172 ⟨1031045, by decide⟩ :=
  accepted_of_selected 12 301172 ⟨1031045, by decide⟩ ⟨12, 2, 0, 1031045, 301172, 1717, 65536⟩
    (by decide) selected_cut_38288

theorem selected_cut_38289 : selected 9 ⟨1031076, by decide⟩
    (prefixPartial 12 301173) = some ⟨12, 2, 0, 1031076, 301173, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_301173_1031076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301173 ⟨1031076, by decide⟩ :=
  accepted_of_selected 12 301173 ⟨1031076, by decide⟩ ⟨12, 2, 0, 1031076, 301173, 1665, 65536⟩
    (by decide) selected_cut_38289

theorem selected_cut_38290 : selected 9 ⟨1031097, by decide⟩
    (prefixPartial 12 301174) = some ⟨12, 2, 0, 1031097, 301174, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_301174_1031097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301174 ⟨1031097, by decide⟩ :=
  accepted_of_selected 12 301174 ⟨1031097, by decide⟩ ⟨12, 2, 0, 1031097, 301174, 1533, 65536⟩
    (by decide) selected_cut_38290

theorem selected_cut_38291 : selected 9 ⟨1031122, by decide⟩
    (prefixPartial 12 301175) = some ⟨12, 2, 0, 1031122, 301175, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_301175_1031122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301175 ⟨1031122, by decide⟩ :=
  accepted_of_selected 12 301175 ⟨1031122, by decide⟩ ⟨12, 2, 0, 1031122, 301175, 1649, 65536⟩
    (by decide) selected_cut_38291

theorem unmarked_context_11_75293_1031123 : frontier 10 ⟨1031123, by decide⟩
    (prefixCache 11 75293) (prefixPartial 11 75293) = false := by
  decide +kernel

theorem node_context_11_75293_1031123 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031123, by decide⟩ =
    .split (coordinate 11) (![⟨1031045, by decide⟩,⟨1031076, by decide⟩,⟨1031097, by decide⟩,⟨1031122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75293_1031123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75293 ⟨1031123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75293
    ⟨1031123, by decide⟩ (by decide) (![⟨1031045, by decide⟩,⟨1031076, by decide⟩,⟨1031097, by decide⟩,⟨1031122, by decide⟩]) unmarked_context_11_75293_1031123 node_context_11_75293_1031123
  intro a
  fin_cases a
  · exact context_12_301172_1031045
  · exact context_12_301173_1031076
  · exact context_12_301174_1031097
  · exact context_12_301175_1031122

theorem selected_cut_38292 : selected 9 ⟨1031143, by decide⟩
    (prefixPartial 12 301176) = some ⟨12, 2, 0, 1031143, 301176, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_301176_1031143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301176 ⟨1031143, by decide⟩ :=
  accepted_of_selected 12 301176 ⟨1031143, by decide⟩ ⟨12, 2, 0, 1031143, 301176, 1485, 65536⟩
    (by decide) selected_cut_38292

theorem selected_cut_38293 : selected 9 ⟨1031166, by decide⟩
    (prefixPartial 12 301177) = some ⟨12, 2, 0, 1031166, 301177, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_301177_1031166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301177 ⟨1031166, by decide⟩ :=
  accepted_of_selected 12 301177 ⟨1031166, by decide⟩ ⟨12, 2, 0, 1031166, 301177, 1533, 65536⟩
    (by decide) selected_cut_38293

theorem selected_cut_38294 : selected 9 ⟨1031185, by decide⟩
    (prefixPartial 12 301178) = some ⟨12, 2, 0, 1031185, 301178, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_301178_1031185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301178 ⟨1031185, by decide⟩ :=
  accepted_of_selected 12 301178 ⟨1031185, by decide⟩ ⟨12, 2, 0, 1031185, 301178, 1357, 65536⟩
    (by decide) selected_cut_38294

theorem selected_cut_38295 : selected 9 ⟨1031208, by decide⟩
    (prefixPartial 12 301179) = some ⟨12, 2, 0, 1031208, 301179, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_301179_1031208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301179 ⟨1031208, by decide⟩ :=
  accepted_of_selected 12 301179 ⟨1031208, by decide⟩ ⟨12, 2, 0, 1031208, 301179, 1533, 65536⟩
    (by decide) selected_cut_38295

theorem unmarked_context_11_75294_1031209 : frontier 10 ⟨1031209, by decide⟩
    (prefixCache 11 75294) (prefixPartial 11 75294) = false := by
  decide +kernel

theorem node_context_11_75294_1031209 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031209, by decide⟩ =
    .split (coordinate 11) (![⟨1031143, by decide⟩,⟨1031166, by decide⟩,⟨1031185, by decide⟩,⟨1031208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75294_1031209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75294 ⟨1031209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75294
    ⟨1031209, by decide⟩ (by decide) (![⟨1031143, by decide⟩,⟨1031166, by decide⟩,⟨1031185, by decide⟩,⟨1031208, by decide⟩]) unmarked_context_11_75294_1031209 node_context_11_75294_1031209
  intro a
  fin_cases a
  · exact context_12_301176_1031143
  · exact context_12_301177_1031166
  · exact context_12_301178_1031185
  · exact context_12_301179_1031208

theorem selected_cut_38296 : selected 9 ⟨1031232, by decide⟩
    (prefixPartial 12 301180) = some ⟨12, 2, 0, 1031232, 301180, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_301180_1031232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301180 ⟨1031232, by decide⟩ :=
  accepted_of_selected 12 301180 ⟨1031232, by decide⟩ ⟨12, 2, 0, 1031232, 301180, 1525, 65536⟩
    (by decide) selected_cut_38296

theorem selected_cut_38297 : selected 9 ⟨1031259, by decide⟩
    (prefixPartial 12 301181) = some ⟨12, 2, 0, 1031259, 301181, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_301181_1031259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301181 ⟨1031259, by decide⟩ :=
  accepted_of_selected 12 301181 ⟨1031259, by decide⟩ ⟨12, 2, 0, 1031259, 301181, 1549, 65536⟩
    (by decide) selected_cut_38297

theorem selected_cut_38298 : selected 9 ⟨1031283, by decide⟩
    (prefixPartial 12 301182) = some ⟨12, 2, 0, 1031283, 301182, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_301182_1031283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301182 ⟨1031283, by decide⟩ :=
  accepted_of_selected 12 301182 ⟨1031283, by decide⟩ ⟨12, 2, 0, 1031283, 301182, 1553, 65536⟩
    (by decide) selected_cut_38298

theorem selected_cut_38299 : selected 9 ⟨1031305, by decide⟩
    (prefixPartial 12 301183) = some ⟨12, 2, 0, 1031305, 301183, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_301183_1031305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301183 ⟨1031305, by decide⟩ :=
  accepted_of_selected 12 301183 ⟨1031305, by decide⟩ ⟨12, 2, 0, 1031305, 301183, 1417, 65536⟩
    (by decide) selected_cut_38299

theorem unmarked_context_11_75295_1031306 : frontier 10 ⟨1031306, by decide⟩
    (prefixCache 11 75295) (prefixPartial 11 75295) = false := by
  decide +kernel

theorem node_context_11_75295_1031306 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031306, by decide⟩ =
    .split (coordinate 11) (![⟨1031232, by decide⟩,⟨1031259, by decide⟩,⟨1031283, by decide⟩,⟨1031305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75295_1031306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75295 ⟨1031306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75295
    ⟨1031306, by decide⟩ (by decide) (![⟨1031232, by decide⟩,⟨1031259, by decide⟩,⟨1031283, by decide⟩,⟨1031305, by decide⟩]) unmarked_context_11_75295_1031306 node_context_11_75295_1031306
  intro a
  fin_cases a
  · exact context_12_301180_1031232
  · exact context_12_301181_1031259
  · exact context_12_301182_1031283
  · exact context_12_301183_1031305

theorem unmarked_context_10_18823_1031307 : frontier 11 ⟨1031307, by decide⟩
    (prefixCache 10 18823) (prefixPartial 10 18823) = false := by
  decide +kernel

theorem node_context_10_18823_1031307 : EJMOriginalGlobalDAGData.nodes 11 ⟨1031307, by decide⟩ =
    .split (coordinate 10) (![⟨1031021, by decide⟩,⟨1031123, by decide⟩,⟨1031209, by decide⟩,⟨1031306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18823_1031307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18823 ⟨1031307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18823
    ⟨1031307, by decide⟩ (by decide) (![⟨1031021, by decide⟩,⟨1031123, by decide⟩,⟨1031209, by decide⟩,⟨1031306, by decide⟩]) unmarked_context_10_18823_1031307 node_context_10_18823_1031307
  intro a
  fin_cases a
  · exact context_11_75292_1031021
  · exact context_11_75293_1031123
  · exact context_11_75294_1031209
  · exact context_11_75295_1031306

theorem unmarked_context_9_4705_1031308 : frontier 12 ⟨1031308, by decide⟩
    (prefixCache 9 4705) (prefixPartial 9 4705) = false := by
  decide +kernel

theorem node_context_9_4705_1031308 : EJMOriginalGlobalDAGData.nodes 12 ⟨1031308, by decide⟩ =
    .split (coordinate 9) (![⟨1030755, by decide⟩,⟨893098, by decide⟩,⟨1030961, by decide⟩,⟨1031307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4705_1031308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4705 ⟨1031308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4705
    ⟨1031308, by decide⟩ (by decide) (![⟨1030755, by decide⟩,⟨893098, by decide⟩,⟨1030961, by decide⟩,⟨1031307, by decide⟩]) unmarked_context_9_4705_1031308 node_context_9_4705_1031308
  intro a
  fin_cases a
  · exact context_10_18820_1030755
  · exact context_10_18821_893098
  · exact context_10_18822_1030961
  · exact context_10_18823_1031307

theorem selected_cut_38300 : selected 10 ⟨1031343, by decide⟩
    (prefixPartial 11 75296) = some ⟨11, 2, 0, 1031343, 75296, 2561, 262144⟩ := by
  decide +kernel

theorem context_11_75296_1031343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75296 ⟨1031343, by decide⟩ :=
  accepted_of_selected 11 75296 ⟨1031343, by decide⟩ ⟨11, 2, 0, 1031343, 75296, 2561, 262144⟩
    (by decide) selected_cut_38300

theorem selected_cut_38301 : selected 9 ⟨1031376, by decide⟩
    (prefixPartial 12 301188) = some ⟨12, 2, 0, 1031376, 301188, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_301188_1031376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301188 ⟨1031376, by decide⟩ :=
  accepted_of_selected 12 301188 ⟨1031376, by decide⟩ ⟨12, 2, 0, 1031376, 301188, 1721, 65536⟩
    (by decide) selected_cut_38301

theorem selected_cut_38302 : selected 9 ⟨1031402, by decide⟩
    (prefixPartial 12 301189) = some ⟨12, 2, 0, 1031402, 301189, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_301189_1031402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301189 ⟨1031402, by decide⟩ :=
  accepted_of_selected 12 301189 ⟨1031402, by decide⟩ ⟨12, 2, 0, 1031402, 301189, 1617, 65536⟩
    (by decide) selected_cut_38302

theorem selected_cut_38303 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 301190) = some ⟨12, 1, 0, 984676, 301190, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301190_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301190 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 301190 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 301190, 1, 65536⟩
    (by decide) selected_cut_38303

theorem selected_cut_38304 : selected 9 ⟨1031430, by decide⟩
    (prefixPartial 12 301191) = some ⟨12, 2, 0, 1031430, 301191, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_301191_1031430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301191 ⟨1031430, by decide⟩ :=
  accepted_of_selected 12 301191 ⟨1031430, by decide⟩ ⟨12, 2, 0, 1031430, 301191, 1517, 65536⟩
    (by decide) selected_cut_38304

theorem unmarked_context_11_75297_1031431 : frontier 10 ⟨1031431, by decide⟩
    (prefixCache 11 75297) (prefixPartial 11 75297) = false := by
  decide +kernel

theorem node_context_11_75297_1031431 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031431, by decide⟩ =
    .split (coordinate 11) (![⟨1031376, by decide⟩,⟨1031402, by decide⟩,⟨984676, by decide⟩,⟨1031430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75297_1031431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75297 ⟨1031431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75297
    ⟨1031431, by decide⟩ (by decide) (![⟨1031376, by decide⟩,⟨1031402, by decide⟩,⟨984676, by decide⟩,⟨1031430, by decide⟩]) unmarked_context_11_75297_1031431 node_context_11_75297_1031431
  intro a
  fin_cases a
  · exact context_12_301188_1031376
  · exact context_12_301189_1031402
  · exact context_12_301190_984676
  · exact context_12_301191_1031430

theorem selected_cut_38305 : selected 9 ⟨1031454, by decide⟩
    (prefixPartial 12 301192) = some ⟨12, 2, 0, 1031454, 301192, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_301192_1031454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301192 ⟨1031454, by decide⟩ :=
  accepted_of_selected 12 301192 ⟨1031454, by decide⟩ ⟨12, 2, 0, 1031454, 301192, 1393, 65536⟩
    (by decide) selected_cut_38305

theorem selected_cut_38306 : selected 9 ⟨1031479, by decide⟩
    (prefixPartial 12 301193) = some ⟨12, 2, 0, 1031479, 301193, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_301193_1031479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301193 ⟨1031479, by decide⟩ :=
  accepted_of_selected 12 301193 ⟨1031479, by decide⟩ ⟨12, 2, 0, 1031479, 301193, 1489, 65536⟩
    (by decide) selected_cut_38306

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
