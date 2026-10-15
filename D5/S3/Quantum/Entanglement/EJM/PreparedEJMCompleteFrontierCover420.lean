/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover419
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_77263_1096116 : frontier 10 ⟨1096116, by decide⟩
    (prefixCache 11 77263) (prefixPartial 11 77263) = false := by
  decide +kernel

theorem node_context_11_77263_1096116 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096116, by decide⟩ =
    .split (coordinate 11) (![⟨1096025, by decide⟩,⟨1096070, by decide⟩,⟨1096115, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77263_1096116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77263 ⟨1096116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77263
    ⟨1096116, by decide⟩ (by decide) (![⟨1096025, by decide⟩,⟨1096070, by decide⟩,⟨1096115, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_77263_1096116 node_context_11_77263_1096116
  intro a
  fin_cases a
  · exact context_12_309052_1096025
  · exact context_12_309053_1096070
  · exact context_12_309054_1096115
  · exact context_12_309055_762108

theorem unmarked_context_10_19315_1096117 : frontier 11 ⟨1096117, by decide⟩
    (prefixCache 10 19315) (prefixPartial 10 19315) = false := by
  decide +kernel

theorem node_context_10_19315_1096117 : EJMOriginalGlobalDAGData.nodes 11 ⟨1096117, by decide⟩ =
    .split (coordinate 10) (![⟨1095631, by decide⟩,⟨1095804, by decide⟩,⟨1095971, by decide⟩,⟨1096116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19315_1096117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19315 ⟨1096117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19315
    ⟨1096117, by decide⟩ (by decide) (![⟨1095631, by decide⟩,⟨1095804, by decide⟩,⟨1095971, by decide⟩,⟨1096116, by decide⟩]) unmarked_context_10_19315_1096117 node_context_10_19315_1096117
  intro a
  fin_cases a
  · exact context_11_77260_1095631
  · exact context_11_77261_1095804
  · exact context_11_77262_1095971
  · exact context_11_77263_1096116

theorem unmarked_context_9_4828_1096118 : frontier 12 ⟨1096118, by decide⟩
    (prefixCache 9 4828) (prefixPartial 9 4828) = false := by
  decide +kernel

theorem node_context_9_4828_1096118 : EJMOriginalGlobalDAGData.nodes 12 ⟨1096118, by decide⟩ =
    .split (coordinate 9) (![⟨1094277, by decide⟩,⟨1094862, by decide⟩,⟨1095496, by decide⟩,⟨1096117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4828_1096118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4828 ⟨1096118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4828
    ⟨1096118, by decide⟩ (by decide) (![⟨1094277, by decide⟩,⟨1094862, by decide⟩,⟨1095496, by decide⟩,⟨1096117, by decide⟩]) unmarked_context_9_4828_1096118 node_context_9_4828_1096118
  intro a
  fin_cases a
  · exact context_10_19312_1094277
  · exact context_10_19313_1094862
  · exact context_10_19314_1095496
  · exact context_10_19315_1096117

theorem selected_cut_40325 : selected 9 ⟨1096119, by decide⟩
    (prefixPartial 12 309056) = some ⟨12, 1, 0, 1096119, 309056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309056_1096119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309056 ⟨1096119, by decide⟩ :=
  accepted_of_selected 12 309056 ⟨1096119, by decide⟩ ⟨12, 1, 0, 1096119, 309056, 1, 65536⟩
    (by decide) selected_cut_40325

theorem selected_cut_40326 : selected 9 ⟨1096156, by decide⟩
    (prefixPartial 12 309057) = some ⟨12, 2, 0, 1096156, 309057, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_309057_1096156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309057 ⟨1096156, by decide⟩ :=
  accepted_of_selected 12 309057 ⟨1096156, by decide⟩ ⟨12, 2, 0, 1096156, 309057, 2645, 65536⟩
    (by decide) selected_cut_40326

theorem selected_cut_40327 : selected 9 ⟨1096198, by decide⟩
    (prefixPartial 12 309058) = some ⟨12, 2, 0, 1096198, 309058, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_309058_1096198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309058 ⟨1096198, by decide⟩ :=
  accepted_of_selected 12 309058 ⟨1096198, by decide⟩ ⟨12, 2, 0, 1096198, 309058, 3077, 65536⟩
    (by decide) selected_cut_40327

theorem selected_cut_40328 : selected 9 ⟨1096236, by decide⟩
    (prefixPartial 12 309059) = some ⟨12, 2, 0, 1096236, 309059, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_309059_1096236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309059 ⟨1096236, by decide⟩ :=
  accepted_of_selected 12 309059 ⟨1096236, by decide⟩ ⟨12, 2, 0, 1096236, 309059, 2681, 65536⟩
    (by decide) selected_cut_40328

theorem unmarked_context_11_77264_1096237 : frontier 10 ⟨1096237, by decide⟩
    (prefixCache 11 77264) (prefixPartial 11 77264) = false := by
  decide +kernel

theorem node_context_11_77264_1096237 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096237, by decide⟩ =
    .split (coordinate 11) (![⟨1096119, by decide⟩,⟨1096156, by decide⟩,⟨1096198, by decide⟩,⟨1096236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77264_1096237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77264 ⟨1096237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77264
    ⟨1096237, by decide⟩ (by decide) (![⟨1096119, by decide⟩,⟨1096156, by decide⟩,⟨1096198, by decide⟩,⟨1096236, by decide⟩]) unmarked_context_11_77264_1096237 node_context_11_77264_1096237
  intro a
  fin_cases a
  · exact context_12_309056_1096119
  · exact context_12_309057_1096156
  · exact context_12_309058_1096198
  · exact context_12_309059_1096236

theorem selected_cut_40329 : selected 9 ⟨1096299, by decide⟩
    (prefixPartial 12 309060) = some ⟨12, 2, 0, 1096299, 309060, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_309060_1096299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309060 ⟨1096299, by decide⟩ :=
  accepted_of_selected 12 309060 ⟨1096299, by decide⟩ ⟨12, 2, 0, 1096299, 309060, 3209, 65536⟩
    (by decide) selected_cut_40329

theorem selected_cut_40330 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 309061) = some ⟨12, 1, 0, 1025817, 309061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309061_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309061 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 309061 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 309061, 1, 65536⟩
    (by decide) selected_cut_40330

theorem selected_cut_40331 : selected 9 ⟨1096351, by decide⟩
    (prefixPartial 12 309062) = some ⟨12, 2, 0, 1096351, 309062, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_309062_1096351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309062 ⟨1096351, by decide⟩ :=
  accepted_of_selected 12 309062 ⟨1096351, by decide⟩ ⟨12, 2, 0, 1096351, 309062, 2725, 65536⟩
    (by decide) selected_cut_40331

theorem selected_cut_40332 : selected 9 ⟨1096399, by decide⟩
    (prefixPartial 12 309063) = some ⟨12, 2, 0, 1096399, 309063, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_309063_1096399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309063 ⟨1096399, by decide⟩ :=
  accepted_of_selected 12 309063 ⟨1096399, by decide⟩ ⟨12, 2, 0, 1096399, 309063, 2657, 65536⟩
    (by decide) selected_cut_40332

theorem unmarked_context_11_77265_1096400 : frontier 10 ⟨1096400, by decide⟩
    (prefixCache 11 77265) (prefixPartial 11 77265) = false := by
  decide +kernel

theorem node_context_11_77265_1096400 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096400, by decide⟩ =
    .split (coordinate 11) (![⟨1096299, by decide⟩,⟨1025817, by decide⟩,⟨1096351, by decide⟩,⟨1096399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77265_1096400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77265 ⟨1096400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77265
    ⟨1096400, by decide⟩ (by decide) (![⟨1096299, by decide⟩,⟨1025817, by decide⟩,⟨1096351, by decide⟩,⟨1096399, by decide⟩]) unmarked_context_11_77265_1096400 node_context_11_77265_1096400
  intro a
  fin_cases a
  · exact context_12_309060_1096299
  · exact context_12_309061_1025817
  · exact context_12_309062_1096351
  · exact context_12_309063_1096399

theorem selected_cut_40333 : selected 9 ⟨1096476, by decide⟩
    (prefixPartial 12 309064) = some ⟨12, 2, 0, 1096476, 309064, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_309064_1096476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309064 ⟨1096476, by decide⟩ :=
  accepted_of_selected 12 309064 ⟨1096476, by decide⟩ ⟨12, 2, 0, 1096476, 309064, 3653, 65536⟩
    (by decide) selected_cut_40333

theorem selected_cut_40334 : selected 9 ⟨1096519, by decide⟩
    (prefixPartial 12 309065) = some ⟨12, 2, 0, 1096519, 309065, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_309065_1096519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309065 ⟨1096519, by decide⟩ :=
  accepted_of_selected 12 309065 ⟨1096519, by decide⟩ ⟨12, 2, 0, 1096519, 309065, 2697, 65536⟩
    (by decide) selected_cut_40334

theorem selected_cut_40335 : selected 9 ⟨1096560, by decide⟩
    (prefixPartial 12 309066) = some ⟨12, 2, 0, 1096560, 309066, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_309066_1096560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309066 ⟨1096560, by decide⟩ :=
  accepted_of_selected 12 309066 ⟨1096560, by decide⟩ ⟨12, 2, 0, 1096560, 309066, 2969, 65536⟩
    (by decide) selected_cut_40335

theorem selected_cut_40336 : selected 9 ⟨1096622, by decide⟩
    (prefixPartial 12 309067) = some ⟨12, 2, 0, 1096622, 309067, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_309067_1096622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309067 ⟨1096622, by decide⟩ :=
  accepted_of_selected 12 309067 ⟨1096622, by decide⟩ ⟨12, 2, 0, 1096622, 309067, 2977, 65536⟩
    (by decide) selected_cut_40336

theorem unmarked_context_11_77266_1096623 : frontier 10 ⟨1096623, by decide⟩
    (prefixCache 11 77266) (prefixPartial 11 77266) = false := by
  decide +kernel

theorem node_context_11_77266_1096623 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096623, by decide⟩ =
    .split (coordinate 11) (![⟨1096476, by decide⟩,⟨1096519, by decide⟩,⟨1096560, by decide⟩,⟨1096622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77266_1096623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77266 ⟨1096623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77266
    ⟨1096623, by decide⟩ (by decide) (![⟨1096476, by decide⟩,⟨1096519, by decide⟩,⟨1096560, by decide⟩,⟨1096622, by decide⟩]) unmarked_context_11_77266_1096623 node_context_11_77266_1096623
  intro a
  fin_cases a
  · exact context_12_309064_1096476
  · exact context_12_309065_1096519
  · exact context_12_309066_1096560
  · exact context_12_309067_1096622

theorem selected_cut_40337 : selected 9 ⟨1096675, by decide⟩
    (prefixPartial 12 309068) = some ⟨12, 2, 0, 1096675, 309068, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_309068_1096675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309068 ⟨1096675, by decide⟩ :=
  accepted_of_selected 12 309068 ⟨1096675, by decide⟩ ⟨12, 2, 0, 1096675, 309068, 3193, 65536⟩
    (by decide) selected_cut_40337

theorem selected_cut_40338 : selected 9 ⟨1096711, by decide⟩
    (prefixPartial 12 309069) = some ⟨12, 2, 0, 1096711, 309069, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_309069_1096711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309069 ⟨1096711, by decide⟩ :=
  accepted_of_selected 12 309069 ⟨1096711, by decide⟩ ⟨12, 2, 0, 1096711, 309069, 2373, 65536⟩
    (by decide) selected_cut_40338

theorem selected_cut_40339 : selected 9 ⟨1096751, by decide⟩
    (prefixPartial 12 309070) = some ⟨12, 2, 0, 1096751, 309070, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_309070_1096751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309070 ⟨1096751, by decide⟩ :=
  accepted_of_selected 12 309070 ⟨1096751, by decide⟩ ⟨12, 2, 0, 1096751, 309070, 2689, 65536⟩
    (by decide) selected_cut_40339

theorem selected_cut_40340 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 309071) = some ⟨12, 1, 0, 903806, 309071, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309071_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309071 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 309071 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 309071, 1, 65536⟩
    (by decide) selected_cut_40340

theorem unmarked_context_11_77267_1096752 : frontier 10 ⟨1096752, by decide⟩
    (prefixCache 11 77267) (prefixPartial 11 77267) = false := by
  decide +kernel

theorem node_context_11_77267_1096752 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096752, by decide⟩ =
    .split (coordinate 11) (![⟨1096675, by decide⟩,⟨1096711, by decide⟩,⟨1096751, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77267_1096752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77267 ⟨1096752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77267
    ⟨1096752, by decide⟩ (by decide) (![⟨1096675, by decide⟩,⟨1096711, by decide⟩,⟨1096751, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77267_1096752 node_context_11_77267_1096752
  intro a
  fin_cases a
  · exact context_12_309068_1096675
  · exact context_12_309069_1096711
  · exact context_12_309070_1096751
  · exact context_12_309071_903806

theorem unmarked_context_10_19316_1096753 : frontier 11 ⟨1096753, by decide⟩
    (prefixCache 10 19316) (prefixPartial 10 19316) = false := by
  decide +kernel

theorem node_context_10_19316_1096753 : EJMOriginalGlobalDAGData.nodes 11 ⟨1096753, by decide⟩ =
    .split (coordinate 10) (![⟨1096237, by decide⟩,⟨1096400, by decide⟩,⟨1096623, by decide⟩,⟨1096752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19316_1096753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19316 ⟨1096753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19316
    ⟨1096753, by decide⟩ (by decide) (![⟨1096237, by decide⟩,⟨1096400, by decide⟩,⟨1096623, by decide⟩,⟨1096752, by decide⟩]) unmarked_context_10_19316_1096753 node_context_10_19316_1096753
  intro a
  fin_cases a
  · exact context_11_77264_1096237
  · exact context_11_77265_1096400
  · exact context_11_77266_1096623
  · exact context_11_77267_1096752

theorem selected_cut_40341 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19317) = some ⟨10, 1, 0, 893098, 19317, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19317_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19317 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19317 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19317, 1, 1048576⟩
    (by decide) selected_cut_40341

theorem selected_cut_40342 : selected 9 ⟨1096794, by decide⟩
    (prefixPartial 12 309088) = some ⟨12, 2, 0, 1096794, 309088, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_309088_1096794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309088 ⟨1096794, by decide⟩ :=
  accepted_of_selected 12 309088 ⟨1096794, by decide⟩ ⟨12, 2, 0, 1096794, 309088, 2505, 65536⟩
    (by decide) selected_cut_40342

theorem selected_cut_40343 : selected 9 ⟨1096830, by decide⟩
    (prefixPartial 12 309089) = some ⟨12, 2, 0, 1096830, 309089, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_309089_1096830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309089 ⟨1096830, by decide⟩ :=
  accepted_of_selected 12 309089 ⟨1096830, by decide⟩ ⟨12, 2, 0, 1096830, 309089, 2269, 65536⟩
    (by decide) selected_cut_40343

theorem selected_cut_40344 : selected 9 ⟨1096867, by decide⟩
    (prefixPartial 12 309090) = some ⟨12, 2, 0, 1096867, 309090, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_309090_1096867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309090 ⟨1096867, by decide⟩ :=
  accepted_of_selected 12 309090 ⟨1096867, by decide⟩ ⟨12, 2, 0, 1096867, 309090, 2513, 65536⟩
    (by decide) selected_cut_40344

theorem selected_cut_40345 : selected 9 ⟨1096897, by decide⟩
    (prefixPartial 12 309091) = some ⟨12, 2, 0, 1096897, 309091, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_309091_1096897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309091 ⟨1096897, by decide⟩ :=
  accepted_of_selected 12 309091 ⟨1096897, by decide⟩ ⟨12, 2, 0, 1096897, 309091, 2233, 65536⟩
    (by decide) selected_cut_40345

theorem unmarked_context_11_77272_1096898 : frontier 10 ⟨1096898, by decide⟩
    (prefixCache 11 77272) (prefixPartial 11 77272) = false := by
  decide +kernel

theorem node_context_11_77272_1096898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096898, by decide⟩ =
    .split (coordinate 11) (![⟨1096794, by decide⟩,⟨1096830, by decide⟩,⟨1096867, by decide⟩,⟨1096897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77272_1096898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77272 ⟨1096898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77272
    ⟨1096898, by decide⟩ (by decide) (![⟨1096794, by decide⟩,⟨1096830, by decide⟩,⟨1096867, by decide⟩,⟨1096897, by decide⟩]) unmarked_context_11_77272_1096898 node_context_11_77272_1096898
  intro a
  fin_cases a
  · exact context_12_309088_1096794
  · exact context_12_309089_1096830
  · exact context_12_309090_1096867
  · exact context_12_309091_1096897

theorem selected_cut_40346 : selected 9 ⟨1096930, by decide⟩
    (prefixPartial 12 309092) = some ⟨12, 2, 0, 1096930, 309092, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_309092_1096930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309092 ⟨1096930, by decide⟩ :=
  accepted_of_selected 12 309092 ⟨1096930, by decide⟩ ⟨12, 2, 0, 1096930, 309092, 2121, 65536⟩
    (by decide) selected_cut_40346

theorem selected_cut_40347 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 309093) = some ⟨12, 1, 0, 1084018, 309093, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309093_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309093 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 309093 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 309093, 1, 65536⟩
    (by decide) selected_cut_40347

theorem selected_cut_40348 : selected 9 ⟨1096960, by decide⟩
    (prefixPartial 12 309094) = some ⟨12, 2, 0, 1096960, 309094, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_309094_1096960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309094 ⟨1096960, by decide⟩ :=
  accepted_of_selected 12 309094 ⟨1096960, by decide⟩ ⟨12, 2, 0, 1096960, 309094, 1977, 65536⟩
    (by decide) selected_cut_40348

theorem selected_cut_40349 : selected 9 ⟨1096988, by decide⟩
    (prefixPartial 12 309095) = some ⟨12, 2, 0, 1096988, 309095, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_309095_1096988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309095 ⟨1096988, by decide⟩ :=
  accepted_of_selected 12 309095 ⟨1096988, by decide⟩ ⟨12, 2, 0, 1096988, 309095, 1985, 65536⟩
    (by decide) selected_cut_40349

theorem unmarked_context_11_77273_1096989 : frontier 10 ⟨1096989, by decide⟩
    (prefixCache 11 77273) (prefixPartial 11 77273) = false := by
  decide +kernel

theorem node_context_11_77273_1096989 : EJMOriginalGlobalDAGData.nodes 10 ⟨1096989, by decide⟩ =
    .split (coordinate 11) (![⟨1096930, by decide⟩,⟨1084018, by decide⟩,⟨1096960, by decide⟩,⟨1096988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77273_1096989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77273 ⟨1096989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77273
    ⟨1096989, by decide⟩ (by decide) (![⟨1096930, by decide⟩,⟨1084018, by decide⟩,⟨1096960, by decide⟩,⟨1096988, by decide⟩]) unmarked_context_11_77273_1096989 node_context_11_77273_1096989
  intro a
  fin_cases a
  · exact context_12_309092_1096930
  · exact context_12_309093_1084018
  · exact context_12_309094_1096960
  · exact context_12_309095_1096988

theorem selected_cut_40350 : selected 9 ⟨1097032, by decide⟩
    (prefixPartial 12 309096) = some ⟨12, 2, 0, 1097032, 309096, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_309096_1097032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309096 ⟨1097032, by decide⟩ :=
  accepted_of_selected 12 309096 ⟨1097032, by decide⟩ ⟨12, 2, 0, 1097032, 309096, 2637, 65536⟩
    (by decide) selected_cut_40350

theorem selected_cut_40351 : selected 9 ⟨1097065, by decide⟩
    (prefixPartial 12 309097) = some ⟨12, 2, 0, 1097065, 309097, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_309097_1097065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309097 ⟨1097065, by decide⟩ :=
  accepted_of_selected 12 309097 ⟨1097065, by decide⟩ ⟨12, 2, 0, 1097065, 309097, 2181, 65536⟩
    (by decide) selected_cut_40351

theorem selected_cut_40352 : selected 9 ⟨1097066, by decide⟩
    (prefixPartial 12 309098) = some ⟨12, 1, 0, 1097066, 309098, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309098_1097066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309098 ⟨1097066, by decide⟩ :=
  accepted_of_selected 12 309098 ⟨1097066, by decide⟩ ⟨12, 1, 0, 1097066, 309098, 1, 65536⟩
    (by decide) selected_cut_40352

theorem selected_cut_40353 : selected 9 ⟨1097104, by decide⟩
    (prefixPartial 12 309099) = some ⟨12, 2, 0, 1097104, 309099, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_309099_1097104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309099 ⟨1097104, by decide⟩ :=
  accepted_of_selected 12 309099 ⟨1097104, by decide⟩ ⟨12, 2, 0, 1097104, 309099, 2393, 65536⟩
    (by decide) selected_cut_40353

theorem unmarked_context_11_77274_1097105 : frontier 10 ⟨1097105, by decide⟩
    (prefixCache 11 77274) (prefixPartial 11 77274) = false := by
  decide +kernel

theorem node_context_11_77274_1097105 : EJMOriginalGlobalDAGData.nodes 10 ⟨1097105, by decide⟩ =
    .split (coordinate 11) (![⟨1097032, by decide⟩,⟨1097065, by decide⟩,⟨1097066, by decide⟩,⟨1097104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77274_1097105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77274 ⟨1097105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77274
    ⟨1097105, by decide⟩ (by decide) (![⟨1097032, by decide⟩,⟨1097065, by decide⟩,⟨1097066, by decide⟩,⟨1097104, by decide⟩]) unmarked_context_11_77274_1097105 node_context_11_77274_1097105
  intro a
  fin_cases a
  · exact context_12_309096_1097032
  · exact context_12_309097_1097065
  · exact context_12_309098_1097066
  · exact context_12_309099_1097104

theorem selected_cut_40354 : selected 9 ⟨1097147, by decide⟩
    (prefixPartial 12 309100) = some ⟨12, 2, 0, 1097147, 309100, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_309100_1097147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309100 ⟨1097147, by decide⟩ :=
  accepted_of_selected 12 309100 ⟨1097147, by decide⟩ ⟨12, 2, 0, 1097147, 309100, 2201, 65536⟩
    (by decide) selected_cut_40354

theorem selected_cut_40355 : selected 9 ⟨1097177, by decide⟩
    (prefixPartial 12 309101) = some ⟨12, 2, 0, 1097177, 309101, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_309101_1097177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309101 ⟨1097177, by decide⟩ :=
  accepted_of_selected 12 309101 ⟨1097177, by decide⟩ ⟨12, 2, 0, 1097177, 309101, 1857, 65536⟩
    (by decide) selected_cut_40355

theorem selected_cut_40356 : selected 9 ⟨1097210, by decide⟩
    (prefixPartial 12 309102) = some ⟨12, 2, 0, 1097210, 309102, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_309102_1097210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309102 ⟨1097210, by decide⟩ :=
  accepted_of_selected 12 309102 ⟨1097210, by decide⟩ ⟨12, 2, 0, 1097210, 309102, 2005, 65536⟩
    (by decide) selected_cut_40356

theorem selected_cut_40357 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 309103) = some ⟨12, 1, 0, 903806, 309103, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309103_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309103 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 309103 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 309103, 1, 65536⟩
    (by decide) selected_cut_40357

theorem unmarked_context_11_77275_1097211 : frontier 10 ⟨1097211, by decide⟩
    (prefixCache 11 77275) (prefixPartial 11 77275) = false := by
  decide +kernel

theorem node_context_11_77275_1097211 : EJMOriginalGlobalDAGData.nodes 10 ⟨1097211, by decide⟩ =
    .split (coordinate 11) (![⟨1097147, by decide⟩,⟨1097177, by decide⟩,⟨1097210, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77275_1097211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77275 ⟨1097211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77275
    ⟨1097211, by decide⟩ (by decide) (![⟨1097147, by decide⟩,⟨1097177, by decide⟩,⟨1097210, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77275_1097211 node_context_11_77275_1097211
  intro a
  fin_cases a
  · exact context_12_309100_1097147
  · exact context_12_309101_1097177
  · exact context_12_309102_1097210
  · exact context_12_309103_903806

theorem unmarked_context_10_19318_1097212 : frontier 11 ⟨1097212, by decide⟩
    (prefixCache 10 19318) (prefixPartial 10 19318) = false := by
  decide +kernel

theorem node_context_10_19318_1097212 : EJMOriginalGlobalDAGData.nodes 11 ⟨1097212, by decide⟩ =
    .split (coordinate 10) (![⟨1096898, by decide⟩,⟨1096989, by decide⟩,⟨1097105, by decide⟩,⟨1097211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19318_1097212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19318 ⟨1097212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19318
    ⟨1097212, by decide⟩ (by decide) (![⟨1096898, by decide⟩,⟨1096989, by decide⟩,⟨1097105, by decide⟩,⟨1097211, by decide⟩]) unmarked_context_10_19318_1097212 node_context_10_19318_1097212
  intro a
  fin_cases a
  · exact context_11_77272_1096898
  · exact context_11_77273_1096989
  · exact context_11_77274_1097105
  · exact context_11_77275_1097211

theorem selected_cut_40358 : selected 9 ⟨1097241, by decide⟩
    (prefixPartial 12 309104) = some ⟨12, 2, 0, 1097241, 309104, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_309104_1097241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309104 ⟨1097241, by decide⟩ :=
  accepted_of_selected 12 309104 ⟨1097241, by decide⟩ ⟨12, 2, 0, 1097241, 309104, 1941, 65536⟩
    (by decide) selected_cut_40358

theorem selected_cut_40359 : selected 9 ⟨1097266, by decide⟩
    (prefixPartial 12 309105) = some ⟨12, 2, 0, 1097266, 309105, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_309105_1097266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309105 ⟨1097266, by decide⟩ :=
  accepted_of_selected 12 309105 ⟨1097266, by decide⟩ ⟨12, 2, 0, 1097266, 309105, 1785, 65536⟩
    (by decide) selected_cut_40359

theorem selected_cut_40360 : selected 9 ⟨1097295, by decide⟩
    (prefixPartial 12 309106) = some ⟨12, 2, 0, 1097295, 309106, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_309106_1097295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309106 ⟨1097295, by decide⟩ :=
  accepted_of_selected 12 309106 ⟨1097295, by decide⟩ ⟨12, 2, 0, 1097295, 309106, 2077, 65536⟩
    (by decide) selected_cut_40360

theorem selected_cut_40361 : selected 9 ⟨1097316, by decide⟩
    (prefixPartial 12 309107) = some ⟨12, 2, 0, 1097316, 309107, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_309107_1097316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309107 ⟨1097316, by decide⟩ :=
  accepted_of_selected 12 309107 ⟨1097316, by decide⟩ ⟨12, 2, 0, 1097316, 309107, 1517, 65536⟩
    (by decide) selected_cut_40361

theorem unmarked_context_11_77276_1097317 : frontier 10 ⟨1097317, by decide⟩
    (prefixCache 11 77276) (prefixPartial 11 77276) = false := by
  decide +kernel

theorem node_context_11_77276_1097317 : EJMOriginalGlobalDAGData.nodes 10 ⟨1097317, by decide⟩ =
    .split (coordinate 11) (![⟨1097241, by decide⟩,⟨1097266, by decide⟩,⟨1097295, by decide⟩,⟨1097316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77276_1097317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77276 ⟨1097317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77276
    ⟨1097317, by decide⟩ (by decide) (![⟨1097241, by decide⟩,⟨1097266, by decide⟩,⟨1097295, by decide⟩,⟨1097316, by decide⟩]) unmarked_context_11_77276_1097317 node_context_11_77276_1097317
  intro a
  fin_cases a
  · exact context_12_309104_1097241
  · exact context_12_309105_1097266
  · exact context_12_309106_1097295
  · exact context_12_309107_1097316

theorem selected_cut_40362 : selected 9 ⟨1097349, by decide⟩
    (prefixPartial 12 309108) = some ⟨12, 2, 0, 1097349, 309108, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_309108_1097349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309108 ⟨1097349, by decide⟩ :=
  accepted_of_selected 12 309108 ⟨1097349, by decide⟩ ⟨12, 2, 0, 1097349, 309108, 1793, 65536⟩
    (by decide) selected_cut_40362

theorem selected_cut_40363 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 309109) = some ⟨12, 1, 0, 1084018, 309109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309109_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309109 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 309109 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 309109, 1, 65536⟩
    (by decide) selected_cut_40363

theorem selected_cut_40364 : selected 9 ⟨1097376, by decide⟩
    (prefixPartial 12 309110) = some ⟨12, 2, 0, 1097376, 309110, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_309110_1097376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309110 ⟨1097376, by decide⟩ :=
  accepted_of_selected 12 309110 ⟨1097376, by decide⟩ ⟨12, 2, 0, 1097376, 309110, 1753, 65536⟩
    (by decide) selected_cut_40364

theorem selected_cut_40365 : selected 9 ⟨1097399, by decide⟩
    (prefixPartial 12 309111) = some ⟨12, 2, 0, 1097399, 309111, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_309111_1097399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309111 ⟨1097399, by decide⟩ :=
  accepted_of_selected 12 309111 ⟨1097399, by decide⟩ ⟨12, 2, 0, 1097399, 309111, 1505, 65536⟩
    (by decide) selected_cut_40365

theorem unmarked_context_11_77277_1097400 : frontier 10 ⟨1097400, by decide⟩
    (prefixCache 11 77277) (prefixPartial 11 77277) = false := by
  decide +kernel

theorem node_context_11_77277_1097400 : EJMOriginalGlobalDAGData.nodes 10 ⟨1097400, by decide⟩ =
    .split (coordinate 11) (![⟨1097349, by decide⟩,⟨1084018, by decide⟩,⟨1097376, by decide⟩,⟨1097399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77277_1097400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77277 ⟨1097400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77277
    ⟨1097400, by decide⟩ (by decide) (![⟨1097349, by decide⟩,⟨1084018, by decide⟩,⟨1097376, by decide⟩,⟨1097399, by decide⟩]) unmarked_context_11_77277_1097400 node_context_11_77277_1097400
  intro a
  fin_cases a
  · exact context_12_309108_1097349
  · exact context_12_309109_1084018
  · exact context_12_309110_1097376
  · exact context_12_309111_1097399

theorem selected_cut_40366 : selected 9 ⟨1097436, by decide⟩
    (prefixPartial 12 309112) = some ⟨12, 2, 0, 1097436, 309112, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_309112_1097436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309112 ⟨1097436, by decide⟩ :=
  accepted_of_selected 12 309112 ⟨1097436, by decide⟩ ⟨12, 2, 0, 1097436, 309112, 1921, 65536⟩
    (by decide) selected_cut_40366

theorem selected_cut_40367 : selected 9 ⟨1097458, by decide⟩
    (prefixPartial 12 309113) = some ⟨12, 2, 0, 1097458, 309113, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_309113_1097458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309113 ⟨1097458, by decide⟩ :=
  accepted_of_selected 12 309113 ⟨1097458, by decide⟩ ⟨12, 2, 0, 1097458, 309113, 1605, 65536⟩
    (by decide) selected_cut_40367

theorem selected_cut_40368 : selected 9 ⟨1097489, by decide⟩
    (prefixPartial 12 309114) = some ⟨12, 2, 0, 1097489, 309114, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_309114_1097489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309114 ⟨1097489, by decide⟩ :=
  accepted_of_selected 12 309114 ⟨1097489, by decide⟩ ⟨12, 2, 0, 1097489, 309114, 1749, 65536⟩
    (by decide) selected_cut_40368

theorem selected_cut_40369 : selected 9 ⟨1097516, by decide⟩
    (prefixPartial 12 309115) = some ⟨12, 2, 0, 1097516, 309115, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_309115_1097516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309115 ⟨1097516, by decide⟩ :=
  accepted_of_selected 12 309115 ⟨1097516, by decide⟩ ⟨12, 2, 0, 1097516, 309115, 1561, 65536⟩
    (by decide) selected_cut_40369

theorem unmarked_context_11_77278_1097517 : frontier 10 ⟨1097517, by decide⟩
    (prefixCache 11 77278) (prefixPartial 11 77278) = false := by
  decide +kernel

theorem node_context_11_77278_1097517 : EJMOriginalGlobalDAGData.nodes 10 ⟨1097517, by decide⟩ =
    .split (coordinate 11) (![⟨1097436, by decide⟩,⟨1097458, by decide⟩,⟨1097489, by decide⟩,⟨1097516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77278_1097517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77278 ⟨1097517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77278
    ⟨1097517, by decide⟩ (by decide) (![⟨1097436, by decide⟩,⟨1097458, by decide⟩,⟨1097489, by decide⟩,⟨1097516, by decide⟩]) unmarked_context_11_77278_1097517 node_context_11_77278_1097517
  intro a
  fin_cases a
  · exact context_12_309112_1097436
  · exact context_12_309113_1097458
  · exact context_12_309114_1097489
  · exact context_12_309115_1097516

theorem selected_cut_40370 : selected 9 ⟨1097544, by decide⟩
    (prefixPartial 12 309116) = some ⟨12, 2, 0, 1097544, 309116, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_309116_1097544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309116 ⟨1097544, by decide⟩ :=
  accepted_of_selected 12 309116 ⟨1097544, by decide⟩ ⟨12, 2, 0, 1097544, 309116, 1565, 65536⟩
    (by decide) selected_cut_40370

theorem selected_cut_40371 : selected 9 ⟨1097570, by decide⟩
    (prefixPartial 12 309117) = some ⟨12, 2, 0, 1097570, 309117, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_309117_1097570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309117 ⟨1097570, by decide⟩ :=
  accepted_of_selected 12 309117 ⟨1097570, by decide⟩ ⟨12, 2, 0, 1097570, 309117, 1325, 65536⟩
    (by decide) selected_cut_40371

theorem selected_cut_40372 : selected 9 ⟨1097591, by decide⟩
    (prefixPartial 12 309118) = some ⟨12, 2, 0, 1097591, 309118, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_309118_1097591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309118 ⟨1097591, by decide⟩ :=
  accepted_of_selected 12 309118 ⟨1097591, by decide⟩ ⟨12, 2, 0, 1097591, 309118, 1481, 65536⟩
    (by decide) selected_cut_40372

theorem selected_cut_40373 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 309119) = some ⟨12, 1, 0, 762108, 309119, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309119_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309119 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 309119 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 309119, 1, 65536⟩
    (by decide) selected_cut_40373

theorem unmarked_context_11_77279_1097592 : frontier 10 ⟨1097592, by decide⟩
    (prefixCache 11 77279) (prefixPartial 11 77279) = false := by
  decide +kernel

theorem node_context_11_77279_1097592 : EJMOriginalGlobalDAGData.nodes 10 ⟨1097592, by decide⟩ =
    .split (coordinate 11) (![⟨1097544, by decide⟩,⟨1097570, by decide⟩,⟨1097591, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77279_1097592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77279 ⟨1097592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77279
    ⟨1097592, by decide⟩ (by decide) (![⟨1097544, by decide⟩,⟨1097570, by decide⟩,⟨1097591, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_77279_1097592 node_context_11_77279_1097592
  intro a
  fin_cases a
  · exact context_12_309116_1097544
  · exact context_12_309117_1097570
  · exact context_12_309118_1097591
  · exact context_12_309119_762108

theorem unmarked_context_10_19319_1097593 : frontier 11 ⟨1097593, by decide⟩
    (prefixCache 10 19319) (prefixPartial 10 19319) = false := by
  decide +kernel

theorem node_context_10_19319_1097593 : EJMOriginalGlobalDAGData.nodes 11 ⟨1097593, by decide⟩ =
    .split (coordinate 10) (![⟨1097317, by decide⟩,⟨1097400, by decide⟩,⟨1097517, by decide⟩,⟨1097592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19319_1097593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19319 ⟨1097593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19319
    ⟨1097593, by decide⟩ (by decide) (![⟨1097317, by decide⟩,⟨1097400, by decide⟩,⟨1097517, by decide⟩,⟨1097592, by decide⟩]) unmarked_context_10_19319_1097593 node_context_10_19319_1097593
  intro a
  fin_cases a
  · exact context_11_77276_1097317
  · exact context_11_77277_1097400
  · exact context_11_77278_1097517
  · exact context_11_77279_1097592

theorem unmarked_context_9_4829_1097594 : frontier 12 ⟨1097594, by decide⟩
    (prefixCache 9 4829) (prefixPartial 9 4829) = false := by
  decide +kernel

theorem node_context_9_4829_1097594 : EJMOriginalGlobalDAGData.nodes 12 ⟨1097594, by decide⟩ =
    .split (coordinate 9) (![⟨1096753, by decide⟩,⟨893098, by decide⟩,⟨1097212, by decide⟩,⟨1097593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4829_1097594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4829 ⟨1097594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4829
    ⟨1097594, by decide⟩ (by decide) (![⟨1096753, by decide⟩,⟨893098, by decide⟩,⟨1097212, by decide⟩,⟨1097593, by decide⟩]) unmarked_context_9_4829_1097594 node_context_9_4829_1097594
  intro a
  fin_cases a
  · exact context_10_19316_1096753
  · exact context_10_19317_893098
  · exact context_10_19318_1097212
  · exact context_10_19319_1097593

theorem selected_cut_40374 : selected 10 ⟨1097688, by decide⟩
    (prefixPartial 11 77280) = some ⟨11, 2, 0, 1097688, 77280, 3141, 262144⟩ := by
  decide +kernel

theorem context_11_77280_1097688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77280 ⟨1097688, by decide⟩ :=
  accepted_of_selected 11 77280 ⟨1097688, by decide⟩ ⟨11, 2, 0, 1097688, 77280, 3141, 262144⟩
    (by decide) selected_cut_40374

theorem selected_cut_40375 : selected 10 ⟨1097752, by decide⟩
    (prefixPartial 11 77281) = some ⟨11, 2, 0, 1097752, 77281, 3953, 262144⟩ := by
  decide +kernel

theorem context_11_77281_1097752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77281 ⟨1097752, by decide⟩ :=
  accepted_of_selected 11 77281 ⟨1097752, by decide⟩ ⟨11, 2, 0, 1097752, 77281, 3953, 262144⟩
    (by decide) selected_cut_40375

theorem selected_cut_40376 : selected 10 ⟨1097822, by decide⟩
    (prefixPartial 11 77282) = some ⟨11, 2, 0, 1097822, 77282, 4029, 262144⟩ := by
  decide +kernel

theorem context_11_77282_1097822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77282 ⟨1097822, by decide⟩ :=
  accepted_of_selected 11 77282 ⟨1097822, by decide⟩ ⟨11, 2, 0, 1097822, 77282, 4029, 262144⟩
    (by decide) selected_cut_40376

theorem selected_cut_40377 : selected 10 ⟨1097865, by decide⟩
    (prefixPartial 11 77283) = some ⟨11, 2, 0, 1097865, 77283, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_77283_1097865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77283 ⟨1097865, by decide⟩ :=
  accepted_of_selected 11 77283 ⟨1097865, by decide⟩ ⟨11, 2, 0, 1097865, 77283, 2405, 262144⟩
    (by decide) selected_cut_40377

theorem unmarked_context_10_19320_1097866 : frontier 11 ⟨1097866, by decide⟩
    (prefixCache 10 19320) (prefixPartial 10 19320) = false := by
  decide +kernel

theorem node_context_10_19320_1097866 : EJMOriginalGlobalDAGData.nodes 11 ⟨1097866, by decide⟩ =
    .split (coordinate 10) (![⟨1097688, by decide⟩,⟨1097752, by decide⟩,⟨1097822, by decide⟩,⟨1097865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19320_1097866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19320 ⟨1097866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19320
    ⟨1097866, by decide⟩ (by decide) (![⟨1097688, by decide⟩,⟨1097752, by decide⟩,⟨1097822, by decide⟩,⟨1097865, by decide⟩]) unmarked_context_10_19320_1097866 node_context_10_19320_1097866
  intro a
  fin_cases a
  · exact context_11_77280_1097688
  · exact context_11_77281_1097752
  · exact context_11_77282_1097822
  · exact context_11_77283_1097865

theorem selected_cut_40378 : selected 10 ⟨1097904, by decide⟩
    (prefixPartial 11 77284) = some ⟨11, 2, 0, 1097904, 77284, 2829, 262144⟩ := by
  decide +kernel

theorem context_11_77284_1097904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77284 ⟨1097904, by decide⟩ :=
  accepted_of_selected 11 77284 ⟨1097904, by decide⟩ ⟨11, 2, 0, 1097904, 77284, 2829, 262144⟩
    (by decide) selected_cut_40378

theorem selected_cut_40379 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 77285) = some ⟨11, 1, 0, 892405, 77285, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77285_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77285 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 77285 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 77285, 1, 262144⟩
    (by decide) selected_cut_40379

theorem selected_cut_40380 : selected 10 ⟨1097942, by decide⟩
    (prefixPartial 11 77286) = some ⟨11, 2, 0, 1097942, 77286, 2861, 262144⟩ := by
  decide +kernel

theorem context_11_77286_1097942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77286 ⟨1097942, by decide⟩ :=
  accepted_of_selected 11 77286 ⟨1097942, by decide⟩ ⟨11, 2, 0, 1097942, 77286, 2861, 262144⟩
    (by decide) selected_cut_40380

theorem selected_cut_40381 : selected 10 ⟨1097972, by decide⟩
    (prefixPartial 11 77287) = some ⟨11, 2, 0, 1097972, 77287, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_77287_1097972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77287 ⟨1097972, by decide⟩ :=
  accepted_of_selected 11 77287 ⟨1097972, by decide⟩ ⟨11, 2, 0, 1097972, 77287, 1889, 262144⟩
    (by decide) selected_cut_40381

theorem unmarked_context_10_19321_1097973 : frontier 11 ⟨1097973, by decide⟩
    (prefixCache 10 19321) (prefixPartial 10 19321) = false := by
  decide +kernel

theorem node_context_10_19321_1097973 : EJMOriginalGlobalDAGData.nodes 11 ⟨1097973, by decide⟩ =
    .split (coordinate 10) (![⟨1097904, by decide⟩,⟨892405, by decide⟩,⟨1097942, by decide⟩,⟨1097972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19321_1097973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19321 ⟨1097973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19321
    ⟨1097973, by decide⟩ (by decide) (![⟨1097904, by decide⟩,⟨892405, by decide⟩,⟨1097942, by decide⟩,⟨1097972, by decide⟩]) unmarked_context_10_19321_1097973 node_context_10_19321_1097973
  intro a
  fin_cases a
  · exact context_11_77284_1097904
  · exact context_11_77285_892405
  · exact context_11_77286_1097942
  · exact context_11_77287_1097972

theorem selected_cut_40382 : selected 10 ⟨1098000, by decide⟩
    (prefixPartial 11 77288) = some ⟨11, 2, 0, 1098000, 77288, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_77288_1098000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77288 ⟨1098000, by decide⟩ :=
  accepted_of_selected 11 77288 ⟨1098000, by decide⟩ ⟨11, 2, 0, 1098000, 77288, 2569, 262144⟩
    (by decide) selected_cut_40382

theorem selected_cut_40383 : selected 10 ⟨1098029, by decide⟩
    (prefixPartial 11 77289) = some ⟨11, 2, 0, 1098029, 77289, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_77289_1098029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77289 ⟨1098029, by decide⟩ :=
  accepted_of_selected 11 77289 ⟨1098029, by decide⟩ ⟨11, 2, 0, 1098029, 77289, 2425, 262144⟩
    (by decide) selected_cut_40383

theorem selected_cut_40384 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 77290) = some ⟨11, 1, 0, 906566, 77290, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77290_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77290 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 77290 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 77290, 1, 262144⟩
    (by decide) selected_cut_40384

theorem selected_cut_40385 : selected 10 ⟨1098053, by decide⟩
    (prefixPartial 11 77291) = some ⟨11, 2, 0, 1098053, 77291, 1553, 262144⟩ := by
  decide +kernel

theorem context_11_77291_1098053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77291 ⟨1098053, by decide⟩ :=
  accepted_of_selected 11 77291 ⟨1098053, by decide⟩ ⟨11, 2, 0, 1098053, 77291, 1553, 262144⟩
    (by decide) selected_cut_40385

theorem unmarked_context_10_19322_1098054 : frontier 11 ⟨1098054, by decide⟩
    (prefixCache 10 19322) (prefixPartial 10 19322) = false := by
  decide +kernel

theorem node_context_10_19322_1098054 : EJMOriginalGlobalDAGData.nodes 11 ⟨1098054, by decide⟩ =
    .split (coordinate 10) (![⟨1098000, by decide⟩,⟨1098029, by decide⟩,⟨906566, by decide⟩,⟨1098053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19322_1098054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19322 ⟨1098054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19322
    ⟨1098054, by decide⟩ (by decide) (![⟨1098000, by decide⟩,⟨1098029, by decide⟩,⟨906566, by decide⟩,⟨1098053, by decide⟩]) unmarked_context_10_19322_1098054 node_context_10_19322_1098054
  intro a
  fin_cases a
  · exact context_11_77288_1098000
  · exact context_11_77289_1098029
  · exact context_11_77290_906566
  · exact context_11_77291_1098053

theorem selected_cut_40386 : selected 10 ⟨1098081, by decide⟩
    (prefixPartial 11 77292) = some ⟨11, 2, 0, 1098081, 77292, 2161, 262144⟩ := by
  decide +kernel

theorem context_11_77292_1098081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77292 ⟨1098081, by decide⟩ :=
  accepted_of_selected 11 77292 ⟨1098081, by decide⟩ ⟨11, 2, 0, 1098081, 77292, 2161, 262144⟩
    (by decide) selected_cut_40386

theorem selected_cut_40387 : selected 10 ⟨1098115, by decide⟩
    (prefixPartial 11 77293) = some ⟨11, 2, 0, 1098115, 77293, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_77293_1098115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77293 ⟨1098115, by decide⟩ :=
  accepted_of_selected 11 77293 ⟨1098115, by decide⟩ ⟨11, 2, 0, 1098115, 77293, 2241, 262144⟩
    (by decide) selected_cut_40387

theorem selected_cut_40388 : selected 10 ⟨1098144, by decide⟩
    (prefixPartial 11 77294) = some ⟨11, 2, 0, 1098144, 77294, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_77294_1098144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77294 ⟨1098144, by decide⟩ :=
  accepted_of_selected 11 77294 ⟨1098144, by decide⟩ ⟨11, 2, 0, 1098144, 77294, 1933, 262144⟩
    (by decide) selected_cut_40388

theorem selected_cut_40389 : selected 10 ⟨1098160, by decide⟩
    (prefixPartial 11 77295) = some ⟨11, 2, 0, 1098160, 77295, 1193, 262144⟩ := by
  decide +kernel

theorem context_11_77295_1098160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77295 ⟨1098160, by decide⟩ :=
  accepted_of_selected 11 77295 ⟨1098160, by decide⟩ ⟨11, 2, 0, 1098160, 77295, 1193, 262144⟩
    (by decide) selected_cut_40389

theorem unmarked_context_10_19323_1098161 : frontier 11 ⟨1098161, by decide⟩
    (prefixCache 10 19323) (prefixPartial 10 19323) = false := by
  decide +kernel

theorem node_context_10_19323_1098161 : EJMOriginalGlobalDAGData.nodes 11 ⟨1098161, by decide⟩ =
    .split (coordinate 10) (![⟨1098081, by decide⟩,⟨1098115, by decide⟩,⟨1098144, by decide⟩,⟨1098160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19323_1098161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19323 ⟨1098161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19323
    ⟨1098161, by decide⟩ (by decide) (![⟨1098081, by decide⟩,⟨1098115, by decide⟩,⟨1098144, by decide⟩,⟨1098160, by decide⟩]) unmarked_context_10_19323_1098161 node_context_10_19323_1098161
  intro a
  fin_cases a
  · exact context_11_77292_1098081
  · exact context_11_77293_1098115
  · exact context_11_77294_1098144
  · exact context_11_77295_1098160

theorem unmarked_context_9_4830_1098162 : frontier 12 ⟨1098162, by decide⟩
    (prefixCache 9 4830) (prefixPartial 9 4830) = false := by
  decide +kernel

theorem node_context_9_4830_1098162 : EJMOriginalGlobalDAGData.nodes 12 ⟨1098162, by decide⟩ =
    .split (coordinate 9) (![⟨1097866, by decide⟩,⟨1097973, by decide⟩,⟨1098054, by decide⟩,⟨1098161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4830_1098162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4830 ⟨1098162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4830
    ⟨1098162, by decide⟩ (by decide) (![⟨1097866, by decide⟩,⟨1097973, by decide⟩,⟨1098054, by decide⟩,⟨1098161, by decide⟩]) unmarked_context_9_4830_1098162 node_context_9_4830_1098162
  intro a
  fin_cases a
  · exact context_10_19320_1097866
  · exact context_10_19321_1097973
  · exact context_10_19322_1098054
  · exact context_10_19323_1098161

theorem selected_cut_40390 : selected 10 ⟨1098176, by decide⟩
    (prefixPartial 11 77296) = some ⟨11, 2, 0, 1098176, 77296, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_77296_1098176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77296 ⟨1098176, by decide⟩ :=
  accepted_of_selected 11 77296 ⟨1098176, by decide⟩ ⟨11, 2, 0, 1098176, 77296, 1381, 262144⟩
    (by decide) selected_cut_40390

theorem selected_cut_40391 : selected 10 ⟨1098200, by decide⟩
    (prefixPartial 11 77297) = some ⟨11, 2, 0, 1098200, 77297, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_77297_1098200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77297 ⟨1098200, by decide⟩ :=
  accepted_of_selected 11 77297 ⟨1098200, by decide⟩ ⟨11, 2, 0, 1098200, 77297, 1925, 262144⟩
    (by decide) selected_cut_40391

theorem selected_cut_40392 : selected 10 ⟨1098225, by decide⟩
    (prefixPartial 11 77298) = some ⟨11, 2, 0, 1098225, 77298, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_77298_1098225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77298 ⟨1098225, by decide⟩ :=
  accepted_of_selected 11 77298 ⟨1098225, by decide⟩ ⟨11, 2, 0, 1098225, 77298, 1749, 262144⟩
    (by decide) selected_cut_40392

theorem selected_cut_40393 : selected 10 ⟨1098250, by decide⟩
    (prefixPartial 11 77299) = some ⟨11, 2, 0, 1098250, 77299, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_77299_1098250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77299 ⟨1098250, by decide⟩ :=
  accepted_of_selected 11 77299 ⟨1098250, by decide⟩ ⟨11, 2, 0, 1098250, 77299, 1373, 262144⟩
    (by decide) selected_cut_40393

theorem unmarked_context_10_19324_1098251 : frontier 11 ⟨1098251, by decide⟩
    (prefixCache 10 19324) (prefixPartial 10 19324) = false := by
  decide +kernel

theorem node_context_10_19324_1098251 : EJMOriginalGlobalDAGData.nodes 11 ⟨1098251, by decide⟩ =
    .split (coordinate 10) (![⟨1098176, by decide⟩,⟨1098200, by decide⟩,⟨1098225, by decide⟩,⟨1098250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19324_1098251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19324 ⟨1098251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19324
    ⟨1098251, by decide⟩ (by decide) (![⟨1098176, by decide⟩,⟨1098200, by decide⟩,⟨1098225, by decide⟩,⟨1098250, by decide⟩]) unmarked_context_10_19324_1098251 node_context_10_19324_1098251
  intro a
  fin_cases a
  · exact context_11_77296_1098176
  · exact context_11_77297_1098200
  · exact context_11_77298_1098225
  · exact context_11_77299_1098250

theorem selected_cut_40394 : selected 11 ⟨1098293, by decide⟩
    (prefixPartial 10 19325) = some ⟨10, 2, 0, 1098293, 19325, 3389, 1048576⟩ := by
  decide +kernel

theorem context_10_19325_1098293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19325 ⟨1098293, by decide⟩ :=
  accepted_of_selected 10 19325 ⟨1098293, by decide⟩ ⟨10, 2, 0, 1098293, 19325, 3389, 1048576⟩
    (by decide) selected_cut_40394

theorem selected_cut_40395 : selected 11 ⟨1098343, by decide⟩
    (prefixPartial 10 19326) = some ⟨10, 2, 0, 1098343, 19326, 2613, 1048576⟩ := by
  decide +kernel

theorem context_10_19326_1098343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19326 ⟨1098343, by decide⟩ :=
  accepted_of_selected 10 19326 ⟨1098343, by decide⟩ ⟨10, 2, 0, 1098343, 19326, 2613, 1048576⟩
    (by decide) selected_cut_40395

theorem selected_cut_40396 : selected 11 ⟨1098367, by decide⟩
    (prefixPartial 10 19327) = some ⟨10, 2, 0, 1098367, 19327, 569, 1048576⟩ := by
  decide +kernel

theorem context_10_19327_1098367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19327 ⟨1098367, by decide⟩ :=
  accepted_of_selected 10 19327 ⟨1098367, by decide⟩ ⟨10, 2, 0, 1098367, 19327, 569, 1048576⟩
    (by decide) selected_cut_40396

theorem unmarked_context_9_4831_1098368 : frontier 12 ⟨1098368, by decide⟩
    (prefixCache 9 4831) (prefixPartial 9 4831) = false := by
  decide +kernel

theorem node_context_9_4831_1098368 : EJMOriginalGlobalDAGData.nodes 12 ⟨1098368, by decide⟩ =
    .split (coordinate 9) (![⟨1098251, by decide⟩,⟨1098293, by decide⟩,⟨1098343, by decide⟩,⟨1098367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4831_1098368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4831 ⟨1098368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4831
    ⟨1098368, by decide⟩ (by decide) (![⟨1098251, by decide⟩,⟨1098293, by decide⟩,⟨1098343, by decide⟩,⟨1098367, by decide⟩]) unmarked_context_9_4831_1098368 node_context_9_4831_1098368
  intro a
  fin_cases a
  · exact context_10_19324_1098251
  · exact context_10_19325_1098293
  · exact context_10_19326_1098343
  · exact context_10_19327_1098367

theorem unmarked_context_8_1207_1098369 : frontier 13 ⟨1098369, by decide⟩
    (prefixCache 8 1207) (prefixPartial 8 1207) = false := by
  decide +kernel

theorem node_context_8_1207_1098369 : EJMOriginalGlobalDAGData.nodes 13 ⟨1098369, by decide⟩ =
    .split (coordinate 8) (![⟨1096118, by decide⟩,⟨1097594, by decide⟩,⟨1098162, by decide⟩,⟨1098368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1207_1098369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1207 ⟨1098369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1207
    ⟨1098369, by decide⟩ (by decide) (![⟨1096118, by decide⟩,⟨1097594, by decide⟩,⟨1098162, by decide⟩,⟨1098368, by decide⟩]) unmarked_context_8_1207_1098369 node_context_8_1207_1098369
  intro a
  fin_cases a
  · exact context_9_4828_1096118
  · exact context_9_4829_1097594
  · exact context_9_4830_1098162
  · exact context_9_4831_1098368

theorem unmarked_context_7_301_1098370 : frontier 14 ⟨1098370, by decide⟩
    (prefixCache 7 301) (prefixPartial 7 301) = false := by
  decide +kernel

theorem node_context_7_301_1098370 : EJMOriginalGlobalDAGData.nodes 14 ⟨1098370, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨1089790, by decide⟩,⟨1093630, by decide⟩,⟨1098369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_301_1098370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 301 ⟨1098370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 301
    ⟨1098370, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨1089790, by decide⟩,⟨1093630, by decide⟩,⟨1098369, by decide⟩]) unmarked_context_7_301_1098370 node_context_7_301_1098370
  intro a
  fin_cases a
  · exact context_8_1204_979897
  · exact context_8_1205_1089790
  · exact context_8_1206_1093630
  · exact context_8_1207_1098369

theorem selected_cut_40397 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1208) = some ⟨8, 1, 0, 979897, 1208, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1208_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1208 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1208 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1208, 1, 16777216⟩
    (by decide) selected_cut_40397

theorem selected_cut_40398 : selected 10 ⟨1098418, by decide⟩
    (prefixPartial 11 77376) = some ⟨11, 2, 0, 1098418, 77376, 1585, 262144⟩ := by
  decide +kernel

theorem context_11_77376_1098418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77376 ⟨1098418, by decide⟩ :=
  accepted_of_selected 11 77376 ⟨1098418, by decide⟩ ⟨11, 2, 0, 1098418, 77376, 1585, 262144⟩
    (by decide) selected_cut_40398

theorem selected_cut_40399 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 309508) = some ⟨12, 1, 0, 34034, 309508, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309508_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309508 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 309508 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 309508, 1, 65536⟩
    (by decide) selected_cut_40399

theorem selected_cut_40400 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 309509) = some ⟨12, 1, 0, 891951, 309509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309509_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309509 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 309509 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 309509, 1, 65536⟩
    (by decide) selected_cut_40400

theorem selected_cut_40401 : selected 9 ⟨1098466, by decide⟩
    (prefixPartial 12 309510) = some ⟨12, 2, 0, 1098466, 309510, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_309510_1098466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309510 ⟨1098466, by decide⟩ :=
  accepted_of_selected 12 309510 ⟨1098466, by decide⟩ ⟨12, 2, 0, 1098466, 309510, 2801, 65536⟩
    (by decide) selected_cut_40401

theorem selected_cut_40402 : selected 9 ⟨1098513, by decide⟩
    (prefixPartial 12 309511) = some ⟨12, 2, 0, 1098513, 309511, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_309511_1098513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309511 ⟨1098513, by decide⟩ :=
  accepted_of_selected 12 309511 ⟨1098513, by decide⟩ ⟨12, 2, 0, 1098513, 309511, 2865, 65536⟩
    (by decide) selected_cut_40402

theorem unmarked_context_11_77377_1098514 : frontier 10 ⟨1098514, by decide⟩
    (prefixCache 11 77377) (prefixPartial 11 77377) = false := by
  decide +kernel

theorem node_context_11_77377_1098514 : EJMOriginalGlobalDAGData.nodes 10 ⟨1098514, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨1098466, by decide⟩,⟨1098513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77377_1098514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77377 ⟨1098514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77377
    ⟨1098514, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨1098466, by decide⟩,⟨1098513, by decide⟩]) unmarked_context_11_77377_1098514 node_context_11_77377_1098514
  intro a
  fin_cases a
  · exact context_12_309508_34034
  · exact context_12_309509_891951
  · exact context_12_309510_1098466
  · exact context_12_309511_1098513

theorem selected_cut_40403 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 309512) = some ⟨12, 1, 0, 3161, 309512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309512_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309512 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 309512 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 309512, 1, 65536⟩
    (by decide) selected_cut_40403

theorem selected_cut_40404 : selected 9 ⟨1098561, by decide⟩
    (prefixPartial 12 309513) = some ⟨12, 2, 0, 1098561, 309513, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_309513_1098561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309513 ⟨1098561, by decide⟩ :=
  accepted_of_selected 12 309513 ⟨1098561, by decide⟩ ⟨12, 2, 0, 1098561, 309513, 2917, 65536⟩
    (by decide) selected_cut_40404

theorem selected_cut_40405 : selected 9 ⟨1098605, by decide⟩
    (prefixPartial 12 309514) = some ⟨12, 2, 0, 1098605, 309514, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_309514_1098605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309514 ⟨1098605, by decide⟩ :=
  accepted_of_selected 12 309514 ⟨1098605, by decide⟩ ⟨12, 2, 0, 1098605, 309514, 2753, 65536⟩
    (by decide) selected_cut_40405

theorem selected_cut_40406 : selected 9 ⟨1098648, by decide⟩
    (prefixPartial 12 309515) = some ⟨12, 2, 0, 1098648, 309515, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_309515_1098648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309515 ⟨1098648, by decide⟩ :=
  accepted_of_selected 12 309515 ⟨1098648, by decide⟩ ⟨12, 2, 0, 1098648, 309515, 2769, 65536⟩
    (by decide) selected_cut_40406

theorem unmarked_context_11_77378_1098649 : frontier 10 ⟨1098649, by decide⟩
    (prefixCache 11 77378) (prefixPartial 11 77378) = false := by
  decide +kernel

theorem node_context_11_77378_1098649 : EJMOriginalGlobalDAGData.nodes 10 ⟨1098649, by decide⟩ =
    .split (coordinate 11) (![⟨3161, by decide⟩,⟨1098561, by decide⟩,⟨1098605, by decide⟩,⟨1098648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77378_1098649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77378 ⟨1098649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77378
    ⟨1098649, by decide⟩ (by decide) (![⟨3161, by decide⟩,⟨1098561, by decide⟩,⟨1098605, by decide⟩,⟨1098648, by decide⟩]) unmarked_context_11_77378_1098649 node_context_11_77378_1098649
  intro a
  fin_cases a
  · exact context_12_309512_3161
  · exact context_12_309513_1098561
  · exact context_12_309514_1098605
  · exact context_12_309515_1098648

theorem selected_cut_40407 : selected 9 ⟨1098701, by decide⟩
    (prefixPartial 12 309516) = some ⟨12, 2, 0, 1098701, 309516, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_309516_1098701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309516 ⟨1098701, by decide⟩ :=
  accepted_of_selected 12 309516 ⟨1098701, by decide⟩ ⟨12, 2, 0, 1098701, 309516, 2069, 65536⟩
    (by decide) selected_cut_40407

theorem selected_cut_40408 : selected 9 ⟨1098757, by decide⟩
    (prefixPartial 12 309517) = some ⟨12, 2, 0, 1098757, 309517, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_309517_1098757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309517 ⟨1098757, by decide⟩ :=
  accepted_of_selected 12 309517 ⟨1098757, by decide⟩ ⟨12, 2, 0, 1098757, 309517, 3085, 65536⟩
    (by decide) selected_cut_40408

theorem selected_cut_40409 : selected 9 ⟨1098815, by decide⟩
    (prefixPartial 12 309518) = some ⟨12, 2, 0, 1098815, 309518, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_309518_1098815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309518 ⟨1098815, by decide⟩ :=
  accepted_of_selected 12 309518 ⟨1098815, by decide⟩ ⟨12, 2, 0, 1098815, 309518, 3005, 65536⟩
    (by decide) selected_cut_40409

theorem selected_cut_40410 : selected 9 ⟨1098866, by decide⟩
    (prefixPartial 12 309519) = some ⟨12, 2, 0, 1098866, 309519, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_309519_1098866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309519 ⟨1098866, by decide⟩ :=
  accepted_of_selected 12 309519 ⟨1098866, by decide⟩ ⟨12, 2, 0, 1098866, 309519, 2849, 65536⟩
    (by decide) selected_cut_40410

theorem unmarked_context_11_77379_1098867 : frontier 10 ⟨1098867, by decide⟩
    (prefixCache 11 77379) (prefixPartial 11 77379) = false := by
  decide +kernel

theorem node_context_11_77379_1098867 : EJMOriginalGlobalDAGData.nodes 10 ⟨1098867, by decide⟩ =
    .split (coordinate 11) (![⟨1098701, by decide⟩,⟨1098757, by decide⟩,⟨1098815, by decide⟩,⟨1098866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77379_1098867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77379 ⟨1098867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77379
    ⟨1098867, by decide⟩ (by decide) (![⟨1098701, by decide⟩,⟨1098757, by decide⟩,⟨1098815, by decide⟩,⟨1098866, by decide⟩]) unmarked_context_11_77379_1098867 node_context_11_77379_1098867
  intro a
  fin_cases a
  · exact context_12_309516_1098701
  · exact context_12_309517_1098757
  · exact context_12_309518_1098815
  · exact context_12_309519_1098866

theorem unmarked_context_10_19344_1098868 : frontier 11 ⟨1098868, by decide⟩
    (prefixCache 10 19344) (prefixPartial 10 19344) = false := by
  decide +kernel

theorem node_context_10_19344_1098868 : EJMOriginalGlobalDAGData.nodes 11 ⟨1098868, by decide⟩ =
    .split (coordinate 10) (![⟨1098418, by decide⟩,⟨1098514, by decide⟩,⟨1098649, by decide⟩,⟨1098867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19344_1098868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19344 ⟨1098868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19344
    ⟨1098868, by decide⟩ (by decide) (![⟨1098418, by decide⟩,⟨1098514, by decide⟩,⟨1098649, by decide⟩,⟨1098867, by decide⟩]) unmarked_context_10_19344_1098868 node_context_10_19344_1098868
  intro a
  fin_cases a
  · exact context_11_77376_1098418
  · exact context_11_77377_1098514
  · exact context_11_77378_1098649
  · exact context_11_77379_1098867

theorem selected_cut_40411 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 309520) = some ⟨12, 1, 0, 26677, 309520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309520_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309520 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 309520 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 309520, 1, 65536⟩
    (by decide) selected_cut_40411

theorem selected_cut_40412 : selected 9 ⟨1098915, by decide⟩
    (prefixPartial 12 309521) = some ⟨12, 2, 0, 1098915, 309521, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_309521_1098915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309521 ⟨1098915, by decide⟩ :=
  accepted_of_selected 12 309521 ⟨1098915, by decide⟩ ⟨12, 2, 0, 1098915, 309521, 2461, 65536⟩
    (by decide) selected_cut_40412

theorem selected_cut_40413 : selected 9 ⟨1098943, by decide⟩
    (prefixPartial 12 309522) = some ⟨12, 2, 0, 1098943, 309522, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_309522_1098943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309522 ⟨1098943, by decide⟩ :=
  accepted_of_selected 12 309522 ⟨1098943, by decide⟩ ⟨12, 2, 0, 1098943, 309522, 1281, 65536⟩
    (by decide) selected_cut_40413

theorem selected_cut_40414 : selected 9 ⟨1098984, by decide⟩
    (prefixPartial 12 309523) = some ⟨12, 2, 0, 1098984, 309523, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_309523_1098984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309523 ⟨1098984, by decide⟩ :=
  accepted_of_selected 12 309523 ⟨1098984, by decide⟩ ⟨12, 2, 0, 1098984, 309523, 2397, 65536⟩
    (by decide) selected_cut_40414

theorem unmarked_context_11_77380_1098985 : frontier 10 ⟨1098985, by decide⟩
    (prefixCache 11 77380) (prefixPartial 11 77380) = false := by
  decide +kernel

theorem node_context_11_77380_1098985 : EJMOriginalGlobalDAGData.nodes 10 ⟨1098985, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1098915, by decide⟩,⟨1098943, by decide⟩,⟨1098984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77380_1098985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77380 ⟨1098985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77380
    ⟨1098985, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1098915, by decide⟩,⟨1098943, by decide⟩,⟨1098984, by decide⟩]) unmarked_context_11_77380_1098985 node_context_11_77380_1098985
  intro a
  fin_cases a
  · exact context_12_309520_26677
  · exact context_12_309521_1098915
  · exact context_12_309522_1098943
  · exact context_12_309523_1098984

theorem selected_cut_40415 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 309524) = some ⟨12, 1, 0, 26677, 309524, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309524_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309524 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 309524 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 309524, 1, 65536⟩
    (by decide) selected_cut_40415

theorem selected_cut_40416 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 309525) = some ⟨12, 1, 0, 692793, 309525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309525_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309525 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 309525 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 309525, 1, 65536⟩
    (by decide) selected_cut_40416

theorem selected_cut_40417 : selected 9 ⟨1099020, by decide⟩
    (prefixPartial 12 309526) = some ⟨12, 2, 0, 1099020, 309526, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_309526_1099020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309526 ⟨1099020, by decide⟩ :=
  accepted_of_selected 12 309526 ⟨1099020, by decide⟩ ⟨12, 2, 0, 1099020, 309526, 2205, 65536⟩
    (by decide) selected_cut_40417

theorem selected_cut_40418 : selected 9 ⟨1099054, by decide⟩
    (prefixPartial 12 309527) = some ⟨12, 2, 0, 1099054, 309527, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_309527_1099054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309527 ⟨1099054, by decide⟩ :=
  accepted_of_selected 12 309527 ⟨1099054, by decide⟩ ⟨12, 2, 0, 1099054, 309527, 2381, 65536⟩
    (by decide) selected_cut_40418

theorem unmarked_context_11_77381_1099055 : frontier 10 ⟨1099055, by decide⟩
    (prefixCache 11 77381) (prefixPartial 11 77381) = false := by
  decide +kernel

theorem node_context_11_77381_1099055 : EJMOriginalGlobalDAGData.nodes 10 ⟨1099055, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨692793, by decide⟩,⟨1099020, by decide⟩,⟨1099054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77381_1099055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77381 ⟨1099055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77381
    ⟨1099055, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨692793, by decide⟩,⟨1099020, by decide⟩,⟨1099054, by decide⟩]) unmarked_context_11_77381_1099055 node_context_11_77381_1099055
  intro a
  fin_cases a
  · exact context_12_309524_26677
  · exact context_12_309525_692793
  · exact context_12_309526_1099020
  · exact context_12_309527_1099054

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
