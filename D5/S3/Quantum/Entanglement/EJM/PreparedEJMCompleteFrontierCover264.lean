/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover263
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_87062_641009 : frontier 9 ⟨641009, by decide⟩
    (prefixCache 12 87062) (prefixPartial 12 87062) = false := by
  decide +kernel

theorem node_context_12_87062_641009 : EJMOriginalGlobalDAGData.nodes 9 ⟨641009, by decide⟩ =
    .split (coordinate 12) (![⟨640899, by decide⟩,⟨640974, by decide⟩,⟨640996, by decide⟩,⟨641008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87062_641009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87062 ⟨641009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87062
    ⟨641009, by decide⟩ (by decide) (![⟨640899, by decide⟩,⟨640974, by decide⟩,⟨640996, by decide⟩,⟨641008, by decide⟩]) unmarked_context_12_87062_641009 node_context_12_87062_641009
  intro a
  fin_cases a
  · exact context_13_348248_640899
  · exact context_13_348249_640974
  · exact context_13_348250_640996
  · exact context_13_348251_641008

theorem selected_cut_25347 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 87063) = some ⟨12, 1, 0, 893, 87063, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87063_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87063 ⟨893, by decide⟩ :=
  accepted_of_selected 12 87063 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 87063, 1, 65536⟩
    (by decide) selected_cut_25347

theorem unmarked_context_11_21765_641010 : frontier 10 ⟨641010, by decide⟩
    (prefixCache 11 21765) (prefixPartial 11 21765) = false := by
  decide +kernel

theorem node_context_11_21765_641010 : EJMOriginalGlobalDAGData.nodes 10 ⟨641010, by decide⟩ =
    .split (coordinate 11) (![⟨640840, by decide⟩,⟨308705, by decide⟩,⟨641009, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21765_641010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21765 ⟨641010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21765
    ⟨641010, by decide⟩ (by decide) (![⟨640840, by decide⟩,⟨308705, by decide⟩,⟨641009, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_21765_641010 node_context_11_21765_641010
  intro a
  fin_cases a
  · exact context_12_87060_640840
  · exact context_12_87061_308705
  · exact context_12_87062_641009
  · exact context_12_87063_893

theorem selected_cut_25348 : selected 8 ⟨641036, by decide⟩
    (prefixPartial 13 348256) = some ⟨13, 2, 0, 641036, 348256, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_348256_641036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348256 ⟨641036, by decide⟩ :=
  accepted_of_selected 13 348256 ⟨641036, by decide⟩ ⟨13, 2, 0, 641036, 348256, 1193, 16384⟩
    (by decide) selected_cut_25348

theorem selected_cut_25349 : selected 8 ⟨641079, by decide⟩
    (prefixPartial 13 348257) = some ⟨13, 2, 0, 641079, 348257, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_348257_641079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348257 ⟨641079, by decide⟩ :=
  accepted_of_selected 13 348257 ⟨641079, by decide⟩ ⟨13, 2, 0, 641079, 348257, 1857, 16384⟩
    (by decide) selected_cut_25349

theorem selected_cut_25350 : selected 8 ⟨641104, by decide⟩
    (prefixPartial 13 348258) = some ⟨13, 2, 0, 641104, 348258, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_348258_641104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348258 ⟨641104, by decide⟩ :=
  accepted_of_selected 13 348258 ⟨641104, by decide⟩ ⟨13, 2, 0, 641104, 348258, 1697, 16384⟩
    (by decide) selected_cut_25350

theorem selected_cut_25351 : selected 8 ⟨641111, by decide⟩
    (prefixPartial 13 348259) = some ⟨13, 2, 0, 641111, 348259, 853, 16384⟩ := by
  decide +kernel

theorem context_13_348259_641111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348259 ⟨641111, by decide⟩ :=
  accepted_of_selected 13 348259 ⟨641111, by decide⟩ ⟨13, 2, 0, 641111, 348259, 853, 16384⟩
    (by decide) selected_cut_25351

theorem unmarked_context_12_87064_641112 : frontier 9 ⟨641112, by decide⟩
    (prefixCache 12 87064) (prefixPartial 12 87064) = false := by
  decide +kernel

theorem node_context_12_87064_641112 : EJMOriginalGlobalDAGData.nodes 9 ⟨641112, by decide⟩ =
    .split (coordinate 12) (![⟨641036, by decide⟩,⟨641079, by decide⟩,⟨641104, by decide⟩,⟨641111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87064_641112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87064 ⟨641112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87064
    ⟨641112, by decide⟩ (by decide) (![⟨641036, by decide⟩,⟨641079, by decide⟩,⟨641104, by decide⟩,⟨641111, by decide⟩]) unmarked_context_12_87064_641112 node_context_12_87064_641112
  intro a
  fin_cases a
  · exact context_13_348256_641036
  · exact context_13_348257_641079
  · exact context_13_348258_641104
  · exact context_13_348259_641111

theorem selected_cut_25352 : selected 8 ⟨641131, by decide⟩
    (prefixPartial 13 348260) = some ⟨13, 2, 0, 641131, 348260, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_348260_641131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348260 ⟨641131, by decide⟩ :=
  accepted_of_selected 13 348260 ⟨641131, by decide⟩ ⟨13, 2, 0, 641131, 348260, 1133, 16384⟩
    (by decide) selected_cut_25352

theorem selected_cut_25353 : selected 8 ⟨641154, by decide⟩
    (prefixPartial 13 348261) = some ⟨13, 2, 0, 641154, 348261, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_348261_641154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348261 ⟨641154, by decide⟩ :=
  accepted_of_selected 13 348261 ⟨641154, by decide⟩ ⟨13, 2, 0, 641154, 348261, 1417, 16384⟩
    (by decide) selected_cut_25353

theorem selected_cut_25354 : selected 8 ⟨641171, by decide⟩
    (prefixPartial 13 348262) = some ⟨13, 2, 0, 641171, 348262, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_348262_641171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348262 ⟨641171, by decide⟩ :=
  accepted_of_selected 13 348262 ⟨641171, by decide⟩ ⟨13, 2, 0, 641171, 348262, 1517, 16384⟩
    (by decide) selected_cut_25354

theorem selected_cut_25355 : selected 8 ⟨641177, by decide⟩
    (prefixPartial 13 348263) = some ⟨13, 2, 0, 641177, 348263, 793, 16384⟩ := by
  decide +kernel

theorem context_13_348263_641177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348263 ⟨641177, by decide⟩ :=
  accepted_of_selected 13 348263 ⟨641177, by decide⟩ ⟨13, 2, 0, 641177, 348263, 793, 16384⟩
    (by decide) selected_cut_25355

theorem unmarked_context_12_87065_641178 : frontier 9 ⟨641178, by decide⟩
    (prefixCache 12 87065) (prefixPartial 12 87065) = false := by
  decide +kernel

theorem node_context_12_87065_641178 : EJMOriginalGlobalDAGData.nodes 9 ⟨641178, by decide⟩ =
    .split (coordinate 12) (![⟨641131, by decide⟩,⟨641154, by decide⟩,⟨641171, by decide⟩,⟨641177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87065_641178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87065 ⟨641178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87065
    ⟨641178, by decide⟩ (by decide) (![⟨641131, by decide⟩,⟨641154, by decide⟩,⟨641171, by decide⟩,⟨641177, by decide⟩]) unmarked_context_12_87065_641178 node_context_12_87065_641178
  intro a
  fin_cases a
  · exact context_13_348260_641131
  · exact context_13_348261_641154
  · exact context_13_348262_641171
  · exact context_13_348263_641177

theorem selected_cut_25356 : selected 8 ⟨641203, by decide⟩
    (prefixPartial 13 348264) = some ⟨13, 2, 0, 641203, 348264, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_348264_641203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348264 ⟨641203, by decide⟩ :=
  accepted_of_selected 13 348264 ⟨641203, by decide⟩ ⟨13, 2, 0, 641203, 348264, 1185, 16384⟩
    (by decide) selected_cut_25356

theorem selected_cut_25357 : selected 8 ⟨641234, by decide⟩
    (prefixPartial 13 348265) = some ⟨13, 2, 0, 641234, 348265, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_348265_641234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348265 ⟨641234, by decide⟩ :=
  accepted_of_selected 13 348265 ⟨641234, by decide⟩ ⟨13, 2, 0, 641234, 348265, 1649, 16384⟩
    (by decide) selected_cut_25357

theorem selected_cut_25358 : selected 8 ⟨641249, by decide⟩
    (prefixPartial 13 348266) = some ⟨13, 2, 0, 641249, 348266, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_348266_641249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348266 ⟨641249, by decide⟩ :=
  accepted_of_selected 13 348266 ⟨641249, by decide⟩ ⟨13, 2, 0, 641249, 348266, 1301, 16384⟩
    (by decide) selected_cut_25358

theorem selected_cut_25359 : selected 8 ⟨641254, by decide⟩
    (prefixPartial 13 348267) = some ⟨13, 2, 0, 641254, 348267, 933, 16384⟩ := by
  decide +kernel

theorem context_13_348267_641254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348267 ⟨641254, by decide⟩ :=
  accepted_of_selected 13 348267 ⟨641254, by decide⟩ ⟨13, 2, 0, 641254, 348267, 933, 16384⟩
    (by decide) selected_cut_25359

theorem unmarked_context_12_87066_641255 : frontier 9 ⟨641255, by decide⟩
    (prefixCache 12 87066) (prefixPartial 12 87066) = false := by
  decide +kernel

theorem node_context_12_87066_641255 : EJMOriginalGlobalDAGData.nodes 9 ⟨641255, by decide⟩ =
    .split (coordinate 12) (![⟨641203, by decide⟩,⟨641234, by decide⟩,⟨641249, by decide⟩,⟨641254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87066_641255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87066 ⟨641255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87066
    ⟨641255, by decide⟩ (by decide) (![⟨641203, by decide⟩,⟨641234, by decide⟩,⟨641249, by decide⟩,⟨641254, by decide⟩]) unmarked_context_12_87066_641255 node_context_12_87066_641255
  intro a
  fin_cases a
  · exact context_13_348264_641203
  · exact context_13_348265_641234
  · exact context_13_348266_641249
  · exact context_13_348267_641254

theorem selected_cut_25360 : selected 8 ⟨641276, by decide⟩
    (prefixPartial 13 348268) = some ⟨13, 2, 0, 641276, 348268, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_348268_641276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348268 ⟨641276, by decide⟩ :=
  accepted_of_selected 13 348268 ⟨641276, by decide⟩ ⟨13, 2, 0, 641276, 348268, 1137, 16384⟩
    (by decide) selected_cut_25360

theorem selected_cut_25361 : selected 8 ⟨641307, by decide⟩
    (prefixPartial 13 348269) = some ⟨13, 2, 0, 641307, 348269, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_348269_641307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348269 ⟨641307, by decide⟩ :=
  accepted_of_selected 13 348269 ⟨641307, by decide⟩ ⟨13, 2, 0, 641307, 348269, 1689, 16384⟩
    (by decide) selected_cut_25361

theorem selected_cut_25362 : selected 8 ⟨641326, by decide⟩
    (prefixPartial 13 348270) = some ⟨13, 2, 0, 641326, 348270, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_348270_641326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348270 ⟨641326, by decide⟩ :=
  accepted_of_selected 13 348270 ⟨641326, by decide⟩ ⟨13, 2, 0, 641326, 348270, 1721, 16384⟩
    (by decide) selected_cut_25362

theorem selected_cut_25363 : selected 8 ⟨641333, by decide⟩
    (prefixPartial 13 348271) = some ⟨13, 2, 0, 641333, 348271, 765, 16384⟩ := by
  decide +kernel

theorem context_13_348271_641333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348271 ⟨641333, by decide⟩ :=
  accepted_of_selected 13 348271 ⟨641333, by decide⟩ ⟨13, 2, 0, 641333, 348271, 765, 16384⟩
    (by decide) selected_cut_25363

theorem unmarked_context_12_87067_641334 : frontier 9 ⟨641334, by decide⟩
    (prefixCache 12 87067) (prefixPartial 12 87067) = false := by
  decide +kernel

theorem node_context_12_87067_641334 : EJMOriginalGlobalDAGData.nodes 9 ⟨641334, by decide⟩ =
    .split (coordinate 12) (![⟨641276, by decide⟩,⟨641307, by decide⟩,⟨641326, by decide⟩,⟨641333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87067_641334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87067 ⟨641334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87067
    ⟨641334, by decide⟩ (by decide) (![⟨641276, by decide⟩,⟨641307, by decide⟩,⟨641326, by decide⟩,⟨641333, by decide⟩]) unmarked_context_12_87067_641334 node_context_12_87067_641334
  intro a
  fin_cases a
  · exact context_13_348268_641276
  · exact context_13_348269_641307
  · exact context_13_348270_641326
  · exact context_13_348271_641333

theorem unmarked_context_11_21766_641335 : frontier 10 ⟨641335, by decide⟩
    (prefixCache 11 21766) (prefixPartial 11 21766) = false := by
  decide +kernel

theorem node_context_11_21766_641335 : EJMOriginalGlobalDAGData.nodes 10 ⟨641335, by decide⟩ =
    .split (coordinate 11) (![⟨641112, by decide⟩,⟨641178, by decide⟩,⟨641255, by decide⟩,⟨641334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21766_641335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21766 ⟨641335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21766
    ⟨641335, by decide⟩ (by decide) (![⟨641112, by decide⟩,⟨641178, by decide⟩,⟨641255, by decide⟩,⟨641334, by decide⟩]) unmarked_context_11_21766_641335 node_context_11_21766_641335
  intro a
  fin_cases a
  · exact context_12_87064_641112
  · exact context_12_87065_641178
  · exact context_12_87066_641255
  · exact context_12_87067_641334

theorem selected_cut_25364 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 21767) = some ⟨11, 1, 0, 1736, 21767, 1, 262144⟩ := by
  decide +kernel

theorem context_11_21767_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21767 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 21767 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 21767, 1, 262144⟩
    (by decide) selected_cut_25364

theorem unmarked_context_10_5441_641336 : frontier 11 ⟨641336, by decide⟩
    (prefixCache 10 5441) (prefixPartial 10 5441) = false := by
  decide +kernel

theorem node_context_10_5441_641336 : EJMOriginalGlobalDAGData.nodes 11 ⟨641336, by decide⟩ =
    .split (coordinate 10) (![⟨640676, by decide⟩,⟨641010, by decide⟩,⟨641335, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5441_641336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5441 ⟨641336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5441
    ⟨641336, by decide⟩ (by decide) (![⟨640676, by decide⟩,⟨641010, by decide⟩,⟨641335, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_5441_641336 node_context_10_5441_641336
  intro a
  fin_cases a
  · exact context_11_21764_640676
  · exact context_11_21765_641010
  · exact context_11_21766_641335
  · exact context_11_21767_1736

theorem selected_cut_25365 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 87072) = some ⟨12, 1, 0, 641337, 87072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87072_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87072 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 87072 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 87072, 1, 65536⟩
    (by decide) selected_cut_25365

theorem selected_cut_25366 : selected 9 ⟨641416, by decide⟩
    (prefixPartial 12 87073) = some ⟨12, 2, 0, 641416, 87073, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_87073_641416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87073 ⟨641416, by decide⟩ :=
  accepted_of_selected 12 87073 ⟨641416, by decide⟩ ⟨12, 2, 0, 641416, 87073, 3853, 65536⟩
    (by decide) selected_cut_25366

theorem selected_cut_25367 : selected 8 ⟨641437, by decide⟩
    (prefixPartial 13 348296) = some ⟨13, 2, 0, 641437, 348296, 845, 16384⟩ := by
  decide +kernel

theorem context_13_348296_641437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348296 ⟨641437, by decide⟩ :=
  accepted_of_selected 13 348296 ⟨641437, by decide⟩ ⟨13, 2, 0, 641437, 348296, 845, 16384⟩
    (by decide) selected_cut_25367

theorem selected_cut_25368 : selected 8 ⟨641465, by decide⟩
    (prefixPartial 13 348297) = some ⟨13, 2, 0, 641465, 348297, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_348297_641465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348297 ⟨641465, by decide⟩ :=
  accepted_of_selected 13 348297 ⟨641465, by decide⟩ ⟨13, 2, 0, 641465, 348297, 1473, 16384⟩
    (by decide) selected_cut_25368

theorem selected_cut_25369 : selected 8 ⟨641479, by decide⟩
    (prefixPartial 13 348298) = some ⟨13, 2, 0, 641479, 348298, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_348298_641479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348298 ⟨641479, by decide⟩ :=
  accepted_of_selected 13 348298 ⟨641479, by decide⟩ ⟨13, 2, 0, 641479, 348298, 1101, 16384⟩
    (by decide) selected_cut_25369

theorem selected_cut_25370 : selected 8 ⟨641486, by decide⟩
    (prefixPartial 13 348299) = some ⟨13, 2, 0, 641486, 348299, 841, 16384⟩ := by
  decide +kernel

theorem context_13_348299_641486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348299 ⟨641486, by decide⟩ :=
  accepted_of_selected 13 348299 ⟨641486, by decide⟩ ⟨13, 2, 0, 641486, 348299, 841, 16384⟩
    (by decide) selected_cut_25370

theorem unmarked_context_12_87074_641487 : frontier 9 ⟨641487, by decide⟩
    (prefixCache 12 87074) (prefixPartial 12 87074) = false := by
  decide +kernel

theorem node_context_12_87074_641487 : EJMOriginalGlobalDAGData.nodes 9 ⟨641487, by decide⟩ =
    .split (coordinate 12) (![⟨641437, by decide⟩,⟨641465, by decide⟩,⟨641479, by decide⟩,⟨641486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87074_641487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87074 ⟨641487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87074
    ⟨641487, by decide⟩ (by decide) (![⟨641437, by decide⟩,⟨641465, by decide⟩,⟨641479, by decide⟩,⟨641486, by decide⟩]) unmarked_context_12_87074_641487 node_context_12_87074_641487
  intro a
  fin_cases a
  · exact context_13_348296_641437
  · exact context_13_348297_641465
  · exact context_13_348298_641479
  · exact context_13_348299_641486

theorem selected_cut_25371 : selected 9 ⟨641549, by decide⟩
    (prefixPartial 12 87075) = some ⟨12, 2, 0, 641549, 87075, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_87075_641549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87075 ⟨641549, by decide⟩ :=
  accepted_of_selected 12 87075 ⟨641549, by decide⟩ ⟨12, 2, 0, 641549, 87075, 3977, 65536⟩
    (by decide) selected_cut_25371

theorem unmarked_context_11_21768_641550 : frontier 10 ⟨641550, by decide⟩
    (prefixCache 11 21768) (prefixPartial 11 21768) = false := by
  decide +kernel

theorem node_context_11_21768_641550 : EJMOriginalGlobalDAGData.nodes 10 ⟨641550, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨641416, by decide⟩,⟨641487, by decide⟩,⟨641549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21768_641550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21768 ⟨641550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21768
    ⟨641550, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨641416, by decide⟩,⟨641487, by decide⟩,⟨641549, by decide⟩]) unmarked_context_11_21768_641550 node_context_11_21768_641550
  intro a
  fin_cases a
  · exact context_12_87072_641337
  · exact context_12_87073_641416
  · exact context_12_87074_641487
  · exact context_12_87075_641549

theorem selected_cut_25372 : selected 9 ⟨641614, by decide⟩
    (prefixPartial 12 87076) = some ⟨12, 2, 0, 641614, 87076, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_87076_641614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87076 ⟨641614, by decide⟩ :=
  accepted_of_selected 12 87076 ⟨641614, by decide⟩ ⟨12, 2, 0, 641614, 87076, 4033, 65536⟩
    (by decide) selected_cut_25372

theorem selected_cut_25373 : selected 9 ⟨641667, by decide⟩
    (prefixPartial 12 87077) = some ⟨12, 2, 0, 641667, 87077, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_87077_641667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87077 ⟨641667, by decide⟩ :=
  accepted_of_selected 12 87077 ⟨641667, by decide⟩ ⟨12, 2, 0, 641667, 87077, 3349, 65536⟩
    (by decide) selected_cut_25373

theorem selected_cut_25374 : selected 8 ⟨641688, by decide⟩
    (prefixPartial 13 348312) = some ⟨13, 2, 0, 641688, 348312, 705, 16384⟩ := by
  decide +kernel

theorem context_13_348312_641688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348312 ⟨641688, by decide⟩ :=
  accepted_of_selected 13 348312 ⟨641688, by decide⟩ ⟨13, 2, 0, 641688, 348312, 705, 16384⟩
    (by decide) selected_cut_25374

theorem selected_cut_25375 : selected 8 ⟨641718, by decide⟩
    (prefixPartial 13 348313) = some ⟨13, 2, 0, 641718, 348313, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_348313_641718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348313 ⟨641718, by decide⟩ :=
  accepted_of_selected 13 348313 ⟨641718, by decide⟩ ⟨13, 2, 0, 641718, 348313, 1605, 16384⟩
    (by decide) selected_cut_25375

theorem selected_cut_25376 : selected 8 ⟨641733, by decide⟩
    (prefixPartial 13 348314) = some ⟨13, 2, 0, 641733, 348314, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_348314_641733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348314 ⟨641733, by decide⟩ :=
  accepted_of_selected 13 348314 ⟨641733, by decide⟩ ⟨13, 2, 0, 641733, 348314, 1101, 16384⟩
    (by decide) selected_cut_25376

theorem selected_cut_25377 : selected 8 ⟨641739, by decide⟩
    (prefixPartial 13 348315) = some ⟨13, 2, 0, 641739, 348315, 785, 16384⟩ := by
  decide +kernel

theorem context_13_348315_641739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348315 ⟨641739, by decide⟩ :=
  accepted_of_selected 13 348315 ⟨641739, by decide⟩ ⟨13, 2, 0, 641739, 348315, 785, 16384⟩
    (by decide) selected_cut_25377

theorem unmarked_context_12_87078_641740 : frontier 9 ⟨641740, by decide⟩
    (prefixCache 12 87078) (prefixPartial 12 87078) = false := by
  decide +kernel

theorem node_context_12_87078_641740 : EJMOriginalGlobalDAGData.nodes 9 ⟨641740, by decide⟩ =
    .split (coordinate 12) (![⟨641688, by decide⟩,⟨641718, by decide⟩,⟨641733, by decide⟩,⟨641739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87078_641740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87078 ⟨641740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87078
    ⟨641740, by decide⟩ (by decide) (![⟨641688, by decide⟩,⟨641718, by decide⟩,⟨641733, by decide⟩,⟨641739, by decide⟩]) unmarked_context_12_87078_641740 node_context_12_87078_641740
  intro a
  fin_cases a
  · exact context_13_348312_641688
  · exact context_13_348313_641718
  · exact context_13_348314_641733
  · exact context_13_348315_641739

theorem selected_cut_25378 : selected 9 ⟨641799, by decide⟩
    (prefixPartial 12 87079) = some ⟨12, 2, 0, 641799, 87079, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_87079_641799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87079 ⟨641799, by decide⟩ :=
  accepted_of_selected 12 87079 ⟨641799, by decide⟩ ⟨12, 2, 0, 641799, 87079, 3809, 65536⟩
    (by decide) selected_cut_25378

theorem unmarked_context_11_21769_641800 : frontier 10 ⟨641800, by decide⟩
    (prefixCache 11 21769) (prefixPartial 11 21769) = false := by
  decide +kernel

theorem node_context_11_21769_641800 : EJMOriginalGlobalDAGData.nodes 10 ⟨641800, by decide⟩ =
    .split (coordinate 11) (![⟨641614, by decide⟩,⟨641667, by decide⟩,⟨641740, by decide⟩,⟨641799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21769_641800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21769 ⟨641800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21769
    ⟨641800, by decide⟩ (by decide) (![⟨641614, by decide⟩,⟨641667, by decide⟩,⟨641740, by decide⟩,⟨641799, by decide⟩]) unmarked_context_11_21769_641800 node_context_11_21769_641800
  intro a
  fin_cases a
  · exact context_12_87076_641614
  · exact context_12_87077_641667
  · exact context_12_87078_641740
  · exact context_12_87079_641799

theorem selected_cut_25379 : selected 8 ⟨641807, by decide⟩
    (prefixPartial 13 348320) = some ⟨13, 2, 0, 641807, 348320, 409, 16384⟩ := by
  decide +kernel

theorem context_13_348320_641807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348320 ⟨641807, by decide⟩ :=
  accepted_of_selected 13 348320 ⟨641807, by decide⟩ ⟨13, 2, 0, 641807, 348320, 409, 16384⟩
    (by decide) selected_cut_25379

theorem selected_cut_25380 : selected 8 ⟨641852, by decide⟩
    (prefixPartial 13 348321) = some ⟨13, 2, 0, 641852, 348321, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_348321_641852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348321 ⟨641852, by decide⟩ :=
  accepted_of_selected 13 348321 ⟨641852, by decide⟩ ⟨13, 2, 0, 641852, 348321, 1753, 16384⟩
    (by decide) selected_cut_25380

theorem selected_cut_25381 : selected 8 ⟨641869, by decide⟩
    (prefixPartial 13 348322) = some ⟨13, 2, 0, 641869, 348322, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_348322_641869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348322 ⟨641869, by decide⟩ :=
  accepted_of_selected 13 348322 ⟨641869, by decide⟩ ⟨13, 2, 0, 641869, 348322, 1237, 16384⟩
    (by decide) selected_cut_25381

theorem selected_cut_25382 : selected 8 ⟨641876, by decide⟩
    (prefixPartial 13 348323) = some ⟨13, 2, 0, 641876, 348323, 765, 16384⟩ := by
  decide +kernel

theorem context_13_348323_641876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348323 ⟨641876, by decide⟩ :=
  accepted_of_selected 13 348323 ⟨641876, by decide⟩ ⟨13, 2, 0, 641876, 348323, 765, 16384⟩
    (by decide) selected_cut_25382

theorem unmarked_context_12_87080_641877 : frontier 9 ⟨641877, by decide⟩
    (prefixCache 12 87080) (prefixPartial 12 87080) = false := by
  decide +kernel

theorem node_context_12_87080_641877 : EJMOriginalGlobalDAGData.nodes 9 ⟨641877, by decide⟩ =
    .split (coordinate 12) (![⟨641807, by decide⟩,⟨641852, by decide⟩,⟨641869, by decide⟩,⟨641876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87080_641877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87080 ⟨641877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87080
    ⟨641877, by decide⟩ (by decide) (![⟨641807, by decide⟩,⟨641852, by decide⟩,⟨641869, by decide⟩,⟨641876, by decide⟩]) unmarked_context_12_87080_641877 node_context_12_87080_641877
  intro a
  fin_cases a
  · exact context_13_348320_641807
  · exact context_13_348321_641852
  · exact context_13_348322_641869
  · exact context_13_348323_641876

theorem selected_cut_25383 : selected 9 ⟨641928, by decide⟩
    (prefixPartial 12 87081) = some ⟨12, 2, 0, 641928, 87081, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_87081_641928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87081 ⟨641928, by decide⟩ :=
  accepted_of_selected 12 87081 ⟨641928, by decide⟩ ⟨12, 2, 0, 641928, 87081, 3617, 65536⟩
    (by decide) selected_cut_25383

theorem selected_cut_25384 : selected 9 ⟨641992, by decide⟩
    (prefixPartial 12 87082) = some ⟨12, 2, 0, 641992, 87082, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_87082_641992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87082 ⟨641992, by decide⟩ :=
  accepted_of_selected 12 87082 ⟨641992, by decide⟩ ⟨12, 2, 0, 641992, 87082, 3749, 65536⟩
    (by decide) selected_cut_25384

theorem selected_cut_25385 : selected 9 ⟨642055, by decide⟩
    (prefixPartial 12 87083) = some ⟨12, 2, 0, 642055, 87083, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_87083_642055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87083 ⟨642055, by decide⟩ :=
  accepted_of_selected 12 87083 ⟨642055, by decide⟩ ⟨12, 2, 0, 642055, 87083, 3689, 65536⟩
    (by decide) selected_cut_25385

theorem unmarked_context_11_21770_642056 : frontier 10 ⟨642056, by decide⟩
    (prefixCache 11 21770) (prefixPartial 11 21770) = false := by
  decide +kernel

theorem node_context_11_21770_642056 : EJMOriginalGlobalDAGData.nodes 10 ⟨642056, by decide⟩ =
    .split (coordinate 11) (![⟨641877, by decide⟩,⟨641928, by decide⟩,⟨641992, by decide⟩,⟨642055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21770_642056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21770 ⟨642056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21770
    ⟨642056, by decide⟩ (by decide) (![⟨641877, by decide⟩,⟨641928, by decide⟩,⟨641992, by decide⟩,⟨642055, by decide⟩]) unmarked_context_11_21770_642056 node_context_11_21770_642056
  intro a
  fin_cases a
  · exact context_12_87080_641877
  · exact context_12_87081_641928
  · exact context_12_87082_641992
  · exact context_12_87083_642055

theorem selected_cut_25386 : selected 9 ⟨642124, by decide⟩
    (prefixPartial 12 87084) = some ⟨12, 2, 0, 642124, 87084, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_87084_642124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87084 ⟨642124, by decide⟩ :=
  accepted_of_selected 12 87084 ⟨642124, by decide⟩ ⟨12, 2, 0, 642124, 87084, 3801, 65536⟩
    (by decide) selected_cut_25386

theorem selected_cut_25387 : selected 9 ⟨642177, by decide⟩
    (prefixPartial 12 87085) = some ⟨12, 2, 0, 642177, 87085, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_87085_642177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87085 ⟨642177, by decide⟩ :=
  accepted_of_selected 12 87085 ⟨642177, by decide⟩ ⟨12, 2, 0, 642177, 87085, 3265, 65536⟩
    (by decide) selected_cut_25387

theorem selected_cut_25388 : selected 9 ⟨642243, by decide⟩
    (prefixPartial 12 87086) = some ⟨12, 2, 0, 642243, 87086, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_87086_642243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87086 ⟨642243, by decide⟩ :=
  accepted_of_selected 12 87086 ⟨642243, by decide⟩ ⟨12, 2, 0, 642243, 87086, 3753, 65536⟩
    (by decide) selected_cut_25388

theorem selected_cut_25389 : selected 9 ⟨642290, by decide⟩
    (prefixPartial 12 87087) = some ⟨12, 2, 0, 642290, 87087, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_87087_642290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87087 ⟨642290, by decide⟩ :=
  accepted_of_selected 12 87087 ⟨642290, by decide⟩ ⟨12, 2, 0, 642290, 87087, 3205, 65536⟩
    (by decide) selected_cut_25389

theorem unmarked_context_11_21771_642291 : frontier 10 ⟨642291, by decide⟩
    (prefixCache 11 21771) (prefixPartial 11 21771) = false := by
  decide +kernel

theorem node_context_11_21771_642291 : EJMOriginalGlobalDAGData.nodes 10 ⟨642291, by decide⟩ =
    .split (coordinate 11) (![⟨642124, by decide⟩,⟨642177, by decide⟩,⟨642243, by decide⟩,⟨642290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21771_642291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21771 ⟨642291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21771
    ⟨642291, by decide⟩ (by decide) (![⟨642124, by decide⟩,⟨642177, by decide⟩,⟨642243, by decide⟩,⟨642290, by decide⟩]) unmarked_context_11_21771_642291 node_context_11_21771_642291
  intro a
  fin_cases a
  · exact context_12_87084_642124
  · exact context_12_87085_642177
  · exact context_12_87086_642243
  · exact context_12_87087_642290

theorem unmarked_context_10_5442_642292 : frontier 11 ⟨642292, by decide⟩
    (prefixCache 10 5442) (prefixPartial 10 5442) = false := by
  decide +kernel

theorem node_context_10_5442_642292 : EJMOriginalGlobalDAGData.nodes 11 ⟨642292, by decide⟩ =
    .split (coordinate 10) (![⟨641550, by decide⟩,⟨641800, by decide⟩,⟨642056, by decide⟩,⟨642291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5442_642292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5442 ⟨642292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5442
    ⟨642292, by decide⟩ (by decide) (![⟨641550, by decide⟩,⟨641800, by decide⟩,⟨642056, by decide⟩,⟨642291, by decide⟩]) unmarked_context_10_5442_642292 node_context_10_5442_642292
  intro a
  fin_cases a
  · exact context_11_21768_641550
  · exact context_11_21769_641800
  · exact context_11_21770_642056
  · exact context_11_21771_642291

theorem selected_cut_25390 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 5443) = some ⟨10, 1, 0, 3440, 5443, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5443_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5443 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 5443 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 5443, 1, 1048576⟩
    (by decide) selected_cut_25390

theorem unmarked_context_9_1360_642293 : frontier 12 ⟨642293, by decide⟩
    (prefixCache 9 1360) (prefixPartial 9 1360) = false := by
  decide +kernel

theorem node_context_9_1360_642293 : EJMOriginalGlobalDAGData.nodes 12 ⟨642293, by decide⟩ =
    .split (coordinate 9) (![⟨640546, by decide⟩,⟨641336, by decide⟩,⟨642292, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1360_642293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1360 ⟨642293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1360
    ⟨642293, by decide⟩ (by decide) (![⟨640546, by decide⟩,⟨641336, by decide⟩,⟨642292, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1360_642293 node_context_9_1360_642293
  intro a
  fin_cases a
  · exact context_10_5440_640546
  · exact context_10_5441_641336
  · exact context_10_5442_642292
  · exact context_10_5443_3440

theorem selected_cut_25391 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 5444) = some ⟨10, 1, 0, 3442, 5444, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5444_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5444 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 5444 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 5444, 1, 1048576⟩
    (by decide) selected_cut_25391

theorem selected_cut_25392 : selected 10 ⟨642393, by decide⟩
    (prefixPartial 11 21780) = some ⟨11, 2, 0, 642393, 21780, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_21780_642393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21780 ⟨642393, by decide⟩ :=
  accepted_of_selected 11 21780 ⟨642393, by decide⟩ ⟨11, 2, 0, 642393, 21780, 3957, 262144⟩
    (by decide) selected_cut_25392

theorem selected_cut_25393 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 21781) = some ⟨11, 1, 0, 451541, 21781, 1, 262144⟩ := by
  decide +kernel

theorem context_11_21781_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21781 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 21781 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 21781, 1, 262144⟩
    (by decide) selected_cut_25393

theorem selected_cut_25394 : selected 10 ⟨642478, by decide⟩
    (prefixPartial 11 21782) = some ⟨11, 2, 0, 642478, 21782, 3633, 262144⟩ := by
  decide +kernel

theorem context_11_21782_642478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21782 ⟨642478, by decide⟩ :=
  accepted_of_selected 11 21782 ⟨642478, by decide⟩ ⟨11, 2, 0, 642478, 21782, 3633, 262144⟩
    (by decide) selected_cut_25394

theorem selected_cut_25395 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 21783) = some ⟨11, 1, 0, 1736, 21783, 1, 262144⟩ := by
  decide +kernel

theorem context_11_21783_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21783 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 21783 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 21783, 1, 262144⟩
    (by decide) selected_cut_25395

theorem unmarked_context_10_5445_642479 : frontier 11 ⟨642479, by decide⟩
    (prefixCache 10 5445) (prefixPartial 10 5445) = false := by
  decide +kernel

theorem node_context_10_5445_642479 : EJMOriginalGlobalDAGData.nodes 11 ⟨642479, by decide⟩ =
    .split (coordinate 10) (![⟨642393, by decide⟩,⟨451541, by decide⟩,⟨642478, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5445_642479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5445 ⟨642479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5445
    ⟨642479, by decide⟩ (by decide) (![⟨642393, by decide⟩,⟨451541, by decide⟩,⟨642478, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_5445_642479 node_context_10_5445_642479
  intro a
  fin_cases a
  · exact context_11_21780_642393
  · exact context_11_21781_451541
  · exact context_11_21782_642478
  · exact context_11_21783_1736

theorem selected_cut_25396 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 348544) = some ⟨13, 1, 0, 3444, 348544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_348544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 348544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 348544, 1, 16384⟩
    (by decide) selected_cut_25396

theorem selected_cut_25397 : selected 8 ⟨642543, by decide⟩
    (prefixPartial 13 348545) = some ⟨13, 2, 0, 642543, 348545, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_348545_642543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348545 ⟨642543, by decide⟩ :=
  accepted_of_selected 13 348545 ⟨642543, by decide⟩ ⟨13, 2, 0, 642543, 348545, 2025, 16384⟩
    (by decide) selected_cut_25397

theorem selected_cut_25398 : selected 8 ⟨642569, by decide⟩
    (prefixPartial 13 348546) = some ⟨13, 2, 0, 642569, 348546, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_348546_642569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348546 ⟨642569, by decide⟩ :=
  accepted_of_selected 13 348546 ⟨642569, by decide⟩ ⟨13, 2, 0, 642569, 348546, 1573, 16384⟩
    (by decide) selected_cut_25398

theorem selected_cut_25399 : selected 8 ⟨642576, by decide⟩
    (prefixPartial 13 348547) = some ⟨13, 2, 0, 642576, 348547, 865, 16384⟩ := by
  decide +kernel

theorem context_13_348547_642576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348547 ⟨642576, by decide⟩ :=
  accepted_of_selected 13 348547 ⟨642576, by decide⟩ ⟨13, 2, 0, 642576, 348547, 865, 16384⟩
    (by decide) selected_cut_25399

theorem unmarked_context_12_87136_642577 : frontier 9 ⟨642577, by decide⟩
    (prefixCache 12 87136) (prefixPartial 12 87136) = false := by
  decide +kernel

theorem node_context_12_87136_642577 : EJMOriginalGlobalDAGData.nodes 9 ⟨642577, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨642543, by decide⟩,⟨642569, by decide⟩,⟨642576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87136_642577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87136 ⟨642577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87136
    ⟨642577, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨642543, by decide⟩,⟨642569, by decide⟩,⟨642576, by decide⟩]) unmarked_context_12_87136_642577 node_context_12_87136_642577
  intro a
  fin_cases a
  · exact context_13_348544_3444
  · exact context_13_348545_642543
  · exact context_13_348546_642569
  · exact context_13_348547_642576

theorem selected_cut_25400 : selected 9 ⟨642659, by decide⟩
    (prefixPartial 12 87137) = some ⟨12, 2, 0, 642659, 87137, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_87137_642659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87137 ⟨642659, by decide⟩ :=
  accepted_of_selected 12 87137 ⟨642659, by decide⟩ ⟨12, 2, 0, 642659, 87137, 3269, 65536⟩
    (by decide) selected_cut_25400

theorem selected_cut_25401 : selected 9 ⟨642709, by decide⟩
    (prefixPartial 12 87138) = some ⟨12, 2, 0, 642709, 87138, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_87138_642709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87138 ⟨642709, by decide⟩ :=
  accepted_of_selected 12 87138 ⟨642709, by decide⟩ ⟨12, 2, 0, 642709, 87138, 2681, 65536⟩
    (by decide) selected_cut_25401

theorem selected_cut_25402 : selected 9 ⟨642751, by decide⟩
    (prefixPartial 12 87139) = some ⟨12, 2, 0, 642751, 87139, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_87139_642751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87139 ⟨642751, by decide⟩ :=
  accepted_of_selected 12 87139 ⟨642751, by decide⟩ ⟨12, 2, 0, 642751, 87139, 2393, 65536⟩
    (by decide) selected_cut_25402

theorem unmarked_context_11_21784_642752 : frontier 10 ⟨642752, by decide⟩
    (prefixCache 11 21784) (prefixPartial 11 21784) = false := by
  decide +kernel

theorem node_context_11_21784_642752 : EJMOriginalGlobalDAGData.nodes 10 ⟨642752, by decide⟩ =
    .split (coordinate 11) (![⟨642577, by decide⟩,⟨642659, by decide⟩,⟨642709, by decide⟩,⟨642751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21784_642752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21784 ⟨642752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21784
    ⟨642752, by decide⟩ (by decide) (![⟨642577, by decide⟩,⟨642659, by decide⟩,⟨642709, by decide⟩,⟨642751, by decide⟩]) unmarked_context_11_21784_642752 node_context_11_21784_642752
  intro a
  fin_cases a
  · exact context_12_87136_642577
  · exact context_12_87137_642659
  · exact context_12_87138_642709
  · exact context_12_87139_642751

theorem selected_cut_25403 : selected 9 ⟨642793, by decide⟩
    (prefixPartial 12 87140) = some ⟨12, 2, 0, 642793, 87140, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_87140_642793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87140 ⟨642793, by decide⟩ :=
  accepted_of_selected 12 87140 ⟨642793, by decide⟩ ⟨12, 2, 0, 642793, 87140, 2153, 65536⟩
    (by decide) selected_cut_25403

theorem selected_cut_25404 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 87141) = some ⟨12, 1, 0, 642794, 87141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87141_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87141 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 87141 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 87141, 1, 65536⟩
    (by decide) selected_cut_25404

theorem selected_cut_25405 : selected 9 ⟨642835, by decide⟩
    (prefixPartial 12 87142) = some ⟨12, 2, 0, 642835, 87142, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_87142_642835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87142 ⟨642835, by decide⟩ :=
  accepted_of_selected 12 87142 ⟨642835, by decide⟩ ⟨12, 2, 0, 642835, 87142, 2069, 65536⟩
    (by decide) selected_cut_25405

theorem selected_cut_25406 : selected 9 ⟨642872, by decide⟩
    (prefixPartial 12 87143) = some ⟨12, 2, 0, 642872, 87143, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_87143_642872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87143 ⟨642872, by decide⟩ :=
  accepted_of_selected 12 87143 ⟨642872, by decide⟩ ⟨12, 2, 0, 642872, 87143, 1845, 65536⟩
    (by decide) selected_cut_25406

theorem unmarked_context_11_21785_642873 : frontier 10 ⟨642873, by decide⟩
    (prefixCache 11 21785) (prefixPartial 11 21785) = false := by
  decide +kernel

theorem node_context_11_21785_642873 : EJMOriginalGlobalDAGData.nodes 10 ⟨642873, by decide⟩ =
    .split (coordinate 11) (![⟨642793, by decide⟩,⟨642794, by decide⟩,⟨642835, by decide⟩,⟨642872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21785_642873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21785 ⟨642873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21785
    ⟨642873, by decide⟩ (by decide) (![⟨642793, by decide⟩,⟨642794, by decide⟩,⟨642835, by decide⟩,⟨642872, by decide⟩]) unmarked_context_11_21785_642873 node_context_11_21785_642873
  intro a
  fin_cases a
  · exact context_12_87140_642793
  · exact context_12_87141_642794
  · exact context_12_87142_642835
  · exact context_12_87143_642872

theorem selected_cut_25407 : selected 9 ⟨642910, by decide⟩
    (prefixPartial 12 87144) = some ⟨12, 2, 0, 642910, 87144, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_87144_642910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87144 ⟨642910, by decide⟩ :=
  accepted_of_selected 12 87144 ⟨642910, by decide⟩ ⟨12, 2, 0, 642910, 87144, 2049, 65536⟩
    (by decide) selected_cut_25407

theorem selected_cut_25408 : selected 9 ⟨642962, by decide⟩
    (prefixPartial 12 87145) = some ⟨12, 2, 0, 642962, 87145, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_87145_642962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87145 ⟨642962, by decide⟩ :=
  accepted_of_selected 12 87145 ⟨642962, by decide⟩ ⟨12, 2, 0, 642962, 87145, 2253, 65536⟩
    (by decide) selected_cut_25408

theorem selected_cut_25409 : selected 9 ⟨642995, by decide⟩
    (prefixPartial 12 87146) = some ⟨12, 2, 0, 642995, 87146, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_87146_642995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87146 ⟨642995, by decide⟩ :=
  accepted_of_selected 12 87146 ⟨642995, by decide⟩ ⟨12, 2, 0, 642995, 87146, 1785, 65536⟩
    (by decide) selected_cut_25409

theorem selected_cut_25410 : selected 9 ⟨643024, by decide⟩
    (prefixPartial 12 87147) = some ⟨12, 2, 0, 643024, 87147, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_87147_643024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87147 ⟨643024, by decide⟩ :=
  accepted_of_selected 12 87147 ⟨643024, by decide⟩ ⟨12, 2, 0, 643024, 87147, 1561, 65536⟩
    (by decide) selected_cut_25410

theorem unmarked_context_11_21786_643025 : frontier 10 ⟨643025, by decide⟩
    (prefixCache 11 21786) (prefixPartial 11 21786) = false := by
  decide +kernel

theorem node_context_11_21786_643025 : EJMOriginalGlobalDAGData.nodes 10 ⟨643025, by decide⟩ =
    .split (coordinate 11) (![⟨642910, by decide⟩,⟨642962, by decide⟩,⟨642995, by decide⟩,⟨643024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21786_643025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21786 ⟨643025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21786
    ⟨643025, by decide⟩ (by decide) (![⟨642910, by decide⟩,⟨642962, by decide⟩,⟨642995, by decide⟩,⟨643024, by decide⟩]) unmarked_context_11_21786_643025 node_context_11_21786_643025
  intro a
  fin_cases a
  · exact context_12_87144_642910
  · exact context_12_87145_642962
  · exact context_12_87146_642995
  · exact context_12_87147_643024

theorem selected_cut_25411 : selected 9 ⟨643054, by decide⟩
    (prefixPartial 12 87148) = some ⟨12, 2, 0, 643054, 87148, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_87148_643054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87148 ⟨643054, by decide⟩ :=
  accepted_of_selected 12 87148 ⟨643054, by decide⟩ ⟨12, 2, 0, 643054, 87148, 1645, 65536⟩
    (by decide) selected_cut_25411

theorem selected_cut_25412 : selected 9 ⟨643091, by decide⟩
    (prefixPartial 12 87149) = some ⟨12, 2, 0, 643091, 87149, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_87149_643091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87149 ⟨643091, by decide⟩ :=
  accepted_of_selected 12 87149 ⟨643091, by decide⟩ ⟨12, 2, 0, 643091, 87149, 1805, 65536⟩
    (by decide) selected_cut_25412

theorem selected_cut_25413 : selected 9 ⟨643117, by decide⟩
    (prefixPartial 12 87150) = some ⟨12, 2, 0, 643117, 87150, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_87150_643117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87150 ⟨643117, by decide⟩ :=
  accepted_of_selected 12 87150 ⟨643117, by decide⟩ ⟨12, 2, 0, 643117, 87150, 1421, 65536⟩
    (by decide) selected_cut_25413

theorem selected_cut_25414 : selected 9 ⟨643134, by decide⟩
    (prefixPartial 12 87151) = some ⟨12, 2, 0, 643134, 87151, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_87151_643134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87151 ⟨643134, by decide⟩ :=
  accepted_of_selected 12 87151 ⟨643134, by decide⟩ ⟨12, 2, 0, 643134, 87151, 1133, 65536⟩
    (by decide) selected_cut_25414

theorem unmarked_context_11_21787_643135 : frontier 10 ⟨643135, by decide⟩
    (prefixCache 11 21787) (prefixPartial 11 21787) = false := by
  decide +kernel

theorem node_context_11_21787_643135 : EJMOriginalGlobalDAGData.nodes 10 ⟨643135, by decide⟩ =
    .split (coordinate 11) (![⟨643054, by decide⟩,⟨643091, by decide⟩,⟨643117, by decide⟩,⟨643134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21787_643135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21787 ⟨643135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21787
    ⟨643135, by decide⟩ (by decide) (![⟨643054, by decide⟩,⟨643091, by decide⟩,⟨643117, by decide⟩,⟨643134, by decide⟩]) unmarked_context_11_21787_643135 node_context_11_21787_643135
  intro a
  fin_cases a
  · exact context_12_87148_643054
  · exact context_12_87149_643091
  · exact context_12_87150_643117
  · exact context_12_87151_643134

theorem unmarked_context_10_5446_643136 : frontier 11 ⟨643136, by decide⟩
    (prefixCache 10 5446) (prefixPartial 10 5446) = false := by
  decide +kernel

theorem node_context_10_5446_643136 : EJMOriginalGlobalDAGData.nodes 11 ⟨643136, by decide⟩ =
    .split (coordinate 10) (![⟨642752, by decide⟩,⟨642873, by decide⟩,⟨643025, by decide⟩,⟨643135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5446_643136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5446 ⟨643136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5446
    ⟨643136, by decide⟩ (by decide) (![⟨642752, by decide⟩,⟨642873, by decide⟩,⟨643025, by decide⟩,⟨643135, by decide⟩]) unmarked_context_10_5446_643136 node_context_10_5446_643136
  intro a
  fin_cases a
  · exact context_11_21784_642752
  · exact context_11_21785_642873
  · exact context_11_21786_643025
  · exact context_11_21787_643135

theorem selected_cut_25415 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 5447) = some ⟨10, 1, 0, 3440, 5447, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5447_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5447 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 5447 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 5447, 1, 1048576⟩
    (by decide) selected_cut_25415

theorem unmarked_context_9_1361_643137 : frontier 12 ⟨643137, by decide⟩
    (prefixCache 9 1361) (prefixPartial 9 1361) = false := by
  decide +kernel

theorem node_context_9_1361_643137 : EJMOriginalGlobalDAGData.nodes 12 ⟨643137, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨642479, by decide⟩,⟨643136, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1361_643137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1361 ⟨643137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1361
    ⟨643137, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨642479, by decide⟩,⟨643136, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1361_643137 node_context_9_1361_643137
  intro a
  fin_cases a
  · exact context_10_5444_3442
  · exact context_10_5445_642479
  · exact context_10_5446_643136
  · exact context_10_5447_3440

theorem selected_cut_25416 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 5448) = some ⟨10, 1, 0, 3442, 5448, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5448_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5448 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 5448 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 5448, 1, 1048576⟩
    (by decide) selected_cut_25416

theorem selected_cut_25417 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 5449) = some ⟨10, 1, 0, 3442, 5449, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5449_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5449 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 5449 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 5449, 1, 1048576⟩
    (by decide) selected_cut_25417

theorem selected_cut_25418 : selected 10 ⟨643174, by decide⟩
    (prefixPartial 11 21800) = some ⟨11, 2, 0, 643174, 21800, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_21800_643174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21800 ⟨643174, by decide⟩ :=
  accepted_of_selected 11 21800 ⟨643174, by decide⟩ ⟨11, 2, 0, 643174, 21800, 2817, 262144⟩
    (by decide) selected_cut_25418

theorem selected_cut_25419 : selected 10 ⟨643200, by decide⟩
    (prefixPartial 11 21801) = some ⟨11, 2, 0, 643200, 21801, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_21801_643200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21801 ⟨643200, by decide⟩ :=
  accepted_of_selected 11 21801 ⟨643200, by decide⟩ ⟨11, 2, 0, 643200, 21801, 1525, 262144⟩
    (by decide) selected_cut_25419

theorem selected_cut_25420 : selected 10 ⟨643210, by decide⟩
    (prefixPartial 11 21802) = some ⟨11, 2, 0, 643210, 21802, 817, 262144⟩ := by
  decide +kernel

theorem context_11_21802_643210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21802 ⟨643210, by decide⟩ :=
  accepted_of_selected 11 21802 ⟨643210, by decide⟩ ⟨11, 2, 0, 643210, 21802, 817, 262144⟩
    (by decide) selected_cut_25420

theorem selected_cut_25421 : selected 10 ⟨643216, by decide⟩
    (prefixPartial 11 21803) = some ⟨11, 2, 0, 643216, 21803, 269, 262144⟩ := by
  decide +kernel

theorem context_11_21803_643216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21803 ⟨643216, by decide⟩ :=
  accepted_of_selected 11 21803 ⟨643216, by decide⟩ ⟨11, 2, 0, 643216, 21803, 269, 262144⟩
    (by decide) selected_cut_25421

theorem unmarked_context_10_5450_643217 : frontier 11 ⟨643217, by decide⟩
    (prefixCache 10 5450) (prefixPartial 10 5450) = false := by
  decide +kernel

theorem node_context_10_5450_643217 : EJMOriginalGlobalDAGData.nodes 11 ⟨643217, by decide⟩ =
    .split (coordinate 10) (![⟨643174, by decide⟩,⟨643200, by decide⟩,⟨643210, by decide⟩,⟨643216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5450_643217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5450 ⟨643217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5450
    ⟨643217, by decide⟩ (by decide) (![⟨643174, by decide⟩,⟨643200, by decide⟩,⟨643210, by decide⟩,⟨643216, by decide⟩]) unmarked_context_10_5450_643217 node_context_10_5450_643217
  intro a
  fin_cases a
  · exact context_11_21800_643174
  · exact context_11_21801_643200
  · exact context_11_21802_643210
  · exact context_11_21803_643216

theorem selected_cut_25422 : selected 11 ⟨643291, by decide⟩
    (prefixPartial 10 5451) = some ⟨10, 2, 0, 643291, 5451, 2341, 1048576⟩ := by
  decide +kernel

theorem context_10_5451_643291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5451 ⟨643291, by decide⟩ :=
  accepted_of_selected 10 5451 ⟨643291, by decide⟩ ⟨10, 2, 0, 643291, 5451, 2341, 1048576⟩
    (by decide) selected_cut_25422

theorem unmarked_context_9_1362_643292 : frontier 12 ⟨643292, by decide⟩
    (prefixCache 9 1362) (prefixPartial 9 1362) = false := by
  decide +kernel

theorem node_context_9_1362_643292 : EJMOriginalGlobalDAGData.nodes 12 ⟨643292, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨643217, by decide⟩,⟨643291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1362_643292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1362 ⟨643292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1362
    ⟨643292, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨643217, by decide⟩,⟨643291, by decide⟩]) unmarked_context_9_1362_643292 node_context_9_1362_643292
  intro a
  fin_cases a
  · exact context_10_5448_3442
  · exact context_10_5449_3442
  · exact context_10_5450_643217
  · exact context_10_5451_643291

theorem selected_cut_25423 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 1363) = some ⟨9, 1, 0, 4601, 1363, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_1363_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1363 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 1363 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 1363, 1, 4194304⟩
    (by decide) selected_cut_25423

theorem unmarked_context_8_340_643293 : frontier 13 ⟨643293, by decide⟩
    (prefixCache 8 340) (prefixPartial 8 340) = false := by
  decide +kernel

theorem node_context_8_340_643293 : EJMOriginalGlobalDAGData.nodes 13 ⟨643293, by decide⟩ =
    .split (coordinate 8) (![⟨642293, by decide⟩,⟨643137, by decide⟩,⟨643292, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_340_643293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 340 ⟨643293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 340
    ⟨643293, by decide⟩ (by decide) (![⟨642293, by decide⟩,⟨643137, by decide⟩,⟨643292, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_340_643293 node_context_8_340_643293
  intro a
  fin_cases a
  · exact context_9_1360_642293
  · exact context_9_1361_643137
  · exact context_9_1362_643292
  · exact context_9_1363_4601

theorem selected_cut_25424 : selected 13 ⟨643294, by decide⟩
    (prefixPartial 8 341) = some ⟨8, 1, 0, 643294, 341, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_341_643294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 341 ⟨643294, by decide⟩ :=
  accepted_of_selected 8 341 ⟨643294, by decide⟩ ⟨8, 1, 0, 643294, 341, 1, 16777216⟩
    (by decide) selected_cut_25424

theorem selected_cut_25425 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 21888) = some ⟨11, 1, 0, 434745, 21888, 1, 262144⟩ := by
  decide +kernel

theorem context_11_21888_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21888 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 21888 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 21888, 1, 262144⟩
    (by decide) selected_cut_25425

theorem selected_cut_25426 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87556) = some ⟨12, 1, 0, 895, 87556, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87556_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87556 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87556 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87556, 1, 65536⟩
    (by decide) selected_cut_25426

theorem selected_cut_25427 : selected 8 ⟨643363, by decide⟩
    (prefixPartial 13 350228) = some ⟨13, 2, 0, 643363, 350228, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_350228_643363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350228 ⟨643363, by decide⟩ :=
  accepted_of_selected 13 350228 ⟨643363, by decide⟩ ⟨13, 2, 0, 643363, 350228, 2485, 16384⟩
    (by decide) selected_cut_25427

theorem selected_cut_25428 : selected 8 ⟨643412, by decide⟩
    (prefixPartial 13 350229) = some ⟨13, 2, 0, 643412, 350229, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_350229_643412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350229 ⟨643412, by decide⟩ :=
  accepted_of_selected 13 350229 ⟨643412, by decide⟩ ⟨13, 2, 0, 643412, 350229, 1361, 16384⟩
    (by decide) selected_cut_25428

theorem selected_cut_25429 : selected 8 ⟨643422, by decide⟩
    (prefixPartial 13 350230) = some ⟨13, 2, 0, 643422, 350230, 469, 16384⟩ := by
  decide +kernel

theorem context_13_350230_643422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350230 ⟨643422, by decide⟩ :=
  accepted_of_selected 13 350230 ⟨643422, by decide⟩ ⟨13, 2, 0, 643422, 350230, 469, 16384⟩
    (by decide) selected_cut_25429

theorem selected_cut_25430 : selected 8 ⟨643424, by decide⟩
    (prefixPartial 13 350231) = some ⟨13, 2, 0, 643424, 350231, 109, 16384⟩ := by
  decide +kernel

theorem context_13_350231_643424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350231 ⟨643424, by decide⟩ :=
  accepted_of_selected 13 350231 ⟨643424, by decide⟩ ⟨13, 2, 0, 643424, 350231, 109, 16384⟩
    (by decide) selected_cut_25430

theorem unmarked_context_12_87557_643425 : frontier 9 ⟨643425, by decide⟩
    (prefixCache 12 87557) (prefixPartial 12 87557) = false := by
  decide +kernel

theorem node_context_12_87557_643425 : EJMOriginalGlobalDAGData.nodes 9 ⟨643425, by decide⟩ =
    .split (coordinate 12) (![⟨643363, by decide⟩,⟨643412, by decide⟩,⟨643422, by decide⟩,⟨643424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87557_643425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87557 ⟨643425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87557
    ⟨643425, by decide⟩ (by decide) (![⟨643363, by decide⟩,⟨643412, by decide⟩,⟨643422, by decide⟩,⟨643424, by decide⟩]) unmarked_context_12_87557_643425 node_context_12_87557_643425
  intro a
  fin_cases a
  · exact context_13_350228_643363
  · exact context_13_350229_643412
  · exact context_13_350230_643422
  · exact context_13_350231_643424

theorem selected_cut_25431 : selected 8 ⟨643477, by decide⟩
    (prefixPartial 13 350232) = some ⟨13, 2, 0, 643477, 350232, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_350232_643477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350232 ⟨643477, by decide⟩ :=
  accepted_of_selected 13 350232 ⟨643477, by decide⟩ ⟨13, 2, 0, 643477, 350232, 2745, 16384⟩
    (by decide) selected_cut_25431

theorem selected_cut_25432 : selected 8 ⟨643527, by decide⟩
    (prefixPartial 13 350233) = some ⟨13, 2, 0, 643527, 350233, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_350233_643527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350233 ⟨643527, by decide⟩ :=
  accepted_of_selected 13 350233 ⟨643527, by decide⟩ ⟨13, 2, 0, 643527, 350233, 2677, 16384⟩
    (by decide) selected_cut_25432

theorem selected_cut_25433 : selected 8 ⟨643546, by decide⟩
    (prefixPartial 13 350234) = some ⟨13, 2, 0, 643546, 350234, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_350234_643546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350234 ⟨643546, by decide⟩ :=
  accepted_of_selected 13 350234 ⟨643546, by decide⟩ ⟨13, 2, 0, 643546, 350234, 1437, 16384⟩
    (by decide) selected_cut_25433

theorem selected_cut_25434 : selected 8 ⟨643566, by decide⟩
    (prefixPartial 13 350235) = some ⟨13, 2, 0, 643566, 350235, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_350235_643566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350235 ⟨643566, by decide⟩ :=
  accepted_of_selected 13 350235 ⟨643566, by decide⟩ ⟨13, 2, 0, 643566, 350235, 1241, 16384⟩
    (by decide) selected_cut_25434

theorem unmarked_context_12_87558_643567 : frontier 9 ⟨643567, by decide⟩
    (prefixCache 12 87558) (prefixPartial 12 87558) = false := by
  decide +kernel

theorem node_context_12_87558_643567 : EJMOriginalGlobalDAGData.nodes 9 ⟨643567, by decide⟩ =
    .split (coordinate 12) (![⟨643477, by decide⟩,⟨643527, by decide⟩,⟨643546, by decide⟩,⟨643566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87558_643567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87558 ⟨643567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87558
    ⟨643567, by decide⟩ (by decide) (![⟨643477, by decide⟩,⟨643527, by decide⟩,⟨643546, by decide⟩,⟨643566, by decide⟩]) unmarked_context_12_87558_643567 node_context_12_87558_643567
  intro a
  fin_cases a
  · exact context_13_350232_643477
  · exact context_13_350233_643527
  · exact context_13_350234_643546
  · exact context_13_350235_643566

theorem selected_cut_25435 : selected 8 ⟨643625, by decide⟩
    (prefixPartial 13 350236) = some ⟨13, 2, 0, 643625, 350236, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_350236_643625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350236 ⟨643625, by decide⟩ :=
  accepted_of_selected 13 350236 ⟨643625, by decide⟩ ⟨13, 2, 0, 643625, 350236, 3041, 16384⟩
    (by decide) selected_cut_25435

theorem selected_cut_25436 : selected 8 ⟨643693, by decide⟩
    (prefixPartial 13 350237) = some ⟨13, 2, 0, 643693, 350237, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_350237_643693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350237 ⟨643693, by decide⟩ :=
  accepted_of_selected 13 350237 ⟨643693, by decide⟩ ⟨13, 2, 0, 643693, 350237, 2893, 16384⟩
    (by decide) selected_cut_25436

theorem selected_cut_25437 : selected 8 ⟨643724, by decide⟩
    (prefixPartial 13 350238) = some ⟨13, 2, 0, 643724, 350238, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_350238_643724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350238 ⟨643724, by decide⟩ :=
  accepted_of_selected 13 350238 ⟨643724, by decide⟩ ⟨13, 2, 0, 643724, 350238, 1641, 16384⟩
    (by decide) selected_cut_25437

theorem selected_cut_25438 : selected 8 ⟨643732, by decide⟩
    (prefixPartial 13 350239) = some ⟨13, 2, 0, 643732, 350239, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_350239_643732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350239 ⟨643732, by decide⟩ :=
  accepted_of_selected 13 350239 ⟨643732, by decide⟩ ⟨13, 2, 0, 643732, 350239, 1017, 16384⟩
    (by decide) selected_cut_25438

theorem unmarked_context_12_87559_643733 : frontier 9 ⟨643733, by decide⟩
    (prefixCache 12 87559) (prefixPartial 12 87559) = false := by
  decide +kernel

theorem node_context_12_87559_643733 : EJMOriginalGlobalDAGData.nodes 9 ⟨643733, by decide⟩ =
    .split (coordinate 12) (![⟨643625, by decide⟩,⟨643693, by decide⟩,⟨643724, by decide⟩,⟨643732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87559_643733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87559 ⟨643733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87559
    ⟨643733, by decide⟩ (by decide) (![⟨643625, by decide⟩,⟨643693, by decide⟩,⟨643724, by decide⟩,⟨643732, by decide⟩]) unmarked_context_12_87559_643733 node_context_12_87559_643733
  intro a
  fin_cases a
  · exact context_13_350236_643625
  · exact context_13_350237_643693
  · exact context_13_350238_643724
  · exact context_13_350239_643732

theorem unmarked_context_11_21889_643734 : frontier 10 ⟨643734, by decide⟩
    (prefixCache 11 21889) (prefixPartial 11 21889) = false := by
  decide +kernel

theorem node_context_11_21889_643734 : EJMOriginalGlobalDAGData.nodes 10 ⟨643734, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨643425, by decide⟩,⟨643567, by decide⟩,⟨643733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21889_643734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21889 ⟨643734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21889
    ⟨643734, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨643425, by decide⟩,⟨643567, by decide⟩,⟨643733, by decide⟩]) unmarked_context_11_21889_643734 node_context_11_21889_643734
  intro a
  fin_cases a
  · exact context_12_87556_895
  · exact context_12_87557_643425
  · exact context_12_87558_643567
  · exact context_12_87559_643733

theorem selected_cut_25439 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87560) = some ⟨12, 1, 0, 895, 87560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87560_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87560 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87560 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87560, 1, 65536⟩
    (by decide) selected_cut_25439

theorem selected_cut_25440 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87561) = some ⟨12, 1, 0, 895, 87561, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87561_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87561 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87561 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87561, 1, 65536⟩
    (by decide) selected_cut_25440

theorem selected_cut_25441 : selected 7 ⟨643753, by decide⟩
    (prefixPartial 14 1400992) = some ⟨14, 2, 0, 643753, 1400992, 469, 4096⟩ := by
  decide +kernel

theorem context_14_1400992_643753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1400992 ⟨643753, by decide⟩ :=
  accepted_of_selected 14 1400992 ⟨643753, by decide⟩ ⟨14, 2, 0, 643753, 1400992, 469, 4096⟩
    (by decide) selected_cut_25441

theorem selected_cut_25442 : selected 7 ⟨643785, by decide⟩
    (prefixPartial 14 1400993) = some ⟨14, 2, 0, 643785, 1400993, 1597, 4096⟩ := by
  decide +kernel

theorem context_14_1400993_643785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1400993 ⟨643785, by decide⟩ :=
  accepted_of_selected 14 1400993 ⟨643785, by decide⟩ ⟨14, 2, 0, 643785, 1400993, 1597, 4096⟩
    (by decide) selected_cut_25442

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
