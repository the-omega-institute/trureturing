/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover001
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00194 : selected 8 ⟨11323, by decide⟩
    (prefixPartial 13 1202) = some ⟨13, 2, 0, 11323, 1202, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_1202_11323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202 ⟨11323, by decide⟩ :=
  accepted_of_selected 13 1202 ⟨11323, by decide⟩ ⟨13, 2, 0, 11323, 1202, 2361, 16384⟩
    (by decide) selected_cut_00194

theorem selected_cut_00195 : selected 8 ⟨11354, by decide⟩
    (prefixPartial 13 1203) = some ⟨13, 2, 0, 11354, 1203, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_1203_11354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203 ⟨11354, by decide⟩ :=
  accepted_of_selected 13 1203 ⟨11354, by decide⟩ ⟨13, 2, 0, 11354, 1203, 1189, 16384⟩
    (by decide) selected_cut_00195

theorem unmarked_context_12_300_11355 : frontier 9 ⟨11355, by decide⟩
    (prefixCache 12 300) (prefixPartial 12 300) = false := by
  decide +kernel

theorem node_context_12_300_11355 : EJMOriginalGlobalDAGData.nodes 9 ⟨11355, by decide⟩ =
    .split (coordinate 12) (![⟨11156, by decide⟩,⟨11251, by decide⟩,⟨11323, by decide⟩,⟨11354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300_11355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300 ⟨11355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300
    ⟨11355, by decide⟩ (by decide) (![⟨11156, by decide⟩,⟨11251, by decide⟩,⟨11323, by decide⟩,⟨11354, by decide⟩]) unmarked_context_12_300_11355 node_context_12_300_11355
  intro a
  fin_cases a
  · exact context_13_1200_11156
  · exact context_13_1201_11251
  · exact context_13_1202_11323
  · exact context_13_1203_11354

theorem selected_cut_00196 : selected 8 ⟨11368, by decide⟩
    (prefixPartial 13 1204) = some ⟨13, 2, 0, 11368, 1204, 481, 16384⟩ := by
  decide +kernel

theorem context_13_1204_11368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204 ⟨11368, by decide⟩ :=
  accepted_of_selected 13 1204 ⟨11368, by decide⟩ ⟨13, 2, 0, 11368, 1204, 481, 16384⟩
    (by decide) selected_cut_00196

theorem selected_cut_00197 : selected 8 ⟨11418, by decide⟩
    (prefixPartial 13 1205) = some ⟨13, 2, 0, 11418, 1205, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_1205_11418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1205 ⟨11418, by decide⟩ :=
  accepted_of_selected 13 1205 ⟨11418, by decide⟩ ⟨13, 2, 0, 11418, 1205, 2605, 16384⟩
    (by decide) selected_cut_00197

theorem selected_cut_00198 : selected 8 ⟨11448, by decide⟩
    (prefixPartial 13 1206) = some ⟨13, 2, 0, 11448, 1206, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_1206_11448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206 ⟨11448, by decide⟩ :=
  accepted_of_selected 13 1206 ⟨11448, by decide⟩ ⟨13, 2, 0, 11448, 1206, 1825, 16384⟩
    (by decide) selected_cut_00198

theorem selected_cut_00199 : selected 8 ⟨11468, by decide⟩
    (prefixPartial 13 1207) = some ⟨13, 2, 0, 11468, 1207, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_1207_11468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207 ⟨11468, by decide⟩ :=
  accepted_of_selected 13 1207 ⟨11468, by decide⟩ ⟨13, 2, 0, 11468, 1207, 1073, 16384⟩
    (by decide) selected_cut_00199

theorem unmarked_context_12_301_11469 : frontier 9 ⟨11469, by decide⟩
    (prefixCache 12 301) (prefixPartial 12 301) = false := by
  decide +kernel

theorem node_context_12_301_11469 : EJMOriginalGlobalDAGData.nodes 9 ⟨11469, by decide⟩ =
    .split (coordinate 12) (![⟨11368, by decide⟩,⟨11418, by decide⟩,⟨11448, by decide⟩,⟨11468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301_11469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301 ⟨11469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301
    ⟨11469, by decide⟩ (by decide) (![⟨11368, by decide⟩,⟨11418, by decide⟩,⟨11448, by decide⟩,⟨11468, by decide⟩]) unmarked_context_12_301_11469 node_context_12_301_11469
  intro a
  fin_cases a
  · exact context_13_1204_11368
  · exact context_13_1205_11418
  · exact context_13_1206_11448
  · exact context_13_1207_11468

theorem selected_cut_00200 : selected 8 ⟨11487, by decide⟩
    (prefixPartial 13 1208) = some ⟨13, 2, 0, 11487, 1208, 373, 16384⟩ := by
  decide +kernel

theorem context_13_1208_11487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208 ⟨11487, by decide⟩ :=
  accepted_of_selected 13 1208 ⟨11487, by decide⟩ ⟨13, 2, 0, 11487, 1208, 373, 16384⟩
    (by decide) selected_cut_00200

theorem selected_cut_00201 : selected 8 ⟨11552, by decide⟩
    (prefixPartial 13 1209) = some ⟨13, 2, 0, 11552, 1209, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_1209_11552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1209 ⟨11552, by decide⟩ :=
  accepted_of_selected 13 1209 ⟨11552, by decide⟩ ⟨13, 2, 0, 11552, 1209, 3457, 16384⟩
    (by decide) selected_cut_00201

theorem selected_cut_00202 : selected 8 ⟨11579, by decide⟩
    (prefixPartial 13 1210) = some ⟨13, 2, 0, 11579, 1210, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_1210_11579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210 ⟨11579, by decide⟩ :=
  accepted_of_selected 13 1210 ⟨11579, by decide⟩ ⟨13, 2, 0, 11579, 1210, 2017, 16384⟩
    (by decide) selected_cut_00202

theorem selected_cut_00203 : selected 8 ⟨11596, by decide⟩
    (prefixPartial 13 1211) = some ⟨13, 2, 0, 11596, 1211, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_1211_11596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211 ⟨11596, by decide⟩ :=
  accepted_of_selected 13 1211 ⟨11596, by decide⟩ ⟨13, 2, 0, 11596, 1211, 1121, 16384⟩
    (by decide) selected_cut_00203

theorem unmarked_context_12_302_11597 : frontier 9 ⟨11597, by decide⟩
    (prefixCache 12 302) (prefixPartial 12 302) = false := by
  decide +kernel

theorem node_context_12_302_11597 : EJMOriginalGlobalDAGData.nodes 9 ⟨11597, by decide⟩ =
    .split (coordinate 12) (![⟨11487, by decide⟩,⟨11552, by decide⟩,⟨11579, by decide⟩,⟨11596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302_11597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302 ⟨11597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302
    ⟨11597, by decide⟩ (by decide) (![⟨11487, by decide⟩,⟨11552, by decide⟩,⟨11579, by decide⟩,⟨11596, by decide⟩]) unmarked_context_12_302_11597 node_context_12_302_11597
  intro a
  fin_cases a
  · exact context_13_1208_11487
  · exact context_13_1209_11552
  · exact context_13_1210_11579
  · exact context_13_1211_11596

theorem selected_cut_00204 : selected 8 ⟨11605, by decide⟩
    (prefixPartial 13 1212) = some ⟨13, 2, 0, 11605, 1212, 145, 16384⟩ := by
  decide +kernel

theorem context_13_1212_11605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1212 ⟨11605, by decide⟩ :=
  accepted_of_selected 13 1212 ⟨11605, by decide⟩ ⟨13, 2, 0, 11605, 1212, 145, 16384⟩
    (by decide) selected_cut_00204

theorem selected_cut_00205 : selected 8 ⟨11645, by decide⟩
    (prefixPartial 13 1213) = some ⟨13, 2, 0, 11645, 1213, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_1213_11645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1213 ⟨11645, by decide⟩ :=
  accepted_of_selected 13 1213 ⟨11645, by decide⟩ ⟨13, 2, 0, 11645, 1213, 2813, 16384⟩
    (by decide) selected_cut_00205

theorem selected_cut_00206 : selected 8 ⟨11668, by decide⟩
    (prefixPartial 13 1214) = some ⟨13, 2, 0, 11668, 1214, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_1214_11668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1214 ⟨11668, by decide⟩ :=
  accepted_of_selected 13 1214 ⟨11668, by decide⟩ ⟨13, 2, 0, 11668, 1214, 1569, 16384⟩
    (by decide) selected_cut_00206

theorem selected_cut_00207 : selected 8 ⟨11682, by decide⟩
    (prefixPartial 13 1215) = some ⟨13, 2, 0, 11682, 1215, 925, 16384⟩ := by
  decide +kernel

theorem context_13_1215_11682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1215 ⟨11682, by decide⟩ :=
  accepted_of_selected 13 1215 ⟨11682, by decide⟩ ⟨13, 2, 0, 11682, 1215, 925, 16384⟩
    (by decide) selected_cut_00207

theorem unmarked_context_12_303_11683 : frontier 9 ⟨11683, by decide⟩
    (prefixCache 12 303) (prefixPartial 12 303) = false := by
  decide +kernel

theorem node_context_12_303_11683 : EJMOriginalGlobalDAGData.nodes 9 ⟨11683, by decide⟩ =
    .split (coordinate 12) (![⟨11605, by decide⟩,⟨11645, by decide⟩,⟨11668, by decide⟩,⟨11682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_303_11683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 303 ⟨11683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 303
    ⟨11683, by decide⟩ (by decide) (![⟨11605, by decide⟩,⟨11645, by decide⟩,⟨11668, by decide⟩,⟨11682, by decide⟩]) unmarked_context_12_303_11683 node_context_12_303_11683
  intro a
  fin_cases a
  · exact context_13_1212_11605
  · exact context_13_1213_11645
  · exact context_13_1214_11668
  · exact context_13_1215_11682

theorem unmarked_context_11_75_11684 : frontier 10 ⟨11684, by decide⟩
    (prefixCache 11 75) (prefixPartial 11 75) = false := by
  decide +kernel

theorem node_context_11_75_11684 : EJMOriginalGlobalDAGData.nodes 10 ⟨11684, by decide⟩ =
    .split (coordinate 11) (![⟨11355, by decide⟩,⟨11469, by decide⟩,⟨11597, by decide⟩,⟨11683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75_11684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75 ⟨11684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75
    ⟨11684, by decide⟩ (by decide) (![⟨11355, by decide⟩,⟨11469, by decide⟩,⟨11597, by decide⟩,⟨11683, by decide⟩]) unmarked_context_11_75_11684 node_context_11_75_11684
  intro a
  fin_cases a
  · exact context_12_300_11355
  · exact context_12_301_11469
  · exact context_12_302_11597
  · exact context_12_303_11683

theorem unmarked_context_10_18_11685 : frontier 11 ⟨11685, by decide⟩
    (prefixCache 10 18) (prefixPartial 10 18) = false := by
  decide +kernel

theorem node_context_10_18_11685 : EJMOriginalGlobalDAGData.nodes 11 ⟨11685, by decide⟩ =
    .split (coordinate 10) (![⟨9579, by decide⟩,⟨10498, by decide⟩,⟨11126, by decide⟩,⟨11684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18_11685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18 ⟨11685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18
    ⟨11685, by decide⟩ (by decide) (![⟨9579, by decide⟩,⟨10498, by decide⟩,⟨11126, by decide⟩,⟨11684, by decide⟩]) unmarked_context_10_18_11685 node_context_10_18_11685
  intro a
  fin_cases a
  · exact context_11_72_9579
  · exact context_11_73_10498
  · exact context_11_74_11126
  · exact context_11_75_11684

theorem selected_cut_00208 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 19) = some ⟨10, 1, 0, 3440, 19, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 19 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 19, 1, 1048576⟩
    (by decide) selected_cut_00208

theorem unmarked_context_9_4_11686 : frontier 12 ⟨11686, by decide⟩
    (prefixCache 9 4) (prefixPartial 9 4) = false := by
  decide +kernel

theorem node_context_9_4_11686 : EJMOriginalGlobalDAGData.nodes 12 ⟨11686, by decide⟩ =
    .split (coordinate 9) (![⟨6968, by decide⟩,⟨8982, by decide⟩,⟨11685, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4_11686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4 ⟨11686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4
    ⟨11686, by decide⟩ (by decide) (![⟨6968, by decide⟩,⟨8982, by decide⟩,⟨11685, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4_11686 node_context_9_4_11686
  intro a
  fin_cases a
  · exact context_10_16_6968
  · exact context_10_17_8982
  · exact context_10_18_11685
  · exact context_10_19_3440

theorem selected_cut_00209 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 20) = some ⟨10, 1, 0, 3442, 20, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 20 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 20, 1, 1048576⟩
    (by decide) selected_cut_00209

theorem selected_cut_00210 : selected 9 ⟨11736, by decide⟩
    (prefixPartial 12 336) = some ⟨12, 2, 0, 11736, 336, 917, 65536⟩ := by
  decide +kernel

theorem context_12_336_11736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336 ⟨11736, by decide⟩ :=
  accepted_of_selected 12 336 ⟨11736, by decide⟩ ⟨12, 2, 0, 11736, 336, 917, 65536⟩
    (by decide) selected_cut_00210

theorem selected_cut_00211 : selected 9 ⟨11794, by decide⟩
    (prefixPartial 12 337) = some ⟨12, 2, 0, 11794, 337, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_337_11794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337 ⟨11794, by decide⟩ :=
  accepted_of_selected 12 337 ⟨11794, by decide⟩ ⟨12, 2, 0, 11794, 337, 1609, 65536⟩
    (by decide) selected_cut_00211

theorem selected_cut_00212 : selected 9 ⟨11911, by decide⟩
    (prefixPartial 12 338) = some ⟨12, 2, 0, 11911, 338, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_338_11911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338 ⟨11911, by decide⟩ :=
  accepted_of_selected 12 338 ⟨11911, by decide⟩ ⟨12, 2, 0, 11911, 338, 3453, 65536⟩
    (by decide) selected_cut_00212

theorem selected_cut_00213 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 339) = some ⟨12, 1, 0, 893, 339, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339 ⟨893, by decide⟩ :=
  accepted_of_selected 12 339 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 339, 1, 65536⟩
    (by decide) selected_cut_00213

theorem unmarked_context_11_84_11912 : frontier 10 ⟨11912, by decide⟩
    (prefixCache 11 84) (prefixPartial 11 84) = false := by
  decide +kernel

theorem node_context_11_84_11912 : EJMOriginalGlobalDAGData.nodes 10 ⟨11912, by decide⟩ =
    .split (coordinate 11) (![⟨11736, by decide⟩,⟨11794, by decide⟩,⟨11911, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84_11912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84 ⟨11912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84
    ⟨11912, by decide⟩ (by decide) (![⟨11736, by decide⟩,⟨11794, by decide⟩,⟨11911, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_84_11912 node_context_11_84_11912
  intro a
  fin_cases a
  · exact context_12_336_11736
  · exact context_12_337_11794
  · exact context_12_338_11911
  · exact context_12_339_893

theorem selected_cut_00214 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 340) = some ⟨12, 1, 0, 895, 340, 1, 65536⟩ := by
  decide +kernel

theorem context_12_340_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 340 ⟨895, by decide⟩ :=
  accepted_of_selected 12 340 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 340, 1, 65536⟩
    (by decide) selected_cut_00214

theorem selected_cut_00215 : selected 9 ⟨11989, by decide⟩
    (prefixPartial 12 341) = some ⟨12, 2, 0, 11989, 341, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_341_11989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 341 ⟨11989, by decide⟩ :=
  accepted_of_selected 12 341 ⟨11989, by decide⟩ ⟨12, 2, 0, 11989, 341, 1973, 65536⟩
    (by decide) selected_cut_00215

theorem selected_cut_00216 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 1368) = some ⟨13, 1, 0, 3444, 1368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 1368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 1368, 1, 16384⟩
    (by decide) selected_cut_00216

theorem selected_cut_00217 : selected 8 ⟨12045, by decide⟩
    (prefixPartial 13 1369) = some ⟨13, 2, 0, 12045, 1369, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_1369_12045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1369 ⟨12045, by decide⟩ :=
  accepted_of_selected 13 1369 ⟨12045, by decide⟩ ⟨13, 2, 0, 12045, 1369, 1809, 16384⟩
    (by decide) selected_cut_00217

theorem selected_cut_00218 : selected 8 ⟨12092, by decide⟩
    (prefixPartial 13 1370) = some ⟨13, 2, 0, 12092, 1370, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_1370_12092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1370 ⟨12092, by decide⟩ :=
  accepted_of_selected 13 1370 ⟨12092, by decide⟩ ⟨13, 2, 0, 12092, 1370, 1765, 16384⟩
    (by decide) selected_cut_00218

theorem selected_cut_00219 : selected 8 ⟨12106, by decide⟩
    (prefixPartial 13 1371) = some ⟨13, 2, 0, 12106, 1371, 985, 16384⟩ := by
  decide +kernel

theorem context_13_1371_12106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1371 ⟨12106, by decide⟩ :=
  accepted_of_selected 13 1371 ⟨12106, by decide⟩ ⟨13, 2, 0, 12106, 1371, 985, 16384⟩
    (by decide) selected_cut_00219

theorem unmarked_context_12_342_12107 : frontier 9 ⟨12107, by decide⟩
    (prefixCache 12 342) (prefixPartial 12 342) = false := by
  decide +kernel

theorem node_context_12_342_12107 : EJMOriginalGlobalDAGData.nodes 9 ⟨12107, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨12045, by decide⟩,⟨12092, by decide⟩,⟨12106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_342_12107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 342 ⟨12107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 342
    ⟨12107, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨12045, by decide⟩,⟨12092, by decide⟩,⟨12106, by decide⟩]) unmarked_context_12_342_12107 node_context_12_342_12107
  intro a
  fin_cases a
  · exact context_13_1368_3444
  · exact context_13_1369_12045
  · exact context_13_1370_12092
  · exact context_13_1371_12106

theorem selected_cut_00220 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 343) = some ⟨12, 1, 0, 893, 343, 1, 65536⟩ := by
  decide +kernel

theorem context_12_343_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 343 ⟨893, by decide⟩ :=
  accepted_of_selected 12 343 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 343, 1, 65536⟩
    (by decide) selected_cut_00220

theorem unmarked_context_11_85_12108 : frontier 10 ⟨12108, by decide⟩
    (prefixCache 11 85) (prefixPartial 11 85) = false := by
  decide +kernel

theorem node_context_11_85_12108 : EJMOriginalGlobalDAGData.nodes 10 ⟨12108, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨11989, by decide⟩,⟨12107, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_85_12108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 85 ⟨12108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 85
    ⟨12108, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨11989, by decide⟩,⟨12107, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_85_12108 node_context_11_85_12108
  intro a
  fin_cases a
  · exact context_12_340_895
  · exact context_12_341_11989
  · exact context_12_342_12107
  · exact context_12_343_893

theorem selected_cut_00221 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 344) = some ⟨12, 1, 0, 895, 344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_344_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 344 ⟨895, by decide⟩ :=
  accepted_of_selected 12 344 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 344, 1, 65536⟩
    (by decide) selected_cut_00221

theorem selected_cut_00222 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 345) = some ⟨12, 1, 0, 895, 345, 1, 65536⟩ := by
  decide +kernel

theorem context_12_345_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 345 ⟨895, by decide⟩ :=
  accepted_of_selected 12 345 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 345, 1, 65536⟩
    (by decide) selected_cut_00222

theorem selected_cut_00223 : selected 9 ⟨12189, by decide⟩
    (prefixPartial 12 346) = some ⟨12, 2, 0, 12189, 346, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_346_12189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 346 ⟨12189, by decide⟩ :=
  accepted_of_selected 12 346 ⟨12189, by decide⟩ ⟨12, 2, 0, 12189, 346, 2597, 65536⟩
    (by decide) selected_cut_00223

theorem selected_cut_00224 : selected 9 ⟨12303, by decide⟩
    (prefixPartial 12 347) = some ⟨12, 2, 0, 12303, 347, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_347_12303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 347 ⟨12303, by decide⟩ :=
  accepted_of_selected 12 347 ⟨12303, by decide⟩ ⟨12, 2, 0, 12303, 347, 2953, 65536⟩
    (by decide) selected_cut_00224

theorem unmarked_context_11_86_12304 : frontier 10 ⟨12304, by decide⟩
    (prefixCache 11 86) (prefixPartial 11 86) = false := by
  decide +kernel

theorem node_context_11_86_12304 : EJMOriginalGlobalDAGData.nodes 10 ⟨12304, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨12189, by decide⟩,⟨12303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_86_12304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 86 ⟨12304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 86
    ⟨12304, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨12189, by decide⟩,⟨12303, by decide⟩]) unmarked_context_11_86_12304 node_context_11_86_12304
  intro a
  fin_cases a
  · exact context_12_344_895
  · exact context_12_345_895
  · exact context_12_346_12189
  · exact context_12_347_12303

theorem selected_cut_00225 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 87) = some ⟨11, 1, 0, 1736, 87, 1, 262144⟩ := by
  decide +kernel

theorem context_11_87_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 87 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 87, 1, 262144⟩
    (by decide) selected_cut_00225

theorem unmarked_context_10_21_12305 : frontier 11 ⟨12305, by decide⟩
    (prefixCache 10 21) (prefixPartial 10 21) = false := by
  decide +kernel

theorem node_context_10_21_12305 : EJMOriginalGlobalDAGData.nodes 11 ⟨12305, by decide⟩ =
    .split (coordinate 10) (![⟨11912, by decide⟩,⟨12108, by decide⟩,⟨12304, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21_12305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21 ⟨12305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21
    ⟨12305, by decide⟩ (by decide) (![⟨11912, by decide⟩,⟨12108, by decide⟩,⟨12304, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_21_12305 node_context_10_21_12305
  intro a
  fin_cases a
  · exact context_11_84_11912
  · exact context_11_85_12108
  · exact context_11_86_12304
  · exact context_11_87_1736

theorem selected_cut_00226 : selected 9 ⟨12385, by decide⟩
    (prefixPartial 12 352) = some ⟨12, 2, 0, 12385, 352, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_352_12385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352 ⟨12385, by decide⟩ :=
  accepted_of_selected 12 352 ⟨12385, by decide⟩ ⟨12, 2, 0, 12385, 352, 2621, 65536⟩
    (by decide) selected_cut_00226

theorem selected_cut_00227 : selected 9 ⟨12440, by decide⟩
    (prefixPartial 12 353) = some ⟨12, 2, 0, 12440, 353, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_353_12440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353 ⟨12440, by decide⟩ :=
  accepted_of_selected 12 353 ⟨12440, by decide⟩ ⟨12, 2, 0, 12440, 353, 2701, 65536⟩
    (by decide) selected_cut_00227

theorem selected_cut_00228 : selected 9 ⟨12531, by decide⟩
    (prefixPartial 12 354) = some ⟨12, 2, 0, 12531, 354, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_354_12531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354 ⟨12531, by decide⟩ :=
  accepted_of_selected 12 354 ⟨12531, by decide⟩ ⟨12, 2, 0, 12531, 354, 3469, 65536⟩
    (by decide) selected_cut_00228

theorem selected_cut_00229 : selected 9 ⟨12595, by decide⟩
    (prefixPartial 12 355) = some ⟨12, 2, 0, 12595, 355, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_355_12595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355 ⟨12595, by decide⟩ :=
  accepted_of_selected 12 355 ⟨12595, by decide⟩ ⟨12, 2, 0, 12595, 355, 3041, 65536⟩
    (by decide) selected_cut_00229

theorem unmarked_context_11_88_12596 : frontier 10 ⟨12596, by decide⟩
    (prefixCache 11 88) (prefixPartial 11 88) = false := by
  decide +kernel

theorem node_context_11_88_12596 : EJMOriginalGlobalDAGData.nodes 10 ⟨12596, by decide⟩ =
    .split (coordinate 11) (![⟨12385, by decide⟩,⟨12440, by decide⟩,⟨12531, by decide⟩,⟨12595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88_12596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88 ⟨12596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88
    ⟨12596, by decide⟩ (by decide) (![⟨12385, by decide⟩,⟨12440, by decide⟩,⟨12531, by decide⟩,⟨12595, by decide⟩]) unmarked_context_11_88_12596 node_context_11_88_12596
  intro a
  fin_cases a
  · exact context_12_352_12385
  · exact context_12_353_12440
  · exact context_12_354_12531
  · exact context_12_355_12595

theorem selected_cut_00230 : selected 9 ⟨12688, by decide⟩
    (prefixPartial 12 356) = some ⟨12, 2, 0, 12688, 356, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_356_12688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356 ⟨12688, by decide⟩ :=
  accepted_of_selected 12 356 ⟨12688, by decide⟩ ⟨12, 2, 0, 12688, 356, 3041, 65536⟩
    (by decide) selected_cut_00230

theorem selected_cut_00231 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 1428) = some ⟨13, 1, 0, 3444, 1428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 1428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 1428, 1, 16384⟩
    (by decide) selected_cut_00231

theorem selected_cut_00232 : selected 8 ⟨12748, by decide⟩
    (prefixPartial 13 1429) = some ⟨13, 2, 0, 12748, 1429, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_1429_12748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1429 ⟨12748, by decide⟩ :=
  accepted_of_selected 13 1429 ⟨12748, by decide⟩ ⟨13, 2, 0, 12748, 1429, 2001, 16384⟩
    (by decide) selected_cut_00232

theorem selected_cut_00233 : selected 8 ⟨12821, by decide⟩
    (prefixPartial 13 1430) = some ⟨13, 2, 0, 12821, 1430, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_1430_12821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1430 ⟨12821, by decide⟩ :=
  accepted_of_selected 13 1430 ⟨12821, by decide⟩ ⟨13, 2, 0, 12821, 1430, 2221, 16384⟩
    (by decide) selected_cut_00233

theorem selected_cut_00234 : selected 8 ⟨12870, by decide⟩
    (prefixPartial 13 1431) = some ⟨13, 2, 0, 12870, 1431, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_1431_12870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1431 ⟨12870, by decide⟩ :=
  accepted_of_selected 13 1431 ⟨12870, by decide⟩ ⟨13, 2, 0, 12870, 1431, 1197, 16384⟩
    (by decide) selected_cut_00234

theorem unmarked_context_12_357_12871 : frontier 9 ⟨12871, by decide⟩
    (prefixCache 12 357) (prefixPartial 12 357) = false := by
  decide +kernel

theorem node_context_12_357_12871 : EJMOriginalGlobalDAGData.nodes 9 ⟨12871, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨12748, by decide⟩,⟨12821, by decide⟩,⟨12870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_357_12871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 357 ⟨12871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 357
    ⟨12871, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨12748, by decide⟩,⟨12821, by decide⟩,⟨12870, by decide⟩]) unmarked_context_12_357_12871 node_context_12_357_12871
  intro a
  fin_cases a
  · exact context_13_1428_3444
  · exact context_13_1429_12748
  · exact context_13_1430_12821
  · exact context_13_1431_12870

theorem selected_cut_00235 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 1432) = some ⟨13, 1, 0, 3444, 1432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 1432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 1432, 1, 16384⟩
    (by decide) selected_cut_00235

theorem selected_cut_00236 : selected 8 ⟨12916, by decide⟩
    (prefixPartial 13 1433) = some ⟨13, 2, 0, 12916, 1433, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1433_12916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1433 ⟨12916, by decide⟩ :=
  accepted_of_selected 13 1433 ⟨12916, by decide⟩ ⟨13, 2, 0, 12916, 1433, 1321, 16384⟩
    (by decide) selected_cut_00236

theorem selected_cut_00237 : selected 8 ⟨12961, by decide⟩
    (prefixPartial 13 1434) = some ⟨13, 2, 0, 12961, 1434, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_1434_12961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1434 ⟨12961, by decide⟩ :=
  accepted_of_selected 13 1434 ⟨12961, by decide⟩ ⟨13, 2, 0, 12961, 1434, 1853, 16384⟩
    (by decide) selected_cut_00237

theorem selected_cut_00238 : selected 8 ⟨12984, by decide⟩
    (prefixPartial 13 1435) = some ⟨13, 2, 0, 12984, 1435, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_1435_12984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1435 ⟨12984, by decide⟩ :=
  accepted_of_selected 13 1435 ⟨12984, by decide⟩ ⟨13, 2, 0, 12984, 1435, 1013, 16384⟩
    (by decide) selected_cut_00238

theorem unmarked_context_12_358_12985 : frontier 9 ⟨12985, by decide⟩
    (prefixCache 12 358) (prefixPartial 12 358) = false := by
  decide +kernel

theorem node_context_12_358_12985 : EJMOriginalGlobalDAGData.nodes 9 ⟨12985, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨12916, by decide⟩,⟨12961, by decide⟩,⟨12984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_358_12985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 358 ⟨12985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 358
    ⟨12985, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨12916, by decide⟩,⟨12961, by decide⟩,⟨12984, by decide⟩]) unmarked_context_12_358_12985 node_context_12_358_12985
  intro a
  fin_cases a
  · exact context_13_1432_3444
  · exact context_13_1433_12916
  · exact context_13_1434_12961
  · exact context_13_1435_12984

theorem selected_cut_00239 : selected 9 ⟨13077, by decide⟩
    (prefixPartial 12 359) = some ⟨12, 2, 0, 13077, 359, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_359_13077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 359 ⟨13077, by decide⟩ :=
  accepted_of_selected 12 359 ⟨13077, by decide⟩ ⟨12, 2, 0, 13077, 359, 3653, 65536⟩
    (by decide) selected_cut_00239

theorem unmarked_context_11_89_13078 : frontier 10 ⟨13078, by decide⟩
    (prefixCache 11 89) (prefixPartial 11 89) = false := by
  decide +kernel

theorem node_context_11_89_13078 : EJMOriginalGlobalDAGData.nodes 10 ⟨13078, by decide⟩ =
    .split (coordinate 11) (![⟨12688, by decide⟩,⟨12871, by decide⟩,⟨12985, by decide⟩,⟨13077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89_13078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89 ⟨13078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89
    ⟨13078, by decide⟩ (by decide) (![⟨12688, by decide⟩,⟨12871, by decide⟩,⟨12985, by decide⟩,⟨13077, by decide⟩]) unmarked_context_11_89_13078 node_context_11_89_13078
  intro a
  fin_cases a
  · exact context_12_356_12688
  · exact context_12_357_12871
  · exact context_12_358_12985
  · exact context_12_359_13077

theorem selected_cut_00240 : selected 9 ⟨13140, by decide⟩
    (prefixPartial 12 360) = some ⟨12, 2, 0, 13140, 360, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_360_13140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 360 ⟨13140, by decide⟩ :=
  accepted_of_selected 12 360 ⟨13140, by decide⟩ ⟨12, 2, 0, 13140, 360, 2369, 65536⟩
    (by decide) selected_cut_00240

theorem selected_cut_00241 : selected 9 ⟨13202, by decide⟩
    (prefixPartial 12 361) = some ⟨12, 2, 0, 13202, 361, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_361_13202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 361 ⟨13202, by decide⟩ :=
  accepted_of_selected 12 361 ⟨13202, by decide⟩ ⟨12, 2, 0, 13202, 361, 2661, 65536⟩
    (by decide) selected_cut_00241

theorem selected_cut_00242 : selected 9 ⟨13269, by decide⟩
    (prefixPartial 12 362) = some ⟨12, 2, 0, 13269, 362, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_362_13269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 362 ⟨13269, by decide⟩ :=
  accepted_of_selected 12 362 ⟨13269, by decide⟩ ⟨12, 2, 0, 13269, 362, 2785, 65536⟩
    (by decide) selected_cut_00242

theorem selected_cut_00243 : selected 9 ⟨13347, by decide⟩
    (prefixPartial 12 363) = some ⟨12, 2, 0, 13347, 363, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_363_13347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 363 ⟨13347, by decide⟩ :=
  accepted_of_selected 12 363 ⟨13347, by decide⟩ ⟨12, 2, 0, 13347, 363, 2713, 65536⟩
    (by decide) selected_cut_00243

theorem unmarked_context_11_90_13348 : frontier 10 ⟨13348, by decide⟩
    (prefixCache 11 90) (prefixPartial 11 90) = false := by
  decide +kernel

theorem node_context_11_90_13348 : EJMOriginalGlobalDAGData.nodes 10 ⟨13348, by decide⟩ =
    .split (coordinate 11) (![⟨13140, by decide⟩,⟨13202, by decide⟩,⟨13269, by decide⟩,⟨13347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_90_13348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 90 ⟨13348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 90
    ⟨13348, by decide⟩ (by decide) (![⟨13140, by decide⟩,⟨13202, by decide⟩,⟨13269, by decide⟩,⟨13347, by decide⟩]) unmarked_context_11_90_13348 node_context_11_90_13348
  intro a
  fin_cases a
  · exact context_12_360_13140
  · exact context_12_361_13202
  · exact context_12_362_13269
  · exact context_12_363_13347

theorem selected_cut_00244 : selected 9 ⟨13411, by decide⟩
    (prefixPartial 12 364) = some ⟨12, 2, 0, 13411, 364, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_364_13411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 364 ⟨13411, by decide⟩ :=
  accepted_of_selected 12 364 ⟨13411, by decide⟩ ⟨12, 2, 0, 13411, 364, 2113, 65536⟩
    (by decide) selected_cut_00244

theorem selected_cut_00245 : selected 9 ⟨13466, by decide⟩
    (prefixPartial 12 365) = some ⟨12, 2, 0, 13466, 365, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_365_13466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 365 ⟨13466, by decide⟩ :=
  accepted_of_selected 12 365 ⟨13466, by decide⟩ ⟨12, 2, 0, 13466, 365, 2269, 65536⟩
    (by decide) selected_cut_00245

theorem selected_cut_00246 : selected 9 ⟨13546, by decide⟩
    (prefixPartial 12 366) = some ⟨12, 2, 0, 13546, 366, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_366_13546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366 ⟨13546, by decide⟩ :=
  accepted_of_selected 12 366 ⟨13546, by decide⟩ ⟨12, 2, 0, 13546, 366, 2661, 65536⟩
    (by decide) selected_cut_00246

theorem selected_cut_00247 : selected 9 ⟨13585, by decide⟩
    (prefixPartial 12 367) = some ⟨12, 2, 0, 13585, 367, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_367_13585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367 ⟨13585, by decide⟩ :=
  accepted_of_selected 12 367 ⟨13585, by decide⟩ ⟨12, 2, 0, 13585, 367, 1973, 65536⟩
    (by decide) selected_cut_00247

theorem unmarked_context_11_91_13586 : frontier 10 ⟨13586, by decide⟩
    (prefixCache 11 91) (prefixPartial 11 91) = false := by
  decide +kernel

theorem node_context_11_91_13586 : EJMOriginalGlobalDAGData.nodes 10 ⟨13586, by decide⟩ =
    .split (coordinate 11) (![⟨13411, by decide⟩,⟨13466, by decide⟩,⟨13546, by decide⟩,⟨13585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91_13586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91 ⟨13586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91
    ⟨13586, by decide⟩ (by decide) (![⟨13411, by decide⟩,⟨13466, by decide⟩,⟨13546, by decide⟩,⟨13585, by decide⟩]) unmarked_context_11_91_13586 node_context_11_91_13586
  intro a
  fin_cases a
  · exact context_12_364_13411
  · exact context_12_365_13466
  · exact context_12_366_13546
  · exact context_12_367_13585

theorem unmarked_context_10_22_13587 : frontier 11 ⟨13587, by decide⟩
    (prefixCache 10 22) (prefixPartial 10 22) = false := by
  decide +kernel

theorem node_context_10_22_13587 : EJMOriginalGlobalDAGData.nodes 11 ⟨13587, by decide⟩ =
    .split (coordinate 10) (![⟨12596, by decide⟩,⟨13078, by decide⟩,⟨13348, by decide⟩,⟨13586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22_13587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22 ⟨13587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22
    ⟨13587, by decide⟩ (by decide) (![⟨12596, by decide⟩,⟨13078, by decide⟩,⟨13348, by decide⟩,⟨13586, by decide⟩]) unmarked_context_10_22_13587 node_context_10_22_13587
  intro a
  fin_cases a
  · exact context_11_88_12596
  · exact context_11_89_13078
  · exact context_11_90_13348
  · exact context_11_91_13586

theorem selected_cut_00248 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 23) = some ⟨10, 1, 0, 3440, 23, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 23 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 23, 1, 1048576⟩
    (by decide) selected_cut_00248

theorem unmarked_context_9_5_13588 : frontier 12 ⟨13588, by decide⟩
    (prefixCache 9 5) (prefixPartial 9 5) = false := by
  decide +kernel

theorem node_context_9_5_13588 : EJMOriginalGlobalDAGData.nodes 12 ⟨13588, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨12305, by decide⟩,⟨13587, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5_13588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5 ⟨13588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5
    ⟨13588, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨12305, by decide⟩,⟨13587, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_5_13588 node_context_9_5_13588
  intro a
  fin_cases a
  · exact context_10_20_3442
  · exact context_10_21_12305
  · exact context_10_22_13587
  · exact context_10_23_3440

theorem selected_cut_00249 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 24) = some ⟨10, 1, 0, 3442, 24, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_24_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 24 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 24 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 24, 1, 1048576⟩
    (by decide) selected_cut_00249

theorem selected_cut_00250 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 25) = some ⟨10, 1, 0, 3442, 25, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 25 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 25, 1, 1048576⟩
    (by decide) selected_cut_00250

theorem selected_cut_00251 : selected 10 ⟨13747, by decide⟩
    (prefixPartial 11 104) = some ⟨11, 2, 0, 13747, 104, 3889, 262144⟩ := by
  decide +kernel

theorem context_11_104_13747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104 ⟨13747, by decide⟩ :=
  accepted_of_selected 11 104 ⟨13747, by decide⟩ ⟨11, 2, 0, 13747, 104, 3889, 262144⟩
    (by decide) selected_cut_00251

theorem selected_cut_00252 : selected 10 ⟨13964, by decide⟩
    (prefixPartial 11 105) = some ⟨11, 2, 0, 13964, 105, 3521, 262144⟩ := by
  decide +kernel

theorem context_11_105_13964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105 ⟨13964, by decide⟩ :=
  accepted_of_selected 11 105 ⟨13964, by decide⟩ ⟨11, 2, 0, 13964, 105, 3521, 262144⟩
    (by decide) selected_cut_00252

theorem selected_cut_00253 : selected 10 ⟨14050, by decide⟩
    (prefixPartial 11 106) = some ⟨11, 2, 0, 14050, 106, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_106_14050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106 ⟨14050, by decide⟩ :=
  accepted_of_selected 11 106 ⟨14050, by decide⟩ ⟨11, 2, 0, 14050, 106, 1461, 262144⟩
    (by decide) selected_cut_00253

theorem selected_cut_00254 : selected 10 ⟨14079, by decide⟩
    (prefixPartial 11 107) = some ⟨11, 2, 0, 14079, 107, 465, 262144⟩ := by
  decide +kernel

theorem context_11_107_14079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 107 ⟨14079, by decide⟩ :=
  accepted_of_selected 11 107 ⟨14079, by decide⟩ ⟨11, 2, 0, 14079, 107, 465, 262144⟩
    (by decide) selected_cut_00254

theorem unmarked_context_10_26_14080 : frontier 11 ⟨14080, by decide⟩
    (prefixCache 10 26) (prefixPartial 10 26) = false := by
  decide +kernel

theorem node_context_10_26_14080 : EJMOriginalGlobalDAGData.nodes 11 ⟨14080, by decide⟩ =
    .split (coordinate 10) (![⟨13747, by decide⟩,⟨13964, by decide⟩,⟨14050, by decide⟩,⟨14079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26_14080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26 ⟨14080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26
    ⟨14080, by decide⟩ (by decide) (![⟨13747, by decide⟩,⟨13964, by decide⟩,⟨14050, by decide⟩,⟨14079, by decide⟩]) unmarked_context_10_26_14080 node_context_10_26_14080
  intro a
  fin_cases a
  · exact context_11_104_13747
  · exact context_11_105_13964
  · exact context_11_106_14050
  · exact context_11_107_14079

theorem selected_cut_00255 : selected 11 ⟨14294, by decide⟩
    (prefixPartial 10 27) = some ⟨10, 2, 0, 14294, 27, 2921, 1048576⟩ := by
  decide +kernel

theorem context_10_27_14294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27 ⟨14294, by decide⟩ :=
  accepted_of_selected 10 27 ⟨14294, by decide⟩ ⟨10, 2, 0, 14294, 27, 2921, 1048576⟩
    (by decide) selected_cut_00255

theorem unmarked_context_9_6_14295 : frontier 12 ⟨14295, by decide⟩
    (prefixCache 9 6) (prefixPartial 9 6) = false := by
  decide +kernel

theorem node_context_9_6_14295 : EJMOriginalGlobalDAGData.nodes 12 ⟨14295, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨14080, by decide⟩,⟨14294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6_14295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6 ⟨14295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6
    ⟨14295, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨14080, by decide⟩,⟨14294, by decide⟩]) unmarked_context_9_6_14295 node_context_9_6_14295
  intro a
  fin_cases a
  · exact context_10_24_3442
  · exact context_10_25_3442
  · exact context_10_26_14080
  · exact context_10_27_14294

theorem selected_cut_00256 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 7) = some ⟨9, 1, 0, 4601, 7, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_7_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 7 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 7, 1, 4194304⟩
    (by decide) selected_cut_00256

theorem unmarked_context_8_1_14296 : frontier 13 ⟨14296, by decide⟩
    (prefixCache 8 1) (prefixPartial 8 1) = false := by
  decide +kernel

theorem node_context_8_1_14296 : EJMOriginalGlobalDAGData.nodes 13 ⟨14296, by decide⟩ =
    .split (coordinate 8) (![⟨11686, by decide⟩,⟨13588, by decide⟩,⟨14295, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1_14296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1 ⟨14296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1
    ⟨14296, by decide⟩ (by decide) (![⟨11686, by decide⟩,⟨13588, by decide⟩,⟨14295, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_1_14296 node_context_8_1_14296
  intro a
  fin_cases a
  · exact context_9_4_11686
  · exact context_9_5_13588
  · exact context_9_6_14295
  · exact context_9_7_4601

theorem selected_cut_00257 : selected 13 ⟨14297, by decide⟩
    (prefixPartial 8 2) = some ⟨8, 1, 0, 14297, 2, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_2_14297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 2 ⟨14297, by decide⟩ :=
  accepted_of_selected 8 2 ⟨14297, by decide⟩ ⟨8, 1, 0, 14297, 2, 1, 16777216⟩
    (by decide) selected_cut_00257

theorem selected_cut_00258 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 3) = some ⟨8, 1, 0, 14298, 3, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_3_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 3 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 3 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 3, 1, 16777216⟩
    (by decide) selected_cut_00258

theorem unmarked_context_7_0_14299 : frontier 14 ⟨14299, by decide⟩
    (prefixCache 7 0) (prefixPartial 7 0) = false := by
  decide +kernel

theorem node_context_7_0_14299 : EJMOriginalGlobalDAGData.nodes 14 ⟨14299, by decide⟩ =
    .split (coordinate 7) (![⟨4602, by decide⟩,⟨14296, by decide⟩,⟨14297, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_0_14299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 0 ⟨14299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 0
    ⟨14299, by decide⟩ (by decide) (![⟨4602, by decide⟩,⟨14296, by decide⟩,⟨14297, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_0_14299 node_context_7_0_14299
  intro a
  fin_cases a
  · exact context_8_0_4602
  · exact context_8_1_14296
  · exact context_8_2_14297
  · exact context_8_3_14298

theorem selected_cut_00259 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4) = some ⟨8, 1, 0, 14300, 4, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4, 1, 16777216⟩
    (by decide) selected_cut_00259

theorem selected_cut_00260 : selected 8 ⟨14393, by decide⟩
    (prefixPartial 13 5120) = some ⟨13, 2, 0, 14393, 5120, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_5120_14393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5120 ⟨14393, by decide⟩ :=
  accepted_of_selected 13 5120 ⟨14393, by decide⟩ ⟨13, 2, 0, 14393, 5120, 2377, 16384⟩
    (by decide) selected_cut_00260

theorem selected_cut_00261 : selected 8 ⟨14448, by decide⟩
    (prefixPartial 13 5121) = some ⟨13, 2, 0, 14448, 5121, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_5121_14448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5121 ⟨14448, by decide⟩ :=
  accepted_of_selected 13 5121 ⟨14448, by decide⟩ ⟨13, 2, 0, 14448, 5121, 1633, 16384⟩
    (by decide) selected_cut_00261

theorem selected_cut_00262 : selected 8 ⟨14563, by decide⟩
    (prefixPartial 13 5122) = some ⟨13, 2, 0, 14563, 5122, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_5122_14563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5122 ⟨14563, by decide⟩ :=
  accepted_of_selected 13 5122 ⟨14563, by decide⟩ ⟨13, 2, 0, 14563, 5122, 1941, 16384⟩
    (by decide) selected_cut_00262

theorem selected_cut_00263 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 5123) = some ⟨13, 1, 0, 414, 5123, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5123_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5123 ⟨414, by decide⟩ :=
  accepted_of_selected 13 5123 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 5123, 1, 16384⟩
    (by decide) selected_cut_00263

theorem unmarked_context_12_1280_14564 : frontier 9 ⟨14564, by decide⟩
    (prefixCache 12 1280) (prefixPartial 12 1280) = false := by
  decide +kernel

theorem node_context_12_1280_14564 : EJMOriginalGlobalDAGData.nodes 9 ⟨14564, by decide⟩ =
    .split (coordinate 12) (![⟨14393, by decide⟩,⟨14448, by decide⟩,⟨14563, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1280_14564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1280 ⟨14564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1280
    ⟨14564, by decide⟩ (by decide) (![⟨14393, by decide⟩,⟨14448, by decide⟩,⟨14563, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_1280_14564 node_context_12_1280_14564
  intro a
  fin_cases a
  · exact context_13_5120_14393
  · exact context_13_5121_14448
  · exact context_13_5122_14563
  · exact context_13_5123_414

theorem selected_cut_00264 : selected 8 ⟨14622, by decide⟩
    (prefixPartial 13 5124) = some ⟨13, 2, 0, 14622, 5124, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_5124_14622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5124 ⟨14622, by decide⟩ :=
  accepted_of_selected 13 5124 ⟨14622, by decide⟩ ⟨13, 2, 0, 14622, 5124, 2513, 16384⟩
    (by decide) selected_cut_00264

theorem selected_cut_00265 : selected 8 ⟨14662, by decide⟩
    (prefixPartial 13 5125) = some ⟨13, 2, 0, 14662, 5125, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_5125_14662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5125 ⟨14662, by decide⟩ :=
  accepted_of_selected 13 5125 ⟨14662, by decide⟩ ⟨13, 2, 0, 14662, 5125, 1617, 16384⟩
    (by decide) selected_cut_00265

theorem selected_cut_00266 : selected 8 ⟨14699, by decide⟩
    (prefixPartial 13 5126) = some ⟨13, 2, 0, 14699, 5126, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_5126_14699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5126 ⟨14699, by decide⟩ :=
  accepted_of_selected 13 5126 ⟨14699, by decide⟩ ⟨13, 2, 0, 14699, 5126, 2081, 16384⟩
    (by decide) selected_cut_00266

theorem selected_cut_00267 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 5127) = some ⟨13, 1, 0, 414, 5127, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5127_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5127 ⟨414, by decide⟩ :=
  accepted_of_selected 13 5127 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 5127, 1, 16384⟩
    (by decide) selected_cut_00267

theorem unmarked_context_12_1281_14700 : frontier 9 ⟨14700, by decide⟩
    (prefixCache 12 1281) (prefixPartial 12 1281) = false := by
  decide +kernel

theorem node_context_12_1281_14700 : EJMOriginalGlobalDAGData.nodes 9 ⟨14700, by decide⟩ =
    .split (coordinate 12) (![⟨14622, by decide⟩,⟨14662, by decide⟩,⟨14699, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1281_14700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1281 ⟨14700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1281
    ⟨14700, by decide⟩ (by decide) (![⟨14622, by decide⟩,⟨14662, by decide⟩,⟨14699, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_1281_14700 node_context_12_1281_14700
  intro a
  fin_cases a
  · exact context_13_5124_14622
  · exact context_13_5125_14662
  · exact context_13_5126_14699
  · exact context_13_5127_414

theorem selected_cut_00268 : selected 7 ⟨14735, by decide⟩
    (prefixPartial 14 20512) = some ⟨14, 2, 0, 14735, 20512, 1729, 4096⟩ := by
  decide +kernel

theorem context_14_20512_14735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20512 ⟨14735, by decide⟩ :=
  accepted_of_selected 14 20512 ⟨14735, by decide⟩ ⟨14, 2, 0, 14735, 20512, 1729, 4096⟩
    (by decide) selected_cut_00268

theorem selected_cut_00269 : selected 7 ⟨14757, by decide⟩
    (prefixPartial 14 20513) = some ⟨14, 2, 0, 14757, 20513, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_20513_14757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20513 ⟨14757, by decide⟩ :=
  accepted_of_selected 14 20513 ⟨14757, by decide⟩ ⟨14, 2, 0, 14757, 20513, 1357, 4096⟩
    (by decide) selected_cut_00269

theorem selected_cut_00270 : selected 7 ⟨14780, by decide⟩
    (prefixPartial 14 20514) = some ⟨14, 2, 0, 14780, 20514, 1337, 4096⟩ := by
  decide +kernel

theorem context_14_20514_14780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20514 ⟨14780, by decide⟩ :=
  accepted_of_selected 14 20514 ⟨14780, by decide⟩ ⟨14, 2, 0, 14780, 20514, 1337, 4096⟩
    (by decide) selected_cut_00270

theorem selected_cut_00271 : selected 7 ⟨14800, by decide⟩
    (prefixPartial 14 20515) = some ⟨14, 2, 0, 14800, 20515, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_20515_14800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20515 ⟨14800, by decide⟩ :=
  accepted_of_selected 14 20515 ⟨14800, by decide⟩ ⟨14, 2, 0, 14800, 20515, 1241, 4096⟩
    (by decide) selected_cut_00271

theorem unmarked_context_13_5128_14801 : frontier 8 ⟨14801, by decide⟩
    (prefixCache 13 5128) (prefixPartial 13 5128) = false := by
  decide +kernel

theorem node_context_13_5128_14801 : EJMOriginalGlobalDAGData.nodes 8 ⟨14801, by decide⟩ =
    .split (coordinate 13) (![⟨14735, by decide⟩,⟨14757, by decide⟩,⟨14780, by decide⟩,⟨14800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5128_14801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5128 ⟨14801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5128
    ⟨14801, by decide⟩ (by decide) (![⟨14735, by decide⟩,⟨14757, by decide⟩,⟨14780, by decide⟩,⟨14800, by decide⟩]) unmarked_context_13_5128_14801 node_context_13_5128_14801
  intro a
  fin_cases a
  · exact context_14_20512_14735
  · exact context_14_20513_14757
  · exact context_14_20514_14780
  · exact context_14_20515_14800

theorem selected_cut_00272 : selected 8 ⟨14855, by decide⟩
    (prefixPartial 13 5129) = some ⟨13, 2, 0, 14855, 5129, 3289, 16384⟩ := by
  decide +kernel

theorem context_13_5129_14855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5129 ⟨14855, by decide⟩ :=
  accepted_of_selected 13 5129 ⟨14855, by decide⟩ ⟨13, 2, 0, 14855, 5129, 3289, 16384⟩
    (by decide) selected_cut_00272

theorem selected_cut_00273 : selected 8 ⟨14904, by decide⟩
    (prefixPartial 13 5130) = some ⟨13, 2, 0, 14904, 5130, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_5130_14904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5130 ⟨14904, by decide⟩ :=
  accepted_of_selected 13 5130 ⟨14904, by decide⟩ ⟨13, 2, 0, 14904, 5130, 2485, 16384⟩
    (by decide) selected_cut_00273

theorem selected_cut_00274 : selected 8 ⟨14928, by decide⟩
    (prefixPartial 13 5131) = some ⟨13, 2, 0, 14928, 5131, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_5131_14928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5131 ⟨14928, by decide⟩ :=
  accepted_of_selected 13 5131 ⟨14928, by decide⟩ ⟨13, 2, 0, 14928, 5131, 1381, 16384⟩
    (by decide) selected_cut_00274

theorem unmarked_context_12_1282_14929 : frontier 9 ⟨14929, by decide⟩
    (prefixCache 12 1282) (prefixPartial 12 1282) = false := by
  decide +kernel

theorem node_context_12_1282_14929 : EJMOriginalGlobalDAGData.nodes 9 ⟨14929, by decide⟩ =
    .split (coordinate 12) (![⟨14801, by decide⟩,⟨14855, by decide⟩,⟨14904, by decide⟩,⟨14928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1282_14929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1282 ⟨14929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1282
    ⟨14929, by decide⟩ (by decide) (![⟨14801, by decide⟩,⟨14855, by decide⟩,⟨14904, by decide⟩,⟨14928, by decide⟩]) unmarked_context_12_1282_14929 node_context_12_1282_14929
  intro a
  fin_cases a
  · exact context_13_5128_14801
  · exact context_13_5129_14855
  · exact context_13_5130_14904
  · exact context_13_5131_14928

theorem selected_cut_00275 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1283) = some ⟨12, 1, 0, 893, 1283, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1283_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1283 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1283 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1283, 1, 65536⟩
    (by decide) selected_cut_00275

theorem unmarked_context_11_320_14930 : frontier 10 ⟨14930, by decide⟩
    (prefixCache 11 320) (prefixPartial 11 320) = false := by
  decide +kernel

theorem node_context_11_320_14930 : EJMOriginalGlobalDAGData.nodes 10 ⟨14930, by decide⟩ =
    .split (coordinate 11) (![⟨14564, by decide⟩,⟨14700, by decide⟩,⟨14929, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_320_14930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 320 ⟨14930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 320
    ⟨14930, by decide⟩ (by decide) (![⟨14564, by decide⟩,⟨14700, by decide⟩,⟨14929, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_320_14930 node_context_11_320_14930
  intro a
  fin_cases a
  · exact context_12_1280_14564
  · exact context_12_1281_14700
  · exact context_12_1282_14929
  · exact context_12_1283_893

theorem selected_cut_00276 : selected 8 ⟨14991, by decide⟩
    (prefixPartial 13 5136) = some ⟨13, 2, 0, 14991, 5136, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_5136_14991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5136 ⟨14991, by decide⟩ :=
  accepted_of_selected 13 5136 ⟨14991, by decide⟩ ⟨13, 2, 0, 14991, 5136, 2145, 16384⟩
    (by decide) selected_cut_00276

theorem selected_cut_00277 : selected 8 ⟨15048, by decide⟩
    (prefixPartial 13 5137) = some ⟨13, 2, 0, 15048, 5137, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_5137_15048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5137 ⟨15048, by decide⟩ :=
  accepted_of_selected 13 5137 ⟨15048, by decide⟩ ⟨13, 2, 0, 15048, 5137, 1545, 16384⟩
    (by decide) selected_cut_00277

theorem selected_cut_00278 : selected 8 ⟨15129, by decide⟩
    (prefixPartial 13 5138) = some ⟨13, 2, 0, 15129, 5138, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_5138_15129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5138 ⟨15129, by decide⟩ :=
  accepted_of_selected 13 5138 ⟨15129, by decide⟩ ⟨13, 2, 0, 15129, 5138, 1905, 16384⟩
    (by decide) selected_cut_00278

theorem selected_cut_00279 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 5139) = some ⟨13, 1, 0, 414, 5139, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5139_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5139 ⟨414, by decide⟩ :=
  accepted_of_selected 13 5139 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 5139, 1, 16384⟩
    (by decide) selected_cut_00279

theorem unmarked_context_12_1284_15130 : frontier 9 ⟨15130, by decide⟩
    (prefixCache 12 1284) (prefixPartial 12 1284) = false := by
  decide +kernel

theorem node_context_12_1284_15130 : EJMOriginalGlobalDAGData.nodes 9 ⟨15130, by decide⟩ =
    .split (coordinate 12) (![⟨14991, by decide⟩,⟨15048, by decide⟩,⟨15129, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1284_15130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1284 ⟨15130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1284
    ⟨15130, by decide⟩ (by decide) (![⟨14991, by decide⟩,⟨15048, by decide⟩,⟨15129, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_1284_15130 node_context_12_1284_15130
  intro a
  fin_cases a
  · exact context_13_5136_14991
  · exact context_13_5137_15048
  · exact context_13_5138_15129
  · exact context_13_5139_414

theorem selected_cut_00280 : selected 8 ⟨15224, by decide⟩
    (prefixPartial 13 5140) = some ⟨13, 2, 0, 15224, 5140, 3937, 16384⟩ := by
  decide +kernel

theorem context_13_5140_15224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5140 ⟨15224, by decide⟩ :=
  accepted_of_selected 13 5140 ⟨15224, by decide⟩ ⟨13, 2, 0, 15224, 5140, 3937, 16384⟩
    (by decide) selected_cut_00280

theorem selected_cut_00281 : selected 8 ⟨15301, by decide⟩
    (prefixPartial 13 5141) = some ⟨13, 2, 0, 15301, 5141, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_5141_15301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5141 ⟨15301, by decide⟩ :=
  accepted_of_selected 13 5141 ⟨15301, by decide⟩ ⟨13, 2, 0, 15301, 5141, 2809, 16384⟩
    (by decide) selected_cut_00281

theorem selected_cut_00282 : selected 8 ⟨15382, by decide⟩
    (prefixPartial 13 5142) = some ⟨13, 2, 0, 15382, 5142, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_5142_15382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5142 ⟨15382, by decide⟩ :=
  accepted_of_selected 13 5142 ⟨15382, by decide⟩ ⟨13, 2, 0, 15382, 5142, 2945, 16384⟩
    (by decide) selected_cut_00282

theorem selected_cut_00283 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 5143) = some ⟨13, 1, 0, 414, 5143, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5143_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5143 ⟨414, by decide⟩ :=
  accepted_of_selected 13 5143 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 5143, 1, 16384⟩
    (by decide) selected_cut_00283

theorem unmarked_context_12_1285_15383 : frontier 9 ⟨15383, by decide⟩
    (prefixCache 12 1285) (prefixPartial 12 1285) = false := by
  decide +kernel

theorem node_context_12_1285_15383 : EJMOriginalGlobalDAGData.nodes 9 ⟨15383, by decide⟩ =
    .split (coordinate 12) (![⟨15224, by decide⟩,⟨15301, by decide⟩,⟨15382, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1285_15383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1285 ⟨15383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1285
    ⟨15383, by decide⟩ (by decide) (![⟨15224, by decide⟩,⟨15301, by decide⟩,⟨15382, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_1285_15383 node_context_12_1285_15383
  intro a
  fin_cases a
  · exact context_13_5140_15224
  · exact context_13_5141_15301
  · exact context_13_5142_15382
  · exact context_13_5143_414

theorem selected_cut_00284 : selected 7 ⟨15418, by decide⟩
    (prefixPartial 14 20576) = some ⟨14, 2, 0, 15418, 20576, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_20576_15418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20576 ⟨15418, by decide⟩ :=
  accepted_of_selected 14 20576 ⟨15418, by decide⟩ ⟨14, 2, 0, 15418, 20576, 1229, 4096⟩
    (by decide) selected_cut_00284

theorem selected_cut_00285 : selected 7 ⟨15454, by decide⟩
    (prefixPartial 14 20577) = some ⟨14, 2, 0, 15454, 20577, 1465, 4096⟩ := by
  decide +kernel

theorem context_14_20577_15454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20577 ⟨15454, by decide⟩ :=
  accepted_of_selected 14 20577 ⟨15454, by decide⟩ ⟨14, 2, 0, 15454, 20577, 1465, 4096⟩
    (by decide) selected_cut_00285

theorem selected_cut_00286 : selected 7 ⟨15489, by decide⟩
    (prefixPartial 14 20578) = some ⟨14, 2, 0, 15489, 20578, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_20578_15489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20578 ⟨15489, by decide⟩ :=
  accepted_of_selected 14 20578 ⟨15489, by decide⟩ ⟨14, 2, 0, 15489, 20578, 1433, 4096⟩
    (by decide) selected_cut_00286

theorem selected_cut_00287 : selected 7 ⟨15517, by decide⟩
    (prefixPartial 14 20579) = some ⟨14, 2, 0, 15517, 20579, 1329, 4096⟩ := by
  decide +kernel

theorem context_14_20579_15517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20579 ⟨15517, by decide⟩ :=
  accepted_of_selected 14 20579 ⟨15517, by decide⟩ ⟨14, 2, 0, 15517, 20579, 1329, 4096⟩
    (by decide) selected_cut_00287

theorem unmarked_context_13_5144_15518 : frontier 8 ⟨15518, by decide⟩
    (prefixCache 13 5144) (prefixPartial 13 5144) = false := by
  decide +kernel

theorem node_context_13_5144_15518 : EJMOriginalGlobalDAGData.nodes 8 ⟨15518, by decide⟩ =
    .split (coordinate 13) (![⟨15418, by decide⟩,⟨15454, by decide⟩,⟨15489, by decide⟩,⟨15517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5144_15518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5144 ⟨15518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5144
    ⟨15518, by decide⟩ (by decide) (![⟨15418, by decide⟩,⟨15454, by decide⟩,⟨15489, by decide⟩,⟨15517, by decide⟩]) unmarked_context_13_5144_15518 node_context_13_5144_15518
  intro a
  fin_cases a
  · exact context_14_20576_15418
  · exact context_14_20577_15454
  · exact context_14_20578_15489
  · exact context_14_20579_15517

theorem selected_cut_00288 : selected 8 ⟨15589, by decide⟩
    (prefixPartial 13 5145) = some ⟨13, 2, 0, 15589, 5145, 3737, 16384⟩ := by
  decide +kernel

theorem context_13_5145_15589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5145 ⟨15589, by decide⟩ :=
  accepted_of_selected 13 5145 ⟨15589, by decide⟩ ⟨13, 2, 0, 15589, 5145, 3737, 16384⟩
    (by decide) selected_cut_00288

theorem selected_cut_00289 : selected 8 ⟨15633, by decide⟩
    (prefixPartial 13 5146) = some ⟨13, 2, 0, 15633, 5146, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_5146_15633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5146 ⟨15633, by decide⟩ :=
  accepted_of_selected 13 5146 ⟨15633, by decide⟩ ⟨13, 2, 0, 15633, 5146, 2805, 16384⟩
    (by decide) selected_cut_00289

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
