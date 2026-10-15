/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover002
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00290 : selected 8 ⟨15660, by decide⟩
    (prefixPartial 13 5147) = some ⟨13, 2, 0, 15660, 5147, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_5147_15660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5147 ⟨15660, by decide⟩ :=
  accepted_of_selected 13 5147 ⟨15660, by decide⟩ ⟨13, 2, 0, 15660, 5147, 1497, 16384⟩
    (by decide) selected_cut_00290

theorem unmarked_context_12_1286_15661 : frontier 9 ⟨15661, by decide⟩
    (prefixCache 12 1286) (prefixPartial 12 1286) = false := by
  decide +kernel

theorem node_context_12_1286_15661 : EJMOriginalGlobalDAGData.nodes 9 ⟨15661, by decide⟩ =
    .split (coordinate 12) (![⟨15518, by decide⟩,⟨15589, by decide⟩,⟨15633, by decide⟩,⟨15660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1286_15661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1286 ⟨15661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1286
    ⟨15661, by decide⟩ (by decide) (![⟨15518, by decide⟩,⟨15589, by decide⟩,⟨15633, by decide⟩,⟨15660, by decide⟩]) unmarked_context_12_1286_15661 node_context_12_1286_15661
  intro a
  fin_cases a
  · exact context_13_5144_15518
  · exact context_13_5145_15589
  · exact context_13_5146_15633
  · exact context_13_5147_15660

theorem selected_cut_00291 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1287) = some ⟨12, 1, 0, 893, 1287, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1287_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1287 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1287 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1287, 1, 65536⟩
    (by decide) selected_cut_00291

theorem unmarked_context_11_321_15662 : frontier 10 ⟨15662, by decide⟩
    (prefixCache 11 321) (prefixPartial 11 321) = false := by
  decide +kernel

theorem node_context_11_321_15662 : EJMOriginalGlobalDAGData.nodes 10 ⟨15662, by decide⟩ =
    .split (coordinate 11) (![⟨15130, by decide⟩,⟨15383, by decide⟩,⟨15661, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_321_15662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 321 ⟨15662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 321
    ⟨15662, by decide⟩ (by decide) (![⟨15130, by decide⟩,⟨15383, by decide⟩,⟨15661, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_321_15662 node_context_11_321_15662
  intro a
  fin_cases a
  · exact context_12_1284_15130
  · exact context_12_1285_15383
  · exact context_12_1286_15661
  · exact context_12_1287_893

theorem selected_cut_00292 : selected 8 ⟨15764, by decide⟩
    (prefixPartial 13 5152) = some ⟨13, 2, 0, 15764, 5152, 4029, 16384⟩ := by
  decide +kernel

theorem context_13_5152_15764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5152 ⟨15764, by decide⟩ :=
  accepted_of_selected 13 5152 ⟨15764, by decide⟩ ⟨13, 2, 0, 15764, 5152, 4029, 16384⟩
    (by decide) selected_cut_00292

theorem selected_cut_00293 : selected 8 ⟨15885, by decide⟩
    (prefixPartial 13 5153) = some ⟨13, 2, 0, 15885, 5153, 4041, 16384⟩ := by
  decide +kernel

theorem context_13_5153_15885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5153 ⟨15885, by decide⟩ :=
  accepted_of_selected 13 5153 ⟨15885, by decide⟩ ⟨13, 2, 0, 15885, 5153, 4041, 16384⟩
    (by decide) selected_cut_00293

theorem selected_cut_00294 : selected 8 ⟨15970, by decide⟩
    (prefixPartial 13 5154) = some ⟨13, 2, 0, 15970, 5154, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_5154_15970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5154 ⟨15970, by decide⟩ :=
  accepted_of_selected 13 5154 ⟨15970, by decide⟩ ⟨13, 2, 0, 15970, 5154, 2613, 16384⟩
    (by decide) selected_cut_00294

theorem selected_cut_00295 : selected 8 ⟨16027, by decide⟩
    (prefixPartial 13 5155) = some ⟨13, 2, 0, 16027, 5155, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_5155_16027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5155 ⟨16027, by decide⟩ :=
  accepted_of_selected 13 5155 ⟨16027, by decide⟩ ⟨13, 2, 0, 16027, 5155, 1145, 16384⟩
    (by decide) selected_cut_00295

theorem unmarked_context_12_1288_16028 : frontier 9 ⟨16028, by decide⟩
    (prefixCache 12 1288) (prefixPartial 12 1288) = false := by
  decide +kernel

theorem node_context_12_1288_16028 : EJMOriginalGlobalDAGData.nodes 9 ⟨16028, by decide⟩ =
    .split (coordinate 12) (![⟨15764, by decide⟩,⟨15885, by decide⟩,⟨15970, by decide⟩,⟨16027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1288_16028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1288 ⟨16028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1288
    ⟨16028, by decide⟩ (by decide) (![⟨15764, by decide⟩,⟨15885, by decide⟩,⟨15970, by decide⟩,⟨16027, by decide⟩]) unmarked_context_12_1288_16028 node_context_12_1288_16028
  intro a
  fin_cases a
  · exact context_13_5152_15764
  · exact context_13_5153_15885
  · exact context_13_5154_15970
  · exact context_13_5155_16027

theorem selected_cut_00296 : selected 7 ⟨16051, by decide⟩
    (prefixPartial 14 20624) = some ⟨14, 2, 0, 16051, 20624, 785, 4096⟩ := by
  decide +kernel

theorem context_14_20624_16051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20624 ⟨16051, by decide⟩ :=
  accepted_of_selected 14 20624 ⟨16051, by decide⟩ ⟨14, 2, 0, 16051, 20624, 785, 4096⟩
    (by decide) selected_cut_00296

theorem selected_cut_00297 : selected 7 ⟨16081, by decide⟩
    (prefixPartial 14 20625) = some ⟨14, 2, 0, 16081, 20625, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_20625_16081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20625 ⟨16081, by decide⟩ :=
  accepted_of_selected 14 20625 ⟨16081, by decide⟩ ⟨14, 2, 0, 16081, 20625, 1133, 4096⟩
    (by decide) selected_cut_00297

theorem selected_cut_00298 : selected 7 ⟨16108, by decide⟩
    (prefixPartial 14 20626) = some ⟨14, 2, 0, 16108, 20626, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_20626_16108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20626 ⟨16108, by decide⟩ :=
  accepted_of_selected 14 20626 ⟨16108, by decide⟩ ⟨14, 2, 0, 16108, 20626, 1177, 4096⟩
    (by decide) selected_cut_00298

theorem selected_cut_00299 : selected 7 ⟨16130, by decide⟩
    (prefixPartial 14 20627) = some ⟨14, 2, 0, 16130, 20627, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_20627_16130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20627 ⟨16130, by decide⟩ :=
  accepted_of_selected 14 20627 ⟨16130, by decide⟩ ⟨14, 2, 0, 16130, 20627, 1193, 4096⟩
    (by decide) selected_cut_00299

theorem unmarked_context_13_5156_16131 : frontier 8 ⟨16131, by decide⟩
    (prefixCache 13 5156) (prefixPartial 13 5156) = false := by
  decide +kernel

theorem node_context_13_5156_16131 : EJMOriginalGlobalDAGData.nodes 8 ⟨16131, by decide⟩ =
    .split (coordinate 13) (![⟨16051, by decide⟩,⟨16081, by decide⟩,⟨16108, by decide⟩,⟨16130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5156_16131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5156 ⟨16131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5156
    ⟨16131, by decide⟩ (by decide) (![⟨16051, by decide⟩,⟨16081, by decide⟩,⟨16108, by decide⟩,⟨16130, by decide⟩]) unmarked_context_13_5156_16131 node_context_13_5156_16131
  intro a
  fin_cases a
  · exact context_14_20624_16051
  · exact context_14_20625_16081
  · exact context_14_20626_16108
  · exact context_14_20627_16130

theorem selected_cut_00300 : selected 7 ⟨16149, by decide⟩
    (prefixPartial 14 20628) = some ⟨14, 2, 0, 16149, 20628, 989, 4096⟩ := by
  decide +kernel

theorem context_14_20628_16149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20628 ⟨16149, by decide⟩ :=
  accepted_of_selected 14 20628 ⟨16149, by decide⟩ ⟨14, 2, 0, 16149, 20628, 989, 4096⟩
    (by decide) selected_cut_00300

theorem selected_cut_00301 : selected 7 ⟨16174, by decide⟩
    (prefixPartial 14 20629) = some ⟨14, 2, 0, 16174, 20629, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_20629_16174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20629 ⟨16174, by decide⟩ :=
  accepted_of_selected 14 20629 ⟨16174, by decide⟩ ⟨14, 2, 0, 16174, 20629, 1037, 4096⟩
    (by decide) selected_cut_00301

theorem selected_cut_00302 : selected 7 ⟨16194, by decide⟩
    (prefixPartial 14 20630) = some ⟨14, 2, 0, 16194, 20630, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_20630_16194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20630 ⟨16194, by decide⟩ :=
  accepted_of_selected 14 20630 ⟨16194, by decide⟩ ⟨14, 2, 0, 16194, 20630, 1177, 4096⟩
    (by decide) selected_cut_00302

theorem selected_cut_00303 : selected 7 ⟨16212, by decide⟩
    (prefixPartial 14 20631) = some ⟨14, 2, 0, 16212, 20631, 997, 4096⟩ := by
  decide +kernel

theorem context_14_20631_16212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20631 ⟨16212, by decide⟩ :=
  accepted_of_selected 14 20631 ⟨16212, by decide⟩ ⟨14, 2, 0, 16212, 20631, 997, 4096⟩
    (by decide) selected_cut_00303

theorem unmarked_context_13_5157_16213 : frontier 8 ⟨16213, by decide⟩
    (prefixCache 13 5157) (prefixPartial 13 5157) = false := by
  decide +kernel

theorem node_context_13_5157_16213 : EJMOriginalGlobalDAGData.nodes 8 ⟨16213, by decide⟩ =
    .split (coordinate 13) (![⟨16149, by decide⟩,⟨16174, by decide⟩,⟨16194, by decide⟩,⟨16212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5157_16213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5157 ⟨16213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5157
    ⟨16213, by decide⟩ (by decide) (![⟨16149, by decide⟩,⟨16174, by decide⟩,⟨16194, by decide⟩,⟨16212, by decide⟩]) unmarked_context_13_5157_16213 node_context_13_5157_16213
  intro a
  fin_cases a
  · exact context_14_20628_16149
  · exact context_14_20629_16174
  · exact context_14_20630_16194
  · exact context_14_20631_16212

theorem selected_cut_00304 : selected 8 ⟨16264, by decide⟩
    (prefixPartial 13 5158) = some ⟨13, 2, 0, 16264, 5158, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_5158_16264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5158 ⟨16264, by decide⟩ :=
  accepted_of_selected 13 5158 ⟨16264, by decide⟩ ⟨13, 2, 0, 16264, 5158, 2825, 16384⟩
    (by decide) selected_cut_00304

theorem selected_cut_00305 : selected 8 ⟨16284, by decide⟩
    (prefixPartial 13 5159) = some ⟨13, 2, 0, 16284, 5159, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_5159_16284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5159 ⟨16284, by decide⟩ :=
  accepted_of_selected 13 5159 ⟨16284, by decide⟩ ⟨13, 2, 0, 16284, 5159, 1361, 16384⟩
    (by decide) selected_cut_00305

theorem unmarked_context_12_1289_16285 : frontier 9 ⟨16285, by decide⟩
    (prefixCache 12 1289) (prefixPartial 12 1289) = false := by
  decide +kernel

theorem node_context_12_1289_16285 : EJMOriginalGlobalDAGData.nodes 9 ⟨16285, by decide⟩ =
    .split (coordinate 12) (![⟨16131, by decide⟩,⟨16213, by decide⟩,⟨16264, by decide⟩,⟨16284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1289_16285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1289 ⟨16285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1289
    ⟨16285, by decide⟩ (by decide) (![⟨16131, by decide⟩,⟨16213, by decide⟩,⟨16264, by decide⟩,⟨16284, by decide⟩]) unmarked_context_12_1289_16285 node_context_12_1289_16285
  intro a
  fin_cases a
  · exact context_13_5156_16131
  · exact context_13_5157_16213
  · exact context_13_5158_16264
  · exact context_13_5159_16284

theorem selected_cut_00306 : selected 7 ⟨16311, by decide⟩
    (prefixPartial 14 20640) = some ⟨14, 2, 0, 16311, 20640, 653, 4096⟩ := by
  decide +kernel

theorem context_14_20640_16311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20640 ⟨16311, by decide⟩ :=
  accepted_of_selected 14 20640 ⟨16311, by decide⟩ ⟨14, 2, 0, 16311, 20640, 653, 4096⟩
    (by decide) selected_cut_00306

theorem selected_cut_00307 : selected 7 ⟨16337, by decide⟩
    (prefixPartial 14 20641) = some ⟨14, 2, 0, 16337, 20641, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_20641_16337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20641 ⟨16337, by decide⟩ :=
  accepted_of_selected 14 20641 ⟨16337, by decide⟩ ⟨14, 2, 0, 16337, 20641, 1245, 4096⟩
    (by decide) selected_cut_00307

theorem selected_cut_00308 : selected 7 ⟨16363, by decide⟩
    (prefixPartial 14 20642) = some ⟨14, 2, 0, 16363, 20642, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_20642_16363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20642 ⟨16363, by decide⟩ :=
  accepted_of_selected 14 20642 ⟨16363, by decide⟩ ⟨14, 2, 0, 16363, 20642, 1281, 4096⟩
    (by decide) selected_cut_00308

theorem selected_cut_00309 : selected 7 ⟨16391, by decide⟩
    (prefixPartial 14 20643) = some ⟨14, 2, 0, 16391, 20643, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_20643_16391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20643 ⟨16391, by decide⟩ :=
  accepted_of_selected 14 20643 ⟨16391, by decide⟩ ⟨14, 2, 0, 16391, 20643, 1253, 4096⟩
    (by decide) selected_cut_00309

theorem unmarked_context_13_5160_16392 : frontier 8 ⟨16392, by decide⟩
    (prefixCache 13 5160) (prefixPartial 13 5160) = false := by
  decide +kernel

theorem node_context_13_5160_16392 : EJMOriginalGlobalDAGData.nodes 8 ⟨16392, by decide⟩ =
    .split (coordinate 13) (![⟨16311, by decide⟩,⟨16337, by decide⟩,⟨16363, by decide⟩,⟨16391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5160_16392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5160 ⟨16392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5160
    ⟨16392, by decide⟩ (by decide) (![⟨16311, by decide⟩,⟨16337, by decide⟩,⟨16363, by decide⟩,⟨16391, by decide⟩]) unmarked_context_13_5160_16392 node_context_13_5160_16392
  intro a
  fin_cases a
  · exact context_14_20640_16311
  · exact context_14_20641_16337
  · exact context_14_20642_16363
  · exact context_14_20643_16391

theorem selected_cut_00310 : selected 8 ⟨16459, by decide⟩
    (prefixPartial 13 5161) = some ⟨13, 2, 0, 16459, 5161, 4009, 16384⟩ := by
  decide +kernel

theorem context_13_5161_16459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5161 ⟨16459, by decide⟩ :=
  accepted_of_selected 13 5161 ⟨16459, by decide⟩ ⟨13, 2, 0, 16459, 5161, 4009, 16384⟩
    (by decide) selected_cut_00310

theorem selected_cut_00311 : selected 8 ⟨16496, by decide⟩
    (prefixPartial 13 5162) = some ⟨13, 2, 0, 16496, 5162, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_5162_16496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5162 ⟨16496, by decide⟩ :=
  accepted_of_selected 13 5162 ⟨16496, by decide⟩ ⟨13, 2, 0, 16496, 5162, 2753, 16384⟩
    (by decide) selected_cut_00311

theorem selected_cut_00312 : selected 8 ⟨16518, by decide⟩
    (prefixPartial 13 5163) = some ⟨13, 2, 0, 16518, 5163, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_5163_16518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5163 ⟨16518, by decide⟩ :=
  accepted_of_selected 13 5163 ⟨16518, by decide⟩ ⟨13, 2, 0, 16518, 5163, 1501, 16384⟩
    (by decide) selected_cut_00312

theorem unmarked_context_12_1290_16519 : frontier 9 ⟨16519, by decide⟩
    (prefixCache 12 1290) (prefixPartial 12 1290) = false := by
  decide +kernel

theorem node_context_12_1290_16519 : EJMOriginalGlobalDAGData.nodes 9 ⟨16519, by decide⟩ =
    .split (coordinate 12) (![⟨16392, by decide⟩,⟨16459, by decide⟩,⟨16496, by decide⟩,⟨16518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1290_16519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1290 ⟨16519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1290
    ⟨16519, by decide⟩ (by decide) (![⟨16392, by decide⟩,⟨16459, by decide⟩,⟨16496, by decide⟩,⟨16518, by decide⟩]) unmarked_context_12_1290_16519 node_context_12_1290_16519
  intro a
  fin_cases a
  · exact context_13_5160_16392
  · exact context_13_5161_16459
  · exact context_13_5162_16496
  · exact context_13_5163_16518

theorem selected_cut_00313 : selected 7 ⟨16530, by decide⟩
    (prefixPartial 14 20656) = some ⟨14, 2, 0, 16530, 20656, 325, 4096⟩ := by
  decide +kernel

theorem context_14_20656_16530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20656 ⟨16530, by decide⟩ :=
  accepted_of_selected 14 20656 ⟨16530, by decide⟩ ⟨14, 2, 0, 16530, 20656, 325, 4096⟩
    (by decide) selected_cut_00313

theorem selected_cut_00314 : selected 7 ⟨16559, by decide⟩
    (prefixPartial 14 20657) = some ⟨14, 2, 0, 16559, 20657, 1401, 4096⟩ := by
  decide +kernel

theorem context_14_20657_16559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20657 ⟨16559, by decide⟩ :=
  accepted_of_selected 14 20657 ⟨16559, by decide⟩ ⟨14, 2, 0, 16559, 20657, 1401, 4096⟩
    (by decide) selected_cut_00314

theorem selected_cut_00315 : selected 7 ⟨16590, by decide⟩
    (prefixPartial 14 20658) = some ⟨14, 2, 0, 16590, 20658, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_20658_16590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20658 ⟨16590, by decide⟩ :=
  accepted_of_selected 14 20658 ⟨16590, by decide⟩ ⟨14, 2, 0, 16590, 20658, 1241, 4096⟩
    (by decide) selected_cut_00315

theorem selected_cut_00316 : selected 7 ⟨16619, by decide⟩
    (prefixPartial 14 20659) = some ⟨14, 2, 0, 16619, 20659, 1329, 4096⟩ := by
  decide +kernel

theorem context_14_20659_16619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20659 ⟨16619, by decide⟩ :=
  accepted_of_selected 14 20659 ⟨16619, by decide⟩ ⟨14, 2, 0, 16619, 20659, 1329, 4096⟩
    (by decide) selected_cut_00316

theorem unmarked_context_13_5164_16620 : frontier 8 ⟨16620, by decide⟩
    (prefixCache 13 5164) (prefixPartial 13 5164) = false := by
  decide +kernel

theorem node_context_13_5164_16620 : EJMOriginalGlobalDAGData.nodes 8 ⟨16620, by decide⟩ =
    .split (coordinate 13) (![⟨16530, by decide⟩,⟨16559, by decide⟩,⟨16590, by decide⟩,⟨16619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5164_16620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5164 ⟨16620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5164
    ⟨16620, by decide⟩ (by decide) (![⟨16530, by decide⟩,⟨16559, by decide⟩,⟨16590, by decide⟩,⟨16619, by decide⟩]) unmarked_context_13_5164_16620 node_context_13_5164_16620
  intro a
  fin_cases a
  · exact context_14_20656_16530
  · exact context_14_20657_16559
  · exact context_14_20658_16590
  · exact context_14_20659_16619

theorem selected_cut_00317 : selected 7 ⟨16640, by decide⟩
    (prefixPartial 14 20660) = some ⟨14, 2, 0, 16640, 20660, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_20660_16640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20660 ⟨16640, by decide⟩ :=
  accepted_of_selected 14 20660 ⟨16640, by decide⟩ ⟨14, 2, 0, 16640, 20660, 1057, 4096⟩
    (by decide) selected_cut_00317

theorem selected_cut_00318 : selected 7 ⟨16668, by decide⟩
    (prefixPartial 14 20661) = some ⟨14, 2, 0, 16668, 20661, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_20661_16668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20661 ⟨16668, by decide⟩ :=
  accepted_of_selected 14 20661 ⟨16668, by decide⟩ ⟨14, 2, 0, 16668, 20661, 1121, 4096⟩
    (by decide) selected_cut_00318

theorem selected_cut_00319 : selected 7 ⟨16686, by decide⟩
    (prefixPartial 14 20662) = some ⟨14, 2, 0, 16686, 20662, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_20662_16686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20662 ⟨16686, by decide⟩ :=
  accepted_of_selected 14 20662 ⟨16686, by decide⟩ ⟨14, 2, 0, 16686, 20662, 1241, 4096⟩
    (by decide) selected_cut_00319

theorem selected_cut_00320 : selected 7 ⟨16699, by decide⟩
    (prefixPartial 14 20663) = some ⟨14, 2, 0, 16699, 20663, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_20663_16699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 20663 ⟨16699, by decide⟩ :=
  accepted_of_selected 14 20663 ⟨16699, by decide⟩ ⟨14, 2, 0, 16699, 20663, 1129, 4096⟩
    (by decide) selected_cut_00320

theorem unmarked_context_13_5165_16700 : frontier 8 ⟨16700, by decide⟩
    (prefixCache 13 5165) (prefixPartial 13 5165) = false := by
  decide +kernel

theorem node_context_13_5165_16700 : EJMOriginalGlobalDAGData.nodes 8 ⟨16700, by decide⟩ =
    .split (coordinate 13) (![⟨16640, by decide⟩,⟨16668, by decide⟩,⟨16686, by decide⟩,⟨16699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_5165_16700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5165 ⟨16700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 5165
    ⟨16700, by decide⟩ (by decide) (![⟨16640, by decide⟩,⟨16668, by decide⟩,⟨16686, by decide⟩,⟨16699, by decide⟩]) unmarked_context_13_5165_16700 node_context_13_5165_16700
  intro a
  fin_cases a
  · exact context_14_20660_16640
  · exact context_14_20661_16668
  · exact context_14_20662_16686
  · exact context_14_20663_16699

theorem selected_cut_00321 : selected 8 ⟨16765, by decide⟩
    (prefixPartial 13 5166) = some ⟨13, 2, 0, 16765, 5166, 3285, 16384⟩ := by
  decide +kernel

theorem context_13_5166_16765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5166 ⟨16765, by decide⟩ :=
  accepted_of_selected 13 5166 ⟨16765, by decide⟩ ⟨13, 2, 0, 16765, 5166, 3285, 16384⟩
    (by decide) selected_cut_00321

theorem selected_cut_00322 : selected 8 ⟨16779, by decide⟩
    (prefixPartial 13 5167) = some ⟨13, 2, 0, 16779, 5167, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_5167_16779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5167 ⟨16779, by decide⟩ :=
  accepted_of_selected 13 5167 ⟨16779, by decide⟩ ⟨13, 2, 0, 16779, 5167, 1373, 16384⟩
    (by decide) selected_cut_00322

theorem unmarked_context_12_1291_16780 : frontier 9 ⟨16780, by decide⟩
    (prefixCache 12 1291) (prefixPartial 12 1291) = false := by
  decide +kernel

theorem node_context_12_1291_16780 : EJMOriginalGlobalDAGData.nodes 9 ⟨16780, by decide⟩ =
    .split (coordinate 12) (![⟨16620, by decide⟩,⟨16700, by decide⟩,⟨16765, by decide⟩,⟨16779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1291_16780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1291 ⟨16780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1291
    ⟨16780, by decide⟩ (by decide) (![⟨16620, by decide⟩,⟨16700, by decide⟩,⟨16765, by decide⟩,⟨16779, by decide⟩]) unmarked_context_12_1291_16780 node_context_12_1291_16780
  intro a
  fin_cases a
  · exact context_13_5164_16620
  · exact context_13_5165_16700
  · exact context_13_5166_16765
  · exact context_13_5167_16779

theorem unmarked_context_11_322_16781 : frontier 10 ⟨16781, by decide⟩
    (prefixCache 11 322) (prefixPartial 11 322) = false := by
  decide +kernel

theorem node_context_11_322_16781 : EJMOriginalGlobalDAGData.nodes 10 ⟨16781, by decide⟩ =
    .split (coordinate 11) (![⟨16028, by decide⟩,⟨16285, by decide⟩,⟨16519, by decide⟩,⟨16780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_322_16781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 322 ⟨16781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 322
    ⟨16781, by decide⟩ (by decide) (![⟨16028, by decide⟩,⟨16285, by decide⟩,⟨16519, by decide⟩,⟨16780, by decide⟩]) unmarked_context_11_322_16781 node_context_11_322_16781
  intro a
  fin_cases a
  · exact context_12_1288_16028
  · exact context_12_1289_16285
  · exact context_12_1290_16519
  · exact context_12_1291_16780

theorem selected_cut_00323 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 323) = some ⟨11, 1, 0, 1736, 323, 1, 262144⟩ := by
  decide +kernel

theorem context_11_323_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 323 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 323 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 323, 1, 262144⟩
    (by decide) selected_cut_00323

theorem unmarked_context_10_80_16782 : frontier 11 ⟨16782, by decide⟩
    (prefixCache 10 80) (prefixPartial 10 80) = false := by
  decide +kernel

theorem node_context_10_80_16782 : EJMOriginalGlobalDAGData.nodes 11 ⟨16782, by decide⟩ =
    .split (coordinate 10) (![⟨14930, by decide⟩,⟨15662, by decide⟩,⟨16781, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_80_16782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 80 ⟨16782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 80
    ⟨16782, by decide⟩ (by decide) (![⟨14930, by decide⟩,⟨15662, by decide⟩,⟨16781, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_80_16782 node_context_10_80_16782
  intro a
  fin_cases a
  · exact context_11_320_14930
  · exact context_11_321_15662
  · exact context_11_322_16781
  · exact context_11_323_1736

theorem selected_cut_00324 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1296) = some ⟨12, 1, 0, 1738, 1296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1296_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1296 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1296 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1296, 1, 65536⟩
    (by decide) selected_cut_00324

theorem selected_cut_00325 : selected 9 ⟨16860, by decide⟩
    (prefixPartial 12 1297) = some ⟨12, 2, 0, 16860, 1297, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_1297_16860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1297 ⟨16860, by decide⟩ :=
  accepted_of_selected 12 1297 ⟨16860, by decide⟩ ⟨12, 2, 0, 16860, 1297, 1977, 65536⟩
    (by decide) selected_cut_00325

theorem selected_cut_00326 : selected 8 ⟨16914, by decide⟩
    (prefixPartial 13 5192) = some ⟨13, 2, 0, 16914, 5192, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_5192_16914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5192 ⟨16914, by decide⟩ :=
  accepted_of_selected 13 5192 ⟨16914, by decide⟩ ⟨13, 2, 0, 16914, 5192, 1853, 16384⟩
    (by decide) selected_cut_00326

theorem selected_cut_00327 : selected 8 ⟨16957, by decide⟩
    (prefixPartial 13 5193) = some ⟨13, 2, 0, 16957, 5193, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_5193_16957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5193 ⟨16957, by decide⟩ :=
  accepted_of_selected 13 5193 ⟨16957, by decide⟩ ⟨13, 2, 0, 16957, 5193, 1457, 16384⟩
    (by decide) selected_cut_00327

theorem selected_cut_00328 : selected 8 ⟨16997, by decide⟩
    (prefixPartial 13 5194) = some ⟨13, 2, 0, 16997, 5194, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_5194_16997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5194 ⟨16997, by decide⟩ :=
  accepted_of_selected 13 5194 ⟨16997, by decide⟩ ⟨13, 2, 0, 16997, 5194, 1653, 16384⟩
    (by decide) selected_cut_00328

theorem selected_cut_00329 : selected 8 ⟨17013, by decide⟩
    (prefixPartial 13 5195) = some ⟨13, 2, 0, 17013, 5195, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_5195_17013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5195 ⟨17013, by decide⟩ :=
  accepted_of_selected 13 5195 ⟨17013, by decide⟩ ⟨13, 2, 0, 17013, 5195, 1005, 16384⟩
    (by decide) selected_cut_00329

theorem unmarked_context_12_1298_17014 : frontier 9 ⟨17014, by decide⟩
    (prefixCache 12 1298) (prefixPartial 12 1298) = false := by
  decide +kernel

theorem node_context_12_1298_17014 : EJMOriginalGlobalDAGData.nodes 9 ⟨17014, by decide⟩ =
    .split (coordinate 12) (![⟨16914, by decide⟩,⟨16957, by decide⟩,⟨16997, by decide⟩,⟨17013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1298_17014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1298 ⟨17014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1298
    ⟨17014, by decide⟩ (by decide) (![⟨16914, by decide⟩,⟨16957, by decide⟩,⟨16997, by decide⟩,⟨17013, by decide⟩]) unmarked_context_12_1298_17014 node_context_12_1298_17014
  intro a
  fin_cases a
  · exact context_13_5192_16914
  · exact context_13_5193_16957
  · exact context_13_5194_16997
  · exact context_13_5195_17013

theorem selected_cut_00330 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1299) = some ⟨12, 1, 0, 893, 1299, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1299_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1299 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1299 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1299, 1, 65536⟩
    (by decide) selected_cut_00330

theorem unmarked_context_11_324_17015 : frontier 10 ⟨17015, by decide⟩
    (prefixCache 11 324) (prefixPartial 11 324) = false := by
  decide +kernel

theorem node_context_11_324_17015 : EJMOriginalGlobalDAGData.nodes 10 ⟨17015, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨16860, by decide⟩,⟨17014, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_324_17015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 324 ⟨17015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 324
    ⟨17015, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨16860, by decide⟩,⟨17014, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_324_17015 node_context_11_324_17015
  intro a
  fin_cases a
  · exact context_12_1296_1738
  · exact context_12_1297_16860
  · exact context_12_1298_17014
  · exact context_12_1299_893

theorem selected_cut_00331 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1300) = some ⟨12, 1, 0, 1738, 1300, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1300_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1300 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1300 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1300, 1, 65536⟩
    (by decide) selected_cut_00331

theorem selected_cut_00332 : selected 8 ⟨17084, by decide⟩
    (prefixPartial 13 5204) = some ⟨13, 2, 0, 17084, 5204, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_5204_17084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5204 ⟨17084, by decide⟩ :=
  accepted_of_selected 13 5204 ⟨17084, by decide⟩ ⟨13, 2, 0, 17084, 5204, 1797, 16384⟩
    (by decide) selected_cut_00332

theorem selected_cut_00333 : selected 8 ⟨17134, by decide⟩
    (prefixPartial 13 5205) = some ⟨13, 2, 0, 17134, 5205, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_5205_17134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5205 ⟨17134, by decide⟩ :=
  accepted_of_selected 13 5205 ⟨17134, by decide⟩ ⟨13, 2, 0, 17134, 5205, 1761, 16384⟩
    (by decide) selected_cut_00333

theorem selected_cut_00334 : selected 8 ⟨17263, by decide⟩
    (prefixPartial 13 5206) = some ⟨13, 2, 0, 17263, 5206, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_5206_17263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5206 ⟨17263, by decide⟩ :=
  accepted_of_selected 13 5206 ⟨17263, by decide⟩ ⟨13, 2, 0, 17263, 5206, 2421, 16384⟩
    (by decide) selected_cut_00334

theorem selected_cut_00335 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 5207) = some ⟨13, 1, 0, 414, 5207, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5207_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5207 ⟨414, by decide⟩ :=
  accepted_of_selected 13 5207 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 5207, 1, 16384⟩
    (by decide) selected_cut_00335

theorem unmarked_context_12_1301_17264 : frontier 9 ⟨17264, by decide⟩
    (prefixCache 12 1301) (prefixPartial 12 1301) = false := by
  decide +kernel

theorem node_context_12_1301_17264 : EJMOriginalGlobalDAGData.nodes 9 ⟨17264, by decide⟩ =
    .split (coordinate 12) (![⟨17084, by decide⟩,⟨17134, by decide⟩,⟨17263, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1301_17264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1301 ⟨17264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1301
    ⟨17264, by decide⟩ (by decide) (![⟨17084, by decide⟩,⟨17134, by decide⟩,⟨17263, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_1301_17264 node_context_12_1301_17264
  intro a
  fin_cases a
  · exact context_13_5204_17084
  · exact context_13_5205_17134
  · exact context_13_5206_17263
  · exact context_13_5207_414

theorem selected_cut_00336 : selected 8 ⟨17358, by decide⟩
    (prefixPartial 13 5208) = some ⟨13, 2, 0, 17358, 5208, 3153, 16384⟩ := by
  decide +kernel

theorem context_13_5208_17358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5208 ⟨17358, by decide⟩ :=
  accepted_of_selected 13 5208 ⟨17358, by decide⟩ ⟨13, 2, 0, 17358, 5208, 3153, 16384⟩
    (by decide) selected_cut_00336

theorem selected_cut_00337 : selected 8 ⟨17413, by decide⟩
    (prefixPartial 13 5209) = some ⟨13, 2, 0, 17413, 5209, 3745, 16384⟩ := by
  decide +kernel

theorem context_13_5209_17413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5209 ⟨17413, by decide⟩ :=
  accepted_of_selected 13 5209 ⟨17413, by decide⟩ ⟨13, 2, 0, 17413, 5209, 3745, 16384⟩
    (by decide) selected_cut_00337

theorem selected_cut_00338 : selected 8 ⟨17454, by decide⟩
    (prefixPartial 13 5210) = some ⟨13, 2, 0, 17454, 5210, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_5210_17454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5210 ⟨17454, by decide⟩ :=
  accepted_of_selected 13 5210 ⟨17454, by decide⟩ ⟨13, 2, 0, 17454, 5210, 2749, 16384⟩
    (by decide) selected_cut_00338

theorem selected_cut_00339 : selected 8 ⟨17480, by decide⟩
    (prefixPartial 13 5211) = some ⟨13, 2, 0, 17480, 5211, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_5211_17480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5211 ⟨17480, by decide⟩ :=
  accepted_of_selected 13 5211 ⟨17480, by decide⟩ ⟨13, 2, 0, 17480, 5211, 1481, 16384⟩
    (by decide) selected_cut_00339

theorem unmarked_context_12_1302_17481 : frontier 9 ⟨17481, by decide⟩
    (prefixCache 12 1302) (prefixPartial 12 1302) = false := by
  decide +kernel

theorem node_context_12_1302_17481 : EJMOriginalGlobalDAGData.nodes 9 ⟨17481, by decide⟩ =
    .split (coordinate 12) (![⟨17358, by decide⟩,⟨17413, by decide⟩,⟨17454, by decide⟩,⟨17480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1302_17481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1302 ⟨17481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1302
    ⟨17481, by decide⟩ (by decide) (![⟨17358, by decide⟩,⟨17413, by decide⟩,⟨17454, by decide⟩,⟨17480, by decide⟩]) unmarked_context_12_1302_17481 node_context_12_1302_17481
  intro a
  fin_cases a
  · exact context_13_5208_17358
  · exact context_13_5209_17413
  · exact context_13_5210_17454
  · exact context_13_5211_17480

theorem selected_cut_00340 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1303) = some ⟨12, 1, 0, 893, 1303, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1303_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1303 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1303 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1303, 1, 65536⟩
    (by decide) selected_cut_00340

theorem unmarked_context_11_325_17482 : frontier 10 ⟨17482, by decide⟩
    (prefixCache 11 325) (prefixPartial 11 325) = false := by
  decide +kernel

theorem node_context_11_325_17482 : EJMOriginalGlobalDAGData.nodes 10 ⟨17482, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨17264, by decide⟩,⟨17481, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_325_17482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 325 ⟨17482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 325
    ⟨17482, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨17264, by decide⟩,⟨17481, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_325_17482 node_context_11_325_17482
  intro a
  fin_cases a
  · exact context_12_1300_1738
  · exact context_12_1301_17264
  · exact context_12_1302_17481
  · exact context_12_1303_893

theorem selected_cut_00341 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1304) = some ⟨12, 1, 0, 1738, 1304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1304_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1304 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1304 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1304, 1, 65536⟩
    (by decide) selected_cut_00341

theorem selected_cut_00342 : selected 8 ⟨17524, by decide⟩
    (prefixPartial 13 5220) = some ⟨13, 2, 0, 17524, 5220, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_5220_17524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5220 ⟨17524, by decide⟩ :=
  accepted_of_selected 13 5220 ⟨17524, by decide⟩ ⟨13, 2, 0, 17524, 5220, 1297, 16384⟩
    (by decide) selected_cut_00342

theorem selected_cut_00343 : selected 8 ⟨17570, by decide⟩
    (prefixPartial 13 5221) = some ⟨13, 2, 0, 17570, 5221, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_5221_17570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5221 ⟨17570, by decide⟩ :=
  accepted_of_selected 13 5221 ⟨17570, by decide⟩ ⟨13, 2, 0, 17570, 5221, 1337, 16384⟩
    (by decide) selected_cut_00343

theorem selected_cut_00344 : selected 8 ⟨17607, by decide⟩
    (prefixPartial 13 5222) = some ⟨13, 2, 0, 17607, 5222, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_5222_17607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5222 ⟨17607, by decide⟩ :=
  accepted_of_selected 13 5222 ⟨17607, by decide⟩ ⟨13, 2, 0, 17607, 5222, 1477, 16384⟩
    (by decide) selected_cut_00344

theorem selected_cut_00345 : selected 8 ⟨17629, by decide⟩
    (prefixPartial 13 5223) = some ⟨13, 2, 0, 17629, 5223, 857, 16384⟩ := by
  decide +kernel

theorem context_13_5223_17629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5223 ⟨17629, by decide⟩ :=
  accepted_of_selected 13 5223 ⟨17629, by decide⟩ ⟨13, 2, 0, 17629, 5223, 857, 16384⟩
    (by decide) selected_cut_00345

theorem unmarked_context_12_1305_17630 : frontier 9 ⟨17630, by decide⟩
    (prefixCache 12 1305) (prefixPartial 12 1305) = false := by
  decide +kernel

theorem node_context_12_1305_17630 : EJMOriginalGlobalDAGData.nodes 9 ⟨17630, by decide⟩ =
    .split (coordinate 12) (![⟨17524, by decide⟩,⟨17570, by decide⟩,⟨17607, by decide⟩,⟨17629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1305_17630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1305 ⟨17630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1305
    ⟨17630, by decide⟩ (by decide) (![⟨17524, by decide⟩,⟨17570, by decide⟩,⟨17607, by decide⟩,⟨17629, by decide⟩]) unmarked_context_12_1305_17630 node_context_12_1305_17630
  intro a
  fin_cases a
  · exact context_13_5220_17524
  · exact context_13_5221_17570
  · exact context_13_5222_17607
  · exact context_13_5223_17629

theorem selected_cut_00346 : selected 8 ⟨17676, by decide⟩
    (prefixPartial 13 5224) = some ⟨13, 2, 0, 17676, 5224, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_5224_17676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5224 ⟨17676, by decide⟩ :=
  accepted_of_selected 13 5224 ⟨17676, by decide⟩ ⟨13, 2, 0, 17676, 5224, 1537, 16384⟩
    (by decide) selected_cut_00346

theorem selected_cut_00347 : selected 8 ⟨17729, by decide⟩
    (prefixPartial 13 5225) = some ⟨13, 2, 0, 17729, 5225, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_5225_17729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5225 ⟨17729, by decide⟩ :=
  accepted_of_selected 13 5225 ⟨17729, by decide⟩ ⟨13, 2, 0, 17729, 5225, 2385, 16384⟩
    (by decide) selected_cut_00347

theorem selected_cut_00348 : selected 8 ⟨17762, by decide⟩
    (prefixPartial 13 5226) = some ⟨13, 2, 0, 17762, 5226, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_5226_17762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5226 ⟨17762, by decide⟩ :=
  accepted_of_selected 13 5226 ⟨17762, by decide⟩ ⟨13, 2, 0, 17762, 5226, 1953, 16384⟩
    (by decide) selected_cut_00348

theorem selected_cut_00349 : selected 8 ⟨17776, by decide⟩
    (prefixPartial 13 5227) = some ⟨13, 2, 0, 17776, 5227, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_5227_17776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5227 ⟨17776, by decide⟩ :=
  accepted_of_selected 13 5227 ⟨17776, by decide⟩ ⟨13, 2, 0, 17776, 5227, 1197, 16384⟩
    (by decide) selected_cut_00349

theorem unmarked_context_12_1306_17777 : frontier 9 ⟨17777, by decide⟩
    (prefixCache 12 1306) (prefixPartial 12 1306) = false := by
  decide +kernel

theorem node_context_12_1306_17777 : EJMOriginalGlobalDAGData.nodes 9 ⟨17777, by decide⟩ =
    .split (coordinate 12) (![⟨17676, by decide⟩,⟨17729, by decide⟩,⟨17762, by decide⟩,⟨17776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1306_17777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1306 ⟨17777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1306
    ⟨17777, by decide⟩ (by decide) (![⟨17676, by decide⟩,⟨17729, by decide⟩,⟨17762, by decide⟩,⟨17776, by decide⟩]) unmarked_context_12_1306_17777 node_context_12_1306_17777
  intro a
  fin_cases a
  · exact context_13_5224_17676
  · exact context_13_5225_17729
  · exact context_13_5226_17762
  · exact context_13_5227_17776

theorem selected_cut_00350 : selected 8 ⟨17819, by decide⟩
    (prefixPartial 13 5228) = some ⟨13, 2, 0, 17819, 5228, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_5228_17819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5228 ⟨17819, by decide⟩ :=
  accepted_of_selected 13 5228 ⟨17819, by decide⟩ ⟨13, 2, 0, 17819, 5228, 1513, 16384⟩
    (by decide) selected_cut_00350

theorem selected_cut_00351 : selected 8 ⟨17876, by decide⟩
    (prefixPartial 13 5229) = some ⟨13, 2, 0, 17876, 5229, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_5229_17876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5229 ⟨17876, by decide⟩ :=
  accepted_of_selected 13 5229 ⟨17876, by decide⟩ ⟨13, 2, 0, 17876, 5229, 2741, 16384⟩
    (by decide) selected_cut_00351

theorem selected_cut_00352 : selected 8 ⟨17917, by decide⟩
    (prefixPartial 13 5230) = some ⟨13, 2, 0, 17917, 5230, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_5230_17917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5230 ⟨17917, by decide⟩ :=
  accepted_of_selected 13 5230 ⟨17917, by decide⟩ ⟨13, 2, 0, 17917, 5230, 2313, 16384⟩
    (by decide) selected_cut_00352

theorem selected_cut_00353 : selected 8 ⟨17936, by decide⟩
    (prefixPartial 13 5231) = some ⟨13, 2, 0, 17936, 5231, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_5231_17936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5231 ⟨17936, by decide⟩ :=
  accepted_of_selected 13 5231 ⟨17936, by decide⟩ ⟨13, 2, 0, 17936, 5231, 1189, 16384⟩
    (by decide) selected_cut_00353

theorem unmarked_context_12_1307_17937 : frontier 9 ⟨17937, by decide⟩
    (prefixCache 12 1307) (prefixPartial 12 1307) = false := by
  decide +kernel

theorem node_context_12_1307_17937 : EJMOriginalGlobalDAGData.nodes 9 ⟨17937, by decide⟩ =
    .split (coordinate 12) (![⟨17819, by decide⟩,⟨17876, by decide⟩,⟨17917, by decide⟩,⟨17936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1307_17937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1307 ⟨17937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1307
    ⟨17937, by decide⟩ (by decide) (![⟨17819, by decide⟩,⟨17876, by decide⟩,⟨17917, by decide⟩,⟨17936, by decide⟩]) unmarked_context_12_1307_17937 node_context_12_1307_17937
  intro a
  fin_cases a
  · exact context_13_5228_17819
  · exact context_13_5229_17876
  · exact context_13_5230_17917
  · exact context_13_5231_17936

theorem unmarked_context_11_326_17938 : frontier 10 ⟨17938, by decide⟩
    (prefixCache 11 326) (prefixPartial 11 326) = false := by
  decide +kernel

theorem node_context_11_326_17938 : EJMOriginalGlobalDAGData.nodes 10 ⟨17938, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨17630, by decide⟩,⟨17777, by decide⟩,⟨17937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_326_17938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 326 ⟨17938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 326
    ⟨17938, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨17630, by decide⟩,⟨17777, by decide⟩,⟨17937, by decide⟩]) unmarked_context_11_326_17938 node_context_11_326_17938
  intro a
  fin_cases a
  · exact context_12_1304_1738
  · exact context_12_1305_17630
  · exact context_12_1306_17777
  · exact context_12_1307_17937

theorem selected_cut_00354 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 327) = some ⟨11, 1, 0, 1736, 327, 1, 262144⟩ := by
  decide +kernel

theorem context_11_327_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 327 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 327 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 327, 1, 262144⟩
    (by decide) selected_cut_00354

theorem unmarked_context_10_81_17939 : frontier 11 ⟨17939, by decide⟩
    (prefixCache 10 81) (prefixPartial 10 81) = false := by
  decide +kernel

theorem node_context_10_81_17939 : EJMOriginalGlobalDAGData.nodes 11 ⟨17939, by decide⟩ =
    .split (coordinate 10) (![⟨17015, by decide⟩,⟨17482, by decide⟩,⟨17938, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_81_17939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 81 ⟨17939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 81
    ⟨17939, by decide⟩ (by decide) (![⟨17015, by decide⟩,⟨17482, by decide⟩,⟨17938, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_81_17939 node_context_10_81_17939
  intro a
  fin_cases a
  · exact context_11_324_17015
  · exact context_11_325_17482
  · exact context_11_326_17938
  · exact context_11_327_1736

theorem selected_cut_00355 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1312) = some ⟨12, 1, 0, 1738, 1312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1312_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1312 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1312 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1312, 1, 65536⟩
    (by decide) selected_cut_00355

theorem selected_cut_00356 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1313) = some ⟨12, 1, 0, 1738, 1313, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1313_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1313 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1313 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1313, 1, 65536⟩
    (by decide) selected_cut_00356

theorem selected_cut_00357 : selected 8 ⟨17970, by decide⟩
    (prefixPartial 13 5256) = some ⟨13, 2, 0, 17970, 5256, 941, 16384⟩ := by
  decide +kernel

theorem context_13_5256_17970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5256 ⟨17970, by decide⟩ :=
  accepted_of_selected 13 5256 ⟨17970, by decide⟩ ⟨13, 2, 0, 17970, 5256, 941, 16384⟩
    (by decide) selected_cut_00357

theorem selected_cut_00358 : selected 8 ⟨18006, by decide⟩
    (prefixPartial 13 5257) = some ⟨13, 2, 0, 18006, 5257, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_5257_18006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5257 ⟨18006, by decide⟩ :=
  accepted_of_selected 13 5257 ⟨18006, by decide⟩ ⟨13, 2, 0, 18006, 5257, 1473, 16384⟩
    (by decide) selected_cut_00358

theorem selected_cut_00359 : selected 8 ⟨18045, by decide⟩
    (prefixPartial 13 5258) = some ⟨13, 2, 0, 18045, 5258, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_5258_18045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5258 ⟨18045, by decide⟩ :=
  accepted_of_selected 13 5258 ⟨18045, by decide⟩ ⟨13, 2, 0, 18045, 5258, 1381, 16384⟩
    (by decide) selected_cut_00359

theorem selected_cut_00360 : selected 8 ⟨18096, by decide⟩
    (prefixPartial 13 5259) = some ⟨13, 2, 0, 18096, 5259, 981, 16384⟩ := by
  decide +kernel

theorem context_13_5259_18096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5259 ⟨18096, by decide⟩ :=
  accepted_of_selected 13 5259 ⟨18096, by decide⟩ ⟨13, 2, 0, 18096, 5259, 981, 16384⟩
    (by decide) selected_cut_00360

theorem unmarked_context_12_1314_18097 : frontier 9 ⟨18097, by decide⟩
    (prefixCache 12 1314) (prefixPartial 12 1314) = false := by
  decide +kernel

theorem node_context_12_1314_18097 : EJMOriginalGlobalDAGData.nodes 9 ⟨18097, by decide⟩ =
    .split (coordinate 12) (![⟨17970, by decide⟩,⟨18006, by decide⟩,⟨18045, by decide⟩,⟨18096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1314_18097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1314 ⟨18097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1314
    ⟨18097, by decide⟩ (by decide) (![⟨17970, by decide⟩,⟨18006, by decide⟩,⟨18045, by decide⟩,⟨18096, by decide⟩]) unmarked_context_12_1314_18097 node_context_12_1314_18097
  intro a
  fin_cases a
  · exact context_13_5256_17970
  · exact context_13_5257_18006
  · exact context_13_5258_18045
  · exact context_13_5259_18096

theorem selected_cut_00361 : selected 9 ⟨18230, by decide⟩
    (prefixPartial 12 1315) = some ⟨12, 2, 0, 18230, 1315, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_1315_18230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1315 ⟨18230, by decide⟩ :=
  accepted_of_selected 12 1315 ⟨18230, by decide⟩ ⟨12, 2, 0, 18230, 1315, 3737, 65536⟩
    (by decide) selected_cut_00361

theorem unmarked_context_11_328_18231 : frontier 10 ⟨18231, by decide⟩
    (prefixCache 11 328) (prefixPartial 11 328) = false := by
  decide +kernel

theorem node_context_11_328_18231 : EJMOriginalGlobalDAGData.nodes 10 ⟨18231, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18097, by decide⟩,⟨18230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_328_18231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 328 ⟨18231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 328
    ⟨18231, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18097, by decide⟩,⟨18230, by decide⟩]) unmarked_context_11_328_18231 node_context_11_328_18231
  intro a
  fin_cases a
  · exact context_12_1312_1738
  · exact context_12_1313_1738
  · exact context_12_1314_18097
  · exact context_12_1315_18230

theorem selected_cut_00362 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1316) = some ⟨12, 1, 0, 1738, 1316, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1316_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1316 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1316 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1316, 1, 65536⟩
    (by decide) selected_cut_00362

theorem selected_cut_00363 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1317) = some ⟨12, 1, 0, 1738, 1317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1317_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1317 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1317 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1317, 1, 65536⟩
    (by decide) selected_cut_00363

theorem selected_cut_00364 : selected 8 ⟨18266, by decide⟩
    (prefixPartial 13 5272) = some ⟨13, 2, 0, 18266, 5272, 853, 16384⟩ := by
  decide +kernel

theorem context_13_5272_18266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5272 ⟨18266, by decide⟩ :=
  accepted_of_selected 13 5272 ⟨18266, by decide⟩ ⟨13, 2, 0, 18266, 5272, 853, 16384⟩
    (by decide) selected_cut_00364

theorem selected_cut_00365 : selected 8 ⟨18325, by decide⟩
    (prefixPartial 13 5273) = some ⟨13, 2, 0, 18325, 5273, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_5273_18325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5273 ⟨18325, by decide⟩ :=
  accepted_of_selected 13 5273 ⟨18325, by decide⟩ ⟨13, 2, 0, 18325, 5273, 2037, 16384⟩
    (by decide) selected_cut_00365

theorem selected_cut_00366 : selected 8 ⟨18360, by decide⟩
    (prefixPartial 13 5274) = some ⟨13, 2, 0, 18360, 5274, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_5274_18360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5274 ⟨18360, by decide⟩ :=
  accepted_of_selected 13 5274 ⟨18360, by decide⟩ ⟨13, 2, 0, 18360, 5274, 1549, 16384⟩
    (by decide) selected_cut_00366

theorem selected_cut_00367 : selected 8 ⟨18393, by decide⟩
    (prefixPartial 13 5275) = some ⟨13, 2, 0, 18393, 5275, 977, 16384⟩ := by
  decide +kernel

theorem context_13_5275_18393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5275 ⟨18393, by decide⟩ :=
  accepted_of_selected 13 5275 ⟨18393, by decide⟩ ⟨13, 2, 0, 18393, 5275, 977, 16384⟩
    (by decide) selected_cut_00367

theorem unmarked_context_12_1318_18394 : frontier 9 ⟨18394, by decide⟩
    (prefixCache 12 1318) (prefixPartial 12 1318) = false := by
  decide +kernel

theorem node_context_12_1318_18394 : EJMOriginalGlobalDAGData.nodes 9 ⟨18394, by decide⟩ =
    .split (coordinate 12) (![⟨18266, by decide⟩,⟨18325, by decide⟩,⟨18360, by decide⟩,⟨18393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1318_18394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1318 ⟨18394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1318
    ⟨18394, by decide⟩ (by decide) (![⟨18266, by decide⟩,⟨18325, by decide⟩,⟨18360, by decide⟩,⟨18393, by decide⟩]) unmarked_context_12_1318_18394 node_context_12_1318_18394
  intro a
  fin_cases a
  · exact context_13_5272_18266
  · exact context_13_5273_18325
  · exact context_13_5274_18360
  · exact context_13_5275_18393

theorem selected_cut_00368 : selected 8 ⟨18413, by decide⟩
    (prefixPartial 13 5276) = some ⟨13, 2, 0, 18413, 5276, 461, 16384⟩ := by
  decide +kernel

theorem context_13_5276_18413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5276 ⟨18413, by decide⟩ :=
  accepted_of_selected 13 5276 ⟨18413, by decide⟩ ⟨13, 2, 0, 18413, 5276, 461, 16384⟩
    (by decide) selected_cut_00368

theorem selected_cut_00369 : selected 8 ⟨18456, by decide⟩
    (prefixPartial 13 5277) = some ⟨13, 2, 0, 18456, 5277, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_5277_18456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5277 ⟨18456, by decide⟩ :=
  accepted_of_selected 13 5277 ⟨18456, by decide⟩ ⟨13, 2, 0, 18456, 5277, 1541, 16384⟩
    (by decide) selected_cut_00369

theorem selected_cut_00370 : selected 8 ⟨18520, by decide⟩
    (prefixPartial 13 5278) = some ⟨13, 2, 0, 18520, 5278, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_5278_18520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5278 ⟨18520, by decide⟩ :=
  accepted_of_selected 13 5278 ⟨18520, by decide⟩ ⟨13, 2, 0, 18520, 5278, 2265, 16384⟩
    (by decide) selected_cut_00370

theorem selected_cut_00371 : selected 8 ⟨4592, by decide⟩
    (prefixPartial 13 5279) = some ⟨13, 1, 0, 4592, 5279, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5279_4592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5279 ⟨4592, by decide⟩ :=
  accepted_of_selected 13 5279 ⟨4592, by decide⟩ ⟨13, 1, 0, 4592, 5279, 1, 16384⟩
    (by decide) selected_cut_00371

theorem unmarked_context_12_1319_18521 : frontier 9 ⟨18521, by decide⟩
    (prefixCache 12 1319) (prefixPartial 12 1319) = false := by
  decide +kernel

theorem node_context_12_1319_18521 : EJMOriginalGlobalDAGData.nodes 9 ⟨18521, by decide⟩ =
    .split (coordinate 12) (![⟨18413, by decide⟩,⟨18456, by decide⟩,⟨18520, by decide⟩,⟨4592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1319_18521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1319 ⟨18521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1319
    ⟨18521, by decide⟩ (by decide) (![⟨18413, by decide⟩,⟨18456, by decide⟩,⟨18520, by decide⟩,⟨4592, by decide⟩]) unmarked_context_12_1319_18521 node_context_12_1319_18521
  intro a
  fin_cases a
  · exact context_13_5276_18413
  · exact context_13_5277_18456
  · exact context_13_5278_18520
  · exact context_13_5279_4592

theorem unmarked_context_11_329_18522 : frontier 10 ⟨18522, by decide⟩
    (prefixCache 11 329) (prefixPartial 11 329) = false := by
  decide +kernel

theorem node_context_11_329_18522 : EJMOriginalGlobalDAGData.nodes 10 ⟨18522, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18394, by decide⟩,⟨18521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_329_18522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 329 ⟨18522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 329
    ⟨18522, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18394, by decide⟩,⟨18521, by decide⟩]) unmarked_context_11_329_18522 node_context_11_329_18522
  intro a
  fin_cases a
  · exact context_12_1316_1738
  · exact context_12_1317_1738
  · exact context_12_1318_18394
  · exact context_12_1319_18521

theorem selected_cut_00372 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1320) = some ⟨12, 1, 0, 1738, 1320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1320_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1320 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1320 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1320, 1, 65536⟩
    (by decide) selected_cut_00372

theorem selected_cut_00373 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1321) = some ⟨12, 1, 0, 1738, 1321, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1321_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1321 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1321 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1321, 1, 65536⟩
    (by decide) selected_cut_00373

theorem selected_cut_00374 : selected 8 ⟨18544, by decide⟩
    (prefixPartial 13 5288) = some ⟨13, 2, 0, 18544, 5288, 497, 16384⟩ := by
  decide +kernel

theorem context_13_5288_18544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5288 ⟨18544, by decide⟩ :=
  accepted_of_selected 13 5288 ⟨18544, by decide⟩ ⟨13, 2, 0, 18544, 5288, 497, 16384⟩
    (by decide) selected_cut_00374

theorem selected_cut_00375 : selected 8 ⟨18592, by decide⟩
    (prefixPartial 13 5289) = some ⟨13, 2, 0, 18592, 5289, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_5289_18592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5289 ⟨18592, by decide⟩ :=
  accepted_of_selected 13 5289 ⟨18592, by decide⟩ ⟨13, 2, 0, 18592, 5289, 1801, 16384⟩
    (by decide) selected_cut_00375

theorem selected_cut_00376 : selected 8 ⟨18626, by decide⟩
    (prefixPartial 13 5290) = some ⟨13, 2, 0, 18626, 5290, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_5290_18626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5290 ⟨18626, by decide⟩ :=
  accepted_of_selected 13 5290 ⟨18626, by decide⟩ ⟨13, 2, 0, 18626, 5290, 1373, 16384⟩
    (by decide) selected_cut_00376

theorem selected_cut_00377 : selected 8 ⟨18653, by decide⟩
    (prefixPartial 13 5291) = some ⟨13, 2, 0, 18653, 5291, 977, 16384⟩ := by
  decide +kernel

theorem context_13_5291_18653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5291 ⟨18653, by decide⟩ :=
  accepted_of_selected 13 5291 ⟨18653, by decide⟩ ⟨13, 2, 0, 18653, 5291, 977, 16384⟩
    (by decide) selected_cut_00377

theorem unmarked_context_12_1322_18654 : frontier 9 ⟨18654, by decide⟩
    (prefixCache 12 1322) (prefixPartial 12 1322) = false := by
  decide +kernel

theorem node_context_12_1322_18654 : EJMOriginalGlobalDAGData.nodes 9 ⟨18654, by decide⟩ =
    .split (coordinate 12) (![⟨18544, by decide⟩,⟨18592, by decide⟩,⟨18626, by decide⟩,⟨18653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1322_18654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1322 ⟨18654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1322
    ⟨18654, by decide⟩ (by decide) (![⟨18544, by decide⟩,⟨18592, by decide⟩,⟨18626, by decide⟩,⟨18653, by decide⟩]) unmarked_context_12_1322_18654 node_context_12_1322_18654
  intro a
  fin_cases a
  · exact context_13_5288_18544
  · exact context_13_5289_18592
  · exact context_13_5290_18626
  · exact context_13_5291_18653

theorem selected_cut_00378 : selected 8 ⟨18671, by decide⟩
    (prefixPartial 13 5292) = some ⟨13, 2, 0, 18671, 5292, 425, 16384⟩ := by
  decide +kernel

theorem context_13_5292_18671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5292 ⟨18671, by decide⟩ :=
  accepted_of_selected 13 5292 ⟨18671, by decide⟩ ⟨13, 2, 0, 18671, 5292, 425, 16384⟩
    (by decide) selected_cut_00378

theorem selected_cut_00379 : selected 8 ⟨18733, by decide⟩
    (prefixPartial 13 5293) = some ⟨13, 2, 0, 18733, 5293, 2845, 16384⟩ := by
  decide +kernel

theorem context_13_5293_18733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5293 ⟨18733, by decide⟩ :=
  accepted_of_selected 13 5293 ⟨18733, by decide⟩ ⟨13, 2, 0, 18733, 5293, 2845, 16384⟩
    (by decide) selected_cut_00379

theorem selected_cut_00380 : selected 8 ⟨18770, by decide⟩
    (prefixPartial 13 5294) = some ⟨13, 2, 0, 18770, 5294, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_5294_18770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5294 ⟨18770, by decide⟩ :=
  accepted_of_selected 13 5294 ⟨18770, by decide⟩ ⟨13, 2, 0, 18770, 5294, 2245, 16384⟩
    (by decide) selected_cut_00380

theorem selected_cut_00381 : selected 8 ⟨18786, by decide⟩
    (prefixPartial 13 5295) = some ⟨13, 2, 0, 18786, 5295, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_5295_18786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5295 ⟨18786, by decide⟩ :=
  accepted_of_selected 13 5295 ⟨18786, by decide⟩ ⟨13, 2, 0, 18786, 5295, 1217, 16384⟩
    (by decide) selected_cut_00381

theorem unmarked_context_12_1323_18787 : frontier 9 ⟨18787, by decide⟩
    (prefixCache 12 1323) (prefixPartial 12 1323) = false := by
  decide +kernel

theorem node_context_12_1323_18787 : EJMOriginalGlobalDAGData.nodes 9 ⟨18787, by decide⟩ =
    .split (coordinate 12) (![⟨18671, by decide⟩,⟨18733, by decide⟩,⟨18770, by decide⟩,⟨18786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1323_18787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1323 ⟨18787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1323
    ⟨18787, by decide⟩ (by decide) (![⟨18671, by decide⟩,⟨18733, by decide⟩,⟨18770, by decide⟩,⟨18786, by decide⟩]) unmarked_context_12_1323_18787 node_context_12_1323_18787
  intro a
  fin_cases a
  · exact context_13_5292_18671
  · exact context_13_5293_18733
  · exact context_13_5294_18770
  · exact context_13_5295_18786

theorem unmarked_context_11_330_18788 : frontier 10 ⟨18788, by decide⟩
    (prefixCache 11 330) (prefixPartial 11 330) = false := by
  decide +kernel

theorem node_context_11_330_18788 : EJMOriginalGlobalDAGData.nodes 10 ⟨18788, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18654, by decide⟩,⟨18787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_330_18788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 330 ⟨18788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 330
    ⟨18788, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18654, by decide⟩,⟨18787, by decide⟩]) unmarked_context_11_330_18788 node_context_11_330_18788
  intro a
  fin_cases a
  · exact context_12_1320_1738
  · exact context_12_1321_1738
  · exact context_12_1322_18654
  · exact context_12_1323_18787

theorem selected_cut_00382 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1324) = some ⟨12, 1, 0, 1738, 1324, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1324_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1324 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1324 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1324, 1, 65536⟩
    (by decide) selected_cut_00382

theorem selected_cut_00383 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1325) = some ⟨12, 1, 0, 1738, 1325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1325_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1325 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1325 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1325, 1, 65536⟩
    (by decide) selected_cut_00383

theorem selected_cut_00384 : selected 8 ⟨18801, by decide⟩
    (prefixPartial 13 5304) = some ⟨13, 2, 0, 18801, 5304, 209, 16384⟩ := by
  decide +kernel

theorem context_13_5304_18801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5304 ⟨18801, by decide⟩ :=
  accepted_of_selected 13 5304 ⟨18801, by decide⟩ ⟨13, 2, 0, 18801, 5304, 209, 16384⟩
    (by decide) selected_cut_00384

theorem selected_cut_00385 : selected 8 ⟨18872, by decide⟩
    (prefixPartial 13 5305) = some ⟨13, 2, 0, 18872, 5305, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_5305_18872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5305 ⟨18872, by decide⟩ :=
  accepted_of_selected 13 5305 ⟨18872, by decide⟩ ⟨13, 2, 0, 18872, 5305, 2473, 16384⟩
    (by decide) selected_cut_00385

theorem selected_cut_00386 : selected 8 ⟨18915, by decide⟩
    (prefixPartial 13 5306) = some ⟨13, 2, 0, 18915, 5306, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_5306_18915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5306 ⟨18915, by decide⟩ :=
  accepted_of_selected 13 5306 ⟨18915, by decide⟩ ⟨13, 2, 0, 18915, 5306, 1941, 16384⟩
    (by decide) selected_cut_00386

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
