/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover408
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_4731_1064723 : frontier 12 ⟨1064723, by decide⟩
    (prefixCache 9 4731) (prefixPartial 9 4731) = false := by
  decide +kernel

theorem node_context_9_4731_1064723 : EJMOriginalGlobalDAGData.nodes 12 ⟨1064723, by decide⟩ =
    .split (coordinate 9) (![⟨1064574, by decide⟩,⟨1064640, by decide⟩,⟨1064691, by decide⟩,⟨1064722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4731_1064723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4731 ⟨1064723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4731
    ⟨1064723, by decide⟩ (by decide) (![⟨1064574, by decide⟩,⟨1064640, by decide⟩,⟨1064691, by decide⟩,⟨1064722, by decide⟩]) unmarked_context_9_4731_1064723 node_context_9_4731_1064723
  intro a
  fin_cases a
  · exact context_10_18924_1064574
  · exact context_10_18925_1064640
  · exact context_10_18926_1064691
  · exact context_10_18927_1064722

theorem unmarked_context_8_1182_1064724 : frontier 13 ⟨1064724, by decide⟩
    (prefixCache 8 1182) (prefixPartial 8 1182) = false := by
  decide +kernel

theorem node_context_8_1182_1064724 : EJMOriginalGlobalDAGData.nodes 13 ⟨1064724, by decide⟩ =
    .split (coordinate 8) (![⟨1062217, by decide⟩,⟨1063718, by decide⟩,⟨1064437, by decide⟩,⟨1064723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1182_1064724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1182 ⟨1064724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1182
    ⟨1064724, by decide⟩ (by decide) (![⟨1062217, by decide⟩,⟨1063718, by decide⟩,⟨1064437, by decide⟩,⟨1064723, by decide⟩]) unmarked_context_8_1182_1064724 node_context_8_1182_1064724
  intro a
  fin_cases a
  · exact context_9_4728_1062217
  · exact context_9_4729_1063718
  · exact context_9_4730_1064437
  · exact context_9_4731_1064723

theorem selected_cut_39268 : selected 10 ⟨1064787, by decide⟩
    (prefixPartial 11 75712) = some ⟨11, 2, 0, 1064787, 75712, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_75712_1064787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75712 ⟨1064787, by decide⟩ :=
  accepted_of_selected 11 75712 ⟨1064787, by decide⟩ ⟨11, 2, 0, 1064787, 75712, 3957, 262144⟩
    (by decide) selected_cut_39268

theorem selected_cut_39269 : selected 8 ⟨1064825, by decide⟩
    (prefixPartial 13 1211408) = some ⟨13, 2, 0, 1064825, 1211408, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_1211408_1064825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211408 ⟨1064825, by decide⟩ :=
  accepted_of_selected 13 1211408 ⟨1064825, by decide⟩ ⟨13, 2, 0, 1064825, 1211408, 1665, 16384⟩
    (by decide) selected_cut_39269

theorem selected_cut_39270 : selected 8 ⟨1064862, by decide⟩
    (prefixPartial 13 1211409) = some ⟨13, 2, 0, 1064862, 1211409, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_1211409_1064862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211409 ⟨1064862, by decide⟩ :=
  accepted_of_selected 13 1211409 ⟨1064862, by decide⟩ ⟨13, 2, 0, 1064862, 1211409, 1345, 16384⟩
    (by decide) selected_cut_39270

theorem selected_cut_39271 : selected 8 ⟨1064894, by decide⟩
    (prefixPartial 13 1211410) = some ⟨13, 2, 0, 1064894, 1211410, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_1211410_1064894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211410 ⟨1064894, by decide⟩ :=
  accepted_of_selected 13 1211410 ⟨1064894, by decide⟩ ⟨13, 2, 0, 1064894, 1211410, 1009, 16384⟩
    (by decide) selected_cut_39271

theorem selected_cut_39272 : selected 8 ⟨1064899, by decide⟩
    (prefixPartial 13 1211411) = some ⟨13, 2, 0, 1064899, 1211411, 533, 16384⟩ := by
  decide +kernel

theorem context_13_1211411_1064899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211411 ⟨1064899, by decide⟩ :=
  accepted_of_selected 13 1211411 ⟨1064899, by decide⟩ ⟨13, 2, 0, 1064899, 1211411, 533, 16384⟩
    (by decide) selected_cut_39272

theorem unmarked_context_12_302852_1064900 : frontier 9 ⟨1064900, by decide⟩
    (prefixCache 12 302852) (prefixPartial 12 302852) = false := by
  decide +kernel

theorem node_context_12_302852_1064900 : EJMOriginalGlobalDAGData.nodes 9 ⟨1064900, by decide⟩ =
    .split (coordinate 12) (![⟨1064825, by decide⟩,⟨1064862, by decide⟩,⟨1064894, by decide⟩,⟨1064899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302852_1064900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302852 ⟨1064900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302852
    ⟨1064900, by decide⟩ (by decide) (![⟨1064825, by decide⟩,⟨1064862, by decide⟩,⟨1064894, by decide⟩,⟨1064899, by decide⟩]) unmarked_context_12_302852_1064900 node_context_12_302852_1064900
  intro a
  fin_cases a
  · exact context_13_1211408_1064825
  · exact context_13_1211409_1064862
  · exact context_13_1211410_1064894
  · exact context_13_1211411_1064899

theorem selected_cut_39273 : selected 8 ⟨1064945, by decide⟩
    (prefixPartial 13 1211412) = some ⟨13, 2, 0, 1064945, 1211412, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_1211412_1064945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211412 ⟨1064945, by decide⟩ :=
  accepted_of_selected 13 1211412 ⟨1064945, by decide⟩ ⟨13, 2, 0, 1064945, 1211412, 2025, 16384⟩
    (by decide) selected_cut_39273

theorem selected_cut_39274 : selected 8 ⟨1064963, by decide⟩
    (prefixPartial 13 1211413) = some ⟨13, 2, 0, 1064963, 1211413, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_1211413_1064963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211413 ⟨1064963, by decide⟩ :=
  accepted_of_selected 13 1211413 ⟨1064963, by decide⟩ ⟨13, 2, 0, 1064963, 1211413, 1337, 16384⟩
    (by decide) selected_cut_39274

theorem selected_cut_39275 : selected 8 ⟨1064982, by decide⟩
    (prefixPartial 13 1211414) = some ⟨13, 2, 0, 1064982, 1211414, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_1211414_1064982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211414 ⟨1064982, by decide⟩ :=
  accepted_of_selected 13 1211414 ⟨1064982, by decide⟩ ⟨13, 2, 0, 1064982, 1211414, 1005, 16384⟩
    (by decide) selected_cut_39275

theorem selected_cut_39276 : selected 8 ⟨1064986, by decide⟩
    (prefixPartial 13 1211415) = some ⟨13, 2, 0, 1064986, 1211415, 465, 16384⟩ := by
  decide +kernel

theorem context_13_1211415_1064986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211415 ⟨1064986, by decide⟩ :=
  accepted_of_selected 13 1211415 ⟨1064986, by decide⟩ ⟨13, 2, 0, 1064986, 1211415, 465, 16384⟩
    (by decide) selected_cut_39276

theorem unmarked_context_12_302853_1064987 : frontier 9 ⟨1064987, by decide⟩
    (prefixCache 12 302853) (prefixPartial 12 302853) = false := by
  decide +kernel

theorem node_context_12_302853_1064987 : EJMOriginalGlobalDAGData.nodes 9 ⟨1064987, by decide⟩ =
    .split (coordinate 12) (![⟨1064945, by decide⟩,⟨1064963, by decide⟩,⟨1064982, by decide⟩,⟨1064986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302853_1064987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302853 ⟨1064987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302853
    ⟨1064987, by decide⟩ (by decide) (![⟨1064945, by decide⟩,⟨1064963, by decide⟩,⟨1064982, by decide⟩,⟨1064986, by decide⟩]) unmarked_context_12_302853_1064987 node_context_12_302853_1064987
  intro a
  fin_cases a
  · exact context_13_1211412_1064945
  · exact context_13_1211413_1064963
  · exact context_13_1211414_1064982
  · exact context_13_1211415_1064986

theorem selected_cut_39277 : selected 8 ⟨1065025, by decide⟩
    (prefixPartial 13 1211416) = some ⟨13, 2, 0, 1065025, 1211416, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_1211416_1065025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211416 ⟨1065025, by decide⟩ :=
  accepted_of_selected 13 1211416 ⟨1065025, by decide⟩ ⟨13, 2, 0, 1065025, 1211416, 1809, 16384⟩
    (by decide) selected_cut_39277

theorem selected_cut_39278 : selected 8 ⟨1065044, by decide⟩
    (prefixPartial 13 1211417) = some ⟨13, 2, 0, 1065044, 1211417, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_1211417_1065044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211417 ⟨1065044, by decide⟩ :=
  accepted_of_selected 13 1211417 ⟨1065044, by decide⟩ ⟨13, 2, 0, 1065044, 1211417, 1185, 16384⟩
    (by decide) selected_cut_39278

theorem selected_cut_39279 : selected 8 ⟨1065062, by decide⟩
    (prefixPartial 13 1211418) = some ⟨13, 2, 0, 1065062, 1211418, 837, 16384⟩ := by
  decide +kernel

theorem context_13_1211418_1065062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211418 ⟨1065062, by decide⟩ :=
  accepted_of_selected 13 1211418 ⟨1065062, by decide⟩ ⟨13, 2, 0, 1065062, 1211418, 837, 16384⟩
    (by decide) selected_cut_39279

theorem selected_cut_39280 : selected 8 ⟨1065069, by decide⟩
    (prefixPartial 13 1211419) = some ⟨13, 2, 0, 1065069, 1211419, 469, 16384⟩ := by
  decide +kernel

theorem context_13_1211419_1065069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211419 ⟨1065069, by decide⟩ :=
  accepted_of_selected 13 1211419 ⟨1065069, by decide⟩ ⟨13, 2, 0, 1065069, 1211419, 469, 16384⟩
    (by decide) selected_cut_39280

theorem unmarked_context_12_302854_1065070 : frontier 9 ⟨1065070, by decide⟩
    (prefixCache 12 302854) (prefixPartial 12 302854) = false := by
  decide +kernel

theorem node_context_12_302854_1065070 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065070, by decide⟩ =
    .split (coordinate 12) (![⟨1065025, by decide⟩,⟨1065044, by decide⟩,⟨1065062, by decide⟩,⟨1065069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302854_1065070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302854 ⟨1065070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302854
    ⟨1065070, by decide⟩ (by decide) (![⟨1065025, by decide⟩,⟨1065044, by decide⟩,⟨1065062, by decide⟩,⟨1065069, by decide⟩]) unmarked_context_12_302854_1065070 node_context_12_302854_1065070
  intro a
  fin_cases a
  · exact context_13_1211416_1065025
  · exact context_13_1211417_1065044
  · exact context_13_1211418_1065062
  · exact context_13_1211419_1065069

theorem selected_cut_39281 : selected 8 ⟨1065094, by decide⟩
    (prefixPartial 13 1211420) = some ⟨13, 2, 0, 1065094, 1211420, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_1211420_1065094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211420 ⟨1065094, by decide⟩ :=
  accepted_of_selected 13 1211420 ⟨1065094, by decide⟩ ⟨13, 2, 0, 1065094, 1211420, 1609, 16384⟩
    (by decide) selected_cut_39281

theorem selected_cut_39282 : selected 8 ⟨1065116, by decide⟩
    (prefixPartial 13 1211421) = some ⟨13, 2, 0, 1065116, 1211421, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_1211421_1065116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211421 ⟨1065116, by decide⟩ :=
  accepted_of_selected 13 1211421 ⟨1065116, by decide⟩ ⟨13, 2, 0, 1065116, 1211421, 1265, 16384⟩
    (by decide) selected_cut_39282

theorem selected_cut_39283 : selected 8 ⟨1065130, by decide⟩
    (prefixPartial 13 1211422) = some ⟨13, 2, 0, 1065130, 1211422, 921, 16384⟩ := by
  decide +kernel

theorem context_13_1211422_1065130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211422 ⟨1065130, by decide⟩ :=
  accepted_of_selected 13 1211422 ⟨1065130, by decide⟩ ⟨13, 2, 0, 1065130, 1211422, 921, 16384⟩
    (by decide) selected_cut_39283

theorem selected_cut_39284 : selected 8 ⟨1065136, by decide⟩
    (prefixPartial 13 1211423) = some ⟨13, 2, 0, 1065136, 1211423, 561, 16384⟩ := by
  decide +kernel

theorem context_13_1211423_1065136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211423 ⟨1065136, by decide⟩ :=
  accepted_of_selected 13 1211423 ⟨1065136, by decide⟩ ⟨13, 2, 0, 1065136, 1211423, 561, 16384⟩
    (by decide) selected_cut_39284

theorem unmarked_context_12_302855_1065137 : frontier 9 ⟨1065137, by decide⟩
    (prefixCache 12 302855) (prefixPartial 12 302855) = false := by
  decide +kernel

theorem node_context_12_302855_1065137 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065137, by decide⟩ =
    .split (coordinate 12) (![⟨1065094, by decide⟩,⟨1065116, by decide⟩,⟨1065130, by decide⟩,⟨1065136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302855_1065137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302855 ⟨1065137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302855
    ⟨1065137, by decide⟩ (by decide) (![⟨1065094, by decide⟩,⟨1065116, by decide⟩,⟨1065130, by decide⟩,⟨1065136, by decide⟩]) unmarked_context_12_302855_1065137 node_context_12_302855_1065137
  intro a
  fin_cases a
  · exact context_13_1211420_1065094
  · exact context_13_1211421_1065116
  · exact context_13_1211422_1065130
  · exact context_13_1211423_1065136

theorem unmarked_context_11_75713_1065138 : frontier 10 ⟨1065138, by decide⟩
    (prefixCache 11 75713) (prefixPartial 11 75713) = false := by
  decide +kernel

theorem node_context_11_75713_1065138 : EJMOriginalGlobalDAGData.nodes 10 ⟨1065138, by decide⟩ =
    .split (coordinate 11) (![⟨1064900, by decide⟩,⟨1064987, by decide⟩,⟨1065070, by decide⟩,⟨1065137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75713_1065138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75713 ⟨1065138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75713
    ⟨1065138, by decide⟩ (by decide) (![⟨1064900, by decide⟩,⟨1064987, by decide⟩,⟨1065070, by decide⟩,⟨1065137, by decide⟩]) unmarked_context_11_75713_1065138 node_context_11_75713_1065138
  intro a
  fin_cases a
  · exact context_12_302852_1064900
  · exact context_12_302853_1064987
  · exact context_12_302854_1065070
  · exact context_12_302855_1065137

theorem selected_cut_39285 : selected 9 ⟨1065229, by decide⟩
    (prefixPartial 12 302856) = some ⟨12, 2, 0, 1065229, 302856, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_302856_1065229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302856 ⟨1065229, by decide⟩ :=
  accepted_of_selected 12 302856 ⟨1065229, by decide⟩ ⟨12, 2, 0, 1065229, 302856, 2701, 65536⟩
    (by decide) selected_cut_39285

theorem selected_cut_39286 : selected 8 ⟨1065277, by decide⟩
    (prefixPartial 13 1211428) = some ⟨13, 2, 0, 1065277, 1211428, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_1211428_1065277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211428 ⟨1065277, by decide⟩ :=
  accepted_of_selected 13 1211428 ⟨1065277, by decide⟩ ⟨13, 2, 0, 1065277, 1211428, 1965, 16384⟩
    (by decide) selected_cut_39286

theorem selected_cut_39287 : selected 8 ⟨1065302, by decide⟩
    (prefixPartial 13 1211429) = some ⟨13, 2, 0, 1065302, 1211429, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_1211429_1065302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211429 ⟨1065302, by decide⟩ :=
  accepted_of_selected 13 1211429 ⟨1065302, by decide⟩ ⟨13, 2, 0, 1065302, 1211429, 1477, 16384⟩
    (by decide) selected_cut_39287

theorem selected_cut_39288 : selected 8 ⟨1065330, by decide⟩
    (prefixPartial 13 1211430) = some ⟨13, 2, 0, 1065330, 1211430, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_1211430_1065330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211430 ⟨1065330, by decide⟩ :=
  accepted_of_selected 13 1211430 ⟨1065330, by decide⟩ ⟨13, 2, 0, 1065330, 1211430, 1077, 16384⟩
    (by decide) selected_cut_39288

theorem selected_cut_39289 : selected 8 ⟨1065339, by decide⟩
    (prefixPartial 13 1211431) = some ⟨13, 2, 0, 1065339, 1211431, 513, 16384⟩ := by
  decide +kernel

theorem context_13_1211431_1065339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211431 ⟨1065339, by decide⟩ :=
  accepted_of_selected 13 1211431 ⟨1065339, by decide⟩ ⟨13, 2, 0, 1065339, 1211431, 513, 16384⟩
    (by decide) selected_cut_39289

theorem unmarked_context_12_302857_1065340 : frontier 9 ⟨1065340, by decide⟩
    (prefixCache 12 302857) (prefixPartial 12 302857) = false := by
  decide +kernel

theorem node_context_12_302857_1065340 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065340, by decide⟩ =
    .split (coordinate 12) (![⟨1065277, by decide⟩,⟨1065302, by decide⟩,⟨1065330, by decide⟩,⟨1065339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302857_1065340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302857 ⟨1065340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302857
    ⟨1065340, by decide⟩ (by decide) (![⟨1065277, by decide⟩,⟨1065302, by decide⟩,⟨1065330, by decide⟩,⟨1065339, by decide⟩]) unmarked_context_12_302857_1065340 node_context_12_302857_1065340
  intro a
  fin_cases a
  · exact context_13_1211428_1065277
  · exact context_13_1211429_1065302
  · exact context_13_1211430_1065330
  · exact context_13_1211431_1065339

theorem selected_cut_39290 : selected 8 ⟨1065374, by decide⟩
    (prefixPartial 13 1211432) = some ⟨13, 2, 0, 1065374, 1211432, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_1211432_1065374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211432 ⟨1065374, by decide⟩ :=
  accepted_of_selected 13 1211432 ⟨1065374, by decide⟩ ⟨13, 2, 0, 1065374, 1211432, 1673, 16384⟩
    (by decide) selected_cut_39290

theorem selected_cut_39291 : selected 8 ⟨1065399, by decide⟩
    (prefixPartial 13 1211433) = some ⟨13, 2, 0, 1065399, 1211433, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_1211433_1065399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211433 ⟨1065399, by decide⟩ :=
  accepted_of_selected 13 1211433 ⟨1065399, by decide⟩ ⟨13, 2, 0, 1065399, 1211433, 1425, 16384⟩
    (by decide) selected_cut_39291

theorem selected_cut_39292 : selected 8 ⟨1065416, by decide⟩
    (prefixPartial 13 1211434) = some ⟨13, 2, 0, 1065416, 1211434, 957, 16384⟩ := by
  decide +kernel

theorem context_13_1211434_1065416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211434 ⟨1065416, by decide⟩ :=
  accepted_of_selected 13 1211434 ⟨1065416, by decide⟩ ⟨13, 2, 0, 1065416, 1211434, 957, 16384⟩
    (by decide) selected_cut_39292

theorem selected_cut_39293 : selected 8 ⟨1065422, by decide⟩
    (prefixPartial 13 1211435) = some ⟨13, 2, 0, 1065422, 1211435, 493, 16384⟩ := by
  decide +kernel

theorem context_13_1211435_1065422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211435 ⟨1065422, by decide⟩ :=
  accepted_of_selected 13 1211435 ⟨1065422, by decide⟩ ⟨13, 2, 0, 1065422, 1211435, 493, 16384⟩
    (by decide) selected_cut_39293

theorem unmarked_context_12_302858_1065423 : frontier 9 ⟨1065423, by decide⟩
    (prefixCache 12 302858) (prefixPartial 12 302858) = false := by
  decide +kernel

theorem node_context_12_302858_1065423 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065423, by decide⟩ =
    .split (coordinate 12) (![⟨1065374, by decide⟩,⟨1065399, by decide⟩,⟨1065416, by decide⟩,⟨1065422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302858_1065423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302858 ⟨1065423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302858
    ⟨1065423, by decide⟩ (by decide) (![⟨1065374, by decide⟩,⟨1065399, by decide⟩,⟨1065416, by decide⟩,⟨1065422, by decide⟩]) unmarked_context_12_302858_1065423 node_context_12_302858_1065423
  intro a
  fin_cases a
  · exact context_13_1211432_1065374
  · exact context_13_1211433_1065399
  · exact context_13_1211434_1065416
  · exact context_13_1211435_1065422

theorem selected_cut_39294 : selected 8 ⟨1065452, by decide⟩
    (prefixPartial 13 1211436) = some ⟨13, 2, 0, 1065452, 1211436, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_1211436_1065452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211436 ⟨1065452, by decide⟩ :=
  accepted_of_selected 13 1211436 ⟨1065452, by decide⟩ ⟨13, 2, 0, 1065452, 1211436, 1633, 16384⟩
    (by decide) selected_cut_39294

theorem selected_cut_39295 : selected 8 ⟨1065471, by decide⟩
    (prefixPartial 13 1211437) = some ⟨13, 2, 0, 1065471, 1211437, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_1211437_1065471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211437 ⟨1065471, by decide⟩ :=
  accepted_of_selected 13 1211437 ⟨1065471, by decide⟩ ⟨13, 2, 0, 1065471, 1211437, 1513, 16384⟩
    (by decide) selected_cut_39295

theorem selected_cut_39296 : selected 8 ⟨1065488, by decide⟩
    (prefixPartial 13 1211438) = some ⟨13, 2, 0, 1065488, 1211438, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_1211438_1065488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211438 ⟨1065488, by decide⟩ :=
  accepted_of_selected 13 1211438 ⟨1065488, by decide⟩ ⟨13, 2, 0, 1065488, 1211438, 1021, 16384⟩
    (by decide) selected_cut_39296

theorem selected_cut_39297 : selected 8 ⟨1065494, by decide⟩
    (prefixPartial 13 1211439) = some ⟨13, 2, 0, 1065494, 1211439, 609, 16384⟩ := by
  decide +kernel

theorem context_13_1211439_1065494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211439 ⟨1065494, by decide⟩ :=
  accepted_of_selected 13 1211439 ⟨1065494, by decide⟩ ⟨13, 2, 0, 1065494, 1211439, 609, 16384⟩
    (by decide) selected_cut_39297

theorem unmarked_context_12_302859_1065495 : frontier 9 ⟨1065495, by decide⟩
    (prefixCache 12 302859) (prefixPartial 12 302859) = false := by
  decide +kernel

theorem node_context_12_302859_1065495 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065495, by decide⟩ =
    .split (coordinate 12) (![⟨1065452, by decide⟩,⟨1065471, by decide⟩,⟨1065488, by decide⟩,⟨1065494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302859_1065495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302859 ⟨1065495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302859
    ⟨1065495, by decide⟩ (by decide) (![⟨1065452, by decide⟩,⟨1065471, by decide⟩,⟨1065488, by decide⟩,⟨1065494, by decide⟩]) unmarked_context_12_302859_1065495 node_context_12_302859_1065495
  intro a
  fin_cases a
  · exact context_13_1211436_1065452
  · exact context_13_1211437_1065471
  · exact context_13_1211438_1065488
  · exact context_13_1211439_1065494

theorem unmarked_context_11_75714_1065496 : frontier 10 ⟨1065496, by decide⟩
    (prefixCache 11 75714) (prefixPartial 11 75714) = false := by
  decide +kernel

theorem node_context_11_75714_1065496 : EJMOriginalGlobalDAGData.nodes 10 ⟨1065496, by decide⟩ =
    .split (coordinate 11) (![⟨1065229, by decide⟩,⟨1065340, by decide⟩,⟨1065423, by decide⟩,⟨1065495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75714_1065496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75714 ⟨1065496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75714
    ⟨1065496, by decide⟩ (by decide) (![⟨1065229, by decide⟩,⟨1065340, by decide⟩,⟨1065423, by decide⟩,⟨1065495, by decide⟩]) unmarked_context_11_75714_1065496 node_context_11_75714_1065496
  intro a
  fin_cases a
  · exact context_12_302856_1065229
  · exact context_12_302857_1065340
  · exact context_12_302858_1065423
  · exact context_12_302859_1065495

theorem selected_cut_39298 : selected 8 ⟨1065521, by decide⟩
    (prefixPartial 13 1211440) = some ⟨13, 2, 0, 1065521, 1211440, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_1211440_1065521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211440 ⟨1065521, by decide⟩ :=
  accepted_of_selected 13 1211440 ⟨1065521, by decide⟩ ⟨13, 2, 0, 1065521, 1211440, 1185, 16384⟩
    (by decide) selected_cut_39298

theorem selected_cut_39299 : selected 8 ⟨1065544, by decide⟩
    (prefixPartial 13 1211441) = some ⟨13, 2, 0, 1065544, 1211441, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1211441_1065544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211441 ⟨1065544, by decide⟩ :=
  accepted_of_selected 13 1211441 ⟨1065544, by decide⟩ ⟨13, 2, 0, 1065544, 1211441, 1385, 16384⟩
    (by decide) selected_cut_39299

theorem selected_cut_39300 : selected 8 ⟨1065560, by decide⟩
    (prefixPartial 13 1211442) = some ⟨13, 2, 0, 1065560, 1211442, 981, 16384⟩ := by
  decide +kernel

theorem context_13_1211442_1065560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211442 ⟨1065560, by decide⟩ :=
  accepted_of_selected 13 1211442 ⟨1065560, by decide⟩ ⟨13, 2, 0, 1065560, 1211442, 981, 16384⟩
    (by decide) selected_cut_39300

theorem selected_cut_39301 : selected 8 ⟨1065575, by decide⟩
    (prefixPartial 13 1211443) = some ⟨13, 2, 0, 1065575, 1211443, 705, 16384⟩ := by
  decide +kernel

theorem context_13_1211443_1065575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211443 ⟨1065575, by decide⟩ :=
  accepted_of_selected 13 1211443 ⟨1065575, by decide⟩ ⟨13, 2, 0, 1065575, 1211443, 705, 16384⟩
    (by decide) selected_cut_39301

theorem unmarked_context_12_302860_1065576 : frontier 9 ⟨1065576, by decide⟩
    (prefixCache 12 302860) (prefixPartial 12 302860) = false := by
  decide +kernel

theorem node_context_12_302860_1065576 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065576, by decide⟩ =
    .split (coordinate 12) (![⟨1065521, by decide⟩,⟨1065544, by decide⟩,⟨1065560, by decide⟩,⟨1065575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302860_1065576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302860 ⟨1065576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302860
    ⟨1065576, by decide⟩ (by decide) (![⟨1065521, by decide⟩,⟨1065544, by decide⟩,⟨1065560, by decide⟩,⟨1065575, by decide⟩]) unmarked_context_12_302860_1065576 node_context_12_302860_1065576
  intro a
  fin_cases a
  · exact context_13_1211440_1065521
  · exact context_13_1211441_1065544
  · exact context_13_1211442_1065560
  · exact context_13_1211443_1065575

theorem selected_cut_39302 : selected 8 ⟨1065617, by decide⟩
    (prefixPartial 13 1211444) = some ⟨13, 2, 0, 1065617, 1211444, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_1211444_1065617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211444 ⟨1065617, by decide⟩ :=
  accepted_of_selected 13 1211444 ⟨1065617, by decide⟩ ⟨13, 2, 0, 1065617, 1211444, 1737, 16384⟩
    (by decide) selected_cut_39302

theorem selected_cut_39303 : selected 8 ⟨1065638, by decide⟩
    (prefixPartial 13 1211445) = some ⟨13, 2, 0, 1065638, 1211445, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_1211445_1065638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211445 ⟨1065638, by decide⟩ :=
  accepted_of_selected 13 1211445 ⟨1065638, by decide⟩ ⟨13, 2, 0, 1065638, 1211445, 1393, 16384⟩
    (by decide) selected_cut_39303

theorem selected_cut_39304 : selected 8 ⟨1065659, by decide⟩
    (prefixPartial 13 1211446) = some ⟨13, 2, 0, 1065659, 1211446, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_1211446_1065659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211446 ⟨1065659, by decide⟩ :=
  accepted_of_selected 13 1211446 ⟨1065659, by decide⟩ ⟨13, 2, 0, 1065659, 1211446, 1009, 16384⟩
    (by decide) selected_cut_39304

theorem selected_cut_39305 : selected 8 ⟨1065666, by decide⟩
    (prefixPartial 13 1211447) = some ⟨13, 2, 0, 1065666, 1211447, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1211447_1065666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211447 ⟨1065666, by decide⟩ :=
  accepted_of_selected 13 1211447 ⟨1065666, by decide⟩ ⟨13, 2, 0, 1065666, 1211447, 597, 16384⟩
    (by decide) selected_cut_39305

theorem unmarked_context_12_302861_1065667 : frontier 9 ⟨1065667, by decide⟩
    (prefixCache 12 302861) (prefixPartial 12 302861) = false := by
  decide +kernel

theorem node_context_12_302861_1065667 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065667, by decide⟩ =
    .split (coordinate 12) (![⟨1065617, by decide⟩,⟨1065638, by decide⟩,⟨1065659, by decide⟩,⟨1065666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302861_1065667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302861 ⟨1065667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302861
    ⟨1065667, by decide⟩ (by decide) (![⟨1065617, by decide⟩,⟨1065638, by decide⟩,⟨1065659, by decide⟩,⟨1065666, by decide⟩]) unmarked_context_12_302861_1065667 node_context_12_302861_1065667
  intro a
  fin_cases a
  · exact context_13_1211444_1065617
  · exact context_13_1211445_1065638
  · exact context_13_1211446_1065659
  · exact context_13_1211447_1065666

theorem selected_cut_39306 : selected 8 ⟨1065698, by decide⟩
    (prefixPartial 13 1211448) = some ⟨13, 2, 0, 1065698, 1211448, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_1211448_1065698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211448 ⟨1065698, by decide⟩ :=
  accepted_of_selected 13 1211448 ⟨1065698, by decide⟩ ⟨13, 2, 0, 1065698, 1211448, 1409, 16384⟩
    (by decide) selected_cut_39306

theorem selected_cut_39307 : selected 8 ⟨1065720, by decide⟩
    (prefixPartial 13 1211449) = some ⟨13, 2, 0, 1065720, 1211449, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_1211449_1065720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211449 ⟨1065720, by decide⟩ :=
  accepted_of_selected 13 1211449 ⟨1065720, by decide⟩ ⟨13, 2, 0, 1065720, 1211449, 1333, 16384⟩
    (by decide) selected_cut_39307

theorem selected_cut_39308 : selected 8 ⟨1065738, by decide⟩
    (prefixPartial 13 1211450) = some ⟨13, 2, 0, 1065738, 1211450, 905, 16384⟩ := by
  decide +kernel

theorem context_13_1211450_1065738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211450 ⟨1065738, by decide⟩ :=
  accepted_of_selected 13 1211450 ⟨1065738, by decide⟩ ⟨13, 2, 0, 1065738, 1211450, 905, 16384⟩
    (by decide) selected_cut_39308

theorem selected_cut_39309 : selected 8 ⟨1065747, by decide⟩
    (prefixPartial 13 1211451) = some ⟨13, 2, 0, 1065747, 1211451, 605, 16384⟩ := by
  decide +kernel

theorem context_13_1211451_1065747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211451 ⟨1065747, by decide⟩ :=
  accepted_of_selected 13 1211451 ⟨1065747, by decide⟩ ⟨13, 2, 0, 1065747, 1211451, 605, 16384⟩
    (by decide) selected_cut_39309

theorem unmarked_context_12_302862_1065748 : frontier 9 ⟨1065748, by decide⟩
    (prefixCache 12 302862) (prefixPartial 12 302862) = false := by
  decide +kernel

theorem node_context_12_302862_1065748 : EJMOriginalGlobalDAGData.nodes 9 ⟨1065748, by decide⟩ =
    .split (coordinate 12) (![⟨1065698, by decide⟩,⟨1065720, by decide⟩,⟨1065738, by decide⟩,⟨1065747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302862_1065748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302862 ⟨1065748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302862
    ⟨1065748, by decide⟩ (by decide) (![⟨1065698, by decide⟩,⟨1065720, by decide⟩,⟨1065738, by decide⟩,⟨1065747, by decide⟩]) unmarked_context_12_302862_1065748 node_context_12_302862_1065748
  intro a
  fin_cases a
  · exact context_13_1211448_1065698
  · exact context_13_1211449_1065720
  · exact context_13_1211450_1065738
  · exact context_13_1211451_1065747

theorem selected_cut_39310 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 302863) = some ⟨12, 1, 0, 903806, 302863, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302863_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302863 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 302863 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 302863, 1, 65536⟩
    (by decide) selected_cut_39310

theorem unmarked_context_11_75715_1065749 : frontier 10 ⟨1065749, by decide⟩
    (prefixCache 11 75715) (prefixPartial 11 75715) = false := by
  decide +kernel

theorem node_context_11_75715_1065749 : EJMOriginalGlobalDAGData.nodes 10 ⟨1065749, by decide⟩ =
    .split (coordinate 11) (![⟨1065576, by decide⟩,⟨1065667, by decide⟩,⟨1065748, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75715_1065749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75715 ⟨1065749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75715
    ⟨1065749, by decide⟩ (by decide) (![⟨1065576, by decide⟩,⟨1065667, by decide⟩,⟨1065748, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75715_1065749 node_context_11_75715_1065749
  intro a
  fin_cases a
  · exact context_12_302860_1065576
  · exact context_12_302861_1065667
  · exact context_12_302862_1065748
  · exact context_12_302863_903806

theorem unmarked_context_10_18928_1065750 : frontier 11 ⟨1065750, by decide⟩
    (prefixCache 10 18928) (prefixPartial 10 18928) = false := by
  decide +kernel

theorem node_context_10_18928_1065750 : EJMOriginalGlobalDAGData.nodes 11 ⟨1065750, by decide⟩ =
    .split (coordinate 10) (![⟨1064787, by decide⟩,⟨1065138, by decide⟩,⟨1065496, by decide⟩,⟨1065749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18928_1065750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18928 ⟨1065750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18928
    ⟨1065750, by decide⟩ (by decide) (![⟨1064787, by decide⟩,⟨1065138, by decide⟩,⟨1065496, by decide⟩,⟨1065749, by decide⟩]) unmarked_context_10_18928_1065750 node_context_10_18928_1065750
  intro a
  fin_cases a
  · exact context_11_75712_1064787
  · exact context_11_75713_1065138
  · exact context_11_75714_1065496
  · exact context_11_75715_1065749

theorem selected_cut_39311 : selected 9 ⟨1065809, by decide⟩
    (prefixPartial 12 302864) = some ⟨12, 2, 0, 1065809, 302864, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_302864_1065809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302864 ⟨1065809, by decide⟩ :=
  accepted_of_selected 12 302864 ⟨1065809, by decide⟩ ⟨12, 2, 0, 1065809, 302864, 3521, 65536⟩
    (by decide) selected_cut_39311

theorem selected_cut_39312 : selected 9 ⟨1065880, by decide⟩
    (prefixPartial 12 302865) = some ⟨12, 2, 0, 1065880, 302865, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_302865_1065880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302865 ⟨1065880, by decide⟩ :=
  accepted_of_selected 12 302865 ⟨1065880, by decide⟩ ⟨12, 2, 0, 1065880, 302865, 3841, 65536⟩
    (by decide) selected_cut_39312

theorem selected_cut_39313 : selected 9 ⟨1065939, by decide⟩
    (prefixPartial 12 302866) = some ⟨12, 2, 0, 1065939, 302866, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_302866_1065939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302866 ⟨1065939, by decide⟩ :=
  accepted_of_selected 12 302866 ⟨1065939, by decide⟩ ⟨12, 2, 0, 1065939, 302866, 3601, 65536⟩
    (by decide) selected_cut_39313

theorem selected_cut_39314 : selected 9 ⟨1065988, by decide⟩
    (prefixPartial 12 302867) = some ⟨12, 2, 0, 1065988, 302867, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_302867_1065988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302867 ⟨1065988, by decide⟩ :=
  accepted_of_selected 12 302867 ⟨1065988, by decide⟩ ⟨12, 2, 0, 1065988, 302867, 3517, 65536⟩
    (by decide) selected_cut_39314

theorem unmarked_context_11_75716_1065989 : frontier 10 ⟨1065989, by decide⟩
    (prefixCache 11 75716) (prefixPartial 11 75716) = false := by
  decide +kernel

theorem node_context_11_75716_1065989 : EJMOriginalGlobalDAGData.nodes 10 ⟨1065989, by decide⟩ =
    .split (coordinate 11) (![⟨1065809, by decide⟩,⟨1065880, by decide⟩,⟨1065939, by decide⟩,⟨1065988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75716_1065989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75716 ⟨1065989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75716
    ⟨1065989, by decide⟩ (by decide) (![⟨1065809, by decide⟩,⟨1065880, by decide⟩,⟨1065939, by decide⟩,⟨1065988, by decide⟩]) unmarked_context_11_75716_1065989 node_context_11_75716_1065989
  intro a
  fin_cases a
  · exact context_12_302864_1065809
  · exact context_12_302865_1065880
  · exact context_12_302866_1065939
  · exact context_12_302867_1065988

theorem selected_cut_39315 : selected 9 ⟨1066053, by decide⟩
    (prefixPartial 12 302868) = some ⟨12, 2, 0, 1066053, 302868, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_302868_1066053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302868 ⟨1066053, by decide⟩ :=
  accepted_of_selected 12 302868 ⟨1066053, by decide⟩ ⟨12, 2, 0, 1066053, 302868, 3533, 65536⟩
    (by decide) selected_cut_39315

theorem selected_cut_39316 : selected 9 ⟨692794, by decide⟩
    (prefixPartial 12 302869) = some ⟨12, 1, 0, 692794, 302869, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302869_692794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302869 ⟨692794, by decide⟩ :=
  accepted_of_selected 12 302869 ⟨692794, by decide⟩ ⟨12, 1, 0, 692794, 302869, 1, 65536⟩
    (by decide) selected_cut_39316

theorem selected_cut_39317 : selected 9 ⟨1066108, by decide⟩
    (prefixPartial 12 302870) = some ⟨12, 2, 0, 1066108, 302870, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_302870_1066108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302870 ⟨1066108, by decide⟩ :=
  accepted_of_selected 12 302870 ⟨1066108, by decide⟩ ⟨12, 2, 0, 1066108, 302870, 3409, 65536⟩
    (by decide) selected_cut_39317

theorem selected_cut_39318 : selected 9 ⟨1066162, by decide⟩
    (prefixPartial 12 302871) = some ⟨12, 2, 0, 1066162, 302871, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_302871_1066162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302871 ⟨1066162, by decide⟩ :=
  accepted_of_selected 12 302871 ⟨1066162, by decide⟩ ⟨12, 2, 0, 1066162, 302871, 3489, 65536⟩
    (by decide) selected_cut_39318

theorem unmarked_context_11_75717_1066163 : frontier 10 ⟨1066163, by decide⟩
    (prefixCache 11 75717) (prefixPartial 11 75717) = false := by
  decide +kernel

theorem node_context_11_75717_1066163 : EJMOriginalGlobalDAGData.nodes 10 ⟨1066163, by decide⟩ =
    .split (coordinate 11) (![⟨1066053, by decide⟩,⟨692794, by decide⟩,⟨1066108, by decide⟩,⟨1066162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75717_1066163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75717 ⟨1066163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75717
    ⟨1066163, by decide⟩ (by decide) (![⟨1066053, by decide⟩,⟨692794, by decide⟩,⟨1066108, by decide⟩,⟨1066162, by decide⟩]) unmarked_context_11_75717_1066163 node_context_11_75717_1066163
  intro a
  fin_cases a
  · exact context_12_302868_1066053
  · exact context_12_302869_692794
  · exact context_12_302870_1066108
  · exact context_12_302871_1066162

theorem selected_cut_39319 : selected 9 ⟨1066227, by decide⟩
    (prefixPartial 12 302872) = some ⟨12, 2, 0, 1066227, 302872, 3793, 65536⟩ := by
  decide +kernel

theorem context_12_302872_1066227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302872 ⟨1066227, by decide⟩ :=
  accepted_of_selected 12 302872 ⟨1066227, by decide⟩ ⟨12, 2, 0, 1066227, 302872, 3793, 65536⟩
    (by decide) selected_cut_39319

theorem selected_cut_39320 : selected 9 ⟨1066303, by decide⟩
    (prefixPartial 12 302873) = some ⟨12, 2, 0, 1066303, 302873, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_302873_1066303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302873 ⟨1066303, by decide⟩ :=
  accepted_of_selected 12 302873 ⟨1066303, by decide⟩ ⟨12, 2, 0, 1066303, 302873, 4061, 65536⟩
    (by decide) selected_cut_39320

theorem selected_cut_39321 : selected 9 ⟨1066362, by decide⟩
    (prefixPartial 12 302874) = some ⟨12, 2, 0, 1066362, 302874, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_302874_1066362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302874 ⟨1066362, by decide⟩ :=
  accepted_of_selected 12 302874 ⟨1066362, by decide⟩ ⟨12, 2, 0, 1066362, 302874, 3509, 65536⟩
    (by decide) selected_cut_39321

theorem selected_cut_39322 : selected 9 ⟨1066430, by decide⟩
    (prefixPartial 12 302875) = some ⟨12, 2, 0, 1066430, 302875, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_302875_1066430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302875 ⟨1066430, by decide⟩ :=
  accepted_of_selected 12 302875 ⟨1066430, by decide⟩ ⟨12, 2, 0, 1066430, 302875, 3833, 65536⟩
    (by decide) selected_cut_39322

theorem unmarked_context_11_75718_1066431 : frontier 10 ⟨1066431, by decide⟩
    (prefixCache 11 75718) (prefixPartial 11 75718) = false := by
  decide +kernel

theorem node_context_11_75718_1066431 : EJMOriginalGlobalDAGData.nodes 10 ⟨1066431, by decide⟩ =
    .split (coordinate 11) (![⟨1066227, by decide⟩,⟨1066303, by decide⟩,⟨1066362, by decide⟩,⟨1066430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75718_1066431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75718 ⟨1066431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75718
    ⟨1066431, by decide⟩ (by decide) (![⟨1066227, by decide⟩,⟨1066303, by decide⟩,⟨1066362, by decide⟩,⟨1066430, by decide⟩]) unmarked_context_11_75718_1066431 node_context_11_75718_1066431
  intro a
  fin_cases a
  · exact context_12_302872_1066227
  · exact context_12_302873_1066303
  · exact context_12_302874_1066362
  · exact context_12_302875_1066430

theorem selected_cut_39323 : selected 9 ⟨1066480, by decide⟩
    (prefixPartial 12 302876) = some ⟨12, 2, 0, 1066480, 302876, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_302876_1066480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302876 ⟨1066480, by decide⟩ :=
  accepted_of_selected 12 302876 ⟨1066480, by decide⟩ ⟨12, 2, 0, 1066480, 302876, 3273, 65536⟩
    (by decide) selected_cut_39323

theorem selected_cut_39324 : selected 9 ⟨1066561, by decide⟩
    (prefixPartial 12 302877) = some ⟨12, 2, 0, 1066561, 302877, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_302877_1066561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302877 ⟨1066561, by decide⟩ :=
  accepted_of_selected 12 302877 ⟨1066561, by decide⟩ ⟨12, 2, 0, 1066561, 302877, 3941, 65536⟩
    (by decide) selected_cut_39324

theorem selected_cut_39325 : selected 9 ⟨1066626, by decide⟩
    (prefixPartial 12 302878) = some ⟨12, 2, 0, 1066626, 302878, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_302878_1066626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302878 ⟨1066626, by decide⟩ :=
  accepted_of_selected 12 302878 ⟨1066626, by decide⟩ ⟨12, 2, 0, 1066626, 302878, 3525, 65536⟩
    (by decide) selected_cut_39325

theorem selected_cut_39326 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 302879) = some ⟨12, 1, 0, 903806, 302879, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302879_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302879 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 302879 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 302879, 1, 65536⟩
    (by decide) selected_cut_39326

theorem unmarked_context_11_75719_1066627 : frontier 10 ⟨1066627, by decide⟩
    (prefixCache 11 75719) (prefixPartial 11 75719) = false := by
  decide +kernel

theorem node_context_11_75719_1066627 : EJMOriginalGlobalDAGData.nodes 10 ⟨1066627, by decide⟩ =
    .split (coordinate 11) (![⟨1066480, by decide⟩,⟨1066561, by decide⟩,⟨1066626, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75719_1066627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75719 ⟨1066627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75719
    ⟨1066627, by decide⟩ (by decide) (![⟨1066480, by decide⟩,⟨1066561, by decide⟩,⟨1066626, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75719_1066627 node_context_11_75719_1066627
  intro a
  fin_cases a
  · exact context_12_302876_1066480
  · exact context_12_302877_1066561
  · exact context_12_302878_1066626
  · exact context_12_302879_903806

theorem unmarked_context_10_18929_1066628 : frontier 11 ⟨1066628, by decide⟩
    (prefixCache 10 18929) (prefixPartial 10 18929) = false := by
  decide +kernel

theorem node_context_10_18929_1066628 : EJMOriginalGlobalDAGData.nodes 11 ⟨1066628, by decide⟩ =
    .split (coordinate 10) (![⟨1065989, by decide⟩,⟨1066163, by decide⟩,⟨1066431, by decide⟩,⟨1066627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18929_1066628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18929 ⟨1066628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18929
    ⟨1066628, by decide⟩ (by decide) (![⟨1065989, by decide⟩,⟨1066163, by decide⟩,⟨1066431, by decide⟩,⟨1066627, by decide⟩]) unmarked_context_10_18929_1066628 node_context_10_18929_1066628
  intro a
  fin_cases a
  · exact context_11_75716_1065989
  · exact context_11_75717_1066163
  · exact context_11_75718_1066431
  · exact context_11_75719_1066627

theorem selected_cut_39327 : selected 9 ⟨1066629, by decide⟩
    (prefixPartial 12 302880) = some ⟨12, 1, 0, 1066629, 302880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302880_1066629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302880 ⟨1066629, by decide⟩ :=
  accepted_of_selected 12 302880 ⟨1066629, by decide⟩ ⟨12, 1, 0, 1066629, 302880, 1, 65536⟩
    (by decide) selected_cut_39327

theorem selected_cut_39328 : selected 9 ⟨1066691, by decide⟩
    (prefixPartial 12 302881) = some ⟨12, 2, 0, 1066691, 302881, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_302881_1066691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302881 ⟨1066691, by decide⟩ :=
  accepted_of_selected 12 302881 ⟨1066691, by decide⟩ ⟨12, 2, 0, 1066691, 302881, 3909, 65536⟩
    (by decide) selected_cut_39328

theorem selected_cut_39329 : selected 9 ⟨1066749, by decide⟩
    (prefixPartial 12 302882) = some ⟨12, 2, 0, 1066749, 302882, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_302882_1066749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302882 ⟨1066749, by decide⟩ :=
  accepted_of_selected 12 302882 ⟨1066749, by decide⟩ ⟨12, 2, 0, 1066749, 302882, 3601, 65536⟩
    (by decide) selected_cut_39329

theorem selected_cut_39330 : selected 9 ⟨1066801, by decide⟩
    (prefixPartial 12 302883) = some ⟨12, 2, 0, 1066801, 302883, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_302883_1066801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302883 ⟨1066801, by decide⟩ :=
  accepted_of_selected 12 302883 ⟨1066801, by decide⟩ ⟨12, 2, 0, 1066801, 302883, 3545, 65536⟩
    (by decide) selected_cut_39330

theorem unmarked_context_11_75720_1066802 : frontier 10 ⟨1066802, by decide⟩
    (prefixCache 11 75720) (prefixPartial 11 75720) = false := by
  decide +kernel

theorem node_context_11_75720_1066802 : EJMOriginalGlobalDAGData.nodes 10 ⟨1066802, by decide⟩ =
    .split (coordinate 11) (![⟨1066629, by decide⟩,⟨1066691, by decide⟩,⟨1066749, by decide⟩,⟨1066801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75720_1066802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75720 ⟨1066802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75720
    ⟨1066802, by decide⟩ (by decide) (![⟨1066629, by decide⟩,⟨1066691, by decide⟩,⟨1066749, by decide⟩,⟨1066801, by decide⟩]) unmarked_context_11_75720_1066802 node_context_11_75720_1066802
  intro a
  fin_cases a
  · exact context_12_302880_1066629
  · exact context_12_302881_1066691
  · exact context_12_302882_1066749
  · exact context_12_302883_1066801

theorem selected_cut_39331 : selected 9 ⟨1066870, by decide⟩
    (prefixPartial 12 302884) = some ⟨12, 2, 0, 1066870, 302884, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_302884_1066870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302884 ⟨1066870, by decide⟩ :=
  accepted_of_selected 12 302884 ⟨1066870, by decide⟩ ⟨12, 2, 0, 1066870, 302884, 3785, 65536⟩
    (by decide) selected_cut_39331

theorem selected_cut_39332 : selected 8 ⟨1066895, by decide⟩
    (prefixPartial 13 1211540) = some ⟨13, 2, 0, 1066895, 1211540, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_1211540_1066895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211540 ⟨1066895, by decide⟩ :=
  accepted_of_selected 13 1211540 ⟨1066895, by decide⟩ ⟨13, 2, 0, 1066895, 1211540, 1301, 16384⟩
    (by decide) selected_cut_39332

theorem selected_cut_39333 : selected 8 ⟨1066912, by decide⟩
    (prefixPartial 13 1211541) = some ⟨13, 2, 0, 1066912, 1211541, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_1211541_1066912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211541 ⟨1066912, by decide⟩ :=
  accepted_of_selected 13 1211541 ⟨1066912, by decide⟩ ⟨13, 2, 0, 1066912, 1211541, 1365, 16384⟩
    (by decide) selected_cut_39333

theorem selected_cut_39334 : selected 8 ⟨1066931, by decide⟩
    (prefixPartial 13 1211542) = some ⟨13, 2, 0, 1066931, 1211542, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_1211542_1066931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211542 ⟨1066931, by decide⟩ :=
  accepted_of_selected 13 1211542 ⟨1066931, by decide⟩ ⟨13, 2, 0, 1066931, 1211542, 1037, 16384⟩
    (by decide) selected_cut_39334

theorem selected_cut_39335 : selected 8 ⟨1066936, by decide⟩
    (prefixPartial 13 1211543) = some ⟨13, 2, 0, 1066936, 1211543, 449, 16384⟩ := by
  decide +kernel

theorem context_13_1211543_1066936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211543 ⟨1066936, by decide⟩ :=
  accepted_of_selected 13 1211543 ⟨1066936, by decide⟩ ⟨13, 2, 0, 1066936, 1211543, 449, 16384⟩
    (by decide) selected_cut_39335

theorem unmarked_context_12_302885_1066937 : frontier 9 ⟨1066937, by decide⟩
    (prefixCache 12 302885) (prefixPartial 12 302885) = false := by
  decide +kernel

theorem node_context_12_302885_1066937 : EJMOriginalGlobalDAGData.nodes 9 ⟨1066937, by decide⟩ =
    .split (coordinate 12) (![⟨1066895, by decide⟩,⟨1066912, by decide⟩,⟨1066931, by decide⟩,⟨1066936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302885_1066937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302885 ⟨1066937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302885
    ⟨1066937, by decide⟩ (by decide) (![⟨1066895, by decide⟩,⟨1066912, by decide⟩,⟨1066931, by decide⟩,⟨1066936, by decide⟩]) unmarked_context_12_302885_1066937 node_context_12_302885_1066937
  intro a
  fin_cases a
  · exact context_13_1211540_1066895
  · exact context_13_1211541_1066912
  · exact context_13_1211542_1066931
  · exact context_13_1211543_1066936

theorem selected_cut_39336 : selected 9 ⟨1067000, by decide⟩
    (prefixPartial 12 302886) = some ⟨12, 2, 0, 1067000, 302886, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_302886_1067000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302886 ⟨1067000, by decide⟩ :=
  accepted_of_selected 12 302886 ⟨1067000, by decide⟩ ⟨12, 2, 0, 1067000, 302886, 3501, 65536⟩
    (by decide) selected_cut_39336

theorem selected_cut_39337 : selected 9 ⟨1067054, by decide⟩
    (prefixPartial 12 302887) = some ⟨12, 2, 0, 1067054, 302887, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_302887_1067054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302887 ⟨1067054, by decide⟩ :=
  accepted_of_selected 12 302887 ⟨1067054, by decide⟩ ⟨12, 2, 0, 1067054, 302887, 3657, 65536⟩
    (by decide) selected_cut_39337

theorem unmarked_context_11_75721_1067055 : frontier 10 ⟨1067055, by decide⟩
    (prefixCache 11 75721) (prefixPartial 11 75721) = false := by
  decide +kernel

theorem node_context_11_75721_1067055 : EJMOriginalGlobalDAGData.nodes 10 ⟨1067055, by decide⟩ =
    .split (coordinate 11) (![⟨1066870, by decide⟩,⟨1066937, by decide⟩,⟨1067000, by decide⟩,⟨1067054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75721_1067055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75721 ⟨1067055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75721
    ⟨1067055, by decide⟩ (by decide) (![⟨1066870, by decide⟩,⟨1066937, by decide⟩,⟨1067000, by decide⟩,⟨1067054, by decide⟩]) unmarked_context_11_75721_1067055 node_context_11_75721_1067055
  intro a
  fin_cases a
  · exact context_12_302884_1066870
  · exact context_12_302885_1066937
  · exact context_12_302886_1067000
  · exact context_12_302887_1067054

theorem selected_cut_39338 : selected 9 ⟨1067119, by decide⟩
    (prefixPartial 12 302888) = some ⟨12, 2, 0, 1067119, 302888, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_302888_1067119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302888 ⟨1067119, by decide⟩ :=
  accepted_of_selected 12 302888 ⟨1067119, by decide⟩ ⟨12, 2, 0, 1067119, 302888, 3881, 65536⟩
    (by decide) selected_cut_39338

theorem selected_cut_39339 : selected 8 ⟨1067143, by decide⟩
    (prefixPartial 13 1211556) = some ⟨13, 2, 0, 1067143, 1211556, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_1211556_1067143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211556 ⟨1067143, by decide⟩ :=
  accepted_of_selected 13 1211556 ⟨1067143, by decide⟩ ⟨13, 2, 0, 1067143, 1211556, 1049, 16384⟩
    (by decide) selected_cut_39339

theorem selected_cut_39340 : selected 8 ⟨1067172, by decide⟩
    (prefixPartial 13 1211557) = some ⟨13, 2, 0, 1067172, 1211557, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_1211557_1067172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211557 ⟨1067172, by decide⟩ :=
  accepted_of_selected 13 1211557 ⟨1067172, by decide⟩ ⟨13, 2, 0, 1067172, 1211557, 1577, 16384⟩
    (by decide) selected_cut_39340

theorem selected_cut_39341 : selected 8 ⟨1067192, by decide⟩
    (prefixPartial 13 1211558) = some ⟨13, 2, 0, 1067192, 1211558, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_1211558_1067192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211558 ⟨1067192, by decide⟩ :=
  accepted_of_selected 13 1211558 ⟨1067192, by decide⟩ ⟨13, 2, 0, 1067192, 1211558, 1149, 16384⟩
    (by decide) selected_cut_39341

theorem selected_cut_39342 : selected 8 ⟨1067197, by decide⟩
    (prefixPartial 13 1211559) = some ⟨13, 2, 0, 1067197, 1211559, 497, 16384⟩ := by
  decide +kernel

theorem context_13_1211559_1067197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1211559 ⟨1067197, by decide⟩ :=
  accepted_of_selected 13 1211559 ⟨1067197, by decide⟩ ⟨13, 2, 0, 1067197, 1211559, 497, 16384⟩
    (by decide) selected_cut_39342

theorem unmarked_context_12_302889_1067198 : frontier 9 ⟨1067198, by decide⟩
    (prefixCache 12 302889) (prefixPartial 12 302889) = false := by
  decide +kernel

theorem node_context_12_302889_1067198 : EJMOriginalGlobalDAGData.nodes 9 ⟨1067198, by decide⟩ =
    .split (coordinate 12) (![⟨1067143, by decide⟩,⟨1067172, by decide⟩,⟨1067192, by decide⟩,⟨1067197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302889_1067198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302889 ⟨1067198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302889
    ⟨1067198, by decide⟩ (by decide) (![⟨1067143, by decide⟩,⟨1067172, by decide⟩,⟨1067192, by decide⟩,⟨1067197, by decide⟩]) unmarked_context_12_302889_1067198 node_context_12_302889_1067198
  intro a
  fin_cases a
  · exact context_13_1211556_1067143
  · exact context_13_1211557_1067172
  · exact context_13_1211558_1067192
  · exact context_13_1211559_1067197

theorem selected_cut_39343 : selected 9 ⟨661672, by decide⟩
    (prefixPartial 12 302890) = some ⟨12, 1, 0, 661672, 302890, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302890_661672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302890 ⟨661672, by decide⟩ :=
  accepted_of_selected 12 302890 ⟨661672, by decide⟩ ⟨12, 1, 0, 661672, 302890, 1, 65536⟩
    (by decide) selected_cut_39343

theorem selected_cut_39344 : selected 9 ⟨1067252, by decide⟩
    (prefixPartial 12 302891) = some ⟨12, 2, 0, 1067252, 302891, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_302891_1067252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302891 ⟨1067252, by decide⟩ :=
  accepted_of_selected 12 302891 ⟨1067252, by decide⟩ ⟨12, 2, 0, 1067252, 302891, 3961, 65536⟩
    (by decide) selected_cut_39344

theorem unmarked_context_11_75722_1067253 : frontier 10 ⟨1067253, by decide⟩
    (prefixCache 11 75722) (prefixPartial 11 75722) = false := by
  decide +kernel

theorem node_context_11_75722_1067253 : EJMOriginalGlobalDAGData.nodes 10 ⟨1067253, by decide⟩ =
    .split (coordinate 11) (![⟨1067119, by decide⟩,⟨1067198, by decide⟩,⟨661672, by decide⟩,⟨1067252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75722_1067253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75722 ⟨1067253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75722
    ⟨1067253, by decide⟩ (by decide) (![⟨1067119, by decide⟩,⟨1067198, by decide⟩,⟨661672, by decide⟩,⟨1067252, by decide⟩]) unmarked_context_11_75722_1067253 node_context_11_75722_1067253
  intro a
  fin_cases a
  · exact context_12_302888_1067119
  · exact context_12_302889_1067198
  · exact context_12_302890_661672
  · exact context_12_302891_1067252

theorem selected_cut_39345 : selected 9 ⟨1067298, by decide⟩
    (prefixPartial 12 302892) = some ⟨12, 2, 0, 1067298, 302892, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_302892_1067298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302892 ⟨1067298, by decide⟩ :=
  accepted_of_selected 12 302892 ⟨1067298, by decide⟩ ⟨12, 2, 0, 1067298, 302892, 2969, 65536⟩
    (by decide) selected_cut_39345

theorem selected_cut_39346 : selected 9 ⟨1067358, by decide⟩
    (prefixPartial 12 302893) = some ⟨12, 2, 0, 1067358, 302893, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_302893_1067358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302893 ⟨1067358, by decide⟩ :=
  accepted_of_selected 12 302893 ⟨1067358, by decide⟩ ⟨12, 2, 0, 1067358, 302893, 3729, 65536⟩
    (by decide) selected_cut_39346

theorem selected_cut_39347 : selected 9 ⟨1067416, by decide⟩
    (prefixPartial 12 302894) = some ⟨12, 2, 0, 1067416, 302894, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_302894_1067416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302894 ⟨1067416, by decide⟩ :=
  accepted_of_selected 12 302894 ⟨1067416, by decide⟩ ⟨12, 2, 0, 1067416, 302894, 3297, 65536⟩
    (by decide) selected_cut_39347

theorem selected_cut_39348 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 302895) = some ⟨12, 1, 0, 903806, 302895, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302895_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302895 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 302895 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 302895, 1, 65536⟩
    (by decide) selected_cut_39348

theorem unmarked_context_11_75723_1067417 : frontier 10 ⟨1067417, by decide⟩
    (prefixCache 11 75723) (prefixPartial 11 75723) = false := by
  decide +kernel

theorem node_context_11_75723_1067417 : EJMOriginalGlobalDAGData.nodes 10 ⟨1067417, by decide⟩ =
    .split (coordinate 11) (![⟨1067298, by decide⟩,⟨1067358, by decide⟩,⟨1067416, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75723_1067417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75723 ⟨1067417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75723
    ⟨1067417, by decide⟩ (by decide) (![⟨1067298, by decide⟩,⟨1067358, by decide⟩,⟨1067416, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75723_1067417 node_context_11_75723_1067417
  intro a
  fin_cases a
  · exact context_12_302892_1067298
  · exact context_12_302893_1067358
  · exact context_12_302894_1067416
  · exact context_12_302895_903806

theorem unmarked_context_10_18930_1067418 : frontier 11 ⟨1067418, by decide⟩
    (prefixCache 10 18930) (prefixPartial 10 18930) = false := by
  decide +kernel

theorem node_context_10_18930_1067418 : EJMOriginalGlobalDAGData.nodes 11 ⟨1067418, by decide⟩ =
    .split (coordinate 10) (![⟨1066802, by decide⟩,⟨1067055, by decide⟩,⟨1067253, by decide⟩,⟨1067417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18930_1067418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18930 ⟨1067418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18930
    ⟨1067418, by decide⟩ (by decide) (![⟨1066802, by decide⟩,⟨1067055, by decide⟩,⟨1067253, by decide⟩,⟨1067417, by decide⟩]) unmarked_context_10_18930_1067418 node_context_10_18930_1067418
  intro a
  fin_cases a
  · exact context_11_75720_1066802
  · exact context_11_75721_1067055
  · exact context_11_75722_1067253
  · exact context_11_75723_1067417

theorem selected_cut_39349 : selected 9 ⟨612849, by decide⟩
    (prefixPartial 12 302896) = some ⟨12, 1, 0, 612849, 302896, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302896_612849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302896 ⟨612849, by decide⟩ :=
  accepted_of_selected 12 302896 ⟨612849, by decide⟩ ⟨12, 1, 0, 612849, 302896, 1, 65536⟩
    (by decide) selected_cut_39349

theorem selected_cut_39350 : selected 9 ⟨1067469, by decide⟩
    (prefixPartial 12 302897) = some ⟨12, 2, 0, 1067469, 302897, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_302897_1067469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302897 ⟨1067469, by decide⟩ :=
  accepted_of_selected 12 302897 ⟨1067469, by decide⟩ ⟨12, 2, 0, 1067469, 302897, 3477, 65536⟩
    (by decide) selected_cut_39350

theorem selected_cut_39351 : selected 9 ⟨1067520, by decide⟩
    (prefixPartial 12 302898) = some ⟨12, 2, 0, 1067520, 302898, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_302898_1067520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302898 ⟨1067520, by decide⟩ :=
  accepted_of_selected 12 302898 ⟨1067520, by decide⟩ ⟨12, 2, 0, 1067520, 302898, 3217, 65536⟩
    (by decide) selected_cut_39351

theorem selected_cut_39352 : selected 9 ⟨1067562, by decide⟩
    (prefixPartial 12 302899) = some ⟨12, 2, 0, 1067562, 302899, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_302899_1067562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302899 ⟨1067562, by decide⟩ :=
  accepted_of_selected 12 302899 ⟨1067562, by decide⟩ ⟨12, 2, 0, 1067562, 302899, 2977, 65536⟩
    (by decide) selected_cut_39352

theorem unmarked_context_11_75724_1067563 : frontier 10 ⟨1067563, by decide⟩
    (prefixCache 11 75724) (prefixPartial 11 75724) = false := by
  decide +kernel

theorem node_context_11_75724_1067563 : EJMOriginalGlobalDAGData.nodes 10 ⟨1067563, by decide⟩ =
    .split (coordinate 11) (![⟨612849, by decide⟩,⟨1067469, by decide⟩,⟨1067520, by decide⟩,⟨1067562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75724_1067563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75724 ⟨1067563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75724
    ⟨1067563, by decide⟩ (by decide) (![⟨612849, by decide⟩,⟨1067469, by decide⟩,⟨1067520, by decide⟩,⟨1067562, by decide⟩]) unmarked_context_11_75724_1067563 node_context_11_75724_1067563
  intro a
  fin_cases a
  · exact context_12_302896_612849
  · exact context_12_302897_1067469
  · exact context_12_302898_1067520
  · exact context_12_302899_1067562

theorem selected_cut_39353 : selected 9 ⟨1067629, by decide⟩
    (prefixPartial 12 302900) = some ⟨12, 2, 0, 1067629, 302900, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_302900_1067629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302900 ⟨1067629, by decide⟩ :=
  accepted_of_selected 12 302900 ⟨1067629, by decide⟩ ⟨12, 2, 0, 1067629, 302900, 3421, 65536⟩
    (by decide) selected_cut_39353

theorem selected_cut_39354 : selected 9 ⟨1067683, by decide⟩
    (prefixPartial 12 302901) = some ⟨12, 2, 0, 1067683, 302901, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_302901_1067683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302901 ⟨1067683, by decide⟩ :=
  accepted_of_selected 12 302901 ⟨1067683, by decide⟩ ⟨12, 2, 0, 1067683, 302901, 3729, 65536⟩
    (by decide) selected_cut_39354

theorem selected_cut_39355 : selected 9 ⟨1067738, by decide⟩
    (prefixPartial 12 302902) = some ⟨12, 2, 0, 1067738, 302902, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_302902_1067738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302902 ⟨1067738, by decide⟩ :=
  accepted_of_selected 12 302902 ⟨1067738, by decide⟩ ⟨12, 2, 0, 1067738, 302902, 3153, 65536⟩
    (by decide) selected_cut_39355

theorem selected_cut_39356 : selected 9 ⟨1067787, by decide⟩
    (prefixPartial 12 302903) = some ⟨12, 2, 0, 1067787, 302903, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_302903_1067787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302903 ⟨1067787, by decide⟩ :=
  accepted_of_selected 12 302903 ⟨1067787, by decide⟩ ⟨12, 2, 0, 1067787, 302903, 3141, 65536⟩
    (by decide) selected_cut_39356

theorem unmarked_context_11_75725_1067788 : frontier 10 ⟨1067788, by decide⟩
    (prefixCache 11 75725) (prefixPartial 11 75725) = false := by
  decide +kernel

theorem node_context_11_75725_1067788 : EJMOriginalGlobalDAGData.nodes 10 ⟨1067788, by decide⟩ =
    .split (coordinate 11) (![⟨1067629, by decide⟩,⟨1067683, by decide⟩,⟨1067738, by decide⟩,⟨1067787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75725_1067788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75725 ⟨1067788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75725
    ⟨1067788, by decide⟩ (by decide) (![⟨1067629, by decide⟩,⟨1067683, by decide⟩,⟨1067738, by decide⟩,⟨1067787, by decide⟩]) unmarked_context_11_75725_1067788 node_context_11_75725_1067788
  intro a
  fin_cases a
  · exact context_12_302900_1067629
  · exact context_12_302901_1067683
  · exact context_12_302902_1067738
  · exact context_12_302903_1067787

theorem selected_cut_39357 : selected 9 ⟨1067844, by decide⟩
    (prefixPartial 12 302904) = some ⟨12, 2, 0, 1067844, 302904, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_302904_1067844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302904 ⟨1067844, by decide⟩ :=
  accepted_of_selected 12 302904 ⟨1067844, by decide⟩ ⟨12, 2, 0, 1067844, 302904, 3173, 65536⟩
    (by decide) selected_cut_39357

theorem selected_cut_39358 : selected 9 ⟨1067898, by decide⟩
    (prefixPartial 12 302905) = some ⟨12, 2, 0, 1067898, 302905, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_302905_1067898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302905 ⟨1067898, by decide⟩ :=
  accepted_of_selected 12 302905 ⟨1067898, by decide⟩ ⟨12, 2, 0, 1067898, 302905, 3397, 65536⟩
    (by decide) selected_cut_39358

theorem selected_cut_39359 : selected 9 ⟨1067944, by decide⟩
    (prefixPartial 12 302906) = some ⟨12, 2, 0, 1067944, 302906, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_302906_1067944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302906 ⟨1067944, by decide⟩ :=
  accepted_of_selected 12 302906 ⟨1067944, by decide⟩ ⟨12, 2, 0, 1067944, 302906, 2901, 65536⟩
    (by decide) selected_cut_39359

theorem selected_cut_39360 : selected 9 ⟨1067991, by decide⟩
    (prefixPartial 12 302907) = some ⟨12, 2, 0, 1067991, 302907, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_302907_1067991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302907 ⟨1067991, by decide⟩ :=
  accepted_of_selected 12 302907 ⟨1067991, by decide⟩ ⟨12, 2, 0, 1067991, 302907, 2985, 65536⟩
    (by decide) selected_cut_39360

theorem unmarked_context_11_75726_1067992 : frontier 10 ⟨1067992, by decide⟩
    (prefixCache 11 75726) (prefixPartial 11 75726) = false := by
  decide +kernel

theorem node_context_11_75726_1067992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1067992, by decide⟩ =
    .split (coordinate 11) (![⟨1067844, by decide⟩,⟨1067898, by decide⟩,⟨1067944, by decide⟩,⟨1067991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75726_1067992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75726 ⟨1067992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75726
    ⟨1067992, by decide⟩ (by decide) (![⟨1067844, by decide⟩,⟨1067898, by decide⟩,⟨1067944, by decide⟩,⟨1067991, by decide⟩]) unmarked_context_11_75726_1067992 node_context_11_75726_1067992
  intro a
  fin_cases a
  · exact context_12_302904_1067844
  · exact context_12_302905_1067898
  · exact context_12_302906_1067944
  · exact context_12_302907_1067991

theorem selected_cut_39361 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75727) = some ⟨11, 1, 0, 977886, 75727, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75727_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75727 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75727 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75727, 1, 262144⟩
    (by decide) selected_cut_39361

theorem unmarked_context_10_18931_1067993 : frontier 11 ⟨1067993, by decide⟩
    (prefixCache 10 18931) (prefixPartial 10 18931) = false := by
  decide +kernel

theorem node_context_10_18931_1067993 : EJMOriginalGlobalDAGData.nodes 11 ⟨1067993, by decide⟩ =
    .split (coordinate 10) (![⟨1067563, by decide⟩,⟨1067788, by decide⟩,⟨1067992, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18931_1067993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18931 ⟨1067993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18931
    ⟨1067993, by decide⟩ (by decide) (![⟨1067563, by decide⟩,⟨1067788, by decide⟩,⟨1067992, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18931_1067993 node_context_10_18931_1067993
  intro a
  fin_cases a
  · exact context_11_75724_1067563
  · exact context_11_75725_1067788
  · exact context_11_75726_1067992
  · exact context_11_75727_977886

theorem unmarked_context_9_4732_1067994 : frontier 12 ⟨1067994, by decide⟩
    (prefixCache 9 4732) (prefixPartial 9 4732) = false := by
  decide +kernel

theorem node_context_9_4732_1067994 : EJMOriginalGlobalDAGData.nodes 12 ⟨1067994, by decide⟩ =
    .split (coordinate 9) (![⟨1065750, by decide⟩,⟨1066628, by decide⟩,⟨1067418, by decide⟩,⟨1067993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4732_1067994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4732 ⟨1067994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4732
    ⟨1067994, by decide⟩ (by decide) (![⟨1065750, by decide⟩,⟨1066628, by decide⟩,⟨1067418, by decide⟩,⟨1067993, by decide⟩]) unmarked_context_9_4732_1067994 node_context_9_4732_1067994
  intro a
  fin_cases a
  · exact context_10_18928_1065750
  · exact context_10_18929_1066628
  · exact context_10_18930_1067418
  · exact context_10_18931_1067993

theorem selected_cut_39362 : selected 9 ⟨1051681, by decide⟩
    (prefixPartial 12 302912) = some ⟨12, 1, 0, 1051681, 302912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302912_1051681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302912 ⟨1051681, by decide⟩ :=
  accepted_of_selected 12 302912 ⟨1051681, by decide⟩ ⟨12, 1, 0, 1051681, 302912, 1, 65536⟩
    (by decide) selected_cut_39362

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
