/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover294
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28323 : selected 10 ⟨715768, by decide⟩
    (prefixPartial 11 23079) = some ⟨11, 2, 0, 715768, 23079, 497, 262144⟩ := by
  decide +kernel

theorem context_11_23079_715768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23079 ⟨715768, by decide⟩ :=
  accepted_of_selected 11 23079 ⟨715768, by decide⟩ ⟨11, 2, 0, 715768, 23079, 497, 262144⟩
    (by decide) selected_cut_28323

theorem unmarked_context_10_5769_715769 : frontier 11 ⟨715769, by decide⟩
    (prefixCache 10 5769) (prefixPartial 10 5769) = false := by
  decide +kernel

theorem node_context_10_5769_715769 : EJMOriginalGlobalDAGData.nodes 11 ⟨715769, by decide⟩ =
    .split (coordinate 10) (![⟨715669, by decide⟩,⟨715725, by decide⟩,⟨715756, by decide⟩,⟨715768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5769_715769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5769 ⟨715769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5769
    ⟨715769, by decide⟩ (by decide) (![⟨715669, by decide⟩,⟨715725, by decide⟩,⟨715756, by decide⟩,⟨715768, by decide⟩]) unmarked_context_10_5769_715769 node_context_10_5769_715769
  intro a
  fin_cases a
  · exact context_11_23076_715669
  · exact context_11_23077_715725
  · exact context_11_23078_715756
  · exact context_11_23079_715768

theorem selected_cut_28324 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 5770) = some ⟨10, 1, 0, 145424, 5770, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5770_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5770 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 5770 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 5770, 1, 1048576⟩
    (by decide) selected_cut_28324

theorem selected_cut_28325 : selected 10 ⟨715858, by decide⟩
    (prefixPartial 11 23084) = some ⟨11, 2, 0, 715858, 23084, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_23084_715858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23084 ⟨715858, by decide⟩ :=
  accepted_of_selected 11 23084 ⟨715858, by decide⟩ ⟨11, 2, 0, 715858, 23084, 3485, 262144⟩
    (by decide) selected_cut_28325

theorem selected_cut_28326 : selected 10 ⟨715913, by decide⟩
    (prefixPartial 11 23085) = some ⟨11, 2, 0, 715913, 23085, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_23085_715913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23085 ⟨715913, by decide⟩ :=
  accepted_of_selected 11 23085 ⟨715913, by decide⟩ ⟨11, 2, 0, 715913, 23085, 2649, 262144⟩
    (by decide) selected_cut_28326

theorem selected_cut_28327 : selected 10 ⟨715946, by decide⟩
    (prefixPartial 11 23086) = some ⟨11, 2, 0, 715946, 23086, 1957, 262144⟩ := by
  decide +kernel

theorem context_11_23086_715946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23086 ⟨715946, by decide⟩ :=
  accepted_of_selected 11 23086 ⟨715946, by decide⟩ ⟨11, 2, 0, 715946, 23086, 1957, 262144⟩
    (by decide) selected_cut_28327

theorem selected_cut_28328 : selected 10 ⟨715964, by decide⟩
    (prefixPartial 11 23087) = some ⟨11, 2, 0, 715964, 23087, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_23087_715964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23087 ⟨715964, by decide⟩ :=
  accepted_of_selected 11 23087 ⟨715964, by decide⟩ ⟨11, 2, 0, 715964, 23087, 1237, 262144⟩
    (by decide) selected_cut_28328

theorem unmarked_context_10_5771_715965 : frontier 11 ⟨715965, by decide⟩
    (prefixCache 10 5771) (prefixPartial 10 5771) = false := by
  decide +kernel

theorem node_context_10_5771_715965 : EJMOriginalGlobalDAGData.nodes 11 ⟨715965, by decide⟩ =
    .split (coordinate 10) (![⟨715858, by decide⟩,⟨715913, by decide⟩,⟨715946, by decide⟩,⟨715964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5771_715965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5771 ⟨715965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5771
    ⟨715965, by decide⟩ (by decide) (![⟨715858, by decide⟩,⟨715913, by decide⟩,⟨715946, by decide⟩,⟨715964, by decide⟩]) unmarked_context_10_5771_715965 node_context_10_5771_715965
  intro a
  fin_cases a
  · exact context_11_23084_715858
  · exact context_11_23085_715913
  · exact context_11_23086_715946
  · exact context_11_23087_715964

theorem unmarked_context_9_1442_715966 : frontier 12 ⟨715966, by decide⟩
    (prefixCache 9 1442) (prefixPartial 9 1442) = false := by
  decide +kernel

theorem node_context_9_1442_715966 : EJMOriginalGlobalDAGData.nodes 12 ⟨715966, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨715769, by decide⟩,⟨145424, by decide⟩,⟨715965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1442_715966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1442 ⟨715966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1442
    ⟨715966, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨715769, by decide⟩,⟨145424, by decide⟩,⟨715965, by decide⟩]) unmarked_context_9_1442_715966 node_context_9_1442_715966
  intro a
  fin_cases a
  · exact context_10_5768_145424
  · exact context_10_5769_715769
  · exact context_10_5770_145424
  · exact context_10_5771_715965

theorem selected_cut_28329 : selected 12 ⟨716006, by decide⟩
    (prefixPartial 9 1443) = some ⟨9, 2, 0, 716006, 1443, 1009, 4194304⟩ := by
  decide +kernel

theorem context_9_1443_716006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1443 ⟨716006, by decide⟩ :=
  accepted_of_selected 9 1443 ⟨716006, by decide⟩ ⟨9, 2, 0, 716006, 1443, 1009, 4194304⟩
    (by decide) selected_cut_28329

theorem unmarked_context_8_360_716007 : frontier 13 ⟨716007, by decide⟩
    (prefixCache 8 360) (prefixPartial 8 360) = false := by
  decide +kernel

theorem node_context_8_360_716007 : EJMOriginalGlobalDAGData.nodes 13 ⟨716007, by decide⟩ =
    .split (coordinate 8) (![⟨714251, by decide⟩,⟨715573, by decide⟩,⟨715966, by decide⟩,⟨716006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_360_716007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 360 ⟨716007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 360
    ⟨716007, by decide⟩ (by decide) (![⟨714251, by decide⟩,⟨715573, by decide⟩,⟨715966, by decide⟩,⟨716006, by decide⟩]) unmarked_context_8_360_716007 node_context_8_360_716007
  intro a
  fin_cases a
  · exact context_9_1440_714251
  · exact context_9_1441_715573
  · exact context_9_1442_715966
  · exact context_9_1443_716006

theorem selected_cut_28330 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23104) = some ⟨11, 1, 0, 434745, 23104, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23104_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23104 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23104 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23104, 1, 262144⟩
    (by decide) selected_cut_28330

theorem selected_cut_28331 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 92420) = some ⟨12, 1, 0, 448748, 92420, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92420_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92420 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 92420 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 92420, 1, 65536⟩
    (by decide) selected_cut_28331

theorem selected_cut_28332 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 92421) = some ⟨12, 1, 0, 34034, 92421, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92421_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92421 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 92421 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 92421, 1, 65536⟩
    (by decide) selected_cut_28332

theorem selected_cut_28333 : selected 8 ⟨716065, by decide⟩
    (prefixPartial 13 369688) = some ⟨13, 2, 0, 716065, 369688, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_369688_716065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369688 ⟨716065, by decide⟩ :=
  accepted_of_selected 13 369688 ⟨716065, by decide⟩ ⟨13, 2, 0, 716065, 369688, 2821, 16384⟩
    (by decide) selected_cut_28333

theorem selected_cut_28334 : selected 8 ⟨716085, by decide⟩
    (prefixPartial 13 369689) = some ⟨13, 2, 0, 716085, 369689, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_369689_716085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369689 ⟨716085, by decide⟩ :=
  accepted_of_selected 13 369689 ⟨716085, by decide⟩ ⟨13, 2, 0, 716085, 369689, 2157, 16384⟩
    (by decide) selected_cut_28334

theorem selected_cut_28335 : selected 8 ⟨716112, by decide⟩
    (prefixPartial 13 369690) = some ⟨13, 2, 0, 716112, 369690, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_369690_716112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369690 ⟨716112, by decide⟩ :=
  accepted_of_selected 13 369690 ⟨716112, by decide⟩ ⟨13, 2, 0, 716112, 369690, 1925, 16384⟩
    (by decide) selected_cut_28335

theorem selected_cut_28336 : selected 8 ⟨716126, by decide⟩
    (prefixPartial 13 369691) = some ⟨13, 2, 0, 716126, 369691, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_369691_716126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369691 ⟨716126, by decide⟩ :=
  accepted_of_selected 13 369691 ⟨716126, by decide⟩ ⟨13, 2, 0, 716126, 369691, 1073, 16384⟩
    (by decide) selected_cut_28336

theorem unmarked_context_12_92422_716127 : frontier 9 ⟨716127, by decide⟩
    (prefixCache 12 92422) (prefixPartial 12 92422) = false := by
  decide +kernel

theorem node_context_12_92422_716127 : EJMOriginalGlobalDAGData.nodes 9 ⟨716127, by decide⟩ =
    .split (coordinate 12) (![⟨716065, by decide⟩,⟨716085, by decide⟩,⟨716112, by decide⟩,⟨716126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92422_716127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92422 ⟨716127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92422
    ⟨716127, by decide⟩ (by decide) (![⟨716065, by decide⟩,⟨716085, by decide⟩,⟨716112, by decide⟩,⟨716126, by decide⟩]) unmarked_context_12_92422_716127 node_context_12_92422_716127
  intro a
  fin_cases a
  · exact context_13_369688_716065
  · exact context_13_369689_716085
  · exact context_13_369690_716112
  · exact context_13_369691_716126

theorem selected_cut_28337 : selected 8 ⟨716177, by decide⟩
    (prefixPartial 13 369692) = some ⟨13, 2, 0, 716177, 369692, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_369692_716177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369692 ⟨716177, by decide⟩ :=
  accepted_of_selected 13 369692 ⟨716177, by decide⟩ ⟨13, 2, 0, 716177, 369692, 2933, 16384⟩
    (by decide) selected_cut_28337

theorem selected_cut_28338 : selected 8 ⟨716209, by decide⟩
    (prefixPartial 13 369693) = some ⟨13, 2, 0, 716209, 369693, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_369693_716209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369693 ⟨716209, by decide⟩ :=
  accepted_of_selected 13 369693 ⟨716209, by decide⟩ ⟨13, 2, 0, 716209, 369693, 2325, 16384⟩
    (by decide) selected_cut_28338

theorem selected_cut_28339 : selected 8 ⟨716230, by decide⟩
    (prefixPartial 13 369694) = some ⟨13, 2, 0, 716230, 369694, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_369694_716230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369694 ⟨716230, by decide⟩ :=
  accepted_of_selected 13 369694 ⟨716230, by decide⟩ ⟨13, 2, 0, 716230, 369694, 2021, 16384⟩
    (by decide) selected_cut_28339

theorem selected_cut_28340 : selected 8 ⟨716248, by decide⟩
    (prefixPartial 13 369695) = some ⟨13, 2, 0, 716248, 369695, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_369695_716248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369695 ⟨716248, by decide⟩ :=
  accepted_of_selected 13 369695 ⟨716248, by decide⟩ ⟨13, 2, 0, 716248, 369695, 1065, 16384⟩
    (by decide) selected_cut_28340

theorem unmarked_context_12_92423_716249 : frontier 9 ⟨716249, by decide⟩
    (prefixCache 12 92423) (prefixPartial 12 92423) = false := by
  decide +kernel

theorem node_context_12_92423_716249 : EJMOriginalGlobalDAGData.nodes 9 ⟨716249, by decide⟩ =
    .split (coordinate 12) (![⟨716177, by decide⟩,⟨716209, by decide⟩,⟨716230, by decide⟩,⟨716248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92423_716249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92423 ⟨716249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92423
    ⟨716249, by decide⟩ (by decide) (![⟨716177, by decide⟩,⟨716209, by decide⟩,⟨716230, by decide⟩,⟨716248, by decide⟩]) unmarked_context_12_92423_716249 node_context_12_92423_716249
  intro a
  fin_cases a
  · exact context_13_369692_716177
  · exact context_13_369693_716209
  · exact context_13_369694_716230
  · exact context_13_369695_716248

theorem unmarked_context_11_23105_716250 : frontier 10 ⟨716250, by decide⟩
    (prefixCache 11 23105) (prefixPartial 11 23105) = false := by
  decide +kernel

theorem node_context_11_23105_716250 : EJMOriginalGlobalDAGData.nodes 10 ⟨716250, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨716127, by decide⟩,⟨716249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23105_716250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23105 ⟨716250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23105
    ⟨716250, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨716127, by decide⟩,⟨716249, by decide⟩]) unmarked_context_11_23105_716250 node_context_11_23105_716250
  intro a
  fin_cases a
  · exact context_12_92420_448748
  · exact context_12_92421_34034
  · exact context_12_92422_716127
  · exact context_12_92423_716249

theorem selected_cut_28341 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 92424) = some ⟨12, 1, 0, 448748, 92424, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92424_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92424 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 92424 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 92424, 1, 65536⟩
    (by decide) selected_cut_28341

theorem selected_cut_28342 : selected 8 ⟨716337, by decide⟩
    (prefixPartial 13 369700) = some ⟨13, 2, 0, 716337, 369700, 3053, 16384⟩ := by
  decide +kernel

theorem context_13_369700_716337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369700 ⟨716337, by decide⟩ :=
  accepted_of_selected 13 369700 ⟨716337, by decide⟩ ⟨13, 2, 0, 716337, 369700, 3053, 16384⟩
    (by decide) selected_cut_28342

theorem selected_cut_28343 : selected 8 ⟨716373, by decide⟩
    (prefixPartial 13 369701) = some ⟨13, 2, 0, 716373, 369701, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_369701_716373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369701 ⟨716373, by decide⟩ :=
  accepted_of_selected 13 369701 ⟨716373, by decide⟩ ⟨13, 2, 0, 716373, 369701, 2017, 16384⟩
    (by decide) selected_cut_28343

theorem selected_cut_28344 : selected 8 ⟨716406, by decide⟩
    (prefixPartial 13 369702) = some ⟨13, 2, 0, 716406, 369702, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_369702_716406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369702 ⟨716406, by decide⟩ :=
  accepted_of_selected 13 369702 ⟨716406, by decide⟩ ⟨13, 2, 0, 716406, 369702, 1925, 16384⟩
    (by decide) selected_cut_28344

theorem selected_cut_28345 : selected 8 ⟨716419, by decide⟩
    (prefixPartial 13 369703) = some ⟨13, 2, 0, 716419, 369703, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_369703_716419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369703 ⟨716419, by decide⟩ :=
  accepted_of_selected 13 369703 ⟨716419, by decide⟩ ⟨13, 2, 0, 716419, 369703, 1021, 16384⟩
    (by decide) selected_cut_28345

theorem unmarked_context_12_92425_716420 : frontier 9 ⟨716420, by decide⟩
    (prefixCache 12 92425) (prefixPartial 12 92425) = false := by
  decide +kernel

theorem node_context_12_92425_716420 : EJMOriginalGlobalDAGData.nodes 9 ⟨716420, by decide⟩ =
    .split (coordinate 12) (![⟨716337, by decide⟩,⟨716373, by decide⟩,⟨716406, by decide⟩,⟨716419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92425_716420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92425 ⟨716420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92425
    ⟨716420, by decide⟩ (by decide) (![⟨716337, by decide⟩,⟨716373, by decide⟩,⟨716406, by decide⟩,⟨716419, by decide⟩]) unmarked_context_12_92425_716420 node_context_12_92425_716420
  intro a
  fin_cases a
  · exact context_13_369700_716337
  · exact context_13_369701_716373
  · exact context_13_369702_716406
  · exact context_13_369703_716419

theorem selected_cut_28346 : selected 9 ⟨347601, by decide⟩
    (prefixPartial 12 92426) = some ⟨12, 1, 0, 347601, 92426, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92426_347601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92426 ⟨347601, by decide⟩ :=
  accepted_of_selected 12 92426 ⟨347601, by decide⟩ ⟨12, 1, 0, 347601, 92426, 1, 65536⟩
    (by decide) selected_cut_28346

theorem selected_cut_28347 : selected 8 ⟨716470, by decide⟩
    (prefixPartial 13 369708) = some ⟨13, 2, 0, 716470, 369708, 2841, 16384⟩ := by
  decide +kernel

theorem context_13_369708_716470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369708 ⟨716470, by decide⟩ :=
  accepted_of_selected 13 369708 ⟨716470, by decide⟩ ⟨13, 2, 0, 716470, 369708, 2841, 16384⟩
    (by decide) selected_cut_28347

theorem selected_cut_28348 : selected 8 ⟨716501, by decide⟩
    (prefixPartial 13 369709) = some ⟨13, 2, 0, 716501, 369709, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_369709_716501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369709 ⟨716501, by decide⟩ :=
  accepted_of_selected 13 369709 ⟨716501, by decide⟩ ⟨13, 2, 0, 716501, 369709, 2653, 16384⟩
    (by decide) selected_cut_28348

theorem selected_cut_28349 : selected 8 ⟨716538, by decide⟩
    (prefixPartial 13 369710) = some ⟨13, 2, 0, 716538, 369710, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_369710_716538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369710 ⟨716538, by decide⟩ :=
  accepted_of_selected 13 369710 ⟨716538, by decide⟩ ⟨13, 2, 0, 716538, 369710, 2125, 16384⟩
    (by decide) selected_cut_28349

theorem selected_cut_28350 : selected 8 ⟨716548, by decide⟩
    (prefixPartial 13 369711) = some ⟨13, 2, 0, 716548, 369711, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_369711_716548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369711 ⟨716548, by decide⟩ :=
  accepted_of_selected 13 369711 ⟨716548, by decide⟩ ⟨13, 2, 0, 716548, 369711, 1065, 16384⟩
    (by decide) selected_cut_28350

theorem unmarked_context_12_92427_716549 : frontier 9 ⟨716549, by decide⟩
    (prefixCache 12 92427) (prefixPartial 12 92427) = false := by
  decide +kernel

theorem node_context_12_92427_716549 : EJMOriginalGlobalDAGData.nodes 9 ⟨716549, by decide⟩ =
    .split (coordinate 12) (![⟨716470, by decide⟩,⟨716501, by decide⟩,⟨716538, by decide⟩,⟨716548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92427_716549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92427 ⟨716549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92427
    ⟨716549, by decide⟩ (by decide) (![⟨716470, by decide⟩,⟨716501, by decide⟩,⟨716538, by decide⟩,⟨716548, by decide⟩]) unmarked_context_12_92427_716549 node_context_12_92427_716549
  intro a
  fin_cases a
  · exact context_13_369708_716470
  · exact context_13_369709_716501
  · exact context_13_369710_716538
  · exact context_13_369711_716548

theorem unmarked_context_11_23106_716550 : frontier 10 ⟨716550, by decide⟩
    (prefixCache 11 23106) (prefixPartial 11 23106) = false := by
  decide +kernel

theorem node_context_11_23106_716550 : EJMOriginalGlobalDAGData.nodes 10 ⟨716550, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨716420, by decide⟩,⟨347601, by decide⟩,⟨716549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23106_716550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23106 ⟨716550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23106
    ⟨716550, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨716420, by decide⟩,⟨347601, by decide⟩,⟨716549, by decide⟩]) unmarked_context_11_23106_716550 node_context_11_23106_716550
  intro a
  fin_cases a
  · exact context_12_92424_448748
  · exact context_12_92425_716420
  · exact context_12_92426_347601
  · exact context_12_92427_716549

theorem selected_cut_28351 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 92428) = some ⟨12, 1, 0, 448748, 92428, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92428_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92428 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 92428 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 92428, 1, 65536⟩
    (by decide) selected_cut_28351

theorem selected_cut_28352 : selected 8 ⟨716598, by decide⟩
    (prefixPartial 13 369716) = some ⟨13, 2, 0, 716598, 369716, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_369716_716598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369716 ⟨716598, by decide⟩ :=
  accepted_of_selected 13 369716 ⟨716598, by decide⟩ ⟨13, 2, 0, 716598, 369716, 3001, 16384⟩
    (by decide) selected_cut_28352

theorem selected_cut_28353 : selected 8 ⟨716622, by decide⟩
    (prefixPartial 13 369717) = some ⟨13, 2, 0, 716622, 369717, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_369717_716622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369717 ⟨716622, by decide⟩ :=
  accepted_of_selected 13 369717 ⟨716622, by decide⟩ ⟨13, 2, 0, 716622, 369717, 2193, 16384⟩
    (by decide) selected_cut_28353

theorem selected_cut_28354 : selected 8 ⟨716640, by decide⟩
    (prefixPartial 13 369718) = some ⟨13, 2, 0, 716640, 369718, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_369718_716640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369718 ⟨716640, by decide⟩ :=
  accepted_of_selected 13 369718 ⟨716640, by decide⟩ ⟨13, 2, 0, 716640, 369718, 1933, 16384⟩
    (by decide) selected_cut_28354

theorem selected_cut_28355 : selected 8 ⟨716653, by decide⟩
    (prefixPartial 13 369719) = some ⟨13, 2, 0, 716653, 369719, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_369719_716653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369719 ⟨716653, by decide⟩ :=
  accepted_of_selected 13 369719 ⟨716653, by decide⟩ ⟨13, 2, 0, 716653, 369719, 1077, 16384⟩
    (by decide) selected_cut_28355

theorem unmarked_context_12_92429_716654 : frontier 9 ⟨716654, by decide⟩
    (prefixCache 12 92429) (prefixPartial 12 92429) = false := by
  decide +kernel

theorem node_context_12_92429_716654 : EJMOriginalGlobalDAGData.nodes 9 ⟨716654, by decide⟩ =
    .split (coordinate 12) (![⟨716598, by decide⟩,⟨716622, by decide⟩,⟨716640, by decide⟩,⟨716653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92429_716654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92429 ⟨716654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92429
    ⟨716654, by decide⟩ (by decide) (![⟨716598, by decide⟩,⟨716622, by decide⟩,⟨716640, by decide⟩,⟨716653, by decide⟩]) unmarked_context_12_92429_716654 node_context_12_92429_716654
  intro a
  fin_cases a
  · exact context_13_369716_716598
  · exact context_13_369717_716622
  · exact context_13_369718_716640
  · exact context_13_369719_716653

theorem selected_cut_28356 : selected 8 ⟨716711, by decide⟩
    (prefixPartial 13 369720) = some ⟨13, 2, 0, 716711, 369720, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_369720_716711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369720 ⟨716711, by decide⟩ :=
  accepted_of_selected 13 369720 ⟨716711, by decide⟩ ⟨13, 2, 0, 716711, 369720, 3025, 16384⟩
    (by decide) selected_cut_28356

theorem selected_cut_28357 : selected 8 ⟨716761, by decide⟩
    (prefixPartial 13 369721) = some ⟨13, 2, 0, 716761, 369721, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_369721_716761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369721 ⟨716761, by decide⟩ :=
  accepted_of_selected 13 369721 ⟨716761, by decide⟩ ⟨13, 2, 0, 716761, 369721, 2633, 16384⟩
    (by decide) selected_cut_28357

theorem selected_cut_28358 : selected 8 ⟨716804, by decide⟩
    (prefixPartial 13 369722) = some ⟨13, 2, 0, 716804, 369722, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_369722_716804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369722 ⟨716804, by decide⟩ :=
  accepted_of_selected 13 369722 ⟨716804, by decide⟩ ⟨13, 2, 0, 716804, 369722, 2229, 16384⟩
    (by decide) selected_cut_28358

theorem selected_cut_28359 : selected 8 ⟨716841, by decide⟩
    (prefixPartial 13 369723) = some ⟨13, 2, 0, 716841, 369723, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_369723_716841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369723 ⟨716841, by decide⟩ :=
  accepted_of_selected 13 369723 ⟨716841, by decide⟩ ⟨13, 2, 0, 716841, 369723, 1277, 16384⟩
    (by decide) selected_cut_28359

theorem unmarked_context_12_92430_716842 : frontier 9 ⟨716842, by decide⟩
    (prefixCache 12 92430) (prefixPartial 12 92430) = false := by
  decide +kernel

theorem node_context_12_92430_716842 : EJMOriginalGlobalDAGData.nodes 9 ⟨716842, by decide⟩ =
    .split (coordinate 12) (![⟨716711, by decide⟩,⟨716761, by decide⟩,⟨716804, by decide⟩,⟨716841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92430_716842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92430 ⟨716842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92430
    ⟨716842, by decide⟩ (by decide) (![⟨716711, by decide⟩,⟨716761, by decide⟩,⟨716804, by decide⟩,⟨716841, by decide⟩]) unmarked_context_12_92430_716842 node_context_12_92430_716842
  intro a
  fin_cases a
  · exact context_13_369720_716711
  · exact context_13_369721_716761
  · exact context_13_369722_716804
  · exact context_13_369723_716841

theorem selected_cut_28360 : selected 8 ⟨716895, by decide⟩
    (prefixPartial 13 369724) = some ⟨13, 2, 0, 716895, 369724, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_369724_716895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369724 ⟨716895, by decide⟩ :=
  accepted_of_selected 13 369724 ⟨716895, by decide⟩ ⟨13, 2, 0, 716895, 369724, 3049, 16384⟩
    (by decide) selected_cut_28360

theorem selected_cut_28361 : selected 8 ⟨716932, by decide⟩
    (prefixPartial 13 369725) = some ⟨13, 2, 0, 716932, 369725, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_369725_716932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369725 ⟨716932, by decide⟩ :=
  accepted_of_selected 13 369725 ⟨716932, by decide⟩ ⟨13, 2, 0, 716932, 369725, 2705, 16384⟩
    (by decide) selected_cut_28361

theorem selected_cut_28362 : selected 8 ⟨716965, by decide⟩
    (prefixPartial 13 369726) = some ⟨13, 2, 0, 716965, 369726, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_369726_716965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369726 ⟨716965, by decide⟩ :=
  accepted_of_selected 13 369726 ⟨716965, by decide⟩ ⟨13, 2, 0, 716965, 369726, 2177, 16384⟩
    (by decide) selected_cut_28362

theorem selected_cut_28363 : selected 8 ⟨716980, by decide⟩
    (prefixPartial 13 369727) = some ⟨13, 2, 0, 716980, 369727, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_369727_716980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369727 ⟨716980, by decide⟩ :=
  accepted_of_selected 13 369727 ⟨716980, by decide⟩ ⟨13, 2, 0, 716980, 369727, 1161, 16384⟩
    (by decide) selected_cut_28363

theorem unmarked_context_12_92431_716981 : frontier 9 ⟨716981, by decide⟩
    (prefixCache 12 92431) (prefixPartial 12 92431) = false := by
  decide +kernel

theorem node_context_12_92431_716981 : EJMOriginalGlobalDAGData.nodes 9 ⟨716981, by decide⟩ =
    .split (coordinate 12) (![⟨716895, by decide⟩,⟨716932, by decide⟩,⟨716965, by decide⟩,⟨716980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92431_716981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92431 ⟨716981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92431
    ⟨716981, by decide⟩ (by decide) (![⟨716895, by decide⟩,⟨716932, by decide⟩,⟨716965, by decide⟩,⟨716980, by decide⟩]) unmarked_context_12_92431_716981 node_context_12_92431_716981
  intro a
  fin_cases a
  · exact context_13_369724_716895
  · exact context_13_369725_716932
  · exact context_13_369726_716965
  · exact context_13_369727_716980

theorem unmarked_context_11_23107_716982 : frontier 10 ⟨716982, by decide⟩
    (prefixCache 11 23107) (prefixPartial 11 23107) = false := by
  decide +kernel

theorem node_context_11_23107_716982 : EJMOriginalGlobalDAGData.nodes 10 ⟨716982, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨716654, by decide⟩,⟨716842, by decide⟩,⟨716981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23107_716982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23107 ⟨716982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23107
    ⟨716982, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨716654, by decide⟩,⟨716842, by decide⟩,⟨716981, by decide⟩]) unmarked_context_11_23107_716982 node_context_11_23107_716982
  intro a
  fin_cases a
  · exact context_12_92428_448748
  · exact context_12_92429_716654
  · exact context_12_92430_716842
  · exact context_12_92431_716981

theorem unmarked_context_10_5776_716983 : frontier 11 ⟨716983, by decide⟩
    (prefixCache 10 5776) (prefixPartial 10 5776) = false := by
  decide +kernel

theorem node_context_10_5776_716983 : EJMOriginalGlobalDAGData.nodes 11 ⟨716983, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨716250, by decide⟩,⟨716550, by decide⟩,⟨716982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5776_716983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5776 ⟨716983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5776
    ⟨716983, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨716250, by decide⟩,⟨716550, by decide⟩,⟨716982, by decide⟩]) unmarked_context_10_5776_716983 node_context_10_5776_716983
  intro a
  fin_cases a
  · exact context_11_23104_434745
  · exact context_11_23105_716250
  · exact context_11_23106_716550
  · exact context_11_23107_716982

theorem selected_cut_28364 : selected 8 ⟨717004, by decide⟩
    (prefixPartial 13 369728) = some ⟨13, 2, 0, 717004, 369728, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_369728_717004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369728 ⟨717004, by decide⟩ :=
  accepted_of_selected 13 369728 ⟨717004, by decide⟩ ⟨13, 2, 0, 717004, 369728, 1577, 16384⟩
    (by decide) selected_cut_28364

theorem selected_cut_28365 : selected 8 ⟨717028, by decide⟩
    (prefixPartial 13 369729) = some ⟨13, 2, 0, 717028, 369729, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_369729_717028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369729 ⟨717028, by decide⟩ :=
  accepted_of_selected 13 369729 ⟨717028, by decide⟩ ⟨13, 2, 0, 717028, 369729, 1485, 16384⟩
    (by decide) selected_cut_28365

theorem selected_cut_28366 : selected 8 ⟨717045, by decide⟩
    (prefixPartial 13 369730) = some ⟨13, 2, 0, 717045, 369730, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_369730_717045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369730 ⟨717045, by decide⟩ :=
  accepted_of_selected 13 369730 ⟨717045, by decide⟩ ⟨13, 2, 0, 717045, 369730, 1169, 16384⟩
    (by decide) selected_cut_28366

theorem selected_cut_28367 : selected 8 ⟨717054, by decide⟩
    (prefixPartial 13 369731) = some ⟨13, 2, 0, 717054, 369731, 721, 16384⟩ := by
  decide +kernel

theorem context_13_369731_717054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369731 ⟨717054, by decide⟩ :=
  accepted_of_selected 13 369731 ⟨717054, by decide⟩ ⟨13, 2, 0, 717054, 369731, 721, 16384⟩
    (by decide) selected_cut_28367

theorem unmarked_context_12_92432_717055 : frontier 9 ⟨717055, by decide⟩
    (prefixCache 12 92432) (prefixPartial 12 92432) = false := by
  decide +kernel

theorem node_context_12_92432_717055 : EJMOriginalGlobalDAGData.nodes 9 ⟨717055, by decide⟩ =
    .split (coordinate 12) (![⟨717004, by decide⟩,⟨717028, by decide⟩,⟨717045, by decide⟩,⟨717054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92432_717055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92432 ⟨717055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92432
    ⟨717055, by decide⟩ (by decide) (![⟨717004, by decide⟩,⟨717028, by decide⟩,⟨717045, by decide⟩,⟨717054, by decide⟩]) unmarked_context_12_92432_717055 node_context_12_92432_717055
  intro a
  fin_cases a
  · exact context_13_369728_717004
  · exact context_13_369729_717028
  · exact context_13_369730_717045
  · exact context_13_369731_717054

theorem selected_cut_28368 : selected 8 ⟨717075, by decide⟩
    (prefixPartial 13 369732) = some ⟨13, 2, 0, 717075, 369732, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_369732_717075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369732 ⟨717075, by decide⟩ :=
  accepted_of_selected 13 369732 ⟨717075, by decide⟩ ⟨13, 2, 0, 717075, 369732, 1457, 16384⟩
    (by decide) selected_cut_28368

theorem selected_cut_28369 : selected 8 ⟨717094, by decide⟩
    (prefixPartial 13 369733) = some ⟨13, 2, 0, 717094, 369733, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_369733_717094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369733 ⟨717094, by decide⟩ :=
  accepted_of_selected 13 369733 ⟨717094, by decide⟩ ⟨13, 2, 0, 717094, 369733, 1217, 16384⟩
    (by decide) selected_cut_28369

theorem selected_cut_28370 : selected 8 ⟨717110, by decide⟩
    (prefixPartial 13 369734) = some ⟨13, 2, 0, 717110, 369734, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_369734_717110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369734 ⟨717110, by decide⟩ :=
  accepted_of_selected 13 369734 ⟨717110, by decide⟩ ⟨13, 2, 0, 717110, 369734, 1157, 16384⟩
    (by decide) selected_cut_28370

theorem selected_cut_28371 : selected 8 ⟨717118, by decide⟩
    (prefixPartial 13 369735) = some ⟨13, 2, 0, 717118, 369735, 709, 16384⟩ := by
  decide +kernel

theorem context_13_369735_717118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369735 ⟨717118, by decide⟩ :=
  accepted_of_selected 13 369735 ⟨717118, by decide⟩ ⟨13, 2, 0, 717118, 369735, 709, 16384⟩
    (by decide) selected_cut_28371

theorem unmarked_context_12_92433_717119 : frontier 9 ⟨717119, by decide⟩
    (prefixCache 12 92433) (prefixPartial 12 92433) = false := by
  decide +kernel

theorem node_context_12_92433_717119 : EJMOriginalGlobalDAGData.nodes 9 ⟨717119, by decide⟩ =
    .split (coordinate 12) (![⟨717075, by decide⟩,⟨717094, by decide⟩,⟨717110, by decide⟩,⟨717118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92433_717119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92433 ⟨717119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92433
    ⟨717119, by decide⟩ (by decide) (![⟨717075, by decide⟩,⟨717094, by decide⟩,⟨717110, by decide⟩,⟨717118, by decide⟩]) unmarked_context_12_92433_717119 node_context_12_92433_717119
  intro a
  fin_cases a
  · exact context_13_369732_717075
  · exact context_13_369733_717094
  · exact context_13_369734_717110
  · exact context_13_369735_717118

theorem selected_cut_28372 : selected 8 ⟨717145, by decide⟩
    (prefixPartial 13 369736) = some ⟨13, 2, 0, 717145, 369736, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_369736_717145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369736 ⟨717145, by decide⟩ :=
  accepted_of_selected 13 369736 ⟨717145, by decide⟩ ⟨13, 2, 0, 717145, 369736, 1585, 16384⟩
    (by decide) selected_cut_28372

theorem selected_cut_28373 : selected 8 ⟨717168, by decide⟩
    (prefixPartial 13 369737) = some ⟨13, 2, 0, 717168, 369737, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_369737_717168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369737 ⟨717168, by decide⟩ :=
  accepted_of_selected 13 369737 ⟨717168, by decide⟩ ⟨13, 2, 0, 717168, 369737, 1589, 16384⟩
    (by decide) selected_cut_28373

theorem selected_cut_28374 : selected 8 ⟨717185, by decide⟩
    (prefixPartial 13 369738) = some ⟨13, 2, 0, 717185, 369738, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_369738_717185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369738 ⟨717185, by decide⟩ :=
  accepted_of_selected 13 369738 ⟨717185, by decide⟩ ⟨13, 2, 0, 717185, 369738, 1317, 16384⟩
    (by decide) selected_cut_28374

theorem selected_cut_28375 : selected 8 ⟨717194, by decide⟩
    (prefixPartial 13 369739) = some ⟨13, 2, 0, 717194, 369739, 845, 16384⟩ := by
  decide +kernel

theorem context_13_369739_717194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369739 ⟨717194, by decide⟩ :=
  accepted_of_selected 13 369739 ⟨717194, by decide⟩ ⟨13, 2, 0, 717194, 369739, 845, 16384⟩
    (by decide) selected_cut_28375

theorem unmarked_context_12_92434_717195 : frontier 9 ⟨717195, by decide⟩
    (prefixCache 12 92434) (prefixPartial 12 92434) = false := by
  decide +kernel

theorem node_context_12_92434_717195 : EJMOriginalGlobalDAGData.nodes 9 ⟨717195, by decide⟩ =
    .split (coordinate 12) (![⟨717145, by decide⟩,⟨717168, by decide⟩,⟨717185, by decide⟩,⟨717194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92434_717195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92434 ⟨717195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92434
    ⟨717195, by decide⟩ (by decide) (![⟨717145, by decide⟩,⟨717168, by decide⟩,⟨717185, by decide⟩,⟨717194, by decide⟩]) unmarked_context_12_92434_717195 node_context_12_92434_717195
  intro a
  fin_cases a
  · exact context_13_369736_717145
  · exact context_13_369737_717168
  · exact context_13_369738_717185
  · exact context_13_369739_717194

theorem selected_cut_28376 : selected 8 ⟨717216, by decide⟩
    (prefixPartial 13 369740) = some ⟨13, 2, 0, 717216, 369740, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_369740_717216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369740 ⟨717216, by decide⟩ :=
  accepted_of_selected 13 369740 ⟨717216, by decide⟩ ⟨13, 2, 0, 717216, 369740, 1653, 16384⟩
    (by decide) selected_cut_28376

theorem selected_cut_28377 : selected 8 ⟨717238, by decide⟩
    (prefixPartial 13 369741) = some ⟨13, 2, 0, 717238, 369741, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_369741_717238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369741 ⟨717238, by decide⟩ :=
  accepted_of_selected 13 369741 ⟨717238, by decide⟩ ⟨13, 2, 0, 717238, 369741, 1749, 16384⟩
    (by decide) selected_cut_28377

theorem selected_cut_28378 : selected 8 ⟨717257, by decide⟩
    (prefixPartial 13 369742) = some ⟨13, 2, 0, 717257, 369742, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_369742_717257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369742 ⟨717257, by decide⟩ :=
  accepted_of_selected 13 369742 ⟨717257, by decide⟩ ⟨13, 2, 0, 717257, 369742, 1321, 16384⟩
    (by decide) selected_cut_28378

theorem selected_cut_28379 : selected 8 ⟨717263, by decide⟩
    (prefixPartial 13 369743) = some ⟨13, 2, 0, 717263, 369743, 821, 16384⟩ := by
  decide +kernel

theorem context_13_369743_717263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369743 ⟨717263, by decide⟩ :=
  accepted_of_selected 13 369743 ⟨717263, by decide⟩ ⟨13, 2, 0, 717263, 369743, 821, 16384⟩
    (by decide) selected_cut_28379

theorem unmarked_context_12_92435_717264 : frontier 9 ⟨717264, by decide⟩
    (prefixCache 12 92435) (prefixPartial 12 92435) = false := by
  decide +kernel

theorem node_context_12_92435_717264 : EJMOriginalGlobalDAGData.nodes 9 ⟨717264, by decide⟩ =
    .split (coordinate 12) (![⟨717216, by decide⟩,⟨717238, by decide⟩,⟨717257, by decide⟩,⟨717263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92435_717264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92435 ⟨717264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92435
    ⟨717264, by decide⟩ (by decide) (![⟨717216, by decide⟩,⟨717238, by decide⟩,⟨717257, by decide⟩,⟨717263, by decide⟩]) unmarked_context_12_92435_717264 node_context_12_92435_717264
  intro a
  fin_cases a
  · exact context_13_369740_717216
  · exact context_13_369741_717238
  · exact context_13_369742_717257
  · exact context_13_369743_717263

theorem unmarked_context_11_23108_717265 : frontier 10 ⟨717265, by decide⟩
    (prefixCache 11 23108) (prefixPartial 11 23108) = false := by
  decide +kernel

theorem node_context_11_23108_717265 : EJMOriginalGlobalDAGData.nodes 10 ⟨717265, by decide⟩ =
    .split (coordinate 11) (![⟨717055, by decide⟩,⟨717119, by decide⟩,⟨717195, by decide⟩,⟨717264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23108_717265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23108 ⟨717265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23108
    ⟨717265, by decide⟩ (by decide) (![⟨717055, by decide⟩,⟨717119, by decide⟩,⟨717195, by decide⟩,⟨717264, by decide⟩]) unmarked_context_11_23108_717265 node_context_11_23108_717265
  intro a
  fin_cases a
  · exact context_12_92432_717055
  · exact context_12_92433_717119
  · exact context_12_92434_717195
  · exact context_12_92435_717264

theorem selected_cut_28380 : selected 8 ⟨717283, by decide⟩
    (prefixPartial 13 369744) = some ⟨13, 2, 0, 717283, 369744, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_369744_717283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369744 ⟨717283, by decide⟩ :=
  accepted_of_selected 13 369744 ⟨717283, by decide⟩ ⟨13, 2, 0, 717283, 369744, 1265, 16384⟩
    (by decide) selected_cut_28380

theorem selected_cut_28381 : selected 8 ⟨717303, by decide⟩
    (prefixPartial 13 369745) = some ⟨13, 2, 0, 717303, 369745, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_369745_717303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369745 ⟨717303, by decide⟩ :=
  accepted_of_selected 13 369745 ⟨717303, by decide⟩ ⟨13, 2, 0, 717303, 369745, 1449, 16384⟩
    (by decide) selected_cut_28381

theorem selected_cut_28382 : selected 8 ⟨717318, by decide⟩
    (prefixPartial 13 369746) = some ⟨13, 2, 0, 717318, 369746, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_369746_717318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369746 ⟨717318, by decide⟩ :=
  accepted_of_selected 13 369746 ⟨717318, by decide⟩ ⟨13, 2, 0, 717318, 369746, 1065, 16384⟩
    (by decide) selected_cut_28382

theorem selected_cut_28383 : selected 8 ⟨717325, by decide⟩
    (prefixPartial 13 369747) = some ⟨13, 2, 0, 717325, 369747, 729, 16384⟩ := by
  decide +kernel

theorem context_13_369747_717325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369747 ⟨717325, by decide⟩ :=
  accepted_of_selected 13 369747 ⟨717325, by decide⟩ ⟨13, 2, 0, 717325, 369747, 729, 16384⟩
    (by decide) selected_cut_28383

theorem unmarked_context_12_92436_717326 : frontier 9 ⟨717326, by decide⟩
    (prefixCache 12 92436) (prefixPartial 12 92436) = false := by
  decide +kernel

theorem node_context_12_92436_717326 : EJMOriginalGlobalDAGData.nodes 9 ⟨717326, by decide⟩ =
    .split (coordinate 12) (![⟨717283, by decide⟩,⟨717303, by decide⟩,⟨717318, by decide⟩,⟨717325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92436_717326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92436 ⟨717326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92436
    ⟨717326, by decide⟩ (by decide) (![⟨717283, by decide⟩,⟨717303, by decide⟩,⟨717318, by decide⟩,⟨717325, by decide⟩]) unmarked_context_12_92436_717326 node_context_12_92436_717326
  intro a
  fin_cases a
  · exact context_13_369744_717283
  · exact context_13_369745_717303
  · exact context_13_369746_717318
  · exact context_13_369747_717325

theorem selected_cut_28384 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 92437) = some ⟨12, 1, 0, 439069, 92437, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92437_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92437 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 92437 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 92437, 1, 65536⟩
    (by decide) selected_cut_28384

theorem selected_cut_28385 : selected 8 ⟨717343, by decide⟩
    (prefixPartial 13 369752) = some ⟨13, 2, 0, 717343, 369752, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_369752_717343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369752 ⟨717343, by decide⟩ :=
  accepted_of_selected 13 369752 ⟨717343, by decide⟩ ⟨13, 2, 0, 717343, 369752, 1337, 16384⟩
    (by decide) selected_cut_28385

theorem selected_cut_28386 : selected 8 ⟨717364, by decide⟩
    (prefixPartial 13 369753) = some ⟨13, 2, 0, 717364, 369753, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_369753_717364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369753 ⟨717364, by decide⟩ :=
  accepted_of_selected 13 369753 ⟨717364, by decide⟩ ⟨13, 2, 0, 717364, 369753, 1525, 16384⟩
    (by decide) selected_cut_28386

theorem selected_cut_28387 : selected 8 ⟨717378, by decide⟩
    (prefixPartial 13 369754) = some ⟨13, 2, 0, 717378, 369754, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_369754_717378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369754 ⟨717378, by decide⟩ :=
  accepted_of_selected 13 369754 ⟨717378, by decide⟩ ⟨13, 2, 0, 717378, 369754, 1149, 16384⟩
    (by decide) selected_cut_28387

theorem selected_cut_28388 : selected 8 ⟨717386, by decide⟩
    (prefixPartial 13 369755) = some ⟨13, 2, 0, 717386, 369755, 817, 16384⟩ := by
  decide +kernel

theorem context_13_369755_717386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369755 ⟨717386, by decide⟩ :=
  accepted_of_selected 13 369755 ⟨717386, by decide⟩ ⟨13, 2, 0, 717386, 369755, 817, 16384⟩
    (by decide) selected_cut_28388

theorem unmarked_context_12_92438_717387 : frontier 9 ⟨717387, by decide⟩
    (prefixCache 12 92438) (prefixPartial 12 92438) = false := by
  decide +kernel

theorem node_context_12_92438_717387 : EJMOriginalGlobalDAGData.nodes 9 ⟨717387, by decide⟩ =
    .split (coordinate 12) (![⟨717343, by decide⟩,⟨717364, by decide⟩,⟨717378, by decide⟩,⟨717386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92438_717387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92438 ⟨717387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92438
    ⟨717387, by decide⟩ (by decide) (![⟨717343, by decide⟩,⟨717364, by decide⟩,⟨717378, by decide⟩,⟨717386, by decide⟩]) unmarked_context_12_92438_717387 node_context_12_92438_717387
  intro a
  fin_cases a
  · exact context_13_369752_717343
  · exact context_13_369753_717364
  · exact context_13_369754_717378
  · exact context_13_369755_717386

theorem selected_cut_28389 : selected 8 ⟨717406, by decide⟩
    (prefixPartial 13 369756) = some ⟨13, 2, 0, 717406, 369756, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_369756_717406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369756 ⟨717406, by decide⟩ :=
  accepted_of_selected 13 369756 ⟨717406, by decide⟩ ⟨13, 2, 0, 717406, 369756, 1425, 16384⟩
    (by decide) selected_cut_28389

theorem selected_cut_28390 : selected 8 ⟨717428, by decide⟩
    (prefixPartial 13 369757) = some ⟨13, 2, 0, 717428, 369757, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_369757_717428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369757 ⟨717428, by decide⟩ :=
  accepted_of_selected 13 369757 ⟨717428, by decide⟩ ⟨13, 2, 0, 717428, 369757, 1717, 16384⟩
    (by decide) selected_cut_28390

theorem selected_cut_28391 : selected 8 ⟨717444, by decide⟩
    (prefixPartial 13 369758) = some ⟨13, 2, 0, 717444, 369758, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_369758_717444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369758 ⟨717444, by decide⟩ :=
  accepted_of_selected 13 369758 ⟨717444, by decide⟩ ⟨13, 2, 0, 717444, 369758, 1253, 16384⟩
    (by decide) selected_cut_28391

theorem selected_cut_28392 : selected 8 ⟨717451, by decide⟩
    (prefixPartial 13 369759) = some ⟨13, 2, 0, 717451, 369759, 729, 16384⟩ := by
  decide +kernel

theorem context_13_369759_717451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369759 ⟨717451, by decide⟩ :=
  accepted_of_selected 13 369759 ⟨717451, by decide⟩ ⟨13, 2, 0, 717451, 369759, 729, 16384⟩
    (by decide) selected_cut_28392

theorem unmarked_context_12_92439_717452 : frontier 9 ⟨717452, by decide⟩
    (prefixCache 12 92439) (prefixPartial 12 92439) = false := by
  decide +kernel

theorem node_context_12_92439_717452 : EJMOriginalGlobalDAGData.nodes 9 ⟨717452, by decide⟩ =
    .split (coordinate 12) (![⟨717406, by decide⟩,⟨717428, by decide⟩,⟨717444, by decide⟩,⟨717451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92439_717452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92439 ⟨717452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92439
    ⟨717452, by decide⟩ (by decide) (![⟨717406, by decide⟩,⟨717428, by decide⟩,⟨717444, by decide⟩,⟨717451, by decide⟩]) unmarked_context_12_92439_717452 node_context_12_92439_717452
  intro a
  fin_cases a
  · exact context_13_369756_717406
  · exact context_13_369757_717428
  · exact context_13_369758_717444
  · exact context_13_369759_717451

theorem unmarked_context_11_23109_717453 : frontier 10 ⟨717453, by decide⟩
    (prefixCache 11 23109) (prefixPartial 11 23109) = false := by
  decide +kernel

theorem node_context_11_23109_717453 : EJMOriginalGlobalDAGData.nodes 10 ⟨717453, by decide⟩ =
    .split (coordinate 11) (![⟨717326, by decide⟩,⟨439069, by decide⟩,⟨717387, by decide⟩,⟨717452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23109_717453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23109 ⟨717453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23109
    ⟨717453, by decide⟩ (by decide) (![⟨717326, by decide⟩,⟨439069, by decide⟩,⟨717387, by decide⟩,⟨717452, by decide⟩]) unmarked_context_11_23109_717453 node_context_11_23109_717453
  intro a
  fin_cases a
  · exact context_12_92436_717326
  · exact context_12_92437_439069
  · exact context_12_92438_717387
  · exact context_12_92439_717452

theorem selected_cut_28393 : selected 8 ⟨717469, by decide⟩
    (prefixPartial 13 369760) = some ⟨13, 2, 0, 717469, 369760, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_369760_717469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369760 ⟨717469, by decide⟩ :=
  accepted_of_selected 13 369760 ⟨717469, by decide⟩ ⟨13, 2, 0, 717469, 369760, 1185, 16384⟩
    (by decide) selected_cut_28393

theorem selected_cut_28394 : selected 8 ⟨717489, by decide⟩
    (prefixPartial 13 369761) = some ⟨13, 2, 0, 717489, 369761, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_369761_717489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369761 ⟨717489, by decide⟩ :=
  accepted_of_selected 13 369761 ⟨717489, by decide⟩ ⟨13, 2, 0, 717489, 369761, 1385, 16384⟩
    (by decide) selected_cut_28394

theorem selected_cut_28395 : selected 8 ⟨717508, by decide⟩
    (prefixPartial 13 369762) = some ⟨13, 2, 0, 717508, 369762, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_369762_717508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369762 ⟨717508, by decide⟩ :=
  accepted_of_selected 13 369762 ⟨717508, by decide⟩ ⟨13, 2, 0, 717508, 369762, 1141, 16384⟩
    (by decide) selected_cut_28395

theorem selected_cut_28396 : selected 8 ⟨717516, by decide⟩
    (prefixPartial 13 369763) = some ⟨13, 2, 0, 717516, 369763, 749, 16384⟩ := by
  decide +kernel

theorem context_13_369763_717516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369763 ⟨717516, by decide⟩ :=
  accepted_of_selected 13 369763 ⟨717516, by decide⟩ ⟨13, 2, 0, 717516, 369763, 749, 16384⟩
    (by decide) selected_cut_28396

theorem unmarked_context_12_92440_717517 : frontier 9 ⟨717517, by decide⟩
    (prefixCache 12 92440) (prefixPartial 12 92440) = false := by
  decide +kernel

theorem node_context_12_92440_717517 : EJMOriginalGlobalDAGData.nodes 9 ⟨717517, by decide⟩ =
    .split (coordinate 12) (![⟨717469, by decide⟩,⟨717489, by decide⟩,⟨717508, by decide⟩,⟨717516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92440_717517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92440 ⟨717517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92440
    ⟨717517, by decide⟩ (by decide) (![⟨717469, by decide⟩,⟨717489, by decide⟩,⟨717508, by decide⟩,⟨717516, by decide⟩]) unmarked_context_12_92440_717517 node_context_12_92440_717517
  intro a
  fin_cases a
  · exact context_13_369760_717469
  · exact context_13_369761_717489
  · exact context_13_369762_717508
  · exact context_13_369763_717516

theorem selected_cut_28397 : selected 8 ⟨717534, by decide⟩
    (prefixPartial 13 369764) = some ⟨13, 2, 0, 717534, 369764, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_369764_717534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369764 ⟨717534, by decide⟩ :=
  accepted_of_selected 13 369764 ⟨717534, by decide⟩ ⟨13, 2, 0, 717534, 369764, 1165, 16384⟩
    (by decide) selected_cut_28397

theorem selected_cut_28398 : selected 8 ⟨717551, by decide⟩
    (prefixPartial 13 369765) = some ⟨13, 2, 0, 717551, 369765, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_369765_717551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369765 ⟨717551, by decide⟩ :=
  accepted_of_selected 13 369765 ⟨717551, by decide⟩ ⟨13, 2, 0, 717551, 369765, 1141, 16384⟩
    (by decide) selected_cut_28398

theorem selected_cut_28399 : selected 8 ⟨717566, by decide⟩
    (prefixPartial 13 369766) = some ⟨13, 2, 0, 717566, 369766, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_369766_717566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369766 ⟨717566, by decide⟩ :=
  accepted_of_selected 13 369766 ⟨717566, by decide⟩ ⟨13, 2, 0, 717566, 369766, 1193, 16384⟩
    (by decide) selected_cut_28399

theorem selected_cut_28400 : selected 8 ⟨717573, by decide⟩
    (prefixPartial 13 369767) = some ⟨13, 2, 0, 717573, 369767, 705, 16384⟩ := by
  decide +kernel

theorem context_13_369767_717573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369767 ⟨717573, by decide⟩ :=
  accepted_of_selected 13 369767 ⟨717573, by decide⟩ ⟨13, 2, 0, 717573, 369767, 705, 16384⟩
    (by decide) selected_cut_28400

theorem unmarked_context_12_92441_717574 : frontier 9 ⟨717574, by decide⟩
    (prefixCache 12 92441) (prefixPartial 12 92441) = false := by
  decide +kernel

theorem node_context_12_92441_717574 : EJMOriginalGlobalDAGData.nodes 9 ⟨717574, by decide⟩ =
    .split (coordinate 12) (![⟨717534, by decide⟩,⟨717551, by decide⟩,⟨717566, by decide⟩,⟨717573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92441_717574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92441 ⟨717574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92441
    ⟨717574, by decide⟩ (by decide) (![⟨717534, by decide⟩,⟨717551, by decide⟩,⟨717566, by decide⟩,⟨717573, by decide⟩]) unmarked_context_12_92441_717574 node_context_12_92441_717574
  intro a
  fin_cases a
  · exact context_13_369764_717534
  · exact context_13_369765_717551
  · exact context_13_369766_717566
  · exact context_13_369767_717573

theorem selected_cut_28401 : selected 8 ⟨717591, by decide⟩
    (prefixPartial 13 369768) = some ⟨13, 2, 0, 717591, 369768, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_369768_717591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369768 ⟨717591, by decide⟩ :=
  accepted_of_selected 13 369768 ⟨717591, by decide⟩ ⟨13, 2, 0, 717591, 369768, 1209, 16384⟩
    (by decide) selected_cut_28401

theorem selected_cut_28402 : selected 8 ⟨717609, by decide⟩
    (prefixPartial 13 369769) = some ⟨13, 2, 0, 717609, 369769, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_369769_717609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369769 ⟨717609, by decide⟩ :=
  accepted_of_selected 13 369769 ⟨717609, by decide⟩ ⟨13, 2, 0, 717609, 369769, 1397, 16384⟩
    (by decide) selected_cut_28402

theorem selected_cut_28403 : selected 8 ⟨717627, by decide⟩
    (prefixPartial 13 369770) = some ⟨13, 2, 0, 717627, 369770, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_369770_717627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369770 ⟨717627, by decide⟩ :=
  accepted_of_selected 13 369770 ⟨717627, by decide⟩ ⟨13, 2, 0, 717627, 369770, 1209, 16384⟩
    (by decide) selected_cut_28403

theorem selected_cut_28404 : selected 8 ⟨717634, by decide⟩
    (prefixPartial 13 369771) = some ⟨13, 2, 0, 717634, 369771, 813, 16384⟩ := by
  decide +kernel

theorem context_13_369771_717634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369771 ⟨717634, by decide⟩ :=
  accepted_of_selected 13 369771 ⟨717634, by decide⟩ ⟨13, 2, 0, 717634, 369771, 813, 16384⟩
    (by decide) selected_cut_28404

theorem unmarked_context_12_92442_717635 : frontier 9 ⟨717635, by decide⟩
    (prefixCache 12 92442) (prefixPartial 12 92442) = false := by
  decide +kernel

theorem node_context_12_92442_717635 : EJMOriginalGlobalDAGData.nodes 9 ⟨717635, by decide⟩ =
    .split (coordinate 12) (![⟨717591, by decide⟩,⟨717609, by decide⟩,⟨717627, by decide⟩,⟨717634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92442_717635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92442 ⟨717635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92442
    ⟨717635, by decide⟩ (by decide) (![⟨717591, by decide⟩,⟨717609, by decide⟩,⟨717627, by decide⟩,⟨717634, by decide⟩]) unmarked_context_12_92442_717635 node_context_12_92442_717635
  intro a
  fin_cases a
  · exact context_13_369768_717591
  · exact context_13_369769_717609
  · exact context_13_369770_717627
  · exact context_13_369771_717634

theorem selected_cut_28405 : selected 8 ⟨717654, by decide⟩
    (prefixPartial 13 369772) = some ⟨13, 2, 0, 717654, 369772, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_369772_717654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369772 ⟨717654, by decide⟩ :=
  accepted_of_selected 13 369772 ⟨717654, by decide⟩ ⟨13, 2, 0, 717654, 369772, 1257, 16384⟩
    (by decide) selected_cut_28405

theorem selected_cut_28406 : selected 8 ⟨717675, by decide⟩
    (prefixPartial 13 369773) = some ⟨13, 2, 0, 717675, 369773, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_369773_717675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369773 ⟨717675, by decide⟩ :=
  accepted_of_selected 13 369773 ⟨717675, by decide⟩ ⟨13, 2, 0, 717675, 369773, 1597, 16384⟩
    (by decide) selected_cut_28406

theorem selected_cut_28407 : selected 8 ⟨717699, by decide⟩
    (prefixPartial 13 369774) = some ⟨13, 2, 0, 717699, 369774, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_369774_717699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369774 ⟨717699, by decide⟩ :=
  accepted_of_selected 13 369774 ⟨717699, by decide⟩ ⟨13, 2, 0, 717699, 369774, 1305, 16384⟩
    (by decide) selected_cut_28407

theorem selected_cut_28408 : selected 8 ⟨717704, by decide⟩
    (prefixPartial 13 369775) = some ⟨13, 2, 0, 717704, 369775, 689, 16384⟩ := by
  decide +kernel

theorem context_13_369775_717704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369775 ⟨717704, by decide⟩ :=
  accepted_of_selected 13 369775 ⟨717704, by decide⟩ ⟨13, 2, 0, 717704, 369775, 689, 16384⟩
    (by decide) selected_cut_28408

theorem unmarked_context_12_92443_717705 : frontier 9 ⟨717705, by decide⟩
    (prefixCache 12 92443) (prefixPartial 12 92443) = false := by
  decide +kernel

theorem node_context_12_92443_717705 : EJMOriginalGlobalDAGData.nodes 9 ⟨717705, by decide⟩ =
    .split (coordinate 12) (![⟨717654, by decide⟩,⟨717675, by decide⟩,⟨717699, by decide⟩,⟨717704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92443_717705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92443 ⟨717705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92443
    ⟨717705, by decide⟩ (by decide) (![⟨717654, by decide⟩,⟨717675, by decide⟩,⟨717699, by decide⟩,⟨717704, by decide⟩]) unmarked_context_12_92443_717705 node_context_12_92443_717705
  intro a
  fin_cases a
  · exact context_13_369772_717654
  · exact context_13_369773_717675
  · exact context_13_369774_717699
  · exact context_13_369775_717704

theorem unmarked_context_11_23110_717706 : frontier 10 ⟨717706, by decide⟩
    (prefixCache 11 23110) (prefixPartial 11 23110) = false := by
  decide +kernel

theorem node_context_11_23110_717706 : EJMOriginalGlobalDAGData.nodes 10 ⟨717706, by decide⟩ =
    .split (coordinate 11) (![⟨717517, by decide⟩,⟨717574, by decide⟩,⟨717635, by decide⟩,⟨717705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23110_717706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23110 ⟨717706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23110
    ⟨717706, by decide⟩ (by decide) (![⟨717517, by decide⟩,⟨717574, by decide⟩,⟨717635, by decide⟩,⟨717705, by decide⟩]) unmarked_context_11_23110_717706 node_context_11_23110_717706
  intro a
  fin_cases a
  · exact context_12_92440_717517
  · exact context_12_92441_717574
  · exact context_12_92442_717635
  · exact context_12_92443_717705

theorem selected_cut_28409 : selected 8 ⟨717723, by decide⟩
    (prefixPartial 13 369776) = some ⟨13, 2, 0, 717723, 369776, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_369776_717723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369776 ⟨717723, by decide⟩ :=
  accepted_of_selected 13 369776 ⟨717723, by decide⟩ ⟨13, 2, 0, 717723, 369776, 1189, 16384⟩
    (by decide) selected_cut_28409

theorem selected_cut_28410 : selected 8 ⟨717744, by decide⟩
    (prefixPartial 13 369777) = some ⟨13, 2, 0, 717744, 369777, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_369777_717744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369777 ⟨717744, by decide⟩ :=
  accepted_of_selected 13 369777 ⟨717744, by decide⟩ ⟨13, 2, 0, 717744, 369777, 1669, 16384⟩
    (by decide) selected_cut_28410

theorem selected_cut_28411 : selected 8 ⟨717760, by decide⟩
    (prefixPartial 13 369778) = some ⟨13, 2, 0, 717760, 369778, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_369778_717760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369778 ⟨717760, by decide⟩ :=
  accepted_of_selected 13 369778 ⟨717760, by decide⟩ ⟨13, 2, 0, 717760, 369778, 1301, 16384⟩
    (by decide) selected_cut_28411

theorem selected_cut_28412 : selected 8 ⟨717768, by decide⟩
    (prefixPartial 13 369779) = some ⟨13, 2, 0, 717768, 369779, 849, 16384⟩ := by
  decide +kernel

theorem context_13_369779_717768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369779 ⟨717768, by decide⟩ :=
  accepted_of_selected 13 369779 ⟨717768, by decide⟩ ⟨13, 2, 0, 717768, 369779, 849, 16384⟩
    (by decide) selected_cut_28412

theorem unmarked_context_12_92444_717769 : frontier 9 ⟨717769, by decide⟩
    (prefixCache 12 92444) (prefixPartial 12 92444) = false := by
  decide +kernel

theorem node_context_12_92444_717769 : EJMOriginalGlobalDAGData.nodes 9 ⟨717769, by decide⟩ =
    .split (coordinate 12) (![⟨717723, by decide⟩,⟨717744, by decide⟩,⟨717760, by decide⟩,⟨717768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92444_717769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92444 ⟨717769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92444
    ⟨717769, by decide⟩ (by decide) (![⟨717723, by decide⟩,⟨717744, by decide⟩,⟨717760, by decide⟩,⟨717768, by decide⟩]) unmarked_context_12_92444_717769 node_context_12_92444_717769
  intro a
  fin_cases a
  · exact context_13_369776_717723
  · exact context_13_369777_717744
  · exact context_13_369778_717760
  · exact context_13_369779_717768

theorem selected_cut_28413 : selected 8 ⟨717791, by decide⟩
    (prefixPartial 13 369780) = some ⟨13, 2, 0, 717791, 369780, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_369780_717791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369780 ⟨717791, by decide⟩ :=
  accepted_of_selected 13 369780 ⟨717791, by decide⟩ ⟨13, 2, 0, 717791, 369780, 1185, 16384⟩
    (by decide) selected_cut_28413

theorem selected_cut_28414 : selected 8 ⟨717811, by decide⟩
    (prefixPartial 13 369781) = some ⟨13, 2, 0, 717811, 369781, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_369781_717811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369781 ⟨717811, by decide⟩ :=
  accepted_of_selected 13 369781 ⟨717811, by decide⟩ ⟨13, 2, 0, 717811, 369781, 1345, 16384⟩
    (by decide) selected_cut_28414

theorem selected_cut_28415 : selected 8 ⟨717826, by decide⟩
    (prefixPartial 13 369782) = some ⟨13, 2, 0, 717826, 369782, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_369782_717826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369782 ⟨717826, by decide⟩ :=
  accepted_of_selected 13 369782 ⟨717826, by decide⟩ ⟨13, 2, 0, 717826, 369782, 1281, 16384⟩
    (by decide) selected_cut_28415

theorem selected_cut_28416 : selected 8 ⟨717831, by decide⟩
    (prefixPartial 13 369783) = some ⟨13, 2, 0, 717831, 369783, 737, 16384⟩ := by
  decide +kernel

theorem context_13_369783_717831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369783 ⟨717831, by decide⟩ :=
  accepted_of_selected 13 369783 ⟨717831, by decide⟩ ⟨13, 2, 0, 717831, 369783, 737, 16384⟩
    (by decide) selected_cut_28416

theorem unmarked_context_12_92445_717832 : frontier 9 ⟨717832, by decide⟩
    (prefixCache 12 92445) (prefixPartial 12 92445) = false := by
  decide +kernel

theorem node_context_12_92445_717832 : EJMOriginalGlobalDAGData.nodes 9 ⟨717832, by decide⟩ =
    .split (coordinate 12) (![⟨717791, by decide⟩,⟨717811, by decide⟩,⟨717826, by decide⟩,⟨717831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92445_717832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92445 ⟨717832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92445
    ⟨717832, by decide⟩ (by decide) (![⟨717791, by decide⟩,⟨717811, by decide⟩,⟨717826, by decide⟩,⟨717831, by decide⟩]) unmarked_context_12_92445_717832 node_context_12_92445_717832
  intro a
  fin_cases a
  · exact context_13_369780_717791
  · exact context_13_369781_717811
  · exact context_13_369782_717826
  · exact context_13_369783_717831

theorem selected_cut_28417 : selected 8 ⟨717848, by decide⟩
    (prefixPartial 13 369784) = some ⟨13, 2, 0, 717848, 369784, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_369784_717848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369784 ⟨717848, by decide⟩ :=
  accepted_of_selected 13 369784 ⟨717848, by decide⟩ ⟨13, 2, 0, 717848, 369784, 1245, 16384⟩
    (by decide) selected_cut_28417

theorem selected_cut_28418 : selected 8 ⟨717868, by decide⟩
    (prefixPartial 13 369785) = some ⟨13, 2, 0, 717868, 369785, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_369785_717868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369785 ⟨717868, by decide⟩ :=
  accepted_of_selected 13 369785 ⟨717868, by decide⟩ ⟨13, 2, 0, 717868, 369785, 1545, 16384⟩
    (by decide) selected_cut_28418

theorem selected_cut_28419 : selected 8 ⟨717888, by decide⟩
    (prefixPartial 13 369786) = some ⟨13, 2, 0, 717888, 369786, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_369786_717888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369786 ⟨717888, by decide⟩ :=
  accepted_of_selected 13 369786 ⟨717888, by decide⟩ ⟨13, 2, 0, 717888, 369786, 1325, 16384⟩
    (by decide) selected_cut_28419

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
