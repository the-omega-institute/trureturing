/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover227
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21892 : selected 8 ⟨559136, by decide⟩
    (prefixPartial 13 301291) = some ⟨13, 2, 0, 559136, 301291, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_301291_559136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301291 ⟨559136, by decide⟩ :=
  accepted_of_selected 13 301291 ⟨559136, by decide⟩ ⟨13, 2, 0, 559136, 301291, 1313, 16384⟩
    (by decide) selected_cut_21892

theorem unmarked_context_12_75322_559137 : frontier 9 ⟨559137, by decide⟩
    (prefixCache 12 75322) (prefixPartial 12 75322) = false := by
  decide +kernel

theorem node_context_12_75322_559137 : EJMOriginalGlobalDAGData.nodes 9 ⟨559137, by decide⟩ =
    .split (coordinate 12) (![⟨559051, by decide⟩,⟨559099, by decide⟩,⟨559117, by decide⟩,⟨559136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75322_559137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75322 ⟨559137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75322
    ⟨559137, by decide⟩ (by decide) (![⟨559051, by decide⟩,⟨559099, by decide⟩,⟨559117, by decide⟩,⟨559136, by decide⟩]) unmarked_context_12_75322_559137 node_context_12_75322_559137
  intro a
  fin_cases a
  · exact context_13_301288_559051
  · exact context_13_301289_559099
  · exact context_13_301290_559117
  · exact context_13_301291_559136

theorem selected_cut_21893 : selected 8 ⟨559141, by decide⟩
    (prefixPartial 13 301292) = some ⟨13, 2, 0, 559141, 301292, 189, 16384⟩ := by
  decide +kernel

theorem context_13_301292_559141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301292 ⟨559141, by decide⟩ :=
  accepted_of_selected 13 301292 ⟨559141, by decide⟩ ⟨13, 2, 0, 559141, 301292, 189, 16384⟩
    (by decide) selected_cut_21893

theorem selected_cut_21894 : selected 8 ⟨559176, by decide⟩
    (prefixPartial 13 301293) = some ⟨13, 2, 0, 559176, 301293, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_301293_559176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301293 ⟨559176, by decide⟩ :=
  accepted_of_selected 13 301293 ⟨559176, by decide⟩ ⟨13, 2, 0, 559176, 301293, 2809, 16384⟩
    (by decide) selected_cut_21894

theorem selected_cut_21895 : selected 8 ⟨559195, by decide⟩
    (prefixPartial 13 301294) = some ⟨13, 2, 0, 559195, 301294, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_301294_559195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301294 ⟨559195, by decide⟩ :=
  accepted_of_selected 13 301294 ⟨559195, by decide⟩ ⟨13, 2, 0, 559195, 301294, 1533, 16384⟩
    (by decide) selected_cut_21895

theorem selected_cut_21896 : selected 8 ⟨559206, by decide⟩
    (prefixPartial 13 301295) = some ⟨13, 2, 0, 559206, 301295, 865, 16384⟩ := by
  decide +kernel

theorem context_13_301295_559206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301295 ⟨559206, by decide⟩ :=
  accepted_of_selected 13 301295 ⟨559206, by decide⟩ ⟨13, 2, 0, 559206, 301295, 865, 16384⟩
    (by decide) selected_cut_21896

theorem unmarked_context_12_75323_559207 : frontier 9 ⟨559207, by decide⟩
    (prefixCache 12 75323) (prefixPartial 12 75323) = false := by
  decide +kernel

theorem node_context_12_75323_559207 : EJMOriginalGlobalDAGData.nodes 9 ⟨559207, by decide⟩ =
    .split (coordinate 12) (![⟨559141, by decide⟩,⟨559176, by decide⟩,⟨559195, by decide⟩,⟨559206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75323_559207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75323 ⟨559207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75323
    ⟨559207, by decide⟩ (by decide) (![⟨559141, by decide⟩,⟨559176, by decide⟩,⟨559195, by decide⟩,⟨559206, by decide⟩]) unmarked_context_12_75323_559207 node_context_12_75323_559207
  intro a
  fin_cases a
  · exact context_13_301292_559141
  · exact context_13_301293_559176
  · exact context_13_301294_559195
  · exact context_13_301295_559206

theorem unmarked_context_11_18830_559208 : frontier 10 ⟨559208, by decide⟩
    (prefixCache 11 18830) (prefixPartial 11 18830) = false := by
  decide +kernel

theorem node_context_11_18830_559208 : EJMOriginalGlobalDAGData.nodes 10 ⟨559208, by decide⟩ =
    .split (coordinate 11) (![⟨558989, by decide⟩,⟨559044, by decide⟩,⟨559137, by decide⟩,⟨559207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18830_559208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18830 ⟨559208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18830
    ⟨559208, by decide⟩ (by decide) (![⟨558989, by decide⟩,⟨559044, by decide⟩,⟨559137, by decide⟩,⟨559207, by decide⟩]) unmarked_context_11_18830_559208 node_context_11_18830_559208
  intro a
  fin_cases a
  · exact context_12_75320_558989
  · exact context_12_75321_559044
  · exact context_12_75322_559137
  · exact context_12_75323_559207

theorem selected_cut_21897 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75324) = some ⟨12, 1, 0, 445562, 75324, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75324_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75324 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75324 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75324, 1, 65536⟩
    (by decide) selected_cut_21897

theorem selected_cut_21898 : selected 8 ⟨559211, by decide⟩
    (prefixPartial 13 301300) = some ⟨13, 2, 0, 559211, 301300, 105, 16384⟩ := by
  decide +kernel

theorem context_13_301300_559211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301300 ⟨559211, by decide⟩ :=
  accepted_of_selected 13 301300 ⟨559211, by decide⟩ ⟨13, 2, 0, 559211, 301300, 105, 16384⟩
    (by decide) selected_cut_21898

theorem selected_cut_21899 : selected 8 ⟨559240, by decide⟩
    (prefixPartial 13 301301) = some ⟨13, 2, 0, 559240, 301301, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_301301_559240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301301 ⟨559240, by decide⟩ :=
  accepted_of_selected 13 301301 ⟨559240, by decide⟩ ⟨13, 2, 0, 559240, 301301, 2393, 16384⟩
    (by decide) selected_cut_21899

theorem selected_cut_21900 : selected 8 ⟨559254, by decide⟩
    (prefixPartial 13 301302) = some ⟨13, 2, 0, 559254, 301302, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_301302_559254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301302 ⟨559254, by decide⟩ :=
  accepted_of_selected 13 301302 ⟨559254, by decide⟩ ⟨13, 2, 0, 559254, 301302, 1245, 16384⟩
    (by decide) selected_cut_21900

theorem selected_cut_21901 : selected 8 ⟨559261, by decide⟩
    (prefixPartial 13 301303) = some ⟨13, 2, 0, 559261, 301303, 777, 16384⟩ := by
  decide +kernel

theorem context_13_301303_559261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301303 ⟨559261, by decide⟩ :=
  accepted_of_selected 13 301303 ⟨559261, by decide⟩ ⟨13, 2, 0, 559261, 301303, 777, 16384⟩
    (by decide) selected_cut_21901

theorem unmarked_context_12_75325_559262 : frontier 9 ⟨559262, by decide⟩
    (prefixCache 12 75325) (prefixPartial 12 75325) = false := by
  decide +kernel

theorem node_context_12_75325_559262 : EJMOriginalGlobalDAGData.nodes 9 ⟨559262, by decide⟩ =
    .split (coordinate 12) (![⟨559211, by decide⟩,⟨559240, by decide⟩,⟨559254, by decide⟩,⟨559261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75325_559262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75325 ⟨559262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75325
    ⟨559262, by decide⟩ (by decide) (![⟨559211, by decide⟩,⟨559240, by decide⟩,⟨559254, by decide⟩,⟨559261, by decide⟩]) unmarked_context_12_75325_559262 node_context_12_75325_559262
  intro a
  fin_cases a
  · exact context_13_301300_559211
  · exact context_13_301301_559240
  · exact context_13_301302_559254
  · exact context_13_301303_559261

theorem selected_cut_21902 : selected 8 ⟨559265, by decide⟩
    (prefixPartial 13 301304) = some ⟨13, 2, 0, 559265, 301304, 93, 16384⟩ := by
  decide +kernel

theorem context_13_301304_559265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301304 ⟨559265, by decide⟩ :=
  accepted_of_selected 13 301304 ⟨559265, by decide⟩ ⟨13, 2, 0, 559265, 301304, 93, 16384⟩
    (by decide) selected_cut_21902

theorem selected_cut_21903 : selected 8 ⟨559289, by decide⟩
    (prefixPartial 13 301305) = some ⟨13, 2, 0, 559289, 301305, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_301305_559289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301305 ⟨559289, by decide⟩ :=
  accepted_of_selected 13 301305 ⟨559289, by decide⟩ ⟨13, 2, 0, 559289, 301305, 2225, 16384⟩
    (by decide) selected_cut_21903

theorem selected_cut_21904 : selected 8 ⟨559303, by decide⟩
    (prefixPartial 13 301306) = some ⟨13, 2, 0, 559303, 301306, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_301306_559303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301306 ⟨559303, by decide⟩ :=
  accepted_of_selected 13 301306 ⟨559303, by decide⟩ ⟨13, 2, 0, 559303, 301306, 1105, 16384⟩
    (by decide) selected_cut_21904

theorem selected_cut_21905 : selected 8 ⟨559310, by decide⟩
    (prefixPartial 13 301307) = some ⟨13, 2, 0, 559310, 301307, 797, 16384⟩ := by
  decide +kernel

theorem context_13_301307_559310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301307 ⟨559310, by decide⟩ :=
  accepted_of_selected 13 301307 ⟨559310, by decide⟩ ⟨13, 2, 0, 559310, 301307, 797, 16384⟩
    (by decide) selected_cut_21905

theorem unmarked_context_12_75326_559311 : frontier 9 ⟨559311, by decide⟩
    (prefixCache 12 75326) (prefixPartial 12 75326) = false := by
  decide +kernel

theorem node_context_12_75326_559311 : EJMOriginalGlobalDAGData.nodes 9 ⟨559311, by decide⟩ =
    .split (coordinate 12) (![⟨559265, by decide⟩,⟨559289, by decide⟩,⟨559303, by decide⟩,⟨559310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75326_559311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75326 ⟨559311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75326
    ⟨559311, by decide⟩ (by decide) (![⟨559265, by decide⟩,⟨559289, by decide⟩,⟨559303, by decide⟩,⟨559310, by decide⟩]) unmarked_context_12_75326_559311 node_context_12_75326_559311
  intro a
  fin_cases a
  · exact context_13_301304_559265
  · exact context_13_301305_559289
  · exact context_13_301306_559303
  · exact context_13_301307_559310

theorem selected_cut_21906 : selected 8 ⟨559315, by decide⟩
    (prefixPartial 13 301308) = some ⟨13, 2, 0, 559315, 301308, 65, 16384⟩ := by
  decide +kernel

theorem context_13_301308_559315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301308 ⟨559315, by decide⟩ :=
  accepted_of_selected 13 301308 ⟨559315, by decide⟩ ⟨13, 2, 0, 559315, 301308, 65, 16384⟩
    (by decide) selected_cut_21906

theorem selected_cut_21907 : selected 8 ⟨559349, by decide⟩
    (prefixPartial 13 301309) = some ⟨13, 2, 0, 559349, 301309, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_301309_559349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301309 ⟨559349, by decide⟩ :=
  accepted_of_selected 13 301309 ⟨559349, by decide⟩ ⟨13, 2, 0, 559349, 301309, 2757, 16384⟩
    (by decide) selected_cut_21907

theorem selected_cut_21908 : selected 8 ⟨559366, by decide⟩
    (prefixPartial 13 301310) = some ⟨13, 2, 0, 559366, 301310, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_301310_559366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301310 ⟨559366, by decide⟩ :=
  accepted_of_selected 13 301310 ⟨559366, by decide⟩ ⟨13, 2, 0, 559366, 301310, 1569, 16384⟩
    (by decide) selected_cut_21908

theorem selected_cut_21909 : selected 8 ⟨559375, by decide⟩
    (prefixPartial 13 301311) = some ⟨13, 2, 0, 559375, 301311, 821, 16384⟩ := by
  decide +kernel

theorem context_13_301311_559375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301311 ⟨559375, by decide⟩ :=
  accepted_of_selected 13 301311 ⟨559375, by decide⟩ ⟨13, 2, 0, 559375, 301311, 821, 16384⟩
    (by decide) selected_cut_21909

theorem unmarked_context_12_75327_559376 : frontier 9 ⟨559376, by decide⟩
    (prefixCache 12 75327) (prefixPartial 12 75327) = false := by
  decide +kernel

theorem node_context_12_75327_559376 : EJMOriginalGlobalDAGData.nodes 9 ⟨559376, by decide⟩ =
    .split (coordinate 12) (![⟨559315, by decide⟩,⟨559349, by decide⟩,⟨559366, by decide⟩,⟨559375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75327_559376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75327 ⟨559376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75327
    ⟨559376, by decide⟩ (by decide) (![⟨559315, by decide⟩,⟨559349, by decide⟩,⟨559366, by decide⟩,⟨559375, by decide⟩]) unmarked_context_12_75327_559376 node_context_12_75327_559376
  intro a
  fin_cases a
  · exact context_13_301308_559315
  · exact context_13_301309_559349
  · exact context_13_301310_559366
  · exact context_13_301311_559375

theorem unmarked_context_11_18831_559377 : frontier 10 ⟨559377, by decide⟩
    (prefixCache 11 18831) (prefixPartial 11 18831) = false := by
  decide +kernel

theorem node_context_11_18831_559377 : EJMOriginalGlobalDAGData.nodes 10 ⟨559377, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨559262, by decide⟩,⟨559311, by decide⟩,⟨559376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18831_559377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18831 ⟨559377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18831
    ⟨559377, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨559262, by decide⟩,⟨559311, by decide⟩,⟨559376, by decide⟩]) unmarked_context_11_18831_559377 node_context_11_18831_559377
  intro a
  fin_cases a
  · exact context_12_75324_445562
  · exact context_12_75325_559262
  · exact context_12_75326_559311
  · exact context_12_75327_559376

theorem unmarked_context_10_4707_559378 : frontier 11 ⟨559378, by decide⟩
    (prefixCache 10 4707) (prefixPartial 10 4707) = false := by
  decide +kernel

theorem node_context_10_4707_559378 : EJMOriginalGlobalDAGData.nodes 11 ⟨559378, by decide⟩ =
    .split (coordinate 10) (![⟨558627, by decide⟩,⟨558909, by decide⟩,⟨559208, by decide⟩,⟨559377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4707_559378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4707 ⟨559378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4707
    ⟨559378, by decide⟩ (by decide) (![⟨558627, by decide⟩,⟨558909, by decide⟩,⟨559208, by decide⟩,⟨559377, by decide⟩]) unmarked_context_10_4707_559378 node_context_10_4707_559378
  intro a
  fin_cases a
  · exact context_11_18828_558627
  · exact context_11_18829_558909
  · exact context_11_18830_559208
  · exact context_11_18831_559377

theorem unmarked_context_9_1176_559379 : frontier 12 ⟨559379, by decide⟩
    (prefixCache 9 1176) (prefixPartial 9 1176) = false := by
  decide +kernel

theorem node_context_9_1176_559379 : EJMOriginalGlobalDAGData.nodes 12 ⟨559379, by decide⟩ =
    .split (coordinate 9) (![⟨556296, by decide⟩,⟨557492, by decide⟩,⟨558441, by decide⟩,⟨559378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1176_559379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1176 ⟨559379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1176
    ⟨559379, by decide⟩ (by decide) (![⟨556296, by decide⟩,⟨557492, by decide⟩,⟨558441, by decide⟩,⟨559378, by decide⟩]) unmarked_context_9_1176_559379 node_context_9_1176_559379
  intro a
  fin_cases a
  · exact context_10_4704_556296
  · exact context_10_4705_557492
  · exact context_10_4706_558441
  · exact context_10_4707_559378

theorem selected_cut_21910 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301312) = some ⟨13, 1, 0, 3444, 301312, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301312_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301312 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301312 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301312, 1, 16384⟩
    (by decide) selected_cut_21910

theorem selected_cut_21911 : selected 8 ⟨559412, by decide⟩
    (prefixPartial 13 301313) = some ⟨13, 2, 0, 559412, 301313, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_301313_559412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301313 ⟨559412, by decide⟩ :=
  accepted_of_selected 13 301313 ⟨559412, by decide⟩ ⟨13, 2, 0, 559412, 301313, 2157, 16384⟩
    (by decide) selected_cut_21911

theorem selected_cut_21912 : selected 8 ⟨559429, by decide⟩
    (prefixPartial 13 301314) = some ⟨13, 2, 0, 559429, 301314, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_301314_559429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301314 ⟨559429, by decide⟩ :=
  accepted_of_selected 13 301314 ⟨559429, by decide⟩ ⟨13, 2, 0, 559429, 301314, 1301, 16384⟩
    (by decide) selected_cut_21912

theorem selected_cut_21913 : selected 8 ⟨559435, by decide⟩
    (prefixPartial 13 301315) = some ⟨13, 2, 0, 559435, 301315, 653, 16384⟩ := by
  decide +kernel

theorem context_13_301315_559435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301315 ⟨559435, by decide⟩ :=
  accepted_of_selected 13 301315 ⟨559435, by decide⟩ ⟨13, 2, 0, 559435, 301315, 653, 16384⟩
    (by decide) selected_cut_21913

theorem unmarked_context_12_75328_559436 : frontier 9 ⟨559436, by decide⟩
    (prefixCache 12 75328) (prefixPartial 12 75328) = false := by
  decide +kernel

theorem node_context_12_75328_559436 : EJMOriginalGlobalDAGData.nodes 9 ⟨559436, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559412, by decide⟩,⟨559429, by decide⟩,⟨559435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75328_559436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75328 ⟨559436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75328
    ⟨559436, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559412, by decide⟩,⟨559429, by decide⟩,⟨559435, by decide⟩]) unmarked_context_12_75328_559436 node_context_12_75328_559436
  intro a
  fin_cases a
  · exact context_13_301312_3444
  · exact context_13_301313_559412
  · exact context_13_301314_559429
  · exact context_13_301315_559435

theorem selected_cut_21914 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301316) = some ⟨13, 1, 0, 3444, 301316, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301316_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301316 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301316 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301316, 1, 16384⟩
    (by decide) selected_cut_21914

theorem selected_cut_21915 : selected 8 ⟨559463, by decide⟩
    (prefixPartial 13 301317) = some ⟨13, 2, 0, 559463, 301317, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_301317_559463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301317 ⟨559463, by decide⟩ :=
  accepted_of_selected 13 301317 ⟨559463, by decide⟩ ⟨13, 2, 0, 559463, 301317, 2609, 16384⟩
    (by decide) selected_cut_21915

theorem selected_cut_21916 : selected 8 ⟨559480, by decide⟩
    (prefixPartial 13 301318) = some ⟨13, 2, 0, 559480, 301318, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_301318_559480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301318 ⟨559480, by decide⟩ :=
  accepted_of_selected 13 301318 ⟨559480, by decide⟩ ⟨13, 2, 0, 559480, 301318, 1305, 16384⟩
    (by decide) selected_cut_21916

theorem selected_cut_21917 : selected 8 ⟨559486, by decide⟩
    (prefixPartial 13 301319) = some ⟨13, 2, 0, 559486, 301319, 693, 16384⟩ := by
  decide +kernel

theorem context_13_301319_559486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301319 ⟨559486, by decide⟩ :=
  accepted_of_selected 13 301319 ⟨559486, by decide⟩ ⟨13, 2, 0, 559486, 301319, 693, 16384⟩
    (by decide) selected_cut_21917

theorem unmarked_context_12_75329_559487 : frontier 9 ⟨559487, by decide⟩
    (prefixCache 12 75329) (prefixPartial 12 75329) = false := by
  decide +kernel

theorem node_context_12_75329_559487 : EJMOriginalGlobalDAGData.nodes 9 ⟨559487, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559463, by decide⟩,⟨559480, by decide⟩,⟨559486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75329_559487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75329 ⟨559487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75329
    ⟨559487, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559463, by decide⟩,⟨559480, by decide⟩,⟨559486, by decide⟩]) unmarked_context_12_75329_559487 node_context_12_75329_559487
  intro a
  fin_cases a
  · exact context_13_301316_3444
  · exact context_13_301317_559463
  · exact context_13_301318_559480
  · exact context_13_301319_559486

theorem selected_cut_21918 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301320) = some ⟨13, 1, 0, 3444, 301320, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301320_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301320 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301320 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301320, 1, 16384⟩
    (by decide) selected_cut_21918

theorem selected_cut_21919 : selected 8 ⟨559522, by decide⟩
    (prefixPartial 13 301321) = some ⟨13, 2, 0, 559522, 301321, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_301321_559522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301321 ⟨559522, by decide⟩ :=
  accepted_of_selected 13 301321 ⟨559522, by decide⟩ ⟨13, 2, 0, 559522, 301321, 2925, 16384⟩
    (by decide) selected_cut_21919

theorem selected_cut_21920 : selected 8 ⟨559542, by decide⟩
    (prefixPartial 13 301322) = some ⟨13, 2, 0, 559542, 301322, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_301322_559542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301322 ⟨559542, by decide⟩ :=
  accepted_of_selected 13 301322 ⟨559542, by decide⟩ ⟨13, 2, 0, 559542, 301322, 1417, 16384⟩
    (by decide) selected_cut_21920

theorem selected_cut_21921 : selected 8 ⟨559551, by decide⟩
    (prefixPartial 13 301323) = some ⟨13, 2, 0, 559551, 301323, 817, 16384⟩ := by
  decide +kernel

theorem context_13_301323_559551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301323 ⟨559551, by decide⟩ :=
  accepted_of_selected 13 301323 ⟨559551, by decide⟩ ⟨13, 2, 0, 559551, 301323, 817, 16384⟩
    (by decide) selected_cut_21921

theorem unmarked_context_12_75330_559552 : frontier 9 ⟨559552, by decide⟩
    (prefixCache 12 75330) (prefixPartial 12 75330) = false := by
  decide +kernel

theorem node_context_12_75330_559552 : EJMOriginalGlobalDAGData.nodes 9 ⟨559552, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559522, by decide⟩,⟨559542, by decide⟩,⟨559551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75330_559552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75330 ⟨559552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75330
    ⟨559552, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559522, by decide⟩,⟨559542, by decide⟩,⟨559551, by decide⟩]) unmarked_context_12_75330_559552 node_context_12_75330_559552
  intro a
  fin_cases a
  · exact context_13_301320_3444
  · exact context_13_301321_559522
  · exact context_13_301322_559542
  · exact context_13_301323_559551

theorem selected_cut_21922 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301324) = some ⟨13, 1, 0, 3444, 301324, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301324_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301324 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301324 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301324, 1, 16384⟩
    (by decide) selected_cut_21922

theorem selected_cut_21923 : selected 8 ⟨559592, by decide⟩
    (prefixPartial 13 301325) = some ⟨13, 2, 0, 559592, 301325, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_301325_559592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301325 ⟨559592, by decide⟩ :=
  accepted_of_selected 13 301325 ⟨559592, by decide⟩ ⟨13, 2, 0, 559592, 301325, 3141, 16384⟩
    (by decide) selected_cut_21923

theorem selected_cut_21924 : selected 8 ⟨559613, by decide⟩
    (prefixPartial 13 301326) = some ⟨13, 2, 0, 559613, 301326, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_301326_559613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301326 ⟨559613, by decide⟩ :=
  accepted_of_selected 13 301326 ⟨559613, by decide⟩ ⟨13, 2, 0, 559613, 301326, 1605, 16384⟩
    (by decide) selected_cut_21924

theorem selected_cut_21925 : selected 8 ⟨559618, by decide⟩
    (prefixPartial 13 301327) = some ⟨13, 2, 0, 559618, 301327, 705, 16384⟩ := by
  decide +kernel

theorem context_13_301327_559618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301327 ⟨559618, by decide⟩ :=
  accepted_of_selected 13 301327 ⟨559618, by decide⟩ ⟨13, 2, 0, 559618, 301327, 705, 16384⟩
    (by decide) selected_cut_21925

theorem unmarked_context_12_75331_559619 : frontier 9 ⟨559619, by decide⟩
    (prefixCache 12 75331) (prefixPartial 12 75331) = false := by
  decide +kernel

theorem node_context_12_75331_559619 : EJMOriginalGlobalDAGData.nodes 9 ⟨559619, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559592, by decide⟩,⟨559613, by decide⟩,⟨559618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75331_559619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75331 ⟨559619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75331
    ⟨559619, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559592, by decide⟩,⟨559613, by decide⟩,⟨559618, by decide⟩]) unmarked_context_12_75331_559619 node_context_12_75331_559619
  intro a
  fin_cases a
  · exact context_13_301324_3444
  · exact context_13_301325_559592
  · exact context_13_301326_559613
  · exact context_13_301327_559618

theorem unmarked_context_11_18832_559620 : frontier 10 ⟨559620, by decide⟩
    (prefixCache 11 18832) (prefixPartial 11 18832) = false := by
  decide +kernel

theorem node_context_11_18832_559620 : EJMOriginalGlobalDAGData.nodes 10 ⟨559620, by decide⟩ =
    .split (coordinate 11) (![⟨559436, by decide⟩,⟨559487, by decide⟩,⟨559552, by decide⟩,⟨559619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18832_559620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18832 ⟨559620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18832
    ⟨559620, by decide⟩ (by decide) (![⟨559436, by decide⟩,⟨559487, by decide⟩,⟨559552, by decide⟩,⟨559619, by decide⟩]) unmarked_context_11_18832_559620 node_context_11_18832_559620
  intro a
  fin_cases a
  · exact context_12_75328_559436
  · exact context_12_75329_559487
  · exact context_12_75330_559552
  · exact context_12_75331_559619

theorem selected_cut_21926 : selected 9 ⟨559665, by decide⟩
    (prefixPartial 12 75332) = some ⟨12, 2, 0, 559665, 75332, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_75332_559665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75332 ⟨559665, by decide⟩ :=
  accepted_of_selected 12 75332 ⟨559665, by decide⟩ ⟨12, 2, 0, 559665, 75332, 3825, 65536⟩
    (by decide) selected_cut_21926

theorem selected_cut_21927 : selected 9 ⟨559712, by decide⟩
    (prefixPartial 12 75333) = some ⟨12, 2, 0, 559712, 75333, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_75333_559712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75333 ⟨559712, by decide⟩ :=
  accepted_of_selected 12 75333 ⟨559712, by decide⟩ ⟨12, 2, 0, 559712, 75333, 3925, 65536⟩
    (by decide) selected_cut_21927

theorem selected_cut_21928 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301336) = some ⟨13, 1, 0, 3444, 301336, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301336_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301336 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301336 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301336, 1, 16384⟩
    (by decide) selected_cut_21928

theorem selected_cut_21929 : selected 8 ⟨559739, by decide⟩
    (prefixPartial 13 301337) = some ⟨13, 2, 0, 559739, 301337, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_301337_559739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301337 ⟨559739, by decide⟩ :=
  accepted_of_selected 13 301337 ⟨559739, by decide⟩ ⟨13, 2, 0, 559739, 301337, 2381, 16384⟩
    (by decide) selected_cut_21929

theorem selected_cut_21930 : selected 8 ⟨559759, by decide⟩
    (prefixPartial 13 301338) = some ⟨13, 2, 0, 559759, 301338, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_301338_559759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301338 ⟨559759, by decide⟩ :=
  accepted_of_selected 13 301338 ⟨559759, by decide⟩ ⟨13, 2, 0, 559759, 301338, 1561, 16384⟩
    (by decide) selected_cut_21930

theorem selected_cut_21931 : selected 8 ⟨559770, by decide⟩
    (prefixPartial 13 301339) = some ⟨13, 2, 0, 559770, 301339, 917, 16384⟩ := by
  decide +kernel

theorem context_13_301339_559770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301339 ⟨559770, by decide⟩ :=
  accepted_of_selected 13 301339 ⟨559770, by decide⟩ ⟨13, 2, 0, 559770, 301339, 917, 16384⟩
    (by decide) selected_cut_21931

theorem unmarked_context_12_75334_559771 : frontier 9 ⟨559771, by decide⟩
    (prefixCache 12 75334) (prefixPartial 12 75334) = false := by
  decide +kernel

theorem node_context_12_75334_559771 : EJMOriginalGlobalDAGData.nodes 9 ⟨559771, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559739, by decide⟩,⟨559759, by decide⟩,⟨559770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75334_559771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75334 ⟨559771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75334
    ⟨559771, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559739, by decide⟩,⟨559759, by decide⟩,⟨559770, by decide⟩]) unmarked_context_12_75334_559771 node_context_12_75334_559771
  intro a
  fin_cases a
  · exact context_13_301336_3444
  · exact context_13_301337_559739
  · exact context_13_301338_559759
  · exact context_13_301339_559770

theorem selected_cut_21932 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301340) = some ⟨13, 1, 0, 3444, 301340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301340, 1, 16384⟩
    (by decide) selected_cut_21932

theorem selected_cut_21933 : selected 8 ⟨559800, by decide⟩
    (prefixPartial 13 301341) = some ⟨13, 2, 0, 559800, 301341, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_301341_559800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301341 ⟨559800, by decide⟩ :=
  accepted_of_selected 13 301341 ⟨559800, by decide⟩ ⟨13, 2, 0, 559800, 301341, 2493, 16384⟩
    (by decide) selected_cut_21933

theorem selected_cut_21934 : selected 8 ⟨559816, by decide⟩
    (prefixPartial 13 301342) = some ⟨13, 2, 0, 559816, 301342, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_301342_559816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301342 ⟨559816, by decide⟩ :=
  accepted_of_selected 13 301342 ⟨559816, by decide⟩ ⟨13, 2, 0, 559816, 301342, 1733, 16384⟩
    (by decide) selected_cut_21934

theorem selected_cut_21935 : selected 8 ⟨559824, by decide⟩
    (prefixPartial 13 301343) = some ⟨13, 2, 0, 559824, 301343, 817, 16384⟩ := by
  decide +kernel

theorem context_13_301343_559824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301343 ⟨559824, by decide⟩ :=
  accepted_of_selected 13 301343 ⟨559824, by decide⟩ ⟨13, 2, 0, 559824, 301343, 817, 16384⟩
    (by decide) selected_cut_21935

theorem unmarked_context_12_75335_559825 : frontier 9 ⟨559825, by decide⟩
    (prefixCache 12 75335) (prefixPartial 12 75335) = false := by
  decide +kernel

theorem node_context_12_75335_559825 : EJMOriginalGlobalDAGData.nodes 9 ⟨559825, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559800, by decide⟩,⟨559816, by decide⟩,⟨559824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75335_559825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75335 ⟨559825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75335
    ⟨559825, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559800, by decide⟩,⟨559816, by decide⟩,⟨559824, by decide⟩]) unmarked_context_12_75335_559825 node_context_12_75335_559825
  intro a
  fin_cases a
  · exact context_13_301340_3444
  · exact context_13_301341_559800
  · exact context_13_301342_559816
  · exact context_13_301343_559824

theorem unmarked_context_11_18833_559826 : frontier 10 ⟨559826, by decide⟩
    (prefixCache 11 18833) (prefixPartial 11 18833) = false := by
  decide +kernel

theorem node_context_11_18833_559826 : EJMOriginalGlobalDAGData.nodes 10 ⟨559826, by decide⟩ =
    .split (coordinate 11) (![⟨559665, by decide⟩,⟨559712, by decide⟩,⟨559771, by decide⟩,⟨559825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18833_559826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18833 ⟨559826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18833
    ⟨559826, by decide⟩ (by decide) (![⟨559665, by decide⟩,⟨559712, by decide⟩,⟨559771, by decide⟩,⟨559825, by decide⟩]) unmarked_context_11_18833_559826 node_context_11_18833_559826
  intro a
  fin_cases a
  · exact context_12_75332_559665
  · exact context_12_75333_559712
  · exact context_12_75334_559771
  · exact context_12_75335_559825

theorem selected_cut_21936 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301344) = some ⟨13, 1, 0, 3444, 301344, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301344_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301344 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301344 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301344, 1, 16384⟩
    (by decide) selected_cut_21936

theorem selected_cut_21937 : selected 8 ⟨559847, by decide⟩
    (prefixPartial 13 301345) = some ⟨13, 2, 0, 559847, 301345, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_301345_559847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301345 ⟨559847, by decide⟩ :=
  accepted_of_selected 13 301345 ⟨559847, by decide⟩ ⟨13, 2, 0, 559847, 301345, 1841, 16384⟩
    (by decide) selected_cut_21937

theorem selected_cut_21938 : selected 8 ⟨559868, by decide⟩
    (prefixPartial 13 301346) = some ⟨13, 2, 0, 559868, 301346, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_301346_559868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301346 ⟨559868, by decide⟩ :=
  accepted_of_selected 13 301346 ⟨559868, by decide⟩ ⟨13, 2, 0, 559868, 301346, 1577, 16384⟩
    (by decide) selected_cut_21938

theorem selected_cut_21939 : selected 8 ⟨559874, by decide⟩
    (prefixPartial 13 301347) = some ⟨13, 2, 0, 559874, 301347, 849, 16384⟩ := by
  decide +kernel

theorem context_13_301347_559874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301347 ⟨559874, by decide⟩ :=
  accepted_of_selected 13 301347 ⟨559874, by decide⟩ ⟨13, 2, 0, 559874, 301347, 849, 16384⟩
    (by decide) selected_cut_21939

theorem unmarked_context_12_75336_559875 : frontier 9 ⟨559875, by decide⟩
    (prefixCache 12 75336) (prefixPartial 12 75336) = false := by
  decide +kernel

theorem node_context_12_75336_559875 : EJMOriginalGlobalDAGData.nodes 9 ⟨559875, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559847, by decide⟩,⟨559868, by decide⟩,⟨559874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75336_559875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75336 ⟨559875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75336
    ⟨559875, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559847, by decide⟩,⟨559868, by decide⟩,⟨559874, by decide⟩]) unmarked_context_12_75336_559875 node_context_12_75336_559875
  intro a
  fin_cases a
  · exact context_13_301344_3444
  · exact context_13_301345_559847
  · exact context_13_301346_559868
  · exact context_13_301347_559874

theorem selected_cut_21940 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301348) = some ⟨13, 1, 0, 3444, 301348, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301348_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301348 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301348 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301348, 1, 16384⟩
    (by decide) selected_cut_21940

theorem selected_cut_21941 : selected 8 ⟨559907, by decide⟩
    (prefixPartial 13 301349) = some ⟨13, 2, 0, 559907, 301349, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_301349_559907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301349 ⟨559907, by decide⟩ :=
  accepted_of_selected 13 301349 ⟨559907, by decide⟩ ⟨13, 2, 0, 559907, 301349, 2021, 16384⟩
    (by decide) selected_cut_21941

theorem selected_cut_21942 : selected 8 ⟨559925, by decide⟩
    (prefixPartial 13 301350) = some ⟨13, 2, 0, 559925, 301350, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_301350_559925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301350 ⟨559925, by decide⟩ :=
  accepted_of_selected 13 301350 ⟨559925, by decide⟩ ⟨13, 2, 0, 559925, 301350, 1493, 16384⟩
    (by decide) selected_cut_21942

theorem selected_cut_21943 : selected 8 ⟨559932, by decide⟩
    (prefixPartial 13 301351) = some ⟨13, 2, 0, 559932, 301351, 917, 16384⟩ := by
  decide +kernel

theorem context_13_301351_559932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301351 ⟨559932, by decide⟩ :=
  accepted_of_selected 13 301351 ⟨559932, by decide⟩ ⟨13, 2, 0, 559932, 301351, 917, 16384⟩
    (by decide) selected_cut_21943

theorem unmarked_context_12_75337_559933 : frontier 9 ⟨559933, by decide⟩
    (prefixCache 12 75337) (prefixPartial 12 75337) = false := by
  decide +kernel

theorem node_context_12_75337_559933 : EJMOriginalGlobalDAGData.nodes 9 ⟨559933, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨559907, by decide⟩,⟨559925, by decide⟩,⟨559932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75337_559933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75337 ⟨559933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75337
    ⟨559933, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨559907, by decide⟩,⟨559925, by decide⟩,⟨559932, by decide⟩]) unmarked_context_12_75337_559933 node_context_12_75337_559933
  intro a
  fin_cases a
  · exact context_13_301348_3444
  · exact context_13_301349_559907
  · exact context_13_301350_559925
  · exact context_13_301351_559932

theorem selected_cut_21944 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301352) = some ⟨13, 1, 0, 3444, 301352, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301352_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301352 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301352 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301352, 1, 16384⟩
    (by decide) selected_cut_21944

theorem selected_cut_21945 : selected 8 ⟨560003, by decide⟩
    (prefixPartial 13 301353) = some ⟨13, 2, 0, 560003, 301353, 3849, 16384⟩ := by
  decide +kernel

theorem context_13_301353_560003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301353 ⟨560003, by decide⟩ :=
  accepted_of_selected 13 301353 ⟨560003, by decide⟩ ⟨13, 2, 0, 560003, 301353, 3849, 16384⟩
    (by decide) selected_cut_21945

theorem selected_cut_21946 : selected 8 ⟨560058, by decide⟩
    (prefixPartial 13 301354) = some ⟨13, 2, 0, 560058, 301354, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_301354_560058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301354 ⟨560058, by decide⟩ :=
  accepted_of_selected 13 301354 ⟨560058, by decide⟩ ⟨13, 2, 0, 560058, 301354, 2697, 16384⟩
    (by decide) selected_cut_21946

theorem selected_cut_21947 : selected 8 ⟨560087, by decide⟩
    (prefixPartial 13 301355) = some ⟨13, 2, 0, 560087, 301355, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_301355_560087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301355 ⟨560087, by decide⟩ :=
  accepted_of_selected 13 301355 ⟨560087, by decide⟩ ⟨13, 2, 0, 560087, 301355, 1401, 16384⟩
    (by decide) selected_cut_21947

theorem unmarked_context_12_75338_560088 : frontier 9 ⟨560088, by decide⟩
    (prefixCache 12 75338) (prefixPartial 12 75338) = false := by
  decide +kernel

theorem node_context_12_75338_560088 : EJMOriginalGlobalDAGData.nodes 9 ⟨560088, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560003, by decide⟩,⟨560058, by decide⟩,⟨560087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75338_560088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75338 ⟨560088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75338
    ⟨560088, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560003, by decide⟩,⟨560058, by decide⟩,⟨560087, by decide⟩]) unmarked_context_12_75338_560088 node_context_12_75338_560088
  intro a
  fin_cases a
  · exact context_13_301352_3444
  · exact context_13_301353_560003
  · exact context_13_301354_560058
  · exact context_13_301355_560087

theorem selected_cut_21948 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301356) = some ⟨13, 1, 0, 3444, 301356, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301356_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301356 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301356 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301356, 1, 16384⟩
    (by decide) selected_cut_21948

theorem selected_cut_21949 : selected 8 ⟨560123, by decide⟩
    (prefixPartial 13 301357) = some ⟨13, 2, 0, 560123, 301357, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_301357_560123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301357 ⟨560123, by decide⟩ :=
  accepted_of_selected 13 301357 ⟨560123, by decide⟩ ⟨13, 2, 0, 560123, 301357, 2477, 16384⟩
    (by decide) selected_cut_21949

theorem selected_cut_21950 : selected 8 ⟨560144, by decide⟩
    (prefixPartial 13 301358) = some ⟨13, 2, 0, 560144, 301358, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_301358_560144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301358 ⟨560144, by decide⟩ :=
  accepted_of_selected 13 301358 ⟨560144, by decide⟩ ⟨13, 2, 0, 560144, 301358, 1713, 16384⟩
    (by decide) selected_cut_21950

theorem selected_cut_21951 : selected 8 ⟨560152, by decide⟩
    (prefixPartial 13 301359) = some ⟨13, 2, 0, 560152, 301359, 829, 16384⟩ := by
  decide +kernel

theorem context_13_301359_560152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301359 ⟨560152, by decide⟩ :=
  accepted_of_selected 13 301359 ⟨560152, by decide⟩ ⟨13, 2, 0, 560152, 301359, 829, 16384⟩
    (by decide) selected_cut_21951

theorem unmarked_context_12_75339_560153 : frontier 9 ⟨560153, by decide⟩
    (prefixCache 12 75339) (prefixPartial 12 75339) = false := by
  decide +kernel

theorem node_context_12_75339_560153 : EJMOriginalGlobalDAGData.nodes 9 ⟨560153, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560123, by decide⟩,⟨560144, by decide⟩,⟨560152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75339_560153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75339 ⟨560153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75339
    ⟨560153, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560123, by decide⟩,⟨560144, by decide⟩,⟨560152, by decide⟩]) unmarked_context_12_75339_560153 node_context_12_75339_560153
  intro a
  fin_cases a
  · exact context_13_301356_3444
  · exact context_13_301357_560123
  · exact context_13_301358_560144
  · exact context_13_301359_560152

theorem unmarked_context_11_18834_560154 : frontier 10 ⟨560154, by decide⟩
    (prefixCache 11 18834) (prefixPartial 11 18834) = false := by
  decide +kernel

theorem node_context_11_18834_560154 : EJMOriginalGlobalDAGData.nodes 10 ⟨560154, by decide⟩ =
    .split (coordinate 11) (![⟨559875, by decide⟩,⟨559933, by decide⟩,⟨560088, by decide⟩,⟨560153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18834_560154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18834 ⟨560154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18834
    ⟨560154, by decide⟩ (by decide) (![⟨559875, by decide⟩,⟨559933, by decide⟩,⟨560088, by decide⟩,⟨560153, by decide⟩]) unmarked_context_11_18834_560154 node_context_11_18834_560154
  intro a
  fin_cases a
  · exact context_12_75336_559875
  · exact context_12_75337_559933
  · exact context_12_75338_560088
  · exact context_12_75339_560153

theorem selected_cut_21952 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301360) = some ⟨13, 1, 0, 3444, 301360, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301360_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301360 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301360 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301360, 1, 16384⟩
    (by decide) selected_cut_21952

theorem selected_cut_21953 : selected 8 ⟨560174, by decide⟩
    (prefixPartial 13 301361) = some ⟨13, 2, 0, 560174, 301361, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_301361_560174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301361 ⟨560174, by decide⟩ :=
  accepted_of_selected 13 301361 ⟨560174, by decide⟩ ⟨13, 2, 0, 560174, 301361, 1921, 16384⟩
    (by decide) selected_cut_21953

theorem selected_cut_21954 : selected 8 ⟨560192, by decide⟩
    (prefixPartial 13 301362) = some ⟨13, 2, 0, 560192, 301362, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_301362_560192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301362 ⟨560192, by decide⟩ :=
  accepted_of_selected 13 301362 ⟨560192, by decide⟩ ⟨13, 2, 0, 560192, 301362, 1593, 16384⟩
    (by decide) selected_cut_21954

theorem selected_cut_21955 : selected 8 ⟨560200, by decide⟩
    (prefixPartial 13 301363) = some ⟨13, 2, 0, 560200, 301363, 865, 16384⟩ := by
  decide +kernel

theorem context_13_301363_560200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301363 ⟨560200, by decide⟩ :=
  accepted_of_selected 13 301363 ⟨560200, by decide⟩ ⟨13, 2, 0, 560200, 301363, 865, 16384⟩
    (by decide) selected_cut_21955

theorem unmarked_context_12_75340_560201 : frontier 9 ⟨560201, by decide⟩
    (prefixCache 12 75340) (prefixPartial 12 75340) = false := by
  decide +kernel

theorem node_context_12_75340_560201 : EJMOriginalGlobalDAGData.nodes 9 ⟨560201, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560174, by decide⟩,⟨560192, by decide⟩,⟨560200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75340_560201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75340 ⟨560201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75340
    ⟨560201, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560174, by decide⟩,⟨560192, by decide⟩,⟨560200, by decide⟩]) unmarked_context_12_75340_560201 node_context_12_75340_560201
  intro a
  fin_cases a
  · exact context_13_301360_3444
  · exact context_13_301361_560174
  · exact context_13_301362_560192
  · exact context_13_301363_560200

theorem selected_cut_21956 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301364) = some ⟨13, 1, 0, 3444, 301364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301364, 1, 16384⟩
    (by decide) selected_cut_21956

theorem selected_cut_21957 : selected 8 ⟨560231, by decide⟩
    (prefixPartial 13 301365) = some ⟨13, 2, 0, 560231, 301365, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_301365_560231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301365 ⟨560231, by decide⟩ :=
  accepted_of_selected 13 301365 ⟨560231, by decide⟩ ⟨13, 2, 0, 560231, 301365, 2185, 16384⟩
    (by decide) selected_cut_21957

theorem selected_cut_21958 : selected 8 ⟨560247, by decide⟩
    (prefixPartial 13 301366) = some ⟨13, 2, 0, 560247, 301366, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_301366_560247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301366 ⟨560247, by decide⟩ :=
  accepted_of_selected 13 301366 ⟨560247, by decide⟩ ⟨13, 2, 0, 560247, 301366, 1465, 16384⟩
    (by decide) selected_cut_21958

theorem selected_cut_21959 : selected 8 ⟨560253, by decide⟩
    (prefixPartial 13 301367) = some ⟨13, 2, 0, 560253, 301367, 845, 16384⟩ := by
  decide +kernel

theorem context_13_301367_560253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301367 ⟨560253, by decide⟩ :=
  accepted_of_selected 13 301367 ⟨560253, by decide⟩ ⟨13, 2, 0, 560253, 301367, 845, 16384⟩
    (by decide) selected_cut_21959

theorem unmarked_context_12_75341_560254 : frontier 9 ⟨560254, by decide⟩
    (prefixCache 12 75341) (prefixPartial 12 75341) = false := by
  decide +kernel

theorem node_context_12_75341_560254 : EJMOriginalGlobalDAGData.nodes 9 ⟨560254, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560231, by decide⟩,⟨560247, by decide⟩,⟨560253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75341_560254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75341 ⟨560254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75341
    ⟨560254, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560231, by decide⟩,⟨560247, by decide⟩,⟨560253, by decide⟩]) unmarked_context_12_75341_560254 node_context_12_75341_560254
  intro a
  fin_cases a
  · exact context_13_301364_3444
  · exact context_13_301365_560231
  · exact context_13_301366_560247
  · exact context_13_301367_560253

theorem selected_cut_21960 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301368) = some ⟨13, 1, 0, 3444, 301368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301368, 1, 16384⟩
    (by decide) selected_cut_21960

theorem selected_cut_21961 : selected 8 ⟨560280, by decide⟩
    (prefixPartial 13 301369) = some ⟨13, 2, 0, 560280, 301369, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_301369_560280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301369 ⟨560280, by decide⟩ :=
  accepted_of_selected 13 301369 ⟨560280, by decide⟩ ⟨13, 2, 0, 560280, 301369, 2313, 16384⟩
    (by decide) selected_cut_21961

theorem selected_cut_21962 : selected 8 ⟨560303, by decide⟩
    (prefixPartial 13 301370) = some ⟨13, 2, 0, 560303, 301370, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_301370_560303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301370 ⟨560303, by decide⟩ :=
  accepted_of_selected 13 301370 ⟨560303, by decide⟩ ⟨13, 2, 0, 560303, 301370, 1621, 16384⟩
    (by decide) selected_cut_21962

theorem selected_cut_21963 : selected 8 ⟨560310, by decide⟩
    (prefixPartial 13 301371) = some ⟨13, 2, 0, 560310, 301371, 969, 16384⟩ := by
  decide +kernel

theorem context_13_301371_560310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301371 ⟨560310, by decide⟩ :=
  accepted_of_selected 13 301371 ⟨560310, by decide⟩ ⟨13, 2, 0, 560310, 301371, 969, 16384⟩
    (by decide) selected_cut_21963

theorem unmarked_context_12_75342_560311 : frontier 9 ⟨560311, by decide⟩
    (prefixCache 12 75342) (prefixPartial 12 75342) = false := by
  decide +kernel

theorem node_context_12_75342_560311 : EJMOriginalGlobalDAGData.nodes 9 ⟨560311, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560280, by decide⟩,⟨560303, by decide⟩,⟨560310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75342_560311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75342 ⟨560311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75342
    ⟨560311, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560280, by decide⟩,⟨560303, by decide⟩,⟨560310, by decide⟩]) unmarked_context_12_75342_560311 node_context_12_75342_560311
  intro a
  fin_cases a
  · exact context_13_301368_3444
  · exact context_13_301369_560280
  · exact context_13_301370_560303
  · exact context_13_301371_560310

theorem selected_cut_21964 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301372) = some ⟨13, 1, 0, 3444, 301372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301372, 1, 16384⟩
    (by decide) selected_cut_21964

theorem selected_cut_21965 : selected 8 ⟨560335, by decide⟩
    (prefixPartial 13 301373) = some ⟨13, 2, 0, 560335, 301373, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_301373_560335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301373 ⟨560335, by decide⟩ :=
  accepted_of_selected 13 301373 ⟨560335, by decide⟩ ⟨13, 2, 0, 560335, 301373, 2301, 16384⟩
    (by decide) selected_cut_21965

theorem selected_cut_21966 : selected 8 ⟨560354, by decide⟩
    (prefixPartial 13 301374) = some ⟨13, 2, 0, 560354, 301374, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_301374_560354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301374 ⟨560354, by decide⟩ :=
  accepted_of_selected 13 301374 ⟨560354, by decide⟩ ⟨13, 2, 0, 560354, 301374, 1793, 16384⟩
    (by decide) selected_cut_21966

theorem selected_cut_21967 : selected 8 ⟨560362, by decide⟩
    (prefixPartial 13 301375) = some ⟨13, 2, 0, 560362, 301375, 913, 16384⟩ := by
  decide +kernel

theorem context_13_301375_560362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301375 ⟨560362, by decide⟩ :=
  accepted_of_selected 13 301375 ⟨560362, by decide⟩ ⟨13, 2, 0, 560362, 301375, 913, 16384⟩
    (by decide) selected_cut_21967

theorem unmarked_context_12_75343_560363 : frontier 9 ⟨560363, by decide⟩
    (prefixCache 12 75343) (prefixPartial 12 75343) = false := by
  decide +kernel

theorem node_context_12_75343_560363 : EJMOriginalGlobalDAGData.nodes 9 ⟨560363, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560335, by decide⟩,⟨560354, by decide⟩,⟨560362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75343_560363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75343 ⟨560363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75343
    ⟨560363, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560335, by decide⟩,⟨560354, by decide⟩,⟨560362, by decide⟩]) unmarked_context_12_75343_560363 node_context_12_75343_560363
  intro a
  fin_cases a
  · exact context_13_301372_3444
  · exact context_13_301373_560335
  · exact context_13_301374_560354
  · exact context_13_301375_560362

theorem unmarked_context_11_18835_560364 : frontier 10 ⟨560364, by decide⟩
    (prefixCache 11 18835) (prefixPartial 11 18835) = false := by
  decide +kernel

theorem node_context_11_18835_560364 : EJMOriginalGlobalDAGData.nodes 10 ⟨560364, by decide⟩ =
    .split (coordinate 11) (![⟨560201, by decide⟩,⟨560254, by decide⟩,⟨560311, by decide⟩,⟨560363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18835_560364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18835 ⟨560364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18835
    ⟨560364, by decide⟩ (by decide) (![⟨560201, by decide⟩,⟨560254, by decide⟩,⟨560311, by decide⟩,⟨560363, by decide⟩]) unmarked_context_11_18835_560364 node_context_11_18835_560364
  intro a
  fin_cases a
  · exact context_12_75340_560201
  · exact context_12_75341_560254
  · exact context_12_75342_560311
  · exact context_12_75343_560363

theorem unmarked_context_10_4708_560365 : frontier 11 ⟨560365, by decide⟩
    (prefixCache 10 4708) (prefixPartial 10 4708) = false := by
  decide +kernel

theorem node_context_10_4708_560365 : EJMOriginalGlobalDAGData.nodes 11 ⟨560365, by decide⟩ =
    .split (coordinate 10) (![⟨559620, by decide⟩,⟨559826, by decide⟩,⟨560154, by decide⟩,⟨560364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4708_560365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4708 ⟨560365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4708
    ⟨560365, by decide⟩ (by decide) (![⟨559620, by decide⟩,⟨559826, by decide⟩,⟨560154, by decide⟩,⟨560364, by decide⟩]) unmarked_context_10_4708_560365 node_context_10_4708_560365
  intro a
  fin_cases a
  · exact context_11_18832_559620
  · exact context_11_18833_559826
  · exact context_11_18834_560154
  · exact context_11_18835_560364

theorem selected_cut_21968 : selected 9 ⟨560411, by decide⟩
    (prefixPartial 12 75344) = some ⟨12, 2, 0, 560411, 75344, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_75344_560411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75344 ⟨560411, by decide⟩ :=
  accepted_of_selected 12 75344 ⟨560411, by decide⟩ ⟨12, 2, 0, 560411, 75344, 3857, 65536⟩
    (by decide) selected_cut_21968

theorem selected_cut_21969 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301380) = some ⟨13, 1, 0, 3444, 301380, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301380_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301380 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301380 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301380, 1, 16384⟩
    (by decide) selected_cut_21969

theorem selected_cut_21970 : selected 8 ⟨560436, by decide⟩
    (prefixPartial 13 301381) = some ⟨13, 2, 0, 560436, 301381, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_301381_560436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301381 ⟨560436, by decide⟩ :=
  accepted_of_selected 13 301381 ⟨560436, by decide⟩ ⟨13, 2, 0, 560436, 301381, 2021, 16384⟩
    (by decide) selected_cut_21970

theorem selected_cut_21971 : selected 8 ⟨560454, by decide⟩
    (prefixPartial 13 301382) = some ⟨13, 2, 0, 560454, 301382, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_301382_560454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301382 ⟨560454, by decide⟩ :=
  accepted_of_selected 13 301382 ⟨560454, by decide⟩ ⟨13, 2, 0, 560454, 301382, 1425, 16384⟩
    (by decide) selected_cut_21971

theorem selected_cut_21972 : selected 8 ⟨560459, by decide⟩
    (prefixPartial 13 301383) = some ⟨13, 2, 0, 560459, 301383, 725, 16384⟩ := by
  decide +kernel

theorem context_13_301383_560459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301383 ⟨560459, by decide⟩ :=
  accepted_of_selected 13 301383 ⟨560459, by decide⟩ ⟨13, 2, 0, 560459, 301383, 725, 16384⟩
    (by decide) selected_cut_21972

theorem unmarked_context_12_75345_560460 : frontier 9 ⟨560460, by decide⟩
    (prefixCache 12 75345) (prefixPartial 12 75345) = false := by
  decide +kernel

theorem node_context_12_75345_560460 : EJMOriginalGlobalDAGData.nodes 9 ⟨560460, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560436, by decide⟩,⟨560454, by decide⟩,⟨560459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75345_560460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75345 ⟨560460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75345
    ⟨560460, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560436, by decide⟩,⟨560454, by decide⟩,⟨560459, by decide⟩]) unmarked_context_12_75345_560460 node_context_12_75345_560460
  intro a
  fin_cases a
  · exact context_13_301380_3444
  · exact context_13_301381_560436
  · exact context_13_301382_560454
  · exact context_13_301383_560459

theorem selected_cut_21973 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301384) = some ⟨13, 1, 0, 3444, 301384, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301384_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301384 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301384 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301384, 1, 16384⟩
    (by decide) selected_cut_21973

theorem selected_cut_21974 : selected 8 ⟨560484, by decide⟩
    (prefixPartial 13 301385) = some ⟨13, 2, 0, 560484, 301385, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_301385_560484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301385 ⟨560484, by decide⟩ :=
  accepted_of_selected 13 301385 ⟨560484, by decide⟩ ⟨13, 2, 0, 560484, 301385, 2005, 16384⟩
    (by decide) selected_cut_21974

theorem selected_cut_21975 : selected 8 ⟨560504, by decide⟩
    (prefixPartial 13 301386) = some ⟨13, 2, 0, 560504, 301386, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_301386_560504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301386 ⟨560504, by decide⟩ :=
  accepted_of_selected 13 301386 ⟨560504, by decide⟩ ⟨13, 2, 0, 560504, 301386, 1513, 16384⟩
    (by decide) selected_cut_21975

theorem selected_cut_21976 : selected 8 ⟨560510, by decide⟩
    (prefixPartial 13 301387) = some ⟨13, 2, 0, 560510, 301387, 801, 16384⟩ := by
  decide +kernel

theorem context_13_301387_560510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301387 ⟨560510, by decide⟩ :=
  accepted_of_selected 13 301387 ⟨560510, by decide⟩ ⟨13, 2, 0, 560510, 301387, 801, 16384⟩
    (by decide) selected_cut_21976

theorem unmarked_context_12_75346_560511 : frontier 9 ⟨560511, by decide⟩
    (prefixCache 12 75346) (prefixPartial 12 75346) = false := by
  decide +kernel

theorem node_context_12_75346_560511 : EJMOriginalGlobalDAGData.nodes 9 ⟨560511, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560484, by decide⟩,⟨560504, by decide⟩,⟨560510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75346_560511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75346 ⟨560511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75346
    ⟨560511, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560484, by decide⟩,⟨560504, by decide⟩,⟨560510, by decide⟩]) unmarked_context_12_75346_560511 node_context_12_75346_560511
  intro a
  fin_cases a
  · exact context_13_301384_3444
  · exact context_13_301385_560484
  · exact context_13_301386_560504
  · exact context_13_301387_560510

theorem selected_cut_21977 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301388) = some ⟨13, 1, 0, 3444, 301388, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301388_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301388 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301388 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301388, 1, 16384⟩
    (by decide) selected_cut_21977

theorem selected_cut_21978 : selected 8 ⟨560548, by decide⟩
    (prefixPartial 13 301389) = some ⟨13, 2, 0, 560548, 301389, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_301389_560548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301389 ⟨560548, by decide⟩ :=
  accepted_of_selected 13 301389 ⟨560548, by decide⟩ ⟨13, 2, 0, 560548, 301389, 2389, 16384⟩
    (by decide) selected_cut_21978

theorem selected_cut_21979 : selected 8 ⟨560573, by decide⟩
    (prefixPartial 13 301390) = some ⟨13, 2, 0, 560573, 301390, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_301390_560573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301390 ⟨560573, by decide⟩ :=
  accepted_of_selected 13 301390 ⟨560573, by decide⟩ ⟨13, 2, 0, 560573, 301390, 1957, 16384⟩
    (by decide) selected_cut_21979

theorem selected_cut_21980 : selected 8 ⟨560579, by decide⟩
    (prefixPartial 13 301391) = some ⟨13, 2, 0, 560579, 301391, 753, 16384⟩ := by
  decide +kernel

theorem context_13_301391_560579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301391 ⟨560579, by decide⟩ :=
  accepted_of_selected 13 301391 ⟨560579, by decide⟩ ⟨13, 2, 0, 560579, 301391, 753, 16384⟩
    (by decide) selected_cut_21980

theorem unmarked_context_12_75347_560580 : frontier 9 ⟨560580, by decide⟩
    (prefixCache 12 75347) (prefixPartial 12 75347) = false := by
  decide +kernel

theorem node_context_12_75347_560580 : EJMOriginalGlobalDAGData.nodes 9 ⟨560580, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560548, by decide⟩,⟨560573, by decide⟩,⟨560579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75347_560580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75347 ⟨560580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75347
    ⟨560580, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560548, by decide⟩,⟨560573, by decide⟩,⟨560579, by decide⟩]) unmarked_context_12_75347_560580 node_context_12_75347_560580
  intro a
  fin_cases a
  · exact context_13_301388_3444
  · exact context_13_301389_560548
  · exact context_13_301390_560573
  · exact context_13_301391_560579

theorem unmarked_context_11_18836_560581 : frontier 10 ⟨560581, by decide⟩
    (prefixCache 11 18836) (prefixPartial 11 18836) = false := by
  decide +kernel

theorem node_context_11_18836_560581 : EJMOriginalGlobalDAGData.nodes 10 ⟨560581, by decide⟩ =
    .split (coordinate 11) (![⟨560411, by decide⟩,⟨560460, by decide⟩,⟨560511, by decide⟩,⟨560580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18836_560581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18836 ⟨560581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18836
    ⟨560581, by decide⟩ (by decide) (![⟨560411, by decide⟩,⟨560460, by decide⟩,⟨560511, by decide⟩,⟨560580, by decide⟩]) unmarked_context_11_18836_560581 node_context_11_18836_560581
  intro a
  fin_cases a
  · exact context_12_75344_560411
  · exact context_12_75345_560460
  · exact context_12_75346_560511
  · exact context_12_75347_560580

theorem selected_cut_21981 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 18837) = some ⟨11, 1, 0, 451541, 18837, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18837_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18837 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 18837 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 18837, 1, 262144⟩
    (by decide) selected_cut_21981

theorem selected_cut_21982 : selected 9 ⟨560623, by decide⟩
    (prefixPartial 12 75352) = some ⟨12, 2, 0, 560623, 75352, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_75352_560623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75352 ⟨560623, by decide⟩ :=
  accepted_of_selected 12 75352 ⟨560623, by decide⟩ ⟨12, 2, 0, 560623, 75352, 3869, 65536⟩
    (by decide) selected_cut_21982

theorem selected_cut_21983 : selected 9 ⟨560663, by decide⟩
    (prefixPartial 12 75353) = some ⟨12, 2, 0, 560663, 75353, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_75353_560663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75353 ⟨560663, by decide⟩ :=
  accepted_of_selected 12 75353 ⟨560663, by decide⟩ ⟨12, 2, 0, 560663, 75353, 3749, 65536⟩
    (by decide) selected_cut_21983

theorem selected_cut_21984 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301416) = some ⟨13, 1, 0, 3444, 301416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301416, 1, 16384⟩
    (by decide) selected_cut_21984

theorem selected_cut_21985 : selected 8 ⟨560697, by decide⟩
    (prefixPartial 13 301417) = some ⟨13, 2, 0, 560697, 301417, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_301417_560697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301417 ⟨560697, by decide⟩ :=
  accepted_of_selected 13 301417 ⟨560697, by decide⟩ ⟨13, 2, 0, 560697, 301417, 2377, 16384⟩
    (by decide) selected_cut_21985

theorem selected_cut_21986 : selected 8 ⟨560757, by decide⟩
    (prefixPartial 13 301418) = some ⟨13, 2, 0, 560757, 301418, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_301418_560757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301418 ⟨560757, by decide⟩ :=
  accepted_of_selected 13 301418 ⟨560757, by decide⟩ ⟨13, 2, 0, 560757, 301418, 2949, 16384⟩
    (by decide) selected_cut_21986

theorem selected_cut_21987 : selected 8 ⟨560796, by decide⟩
    (prefixPartial 13 301419) = some ⟨13, 2, 0, 560796, 301419, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_301419_560796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301419 ⟨560796, by decide⟩ :=
  accepted_of_selected 13 301419 ⟨560796, by decide⟩ ⟨13, 2, 0, 560796, 301419, 1645, 16384⟩
    (by decide) selected_cut_21987

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
