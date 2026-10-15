/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover131
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12676 : selected 9 ⟨334137, by decide⟩
    (prefixPartial 12 26287) = some ⟨12, 2, 0, 334137, 26287, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_26287_334137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26287 ⟨334137, by decide⟩ :=
  accepted_of_selected 12 26287 ⟨334137, by decide⟩ ⟨12, 2, 0, 334137, 26287, 1605, 65536⟩
    (by decide) selected_cut_12676

theorem unmarked_context_11_6571_334138 : frontier 10 ⟨334138, by decide⟩
    (prefixCache 11 6571) (prefixPartial 11 6571) = false := by
  decide +kernel

theorem node_context_11_6571_334138 : EJMOriginalGlobalDAGData.nodes 10 ⟨334138, by decide⟩ =
    .split (coordinate 11) (![⟨334091, by decide⟩,⟨334109, by decide⟩,⟨334121, by decide⟩,⟨334137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6571_334138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6571 ⟨334138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6571
    ⟨334138, by decide⟩ (by decide) (![⟨334091, by decide⟩,⟨334109, by decide⟩,⟨334121, by decide⟩,⟨334137, by decide⟩]) unmarked_context_11_6571_334138 node_context_11_6571_334138
  intro a
  fin_cases a
  · exact context_12_26284_334091
  · exact context_12_26285_334109
  · exact context_12_26286_334121
  · exact context_12_26287_334137

theorem unmarked_context_10_1642_334139 : frontier 11 ⟨334139, by decide⟩
    (prefixCache 10 1642) (prefixPartial 10 1642) = false := by
  decide +kernel

theorem node_context_10_1642_334139 : EJMOriginalGlobalDAGData.nodes 11 ⟨334139, by decide⟩ =
    .split (coordinate 10) (![⟨333946, by decide⟩,⟨334014, by decide⟩,⟨334072, by decide⟩,⟨334138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1642_334139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1642 ⟨334139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1642
    ⟨334139, by decide⟩ (by decide) (![⟨333946, by decide⟩,⟨334014, by decide⟩,⟨334072, by decide⟩,⟨334138, by decide⟩]) unmarked_context_10_1642_334139 node_context_10_1642_334139
  intro a
  fin_cases a
  · exact context_11_6568_333946
  · exact context_11_6569_334014
  · exact context_11_6570_334072
  · exact context_11_6571_334138

theorem selected_cut_12677 : selected 9 ⟨334151, by decide⟩
    (prefixPartial 12 26288) = some ⟨12, 2, 0, 334151, 26288, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_26288_334151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26288 ⟨334151, by decide⟩ :=
  accepted_of_selected 12 26288 ⟨334151, by decide⟩ ⟨12, 2, 0, 334151, 26288, 1221, 65536⟩
    (by decide) selected_cut_12677

theorem selected_cut_12678 : selected 9 ⟨334166, by decide⟩
    (prefixPartial 12 26289) = some ⟨12, 2, 0, 334166, 26289, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_26289_334166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26289 ⟨334166, by decide⟩ :=
  accepted_of_selected 12 26289 ⟨334166, by decide⟩ ⟨12, 2, 0, 334166, 26289, 1393, 65536⟩
    (by decide) selected_cut_12678

theorem selected_cut_12679 : selected 9 ⟨334180, by decide⟩
    (prefixPartial 12 26290) = some ⟨12, 2, 0, 334180, 26290, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_26290_334180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26290 ⟨334180, by decide⟩ :=
  accepted_of_selected 12 26290 ⟨334180, by decide⟩ ⟨12, 2, 0, 334180, 26290, 1173, 65536⟩
    (by decide) selected_cut_12679

theorem selected_cut_12680 : selected 9 ⟨334194, by decide⟩
    (prefixPartial 12 26291) = some ⟨12, 2, 0, 334194, 26291, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_26291_334194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26291 ⟨334194, by decide⟩ :=
  accepted_of_selected 12 26291 ⟨334194, by decide⟩ ⟨12, 2, 0, 334194, 26291, 1401, 65536⟩
    (by decide) selected_cut_12680

theorem unmarked_context_11_6572_334195 : frontier 10 ⟨334195, by decide⟩
    (prefixCache 11 6572) (prefixPartial 11 6572) = false := by
  decide +kernel

theorem node_context_11_6572_334195 : EJMOriginalGlobalDAGData.nodes 10 ⟨334195, by decide⟩ =
    .split (coordinate 11) (![⟨334151, by decide⟩,⟨334166, by decide⟩,⟨334180, by decide⟩,⟨334194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6572_334195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6572 ⟨334195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6572
    ⟨334195, by decide⟩ (by decide) (![⟨334151, by decide⟩,⟨334166, by decide⟩,⟨334180, by decide⟩,⟨334194, by decide⟩]) unmarked_context_11_6572_334195 node_context_11_6572_334195
  intro a
  fin_cases a
  · exact context_12_26288_334151
  · exact context_12_26289_334166
  · exact context_12_26290_334180
  · exact context_12_26291_334194

theorem selected_cut_12681 : selected 9 ⟨334205, by decide⟩
    (prefixPartial 12 26292) = some ⟨12, 2, 0, 334205, 26292, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_26292_334205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26292 ⟨334205, by decide⟩ :=
  accepted_of_selected 12 26292 ⟨334205, by decide⟩ ⟨12, 2, 0, 334205, 26292, 1201, 65536⟩
    (by decide) selected_cut_12681

theorem selected_cut_12682 : selected 9 ⟨334220, by decide⟩
    (prefixPartial 12 26293) = some ⟨12, 2, 0, 334220, 26293, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_26293_334220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26293 ⟨334220, by decide⟩ :=
  accepted_of_selected 12 26293 ⟨334220, by decide⟩ ⟨12, 2, 0, 334220, 26293, 1205, 65536⟩
    (by decide) selected_cut_12682

theorem selected_cut_12683 : selected 9 ⟨334229, by decide⟩
    (prefixPartial 12 26294) = some ⟨12, 2, 0, 334229, 26294, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_26294_334229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26294 ⟨334229, by decide⟩ :=
  accepted_of_selected 12 26294 ⟨334229, by decide⟩ ⟨12, 2, 0, 334229, 26294, 1089, 65536⟩
    (by decide) selected_cut_12683

theorem selected_cut_12684 : selected 9 ⟨334246, by decide⟩
    (prefixPartial 12 26295) = some ⟨12, 2, 0, 334246, 26295, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_26295_334246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26295 ⟨334246, by decide⟩ :=
  accepted_of_selected 12 26295 ⟨334246, by decide⟩ ⟨12, 2, 0, 334246, 26295, 1277, 65536⟩
    (by decide) selected_cut_12684

theorem unmarked_context_11_6573_334247 : frontier 10 ⟨334247, by decide⟩
    (prefixCache 11 6573) (prefixPartial 11 6573) = false := by
  decide +kernel

theorem node_context_11_6573_334247 : EJMOriginalGlobalDAGData.nodes 10 ⟨334247, by decide⟩ =
    .split (coordinate 11) (![⟨334205, by decide⟩,⟨334220, by decide⟩,⟨334229, by decide⟩,⟨334246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6573_334247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6573 ⟨334247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6573
    ⟨334247, by decide⟩ (by decide) (![⟨334205, by decide⟩,⟨334220, by decide⟩,⟨334229, by decide⟩,⟨334246, by decide⟩]) unmarked_context_11_6573_334247 node_context_11_6573_334247
  intro a
  fin_cases a
  · exact context_12_26292_334205
  · exact context_12_26293_334220
  · exact context_12_26294_334229
  · exact context_12_26295_334246

theorem selected_cut_12685 : selected 9 ⟨334259, by decide⟩
    (prefixPartial 12 26296) = some ⟨12, 2, 0, 334259, 26296, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_26296_334259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26296 ⟨334259, by decide⟩ :=
  accepted_of_selected 12 26296 ⟨334259, by decide⟩ ⟨12, 2, 0, 334259, 26296, 1077, 65536⟩
    (by decide) selected_cut_12685

theorem selected_cut_12686 : selected 9 ⟨334271, by decide⟩
    (prefixPartial 12 26297) = some ⟨12, 2, 0, 334271, 26297, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_26297_334271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26297 ⟨334271, by decide⟩ :=
  accepted_of_selected 12 26297 ⟨334271, by decide⟩ ⟨12, 2, 0, 334271, 26297, 1121, 65536⟩
    (by decide) selected_cut_12686

theorem selected_cut_12687 : selected 9 ⟨334285, by decide⟩
    (prefixPartial 12 26298) = some ⟨12, 2, 0, 334285, 26298, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_26298_334285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26298 ⟨334285, by decide⟩ :=
  accepted_of_selected 12 26298 ⟨334285, by decide⟩ ⟨12, 2, 0, 334285, 26298, 1441, 65536⟩
    (by decide) selected_cut_12687

theorem selected_cut_12688 : selected 9 ⟨334298, by decide⟩
    (prefixPartial 12 26299) = some ⟨12, 2, 0, 334298, 26299, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_26299_334298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26299 ⟨334298, by decide⟩ :=
  accepted_of_selected 12 26299 ⟨334298, by decide⟩ ⟨12, 2, 0, 334298, 26299, 1053, 65536⟩
    (by decide) selected_cut_12688

theorem unmarked_context_11_6574_334299 : frontier 10 ⟨334299, by decide⟩
    (prefixCache 11 6574) (prefixPartial 11 6574) = false := by
  decide +kernel

theorem node_context_11_6574_334299 : EJMOriginalGlobalDAGData.nodes 10 ⟨334299, by decide⟩ =
    .split (coordinate 11) (![⟨334259, by decide⟩,⟨334271, by decide⟩,⟨334285, by decide⟩,⟨334298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6574_334299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6574 ⟨334299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6574
    ⟨334299, by decide⟩ (by decide) (![⟨334259, by decide⟩,⟨334271, by decide⟩,⟨334285, by decide⟩,⟨334298, by decide⟩]) unmarked_context_11_6574_334299 node_context_11_6574_334299
  intro a
  fin_cases a
  · exact context_12_26296_334259
  · exact context_12_26297_334271
  · exact context_12_26298_334285
  · exact context_12_26299_334298

theorem selected_cut_12689 : selected 9 ⟨334311, by decide⟩
    (prefixPartial 12 26300) = some ⟨12, 2, 0, 334311, 26300, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_26300_334311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26300 ⟨334311, by decide⟩ :=
  accepted_of_selected 12 26300 ⟨334311, by decide⟩ ⟨12, 2, 0, 334311, 26300, 1089, 65536⟩
    (by decide) selected_cut_12689

theorem selected_cut_12690 : selected 9 ⟨334322, by decide⟩
    (prefixPartial 12 26301) = some ⟨12, 2, 0, 334322, 26301, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_26301_334322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26301 ⟨334322, by decide⟩ :=
  accepted_of_selected 12 26301 ⟨334322, by decide⟩ ⟨12, 2, 0, 334322, 26301, 1089, 65536⟩
    (by decide) selected_cut_12690

theorem selected_cut_12691 : selected 9 ⟨334334, by decide⟩
    (prefixPartial 12 26302) = some ⟨12, 2, 0, 334334, 26302, 977, 65536⟩ := by
  decide +kernel

theorem context_12_26302_334334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26302 ⟨334334, by decide⟩ :=
  accepted_of_selected 12 26302 ⟨334334, by decide⟩ ⟨12, 2, 0, 334334, 26302, 977, 65536⟩
    (by decide) selected_cut_12691

theorem selected_cut_12692 : selected 9 ⟨334346, by decide⟩
    (prefixPartial 12 26303) = some ⟨12, 2, 0, 334346, 26303, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_26303_334346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26303 ⟨334346, by decide⟩ :=
  accepted_of_selected 12 26303 ⟨334346, by decide⟩ ⟨12, 2, 0, 334346, 26303, 1057, 65536⟩
    (by decide) selected_cut_12692

theorem unmarked_context_11_6575_334347 : frontier 10 ⟨334347, by decide⟩
    (prefixCache 11 6575) (prefixPartial 11 6575) = false := by
  decide +kernel

theorem node_context_11_6575_334347 : EJMOriginalGlobalDAGData.nodes 10 ⟨334347, by decide⟩ =
    .split (coordinate 11) (![⟨334311, by decide⟩,⟨334322, by decide⟩,⟨334334, by decide⟩,⟨334346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6575_334347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6575 ⟨334347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6575
    ⟨334347, by decide⟩ (by decide) (![⟨334311, by decide⟩,⟨334322, by decide⟩,⟨334334, by decide⟩,⟨334346, by decide⟩]) unmarked_context_11_6575_334347 node_context_11_6575_334347
  intro a
  fin_cases a
  · exact context_12_26300_334311
  · exact context_12_26301_334322
  · exact context_12_26302_334334
  · exact context_12_26303_334346

theorem unmarked_context_10_1643_334348 : frontier 11 ⟨334348, by decide⟩
    (prefixCache 10 1643) (prefixPartial 10 1643) = false := by
  decide +kernel

theorem node_context_10_1643_334348 : EJMOriginalGlobalDAGData.nodes 11 ⟨334348, by decide⟩ =
    .split (coordinate 10) (![⟨334195, by decide⟩,⟨334247, by decide⟩,⟨334299, by decide⟩,⟨334347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1643_334348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1643 ⟨334348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1643
    ⟨334348, by decide⟩ (by decide) (![⟨334195, by decide⟩,⟨334247, by decide⟩,⟨334299, by decide⟩,⟨334347, by decide⟩]) unmarked_context_10_1643_334348 node_context_10_1643_334348
  intro a
  fin_cases a
  · exact context_11_6572_334195
  · exact context_11_6573_334247
  · exact context_11_6574_334299
  · exact context_11_6575_334347

theorem unmarked_context_9_410_334349 : frontier 12 ⟨334349, by decide⟩
    (prefixCache 9 410) (prefixPartial 9 410) = false := by
  decide +kernel

theorem node_context_9_410_334349 : EJMOriginalGlobalDAGData.nodes 12 ⟨334349, by decide⟩ =
    .split (coordinate 9) (![⟨333504, by decide⟩,⟨333870, by decide⟩,⟨334139, by decide⟩,⟨334348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_410_334349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 410 ⟨334349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 410
    ⟨334349, by decide⟩ (by decide) (![⟨333504, by decide⟩,⟨333870, by decide⟩,⟨334139, by decide⟩,⟨334348, by decide⟩]) unmarked_context_9_410_334349 node_context_9_410_334349
  intro a
  fin_cases a
  · exact context_10_1640_333504
  · exact context_10_1641_333870
  · exact context_10_1642_334139
  · exact context_10_1643_334348

theorem selected_cut_12693 : selected 9 ⟨334356, by decide⟩
    (prefixPartial 12 26304) = some ⟨12, 2, 0, 334356, 26304, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_26304_334356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26304 ⟨334356, by decide⟩ :=
  accepted_of_selected 12 26304 ⟨334356, by decide⟩ ⟨12, 2, 0, 334356, 26304, 1089, 65536⟩
    (by decide) selected_cut_12693

theorem selected_cut_12694 : selected 9 ⟨334366, by decide⟩
    (prefixPartial 12 26305) = some ⟨12, 2, 0, 334366, 26305, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_26305_334366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26305 ⟨334366, by decide⟩ :=
  accepted_of_selected 12 26305 ⟨334366, by decide⟩ ⟨12, 2, 0, 334366, 26305, 1141, 65536⟩
    (by decide) selected_cut_12694

theorem selected_cut_12695 : selected 9 ⟨334377, by decide⟩
    (prefixPartial 12 26306) = some ⟨12, 2, 0, 334377, 26306, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_26306_334377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26306 ⟨334377, by decide⟩ :=
  accepted_of_selected 12 26306 ⟨334377, by decide⟩ ⟨12, 2, 0, 334377, 26306, 1049, 65536⟩
    (by decide) selected_cut_12695

theorem selected_cut_12696 : selected 9 ⟨334384, by decide⟩
    (prefixPartial 12 26307) = some ⟨12, 2, 0, 334384, 26307, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_26307_334384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26307 ⟨334384, by decide⟩ :=
  accepted_of_selected 12 26307 ⟨334384, by decide⟩ ⟨12, 2, 0, 334384, 26307, 1001, 65536⟩
    (by decide) selected_cut_12696

theorem unmarked_context_11_6576_334385 : frontier 10 ⟨334385, by decide⟩
    (prefixCache 11 6576) (prefixPartial 11 6576) = false := by
  decide +kernel

theorem node_context_11_6576_334385 : EJMOriginalGlobalDAGData.nodes 10 ⟨334385, by decide⟩ =
    .split (coordinate 11) (![⟨334356, by decide⟩,⟨334366, by decide⟩,⟨334377, by decide⟩,⟨334384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6576_334385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6576 ⟨334385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6576
    ⟨334385, by decide⟩ (by decide) (![⟨334356, by decide⟩,⟨334366, by decide⟩,⟨334377, by decide⟩,⟨334384, by decide⟩]) unmarked_context_11_6576_334385 node_context_11_6576_334385
  intro a
  fin_cases a
  · exact context_12_26304_334356
  · exact context_12_26305_334366
  · exact context_12_26306_334377
  · exact context_12_26307_334384

theorem selected_cut_12697 : selected 10 ⟨334418, by decide⟩
    (prefixPartial 11 6577) = some ⟨11, 2, 0, 334418, 6577, 3629, 262144⟩ := by
  decide +kernel

theorem context_11_6577_334418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6577 ⟨334418, by decide⟩ :=
  accepted_of_selected 11 6577 ⟨334418, by decide⟩ ⟨11, 2, 0, 334418, 6577, 3629, 262144⟩
    (by decide) selected_cut_12697

theorem selected_cut_12698 : selected 10 ⟨334461, by decide⟩
    (prefixPartial 11 6578) = some ⟨11, 2, 0, 334461, 6578, 3421, 262144⟩ := by
  decide +kernel

theorem context_11_6578_334461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6578 ⟨334461, by decide⟩ :=
  accepted_of_selected 11 6578 ⟨334461, by decide⟩ ⟨11, 2, 0, 334461, 6578, 3421, 262144⟩
    (by decide) selected_cut_12698

theorem selected_cut_12699 : selected 10 ⟨334494, by decide⟩
    (prefixPartial 11 6579) = some ⟨11, 2, 0, 334494, 6579, 3081, 262144⟩ := by
  decide +kernel

theorem context_11_6579_334494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6579 ⟨334494, by decide⟩ :=
  accepted_of_selected 11 6579 ⟨334494, by decide⟩ ⟨11, 2, 0, 334494, 6579, 3081, 262144⟩
    (by decide) selected_cut_12699

theorem unmarked_context_10_1644_334495 : frontier 11 ⟨334495, by decide⟩
    (prefixCache 10 1644) (prefixPartial 10 1644) = false := by
  decide +kernel

theorem node_context_10_1644_334495 : EJMOriginalGlobalDAGData.nodes 11 ⟨334495, by decide⟩ =
    .split (coordinate 10) (![⟨334385, by decide⟩,⟨334418, by decide⟩,⟨334461, by decide⟩,⟨334494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1644_334495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1644 ⟨334495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1644
    ⟨334495, by decide⟩ (by decide) (![⟨334385, by decide⟩,⟨334418, by decide⟩,⟨334461, by decide⟩,⟨334494, by decide⟩]) unmarked_context_10_1644_334495 node_context_10_1644_334495
  intro a
  fin_cases a
  · exact context_11_6576_334385
  · exact context_11_6577_334418
  · exact context_11_6578_334461
  · exact context_11_6579_334494

theorem selected_cut_12700 : selected 10 ⟨334519, by decide⟩
    (prefixPartial 11 6580) = some ⟨11, 2, 0, 334519, 6580, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_6580_334519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6580 ⟨334519, by decide⟩ :=
  accepted_of_selected 11 6580 ⟨334519, by decide⟩ ⟨11, 2, 0, 334519, 6580, 2985, 262144⟩
    (by decide) selected_cut_12700

theorem selected_cut_12701 : selected 10 ⟨334548, by decide⟩
    (prefixPartial 11 6581) = some ⟨11, 2, 0, 334548, 6581, 3045, 262144⟩ := by
  decide +kernel

theorem context_11_6581_334548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6581 ⟨334548, by decide⟩ :=
  accepted_of_selected 11 6581 ⟨334548, by decide⟩ ⟨11, 2, 0, 334548, 6581, 3045, 262144⟩
    (by decide) selected_cut_12701

theorem selected_cut_12702 : selected 10 ⟨334570, by decide⟩
    (prefixPartial 11 6582) = some ⟨11, 2, 0, 334570, 6582, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_6582_334570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6582 ⟨334570, by decide⟩ :=
  accepted_of_selected 11 6582 ⟨334570, by decide⟩ ⟨11, 2, 0, 334570, 6582, 2185, 262144⟩
    (by decide) selected_cut_12702

theorem selected_cut_12703 : selected 10 ⟨334588, by decide⟩
    (prefixPartial 11 6583) = some ⟨11, 2, 0, 334588, 6583, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_6583_334588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6583 ⟨334588, by decide⟩ :=
  accepted_of_selected 11 6583 ⟨334588, by decide⟩ ⟨11, 2, 0, 334588, 6583, 1961, 262144⟩
    (by decide) selected_cut_12703

theorem unmarked_context_10_1645_334589 : frontier 11 ⟨334589, by decide⟩
    (prefixCache 10 1645) (prefixPartial 10 1645) = false := by
  decide +kernel

theorem node_context_10_1645_334589 : EJMOriginalGlobalDAGData.nodes 11 ⟨334589, by decide⟩ =
    .split (coordinate 10) (![⟨334519, by decide⟩,⟨334548, by decide⟩,⟨334570, by decide⟩,⟨334588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1645_334589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1645 ⟨334589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1645
    ⟨334589, by decide⟩ (by decide) (![⟨334519, by decide⟩,⟨334548, by decide⟩,⟨334570, by decide⟩,⟨334588, by decide⟩]) unmarked_context_10_1645_334589 node_context_10_1645_334589
  intro a
  fin_cases a
  · exact context_11_6580_334519
  · exact context_11_6581_334548
  · exact context_11_6582_334570
  · exact context_11_6583_334588

theorem selected_cut_12704 : selected 10 ⟨334605, by decide⟩
    (prefixPartial 11 6584) = some ⟨11, 2, 0, 334605, 6584, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_6584_334605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6584 ⟨334605, by decide⟩ :=
  accepted_of_selected 11 6584 ⟨334605, by decide⟩ ⟨11, 2, 0, 334605, 6584, 1569, 262144⟩
    (by decide) selected_cut_12704

theorem selected_cut_12705 : selected 10 ⟨334618, by decide⟩
    (prefixPartial 11 6585) = some ⟨11, 2, 0, 334618, 6585, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_6585_334618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6585 ⟨334618, by decide⟩ :=
  accepted_of_selected 11 6585 ⟨334618, by decide⟩ ⟨11, 2, 0, 334618, 6585, 1129, 262144⟩
    (by decide) selected_cut_12705

theorem selected_cut_12706 : selected 10 ⟨334632, by decide⟩
    (prefixPartial 11 6586) = some ⟨11, 2, 0, 334632, 6586, 1037, 262144⟩ := by
  decide +kernel

theorem context_11_6586_334632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6586 ⟨334632, by decide⟩ :=
  accepted_of_selected 11 6586 ⟨334632, by decide⟩ ⟨11, 2, 0, 334632, 6586, 1037, 262144⟩
    (by decide) selected_cut_12706

theorem selected_cut_12707 : selected 10 ⟨334645, by decide⟩
    (prefixPartial 11 6587) = some ⟨11, 2, 0, 334645, 6587, 841, 262144⟩ := by
  decide +kernel

theorem context_11_6587_334645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6587 ⟨334645, by decide⟩ :=
  accepted_of_selected 11 6587 ⟨334645, by decide⟩ ⟨11, 2, 0, 334645, 6587, 841, 262144⟩
    (by decide) selected_cut_12707

theorem unmarked_context_10_1646_334646 : frontier 11 ⟨334646, by decide⟩
    (prefixCache 10 1646) (prefixPartial 10 1646) = false := by
  decide +kernel

theorem node_context_10_1646_334646 : EJMOriginalGlobalDAGData.nodes 11 ⟨334646, by decide⟩ =
    .split (coordinate 10) (![⟨334605, by decide⟩,⟨334618, by decide⟩,⟨334632, by decide⟩,⟨334645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1646_334646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1646 ⟨334646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1646
    ⟨334646, by decide⟩ (by decide) (![⟨334605, by decide⟩,⟨334618, by decide⟩,⟨334632, by decide⟩,⟨334645, by decide⟩]) unmarked_context_10_1646_334646 node_context_10_1646_334646
  intro a
  fin_cases a
  · exact context_11_6584_334605
  · exact context_11_6585_334618
  · exact context_11_6586_334632
  · exact context_11_6587_334645

theorem selected_cut_12708 : selected 11 ⟨334666, by decide⟩
    (prefixPartial 10 1647) = some ⟨10, 2, 0, 334666, 1647, 1993, 1048576⟩ := by
  decide +kernel

theorem context_10_1647_334666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1647 ⟨334666, by decide⟩ :=
  accepted_of_selected 10 1647 ⟨334666, by decide⟩ ⟨10, 2, 0, 334666, 1647, 1993, 1048576⟩
    (by decide) selected_cut_12708

theorem unmarked_context_9_411_334667 : frontier 12 ⟨334667, by decide⟩
    (prefixCache 9 411) (prefixPartial 9 411) = false := by
  decide +kernel

theorem node_context_9_411_334667 : EJMOriginalGlobalDAGData.nodes 12 ⟨334667, by decide⟩ =
    .split (coordinate 9) (![⟨334495, by decide⟩,⟨334589, by decide⟩,⟨334646, by decide⟩,⟨334666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_411_334667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 411 ⟨334667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 411
    ⟨334667, by decide⟩ (by decide) (![⟨334495, by decide⟩,⟨334589, by decide⟩,⟨334646, by decide⟩,⟨334666, by decide⟩]) unmarked_context_9_411_334667 node_context_9_411_334667
  intro a
  fin_cases a
  · exact context_10_1644_334495
  · exact context_10_1645_334589
  · exact context_10_1646_334646
  · exact context_10_1647_334666

theorem unmarked_context_8_102_334668 : frontier 13 ⟨334668, by decide⟩
    (prefixCache 8 102) (prefixPartial 8 102) = false := by
  decide +kernel

theorem node_context_8_102_334668 : EJMOriginalGlobalDAGData.nodes 13 ⟨334668, by decide⟩ =
    .split (coordinate 8) (![⟨329595, by decide⟩,⟨333041, by decide⟩,⟨334349, by decide⟩,⟨334667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_102_334668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 102 ⟨334668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 102
    ⟨334668, by decide⟩ (by decide) (![⟨329595, by decide⟩,⟨333041, by decide⟩,⟨334349, by decide⟩,⟨334667, by decide⟩]) unmarked_context_8_102_334668 node_context_8_102_334668
  intro a
  fin_cases a
  · exact context_9_408_329595
  · exact context_9_409_333041
  · exact context_9_410_334349
  · exact context_9_411_334667

theorem selected_cut_12709 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26368) = some ⟨12, 1, 0, 34034, 26368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26368_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26368 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26368 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26368, 1, 65536⟩
    (by decide) selected_cut_12709

theorem selected_cut_12710 : selected 9 ⟨301653, by decide⟩
    (prefixPartial 12 26369) = some ⟨12, 1, 0, 301653, 26369, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26369_301653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26369 ⟨301653, by decide⟩ :=
  accepted_of_selected 12 26369 ⟨301653, by decide⟩ ⟨12, 1, 0, 301653, 26369, 1, 65536⟩
    (by decide) selected_cut_12710

theorem selected_cut_12711 : selected 8 ⟨334760, by decide⟩
    (prefixPartial 13 105480) = some ⟨13, 2, 0, 334760, 105480, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_105480_334760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105480 ⟨334760, by decide⟩ :=
  accepted_of_selected 13 105480 ⟨334760, by decide⟩ ⟨13, 2, 0, 334760, 105480, 3389, 16384⟩
    (by decide) selected_cut_12711

theorem selected_cut_12712 : selected 8 ⟨334848, by decide⟩
    (prefixPartial 13 105481) = some ⟨13, 2, 0, 334848, 105481, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_105481_334848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105481 ⟨334848, by decide⟩ :=
  accepted_of_selected 13 105481 ⟨334848, by decide⟩ ⟨13, 2, 0, 334848, 105481, 1945, 16384⟩
    (by decide) selected_cut_12712

theorem selected_cut_12713 : selected 8 ⟨334869, by decide⟩
    (prefixPartial 13 105482) = some ⟨13, 2, 0, 334869, 105482, 637, 16384⟩ := by
  decide +kernel

theorem context_13_105482_334869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105482 ⟨334869, by decide⟩ :=
  accepted_of_selected 13 105482 ⟨334869, by decide⟩ ⟨13, 2, 0, 334869, 105482, 637, 16384⟩
    (by decide) selected_cut_12713

theorem selected_cut_12714 : selected 8 ⟨334874, by decide⟩
    (prefixPartial 13 105483) = some ⟨13, 2, 0, 334874, 105483, 97, 16384⟩ := by
  decide +kernel

theorem context_13_105483_334874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105483 ⟨334874, by decide⟩ :=
  accepted_of_selected 13 105483 ⟨334874, by decide⟩ ⟨13, 2, 0, 334874, 105483, 97, 16384⟩
    (by decide) selected_cut_12714

theorem unmarked_context_12_26370_334875 : frontier 9 ⟨334875, by decide⟩
    (prefixCache 12 26370) (prefixPartial 12 26370) = false := by
  decide +kernel

theorem node_context_12_26370_334875 : EJMOriginalGlobalDAGData.nodes 9 ⟨334875, by decide⟩ =
    .split (coordinate 12) (![⟨334760, by decide⟩,⟨334848, by decide⟩,⟨334869, by decide⟩,⟨334874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26370_334875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26370 ⟨334875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26370
    ⟨334875, by decide⟩ (by decide) (![⟨334760, by decide⟩,⟨334848, by decide⟩,⟨334869, by decide⟩,⟨334874, by decide⟩]) unmarked_context_12_26370_334875 node_context_12_26370_334875
  intro a
  fin_cases a
  · exact context_13_105480_334760
  · exact context_13_105481_334848
  · exact context_13_105482_334869
  · exact context_13_105483_334874

theorem selected_cut_12715 : selected 9 ⟨334876, by decide⟩
    (prefixPartial 12 26371) = some ⟨12, 1, 0, 334876, 26371, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26371_334876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26371 ⟨334876, by decide⟩ :=
  accepted_of_selected 12 26371 ⟨334876, by decide⟩ ⟨12, 1, 0, 334876, 26371, 1, 65536⟩
    (by decide) selected_cut_12715

theorem unmarked_context_11_6592_334877 : frontier 10 ⟨334877, by decide⟩
    (prefixCache 11 6592) (prefixPartial 11 6592) = false := by
  decide +kernel

theorem node_context_11_6592_334877 : EJMOriginalGlobalDAGData.nodes 10 ⟨334877, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨334875, by decide⟩,⟨334876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6592_334877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6592 ⟨334877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6592
    ⟨334877, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨334875, by decide⟩,⟨334876, by decide⟩]) unmarked_context_11_6592_334877 node_context_11_6592_334877
  intro a
  fin_cases a
  · exact context_12_26368_34034
  · exact context_12_26369_301653
  · exact context_12_26370_334875
  · exact context_12_26371_334876

theorem selected_cut_12716 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26372) = some ⟨12, 1, 0, 34034, 26372, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26372_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26372 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26372 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26372, 1, 65536⟩
    (by decide) selected_cut_12716

theorem selected_cut_12717 : selected 8 ⟨334937, by decide⟩
    (prefixPartial 13 105492) = some ⟨13, 2, 0, 334937, 105492, 3757, 16384⟩ := by
  decide +kernel

theorem context_13_105492_334937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105492 ⟨334937, by decide⟩ :=
  accepted_of_selected 13 105492 ⟨334937, by decide⟩ ⟨13, 2, 0, 334937, 105492, 3757, 16384⟩
    (by decide) selected_cut_12717

theorem selected_cut_12718 : selected 8 ⟨335033, by decide⟩
    (prefixPartial 13 105493) = some ⟨13, 2, 0, 335033, 105493, 3873, 16384⟩ := by
  decide +kernel

theorem context_13_105493_335033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105493 ⟨335033, by decide⟩ :=
  accepted_of_selected 13 105493 ⟨335033, by decide⟩ ⟨13, 2, 0, 335033, 105493, 3873, 16384⟩
    (by decide) selected_cut_12718

theorem selected_cut_12719 : selected 8 ⟨335082, by decide⟩
    (prefixPartial 13 105494) = some ⟨13, 2, 0, 335082, 105494, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_105494_335082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105494 ⟨335082, by decide⟩ :=
  accepted_of_selected 13 105494 ⟨335082, by decide⟩ ⟨13, 2, 0, 335082, 105494, 2509, 16384⟩
    (by decide) selected_cut_12719

theorem selected_cut_12720 : selected 8 ⟨335094, by decide⟩
    (prefixPartial 13 105495) = some ⟨13, 2, 0, 335094, 105495, 837, 16384⟩ := by
  decide +kernel

theorem context_13_105495_335094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105495 ⟨335094, by decide⟩ :=
  accepted_of_selected 13 105495 ⟨335094, by decide⟩ ⟨13, 2, 0, 335094, 105495, 837, 16384⟩
    (by decide) selected_cut_12720

theorem unmarked_context_12_26373_335095 : frontier 9 ⟨335095, by decide⟩
    (prefixCache 12 26373) (prefixPartial 12 26373) = false := by
  decide +kernel

theorem node_context_12_26373_335095 : EJMOriginalGlobalDAGData.nodes 9 ⟨335095, by decide⟩ =
    .split (coordinate 12) (![⟨334937, by decide⟩,⟨335033, by decide⟩,⟨335082, by decide⟩,⟨335094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26373_335095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26373 ⟨335095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26373
    ⟨335095, by decide⟩ (by decide) (![⟨334937, by decide⟩,⟨335033, by decide⟩,⟨335082, by decide⟩,⟨335094, by decide⟩]) unmarked_context_12_26373_335095 node_context_12_26373_335095
  intro a
  fin_cases a
  · exact context_13_105492_334937
  · exact context_13_105493_335033
  · exact context_13_105494_335082
  · exact context_13_105495_335094

theorem selected_cut_12721 : selected 8 ⟨335145, by decide⟩
    (prefixPartial 13 105496) = some ⟨13, 2, 0, 335145, 105496, 3325, 16384⟩ := by
  decide +kernel

theorem context_13_105496_335145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105496 ⟨335145, by decide⟩ :=
  accepted_of_selected 13 105496 ⟨335145, by decide⟩ ⟨13, 2, 0, 335145, 105496, 3325, 16384⟩
    (by decide) selected_cut_12721

theorem selected_cut_12722 : selected 8 ⟨335227, by decide⟩
    (prefixPartial 13 105497) = some ⟨13, 2, 0, 335227, 105497, 3917, 16384⟩ := by
  decide +kernel

theorem context_13_105497_335227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105497 ⟨335227, by decide⟩ :=
  accepted_of_selected 13 105497 ⟨335227, by decide⟩ ⟨13, 2, 0, 335227, 105497, 3917, 16384⟩
    (by decide) selected_cut_12722

theorem selected_cut_12723 : selected 8 ⟨335271, by decide⟩
    (prefixPartial 13 105498) = some ⟨13, 2, 0, 335271, 105498, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_105498_335271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105498 ⟨335271, by decide⟩ :=
  accepted_of_selected 13 105498 ⟨335271, by decide⟩ ⟨13, 2, 0, 335271, 105498, 2397, 16384⟩
    (by decide) selected_cut_12723

theorem selected_cut_12724 : selected 8 ⟨335288, by decide⟩
    (prefixPartial 13 105499) = some ⟨13, 2, 0, 335288, 105499, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_105499_335288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105499 ⟨335288, by decide⟩ :=
  accepted_of_selected 13 105499 ⟨335288, by decide⟩ ⟨13, 2, 0, 335288, 105499, 1061, 16384⟩
    (by decide) selected_cut_12724

theorem unmarked_context_12_26374_335289 : frontier 9 ⟨335289, by decide⟩
    (prefixCache 12 26374) (prefixPartial 12 26374) = false := by
  decide +kernel

theorem node_context_12_26374_335289 : EJMOriginalGlobalDAGData.nodes 9 ⟨335289, by decide⟩ =
    .split (coordinate 12) (![⟨335145, by decide⟩,⟨335227, by decide⟩,⟨335271, by decide⟩,⟨335288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26374_335289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26374 ⟨335289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26374
    ⟨335289, by decide⟩ (by decide) (![⟨335145, by decide⟩,⟨335227, by decide⟩,⟨335271, by decide⟩,⟨335288, by decide⟩]) unmarked_context_12_26374_335289 node_context_12_26374_335289
  intro a
  fin_cases a
  · exact context_13_105496_335145
  · exact context_13_105497_335227
  · exact context_13_105498_335271
  · exact context_13_105499_335288

theorem selected_cut_12725 : selected 8 ⟨335331, by decide⟩
    (prefixPartial 13 105500) = some ⟨13, 2, 0, 335331, 105500, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_105500_335331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105500 ⟨335331, by decide⟩ :=
  accepted_of_selected 13 105500 ⟨335331, by decide⟩ ⟨13, 2, 0, 335331, 105500, 3229, 16384⟩
    (by decide) selected_cut_12725

theorem selected_cut_12726 : selected 8 ⟨335403, by decide⟩
    (prefixPartial 13 105501) = some ⟨13, 2, 0, 335403, 105501, 3957, 16384⟩ := by
  decide +kernel

theorem context_13_105501_335403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105501 ⟨335403, by decide⟩ :=
  accepted_of_selected 13 105501 ⟨335403, by decide⟩ ⟨13, 2, 0, 335403, 105501, 3957, 16384⟩
    (by decide) selected_cut_12726

theorem selected_cut_12727 : selected 8 ⟨335447, by decide⟩
    (prefixPartial 13 105502) = some ⟨13, 2, 0, 335447, 105502, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_105502_335447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105502 ⟨335447, by decide⟩ :=
  accepted_of_selected 13 105502 ⟨335447, by decide⟩ ⟨13, 2, 0, 335447, 105502, 2545, 16384⟩
    (by decide) selected_cut_12727

theorem selected_cut_12728 : selected 8 ⟨335459, by decide⟩
    (prefixPartial 13 105503) = some ⟨13, 2, 0, 335459, 105503, 929, 16384⟩ := by
  decide +kernel

theorem context_13_105503_335459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105503 ⟨335459, by decide⟩ :=
  accepted_of_selected 13 105503 ⟨335459, by decide⟩ ⟨13, 2, 0, 335459, 105503, 929, 16384⟩
    (by decide) selected_cut_12728

theorem unmarked_context_12_26375_335460 : frontier 9 ⟨335460, by decide⟩
    (prefixCache 12 26375) (prefixPartial 12 26375) = false := by
  decide +kernel

theorem node_context_12_26375_335460 : EJMOriginalGlobalDAGData.nodes 9 ⟨335460, by decide⟩ =
    .split (coordinate 12) (![⟨335331, by decide⟩,⟨335403, by decide⟩,⟨335447, by decide⟩,⟨335459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26375_335460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26375 ⟨335460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26375
    ⟨335460, by decide⟩ (by decide) (![⟨335331, by decide⟩,⟨335403, by decide⟩,⟨335447, by decide⟩,⟨335459, by decide⟩]) unmarked_context_12_26375_335460 node_context_12_26375_335460
  intro a
  fin_cases a
  · exact context_13_105500_335331
  · exact context_13_105501_335403
  · exact context_13_105502_335447
  · exact context_13_105503_335459

theorem unmarked_context_11_6593_335461 : frontier 10 ⟨335461, by decide⟩
    (prefixCache 11 6593) (prefixPartial 11 6593) = false := by
  decide +kernel

theorem node_context_11_6593_335461 : EJMOriginalGlobalDAGData.nodes 10 ⟨335461, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨335095, by decide⟩,⟨335289, by decide⟩,⟨335460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6593_335461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6593 ⟨335461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6593
    ⟨335461, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨335095, by decide⟩,⟨335289, by decide⟩,⟨335460, by decide⟩]) unmarked_context_11_6593_335461 node_context_11_6593_335461
  intro a
  fin_cases a
  · exact context_12_26372_34034
  · exact context_12_26373_335095
  · exact context_12_26374_335289
  · exact context_12_26375_335460

theorem selected_cut_12729 : selected 8 ⟨335517, by decide⟩
    (prefixPartial 13 105504) = some ⟨13, 2, 0, 335517, 105504, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_105504_335517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105504 ⟨335517, by decide⟩ :=
  accepted_of_selected 13 105504 ⟨335517, by decide⟩ ⟨13, 2, 0, 335517, 105504, 2933, 16384⟩
    (by decide) selected_cut_12729

theorem selected_cut_12730 : selected 8 ⟨335600, by decide⟩
    (prefixPartial 13 105505) = some ⟨13, 2, 0, 335600, 105505, 3921, 16384⟩ := by
  decide +kernel

theorem context_13_105505_335600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105505 ⟨335600, by decide⟩ :=
  accepted_of_selected 13 105505 ⟨335600, by decide⟩ ⟨13, 2, 0, 335600, 105505, 3921, 16384⟩
    (by decide) selected_cut_12730

theorem selected_cut_12731 : selected 8 ⟨335650, by decide⟩
    (prefixPartial 13 105506) = some ⟨13, 2, 0, 335650, 105506, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_105506_335650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105506 ⟨335650, by decide⟩ :=
  accepted_of_selected 13 105506 ⟨335650, by decide⟩ ⟨13, 2, 0, 335650, 105506, 2581, 16384⟩
    (by decide) selected_cut_12731

theorem selected_cut_12732 : selected 8 ⟨335677, by decide⟩
    (prefixPartial 13 105507) = some ⟨13, 2, 0, 335677, 105507, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_105507_335677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105507 ⟨335677, by decide⟩ :=
  accepted_of_selected 13 105507 ⟨335677, by decide⟩ ⟨13, 2, 0, 335677, 105507, 1125, 16384⟩
    (by decide) selected_cut_12732

theorem unmarked_context_12_26376_335678 : frontier 9 ⟨335678, by decide⟩
    (prefixCache 12 26376) (prefixPartial 12 26376) = false := by
  decide +kernel

theorem node_context_12_26376_335678 : EJMOriginalGlobalDAGData.nodes 9 ⟨335678, by decide⟩ =
    .split (coordinate 12) (![⟨335517, by decide⟩,⟨335600, by decide⟩,⟨335650, by decide⟩,⟨335677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26376_335678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26376 ⟨335678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26376
    ⟨335678, by decide⟩ (by decide) (![⟨335517, by decide⟩,⟨335600, by decide⟩,⟨335650, by decide⟩,⟨335677, by decide⟩]) unmarked_context_12_26376_335678 node_context_12_26376_335678
  intro a
  fin_cases a
  · exact context_13_105504_335517
  · exact context_13_105505_335600
  · exact context_13_105506_335650
  · exact context_13_105507_335677

theorem selected_cut_12733 : selected 8 ⟨335753, by decide⟩
    (prefixPartial 13 105508) = some ⟨13, 2, 0, 335753, 105508, 4045, 16384⟩ := by
  decide +kernel

theorem context_13_105508_335753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105508 ⟨335753, by decide⟩ :=
  accepted_of_selected 13 105508 ⟨335753, by decide⟩ ⟨13, 2, 0, 335753, 105508, 4045, 16384⟩
    (by decide) selected_cut_12733

theorem selected_cut_12734 : selected 7 ⟨335784, by decide⟩
    (prefixPartial 14 422036) = some ⟨14, 2, 0, 335784, 422036, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_422036_335784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422036 ⟨335784, by decide⟩ :=
  accepted_of_selected 14 422036 ⟨335784, by decide⟩ ⟨14, 2, 0, 335784, 422036, 1385, 4096⟩
    (by decide) selected_cut_12734

theorem selected_cut_12735 : selected 7 ⟨335811, by decide⟩
    (prefixPartial 14 422037) = some ⟨14, 2, 0, 335811, 422037, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_422037_335811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422037 ⟨335811, by decide⟩ :=
  accepted_of_selected 14 422037 ⟨335811, by decide⟩ ⟨14, 2, 0, 335811, 422037, 1061, 4096⟩
    (by decide) selected_cut_12735

theorem selected_cut_12736 : selected 7 ⟨335836, by decide⟩
    (prefixPartial 14 422038) = some ⟨14, 2, 0, 335836, 422038, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_422038_335836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422038 ⟨335836, by decide⟩ :=
  accepted_of_selected 14 422038 ⟨335836, by decide⟩ ⟨14, 2, 0, 335836, 422038, 1069, 4096⟩
    (by decide) selected_cut_12736

theorem selected_cut_12737 : selected 7 ⟨335858, by decide⟩
    (prefixPartial 14 422039) = some ⟨14, 2, 0, 335858, 422039, 753, 4096⟩ := by
  decide +kernel

theorem context_14_422039_335858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422039 ⟨335858, by decide⟩ :=
  accepted_of_selected 14 422039 ⟨335858, by decide⟩ ⟨14, 2, 0, 335858, 422039, 753, 4096⟩
    (by decide) selected_cut_12737

theorem unmarked_context_13_105509_335859 : frontier 8 ⟨335859, by decide⟩
    (prefixCache 13 105509) (prefixPartial 13 105509) = false := by
  decide +kernel

theorem node_context_13_105509_335859 : EJMOriginalGlobalDAGData.nodes 8 ⟨335859, by decide⟩ =
    .split (coordinate 13) (![⟨335784, by decide⟩,⟨335811, by decide⟩,⟨335836, by decide⟩,⟨335858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_105509_335859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105509 ⟨335859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 105509
    ⟨335859, by decide⟩ (by decide) (![⟨335784, by decide⟩,⟨335811, by decide⟩,⟨335836, by decide⟩,⟨335858, by decide⟩]) unmarked_context_13_105509_335859 node_context_13_105509_335859
  intro a
  fin_cases a
  · exact context_14_422036_335784
  · exact context_14_422037_335811
  · exact context_14_422038_335836
  · exact context_14_422039_335858

theorem selected_cut_12738 : selected 8 ⟨335895, by decide⟩
    (prefixPartial 13 105510) = some ⟨13, 2, 0, 335895, 105510, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_105510_335895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105510 ⟨335895, by decide⟩ :=
  accepted_of_selected 13 105510 ⟨335895, by decide⟩ ⟨13, 2, 0, 335895, 105510, 2573, 16384⟩
    (by decide) selected_cut_12738

theorem selected_cut_12739 : selected 8 ⟨335912, by decide⟩
    (prefixPartial 13 105511) = some ⟨13, 2, 0, 335912, 105511, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_105511_335912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105511 ⟨335912, by decide⟩ :=
  accepted_of_selected 13 105511 ⟨335912, by decide⟩ ⟨13, 2, 0, 335912, 105511, 1045, 16384⟩
    (by decide) selected_cut_12739

theorem unmarked_context_12_26377_335913 : frontier 9 ⟨335913, by decide⟩
    (prefixCache 12 26377) (prefixPartial 12 26377) = false := by
  decide +kernel

theorem node_context_12_26377_335913 : EJMOriginalGlobalDAGData.nodes 9 ⟨335913, by decide⟩ =
    .split (coordinate 12) (![⟨335753, by decide⟩,⟨335859, by decide⟩,⟨335895, by decide⟩,⟨335912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26377_335913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26377 ⟨335913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26377
    ⟨335913, by decide⟩ (by decide) (![⟨335753, by decide⟩,⟨335859, by decide⟩,⟨335895, by decide⟩,⟨335912, by decide⟩]) unmarked_context_12_26377_335913 node_context_12_26377_335913
  intro a
  fin_cases a
  · exact context_13_105508_335753
  · exact context_13_105509_335859
  · exact context_13_105510_335895
  · exact context_13_105511_335912

theorem selected_cut_12740 : selected 8 ⟨335979, by decide⟩
    (prefixPartial 13 105512) = some ⟨13, 2, 0, 335979, 105512, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_105512_335979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105512 ⟨335979, by decide⟩ :=
  accepted_of_selected 13 105512 ⟨335979, by decide⟩ ⟨13, 2, 0, 335979, 105512, 3425, 16384⟩
    (by decide) selected_cut_12740

theorem selected_cut_12741 : selected 8 ⟨336067, by decide⟩
    (prefixPartial 13 105513) = some ⟨13, 2, 0, 336067, 105513, 4033, 16384⟩ := by
  decide +kernel

theorem context_13_105513_336067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105513 ⟨336067, by decide⟩ :=
  accepted_of_selected 13 105513 ⟨336067, by decide⟩ ⟨13, 2, 0, 336067, 105513, 4033, 16384⟩
    (by decide) selected_cut_12741

theorem selected_cut_12742 : selected 8 ⟨336105, by decide⟩
    (prefixPartial 13 105514) = some ⟨13, 2, 0, 336105, 105514, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_105514_336105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105514 ⟨336105, by decide⟩ :=
  accepted_of_selected 13 105514 ⟨336105, by decide⟩ ⟨13, 2, 0, 336105, 105514, 2473, 16384⟩
    (by decide) selected_cut_12742

theorem selected_cut_12743 : selected 8 ⟨336120, by decide⟩
    (prefixPartial 13 105515) = some ⟨13, 2, 0, 336120, 105515, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_105515_336120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105515 ⟨336120, by decide⟩ :=
  accepted_of_selected 13 105515 ⟨336120, by decide⟩ ⟨13, 2, 0, 336120, 105515, 1021, 16384⟩
    (by decide) selected_cut_12743

theorem unmarked_context_12_26378_336121 : frontier 9 ⟨336121, by decide⟩
    (prefixCache 12 26378) (prefixPartial 12 26378) = false := by
  decide +kernel

theorem node_context_12_26378_336121 : EJMOriginalGlobalDAGData.nodes 9 ⟨336121, by decide⟩ =
    .split (coordinate 12) (![⟨335979, by decide⟩,⟨336067, by decide⟩,⟨336105, by decide⟩,⟨336120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26378_336121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26378 ⟨336121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26378
    ⟨336121, by decide⟩ (by decide) (![⟨335979, by decide⟩,⟨336067, by decide⟩,⟨336105, by decide⟩,⟨336120, by decide⟩]) unmarked_context_12_26378_336121 node_context_12_26378_336121
  intro a
  fin_cases a
  · exact context_13_105512_335979
  · exact context_13_105513_336067
  · exact context_13_105514_336105
  · exact context_13_105515_336120

theorem selected_cut_12744 : selected 8 ⟨336181, by decide⟩
    (prefixPartial 13 105516) = some ⟨13, 2, 0, 336181, 105516, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_105516_336181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105516 ⟨336181, by decide⟩ :=
  accepted_of_selected 13 105516 ⟨336181, by decide⟩ ⟨13, 2, 0, 336181, 105516, 3225, 16384⟩
    (by decide) selected_cut_12744

theorem selected_cut_12745 : selected 7 ⟨336209, by decide⟩
    (prefixPartial 14 422068) = some ⟨14, 2, 0, 336209, 422068, 1493, 4096⟩ := by
  decide +kernel

theorem context_14_422068_336209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422068 ⟨336209, by decide⟩ :=
  accepted_of_selected 14 422068 ⟨336209, by decide⟩ ⟨14, 2, 0, 336209, 422068, 1493, 4096⟩
    (by decide) selected_cut_12745

theorem selected_cut_12746 : selected 7 ⟨336226, by decide⟩
    (prefixPartial 14 422069) = some ⟨14, 2, 0, 336226, 422069, 965, 4096⟩ := by
  decide +kernel

theorem context_14_422069_336226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422069 ⟨336226, by decide⟩ :=
  accepted_of_selected 14 422069 ⟨336226, by decide⟩ ⟨14, 2, 0, 336226, 422069, 965, 4096⟩
    (by decide) selected_cut_12746

theorem selected_cut_12747 : selected 7 ⟨336250, by decide⟩
    (prefixPartial 14 422070) = some ⟨14, 2, 0, 336250, 422070, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_422070_336250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422070 ⟨336250, by decide⟩ :=
  accepted_of_selected 14 422070 ⟨336250, by decide⟩ ⟨14, 2, 0, 336250, 422070, 1145, 4096⟩
    (by decide) selected_cut_12747

theorem selected_cut_12748 : selected 7 ⟨336263, by decide⟩
    (prefixPartial 14 422071) = some ⟨14, 2, 0, 336263, 422071, 841, 4096⟩ := by
  decide +kernel

theorem context_14_422071_336263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422071 ⟨336263, by decide⟩ :=
  accepted_of_selected 14 422071 ⟨336263, by decide⟩ ⟨14, 2, 0, 336263, 422071, 841, 4096⟩
    (by decide) selected_cut_12748

theorem unmarked_context_13_105517_336264 : frontier 8 ⟨336264, by decide⟩
    (prefixCache 13 105517) (prefixPartial 13 105517) = false := by
  decide +kernel

theorem node_context_13_105517_336264 : EJMOriginalGlobalDAGData.nodes 8 ⟨336264, by decide⟩ =
    .split (coordinate 13) (![⟨336209, by decide⟩,⟨336226, by decide⟩,⟨336250, by decide⟩,⟨336263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_105517_336264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105517 ⟨336264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 105517
    ⟨336264, by decide⟩ (by decide) (![⟨336209, by decide⟩,⟨336226, by decide⟩,⟨336250, by decide⟩,⟨336263, by decide⟩]) unmarked_context_13_105517_336264 node_context_13_105517_336264
  intro a
  fin_cases a
  · exact context_14_422068_336209
  · exact context_14_422069_336226
  · exact context_14_422070_336250
  · exact context_14_422071_336263

theorem selected_cut_12749 : selected 8 ⟨336297, by decide⟩
    (prefixPartial 13 105518) = some ⟨13, 2, 0, 336297, 105518, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_105518_336297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105518 ⟨336297, by decide⟩ :=
  accepted_of_selected 13 105518 ⟨336297, by decide⟩ ⟨13, 2, 0, 336297, 105518, 2313, 16384⟩
    (by decide) selected_cut_12749

theorem selected_cut_12750 : selected 8 ⟨336305, by decide⟩
    (prefixPartial 13 105519) = some ⟨13, 2, 0, 336305, 105519, 889, 16384⟩ := by
  decide +kernel

theorem context_13_105519_336305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105519 ⟨336305, by decide⟩ :=
  accepted_of_selected 13 105519 ⟨336305, by decide⟩ ⟨13, 2, 0, 336305, 105519, 889, 16384⟩
    (by decide) selected_cut_12750

theorem unmarked_context_12_26379_336306 : frontier 9 ⟨336306, by decide⟩
    (prefixCache 12 26379) (prefixPartial 12 26379) = false := by
  decide +kernel

theorem node_context_12_26379_336306 : EJMOriginalGlobalDAGData.nodes 9 ⟨336306, by decide⟩ =
    .split (coordinate 12) (![⟨336181, by decide⟩,⟨336264, by decide⟩,⟨336297, by decide⟩,⟨336305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26379_336306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26379 ⟨336306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26379
    ⟨336306, by decide⟩ (by decide) (![⟨336181, by decide⟩,⟨336264, by decide⟩,⟨336297, by decide⟩,⟨336305, by decide⟩]) unmarked_context_12_26379_336306 node_context_12_26379_336306
  intro a
  fin_cases a
  · exact context_13_105516_336181
  · exact context_13_105517_336264
  · exact context_13_105518_336297
  · exact context_13_105519_336305

theorem unmarked_context_11_6594_336307 : frontier 10 ⟨336307, by decide⟩
    (prefixCache 11 6594) (prefixPartial 11 6594) = false := by
  decide +kernel

theorem node_context_11_6594_336307 : EJMOriginalGlobalDAGData.nodes 10 ⟨336307, by decide⟩ =
    .split (coordinate 11) (![⟨335678, by decide⟩,⟨335913, by decide⟩,⟨336121, by decide⟩,⟨336306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6594_336307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6594 ⟨336307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6594
    ⟨336307, by decide⟩ (by decide) (![⟨335678, by decide⟩,⟨335913, by decide⟩,⟨336121, by decide⟩,⟨336306, by decide⟩]) unmarked_context_11_6594_336307 node_context_11_6594_336307
  intro a
  fin_cases a
  · exact context_12_26376_335678
  · exact context_12_26377_335913
  · exact context_12_26378_336121
  · exact context_12_26379_336306

theorem selected_cut_12751 : selected 9 ⟨292651, by decide⟩
    (prefixPartial 12 26380) = some ⟨12, 1, 0, 292651, 26380, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26380_292651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26380 ⟨292651, by decide⟩ :=
  accepted_of_selected 12 26380 ⟨292651, by decide⟩ ⟨12, 1, 0, 292651, 26380, 1, 65536⟩
    (by decide) selected_cut_12751

theorem selected_cut_12752 : selected 8 ⟨336356, by decide⟩
    (prefixPartial 13 105524) = some ⟨13, 2, 0, 336356, 105524, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_105524_336356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105524 ⟨336356, by decide⟩ :=
  accepted_of_selected 13 105524 ⟨336356, by decide⟩ ⟨13, 2, 0, 336356, 105524, 3229, 16384⟩
    (by decide) selected_cut_12752

theorem selected_cut_12753 : selected 8 ⟨336426, by decide⟩
    (prefixPartial 13 105525) = some ⟨13, 2, 0, 336426, 105525, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_105525_336426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105525 ⟨336426, by decide⟩ :=
  accepted_of_selected 13 105525 ⟨336426, by decide⟩ ⟨13, 2, 0, 336426, 105525, 3457, 16384⟩
    (by decide) selected_cut_12753

theorem selected_cut_12754 : selected 8 ⟨336471, by decide⟩
    (prefixPartial 13 105526) = some ⟨13, 2, 0, 336471, 105526, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_105526_336471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105526 ⟨336471, by decide⟩ :=
  accepted_of_selected 13 105526 ⟨336471, by decide⟩ ⟨13, 2, 0, 336471, 105526, 2497, 16384⟩
    (by decide) selected_cut_12754

theorem selected_cut_12755 : selected 8 ⟨336483, by decide⟩
    (prefixPartial 13 105527) = some ⟨13, 2, 0, 336483, 105527, 753, 16384⟩ := by
  decide +kernel

theorem context_13_105527_336483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105527 ⟨336483, by decide⟩ :=
  accepted_of_selected 13 105527 ⟨336483, by decide⟩ ⟨13, 2, 0, 336483, 105527, 753, 16384⟩
    (by decide) selected_cut_12755

theorem unmarked_context_12_26381_336484 : frontier 9 ⟨336484, by decide⟩
    (prefixCache 12 26381) (prefixPartial 12 26381) = false := by
  decide +kernel

theorem node_context_12_26381_336484 : EJMOriginalGlobalDAGData.nodes 9 ⟨336484, by decide⟩ =
    .split (coordinate 12) (![⟨336356, by decide⟩,⟨336426, by decide⟩,⟨336471, by decide⟩,⟨336483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26381_336484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26381 ⟨336484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26381
    ⟨336484, by decide⟩ (by decide) (![⟨336356, by decide⟩,⟨336426, by decide⟩,⟨336471, by decide⟩,⟨336483, by decide⟩]) unmarked_context_12_26381_336484 node_context_12_26381_336484
  intro a
  fin_cases a
  · exact context_13_105524_336356
  · exact context_13_105525_336426
  · exact context_13_105526_336471
  · exact context_13_105527_336483

theorem selected_cut_12756 : selected 8 ⟨336536, by decide⟩
    (prefixPartial 13 105528) = some ⟨13, 2, 0, 336536, 105528, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_105528_336536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105528 ⟨336536, by decide⟩ :=
  accepted_of_selected 13 105528 ⟨336536, by decide⟩ ⟨13, 2, 0, 336536, 105528, 2997, 16384⟩
    (by decide) selected_cut_12756

theorem selected_cut_12757 : selected 8 ⟨336601, by decide⟩
    (prefixPartial 13 105529) = some ⟨13, 2, 0, 336601, 105529, 3569, 16384⟩ := by
  decide +kernel

theorem context_13_105529_336601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105529 ⟨336601, by decide⟩ :=
  accepted_of_selected 13 105529 ⟨336601, by decide⟩ ⟨13, 2, 0, 336601, 105529, 3569, 16384⟩
    (by decide) selected_cut_12757

theorem selected_cut_12758 : selected 8 ⟨336631, by decide⟩
    (prefixPartial 13 105530) = some ⟨13, 2, 0, 336631, 105530, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_105530_336631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105530 ⟨336631, by decide⟩ :=
  accepted_of_selected 13 105530 ⟨336631, by decide⟩ ⟨13, 2, 0, 336631, 105530, 2093, 16384⟩
    (by decide) selected_cut_12758

theorem selected_cut_12759 : selected 8 ⟨336643, by decide⟩
    (prefixPartial 13 105531) = some ⟨13, 2, 0, 336643, 105531, 857, 16384⟩ := by
  decide +kernel

theorem context_13_105531_336643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105531 ⟨336643, by decide⟩ :=
  accepted_of_selected 13 105531 ⟨336643, by decide⟩ ⟨13, 2, 0, 336643, 105531, 857, 16384⟩
    (by decide) selected_cut_12759

theorem unmarked_context_12_26382_336644 : frontier 9 ⟨336644, by decide⟩
    (prefixCache 12 26382) (prefixPartial 12 26382) = false := by
  decide +kernel

theorem node_context_12_26382_336644 : EJMOriginalGlobalDAGData.nodes 9 ⟨336644, by decide⟩ =
    .split (coordinate 12) (![⟨336536, by decide⟩,⟨336601, by decide⟩,⟨336631, by decide⟩,⟨336643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26382_336644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26382 ⟨336644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26382
    ⟨336644, by decide⟩ (by decide) (![⟨336536, by decide⟩,⟨336601, by decide⟩,⟨336631, by decide⟩,⟨336643, by decide⟩]) unmarked_context_12_26382_336644 node_context_12_26382_336644
  intro a
  fin_cases a
  · exact context_13_105528_336536
  · exact context_13_105529_336601
  · exact context_13_105530_336631
  · exact context_13_105531_336643

theorem selected_cut_12760 : selected 7 ⟨336650, by decide⟩
    (prefixPartial 14 422128) = some ⟨14, 2, 0, 336650, 422128, 297, 4096⟩ := by
  decide +kernel

theorem context_14_422128_336650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422128 ⟨336650, by decide⟩ :=
  accepted_of_selected 14 422128 ⟨336650, by decide⟩ ⟨14, 2, 0, 336650, 422128, 297, 4096⟩
    (by decide) selected_cut_12760

theorem selected_cut_12761 : selected 7 ⟨336680, by decide⟩
    (prefixPartial 14 422129) = some ⟨14, 2, 0, 336680, 422129, 1781, 4096⟩ := by
  decide +kernel

theorem context_14_422129_336680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422129 ⟨336680, by decide⟩ :=
  accepted_of_selected 14 422129 ⟨336680, by decide⟩ ⟨14, 2, 0, 336680, 422129, 1781, 4096⟩
    (by decide) selected_cut_12761

theorem selected_cut_12762 : selected 7 ⟨336710, by decide⟩
    (prefixPartial 14 422130) = some ⟨14, 2, 0, 336710, 422130, 1381, 4096⟩ := by
  decide +kernel

theorem context_14_422130_336710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422130 ⟨336710, by decide⟩ :=
  accepted_of_selected 14 422130 ⟨336710, by decide⟩ ⟨14, 2, 0, 336710, 422130, 1381, 4096⟩
    (by decide) selected_cut_12762

theorem selected_cut_12763 : selected 7 ⟨336731, by decide⟩
    (prefixPartial 14 422131) = some ⟨14, 2, 0, 336731, 422131, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_422131_336731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422131 ⟨336731, by decide⟩ :=
  accepted_of_selected 14 422131 ⟨336731, by decide⟩ ⟨14, 2, 0, 336731, 422131, 1161, 4096⟩
    (by decide) selected_cut_12763

theorem unmarked_context_13_105532_336732 : frontier 8 ⟨336732, by decide⟩
    (prefixCache 13 105532) (prefixPartial 13 105532) = false := by
  decide +kernel

theorem node_context_13_105532_336732 : EJMOriginalGlobalDAGData.nodes 8 ⟨336732, by decide⟩ =
    .split (coordinate 13) (![⟨336650, by decide⟩,⟨336680, by decide⟩,⟨336710, by decide⟩,⟨336731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_105532_336732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105532 ⟨336732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 105532
    ⟨336732, by decide⟩ (by decide) (![⟨336650, by decide⟩,⟨336680, by decide⟩,⟨336710, by decide⟩,⟨336731, by decide⟩]) unmarked_context_13_105532_336732 node_context_13_105532_336732
  intro a
  fin_cases a
  · exact context_14_422128_336650
  · exact context_14_422129_336680
  · exact context_14_422130_336710
  · exact context_14_422131_336731

theorem selected_cut_12764 : selected 7 ⟨336775, by decide⟩
    (prefixPartial 14 422132) = some ⟨14, 2, 0, 336775, 422132, 1977, 4096⟩ := by
  decide +kernel

theorem context_14_422132_336775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422132 ⟨336775, by decide⟩ :=
  accepted_of_selected 14 422132 ⟨336775, by decide⟩ ⟨14, 2, 0, 336775, 422132, 1977, 4096⟩
    (by decide) selected_cut_12764

theorem selected_cut_12765 : selected 7 ⟨336807, by decide⟩
    (prefixPartial 14 422133) = some ⟨14, 2, 0, 336807, 422133, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_422133_336807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422133 ⟨336807, by decide⟩ :=
  accepted_of_selected 14 422133 ⟨336807, by decide⟩ ⟨14, 2, 0, 336807, 422133, 1357, 4096⟩
    (by decide) selected_cut_12765

theorem selected_cut_12766 : selected 7 ⟨336844, by decide⟩
    (prefixPartial 14 422134) = some ⟨14, 2, 0, 336844, 422134, 1529, 4096⟩ := by
  decide +kernel

theorem context_14_422134_336844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422134 ⟨336844, by decide⟩ :=
  accepted_of_selected 14 422134 ⟨336844, by decide⟩ ⟨14, 2, 0, 336844, 422134, 1529, 4096⟩
    (by decide) selected_cut_12766

theorem selected_cut_12767 : selected 7 ⟨336866, by decide⟩
    (prefixPartial 14 422135) = some ⟨14, 2, 0, 336866, 422135, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_422135_336866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 422135 ⟨336866, by decide⟩ :=
  accepted_of_selected 14 422135 ⟨336866, by decide⟩ ⟨14, 2, 0, 336866, 422135, 1121, 4096⟩
    (by decide) selected_cut_12767

theorem unmarked_context_13_105533_336867 : frontier 8 ⟨336867, by decide⟩
    (prefixCache 13 105533) (prefixPartial 13 105533) = false := by
  decide +kernel

theorem node_context_13_105533_336867 : EJMOriginalGlobalDAGData.nodes 8 ⟨336867, by decide⟩ =
    .split (coordinate 13) (![⟨336775, by decide⟩,⟨336807, by decide⟩,⟨336844, by decide⟩,⟨336866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_105533_336867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105533 ⟨336867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 105533
    ⟨336867, by decide⟩ (by decide) (![⟨336775, by decide⟩,⟨336807, by decide⟩,⟨336844, by decide⟩,⟨336866, by decide⟩]) unmarked_context_13_105533_336867 node_context_13_105533_336867
  intro a
  fin_cases a
  · exact context_14_422132_336775
  · exact context_14_422133_336807
  · exact context_14_422134_336844
  · exact context_14_422135_336866

theorem selected_cut_12768 : selected 8 ⟨336985, by decide⟩
    (prefixPartial 13 105534) = some ⟨13, 2, 0, 336985, 105534, 3717, 16384⟩ := by
  decide +kernel

theorem context_13_105534_336985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105534 ⟨336985, by decide⟩ :=
  accepted_of_selected 13 105534 ⟨336985, by decide⟩ ⟨13, 2, 0, 336985, 105534, 3717, 16384⟩
    (by decide) selected_cut_12768

theorem selected_cut_12769 : selected 8 ⟨337053, by decide⟩
    (prefixPartial 13 105535) = some ⟨13, 2, 0, 337053, 105535, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_105535_337053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105535 ⟨337053, by decide⟩ :=
  accepted_of_selected 13 105535 ⟨337053, by decide⟩ ⟨13, 2, 0, 337053, 105535, 1309, 16384⟩
    (by decide) selected_cut_12769

theorem unmarked_context_12_26383_337054 : frontier 9 ⟨337054, by decide⟩
    (prefixCache 12 26383) (prefixPartial 12 26383) = false := by
  decide +kernel

theorem node_context_12_26383_337054 : EJMOriginalGlobalDAGData.nodes 9 ⟨337054, by decide⟩ =
    .split (coordinate 12) (![⟨336732, by decide⟩,⟨336867, by decide⟩,⟨336985, by decide⟩,⟨337053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26383_337054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26383 ⟨337054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26383
    ⟨337054, by decide⟩ (by decide) (![⟨336732, by decide⟩,⟨336867, by decide⟩,⟨336985, by decide⟩,⟨337053, by decide⟩]) unmarked_context_12_26383_337054 node_context_12_26383_337054
  intro a
  fin_cases a
  · exact context_13_105532_336732
  · exact context_13_105533_336867
  · exact context_13_105534_336985
  · exact context_13_105535_337053

theorem unmarked_context_11_6595_337055 : frontier 10 ⟨337055, by decide⟩
    (prefixCache 11 6595) (prefixPartial 11 6595) = false := by
  decide +kernel

theorem node_context_11_6595_337055 : EJMOriginalGlobalDAGData.nodes 10 ⟨337055, by decide⟩ =
    .split (coordinate 11) (![⟨292651, by decide⟩,⟨336484, by decide⟩,⟨336644, by decide⟩,⟨337054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6595_337055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6595 ⟨337055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6595
    ⟨337055, by decide⟩ (by decide) (![⟨292651, by decide⟩,⟨336484, by decide⟩,⟨336644, by decide⟩,⟨337054, by decide⟩]) unmarked_context_11_6595_337055 node_context_11_6595_337055
  intro a
  fin_cases a
  · exact context_12_26380_292651
  · exact context_12_26381_336484
  · exact context_12_26382_336644
  · exact context_12_26383_337054

theorem unmarked_context_10_1648_337056 : frontier 11 ⟨337056, by decide⟩
    (prefixCache 10 1648) (prefixPartial 10 1648) = false := by
  decide +kernel

theorem node_context_10_1648_337056 : EJMOriginalGlobalDAGData.nodes 11 ⟨337056, by decide⟩ =
    .split (coordinate 10) (![⟨334877, by decide⟩,⟨335461, by decide⟩,⟨336307, by decide⟩,⟨337055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1648_337056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1648 ⟨337056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1648
    ⟨337056, by decide⟩ (by decide) (![⟨334877, by decide⟩,⟨335461, by decide⟩,⟨336307, by decide⟩,⟨337055, by decide⟩]) unmarked_context_10_1648_337056 node_context_10_1648_337056
  intro a
  fin_cases a
  · exact context_11_6592_334877
  · exact context_11_6593_335461
  · exact context_11_6594_336307
  · exact context_11_6595_337055

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
