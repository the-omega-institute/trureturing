/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover303
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29188 : selected 9 ⟨737497, by decide⟩
    (prefixPartial 12 93355) = some ⟨12, 2, 0, 737497, 93355, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_93355_737497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93355 ⟨737497, by decide⟩ :=
  accepted_of_selected 12 93355 ⟨737497, by decide⟩ ⟨12, 2, 0, 737497, 93355, 1605, 65536⟩
    (by decide) selected_cut_29188

theorem unmarked_context_11_23338_737498 : frontier 10 ⟨737498, by decide⟩
    (prefixCache 11 23338) (prefixPartial 11 23338) = false := by
  decide +kernel

theorem node_context_11_23338_737498 : EJMOriginalGlobalDAGData.nodes 10 ⟨737498, by decide⟩ =
    .split (coordinate 11) (![⟨737433, by decide⟩,⟨737453, by decide⟩,⟨737472, by decide⟩,⟨737497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23338_737498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23338 ⟨737498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23338
    ⟨737498, by decide⟩ (by decide) (![⟨737433, by decide⟩,⟨737453, by decide⟩,⟨737472, by decide⟩,⟨737497, by decide⟩]) unmarked_context_11_23338_737498 node_context_11_23338_737498
  intro a
  fin_cases a
  · exact context_12_93352_737433
  · exact context_12_93353_737453
  · exact context_12_93354_737472
  · exact context_12_93355_737497

theorem selected_cut_29189 : selected 9 ⟨737514, by decide⟩
    (prefixPartial 12 93356) = some ⟨12, 2, 0, 737514, 93356, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_93356_737514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93356 ⟨737514, by decide⟩ :=
  accepted_of_selected 12 93356 ⟨737514, by decide⟩ ⟨12, 2, 0, 737514, 93356, 1321, 65536⟩
    (by decide) selected_cut_29189

theorem selected_cut_29190 : selected 9 ⟨737534, by decide⟩
    (prefixPartial 12 93357) = some ⟨12, 2, 0, 737534, 93357, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_93357_737534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93357 ⟨737534, by decide⟩ :=
  accepted_of_selected 12 93357 ⟨737534, by decide⟩ ⟨12, 2, 0, 737534, 93357, 1237, 65536⟩
    (by decide) selected_cut_29190

theorem selected_cut_29191 : selected 9 ⟨737555, by decide⟩
    (prefixPartial 12 93358) = some ⟨12, 2, 0, 737555, 93358, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_93358_737555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93358 ⟨737555, by decide⟩ :=
  accepted_of_selected 12 93358 ⟨737555, by decide⟩ ⟨12, 2, 0, 737555, 93358, 1285, 65536⟩
    (by decide) selected_cut_29191

theorem selected_cut_29192 : selected 9 ⟨737572, by decide⟩
    (prefixPartial 12 93359) = some ⟨12, 2, 0, 737572, 93359, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_93359_737572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93359 ⟨737572, by decide⟩ :=
  accepted_of_selected 12 93359 ⟨737572, by decide⟩ ⟨12, 2, 0, 737572, 93359, 1301, 65536⟩
    (by decide) selected_cut_29192

theorem unmarked_context_11_23339_737573 : frontier 10 ⟨737573, by decide⟩
    (prefixCache 11 23339) (prefixPartial 11 23339) = false := by
  decide +kernel

theorem node_context_11_23339_737573 : EJMOriginalGlobalDAGData.nodes 10 ⟨737573, by decide⟩ =
    .split (coordinate 11) (![⟨737514, by decide⟩,⟨737534, by decide⟩,⟨737555, by decide⟩,⟨737572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23339_737573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23339 ⟨737573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23339
    ⟨737573, by decide⟩ (by decide) (![⟨737514, by decide⟩,⟨737534, by decide⟩,⟨737555, by decide⟩,⟨737572, by decide⟩]) unmarked_context_11_23339_737573 node_context_11_23339_737573
  intro a
  fin_cases a
  · exact context_12_93356_737514
  · exact context_12_93357_737534
  · exact context_12_93358_737555
  · exact context_12_93359_737572

theorem unmarked_context_10_5834_737574 : frontier 11 ⟨737574, by decide⟩
    (prefixCache 10 5834) (prefixPartial 10 5834) = false := by
  decide +kernel

theorem node_context_10_5834_737574 : EJMOriginalGlobalDAGData.nodes 11 ⟨737574, by decide⟩ =
    .split (coordinate 10) (![⟨737330, by decide⟩,⟨737419, by decide⟩,⟨737498, by decide⟩,⟨737573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5834_737574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5834 ⟨737574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5834
    ⟨737574, by decide⟩ (by decide) (![⟨737330, by decide⟩,⟨737419, by decide⟩,⟨737498, by decide⟩,⟨737573, by decide⟩]) unmarked_context_10_5834_737574 node_context_10_5834_737574
  intro a
  fin_cases a
  · exact context_11_23336_737330
  · exact context_11_23337_737419
  · exact context_11_23338_737498
  · exact context_11_23339_737573

theorem selected_cut_29193 : selected 9 ⟨737627, by decide⟩
    (prefixPartial 12 93360) = some ⟨12, 2, 0, 737627, 93360, 489, 65536⟩ := by
  decide +kernel

theorem context_12_93360_737627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93360 ⟨737627, by decide⟩ :=
  accepted_of_selected 12 93360 ⟨737627, by decide⟩ ⟨12, 2, 0, 737627, 93360, 489, 65536⟩
    (by decide) selected_cut_29193

theorem selected_cut_29194 : selected 9 ⟨737639, by decide⟩
    (prefixPartial 12 93361) = some ⟨12, 2, 0, 737639, 93361, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_93361_737639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93361 ⟨737639, by decide⟩ :=
  accepted_of_selected 12 93361 ⟨737639, by decide⟩ ⟨12, 2, 0, 737639, 93361, 1385, 65536⟩
    (by decide) selected_cut_29194

theorem selected_cut_29195 : selected 9 ⟨737649, by decide⟩
    (prefixPartial 12 93362) = some ⟨12, 2, 0, 737649, 93362, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_93362_737649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93362 ⟨737649, by decide⟩ :=
  accepted_of_selected 12 93362 ⟨737649, by decide⟩ ⟨12, 2, 0, 737649, 93362, 1269, 65536⟩
    (by decide) selected_cut_29195

theorem selected_cut_29196 : selected 9 ⟨737668, by decide⟩
    (prefixPartial 12 93363) = some ⟨12, 2, 0, 737668, 93363, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_93363_737668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93363 ⟨737668, by decide⟩ :=
  accepted_of_selected 12 93363 ⟨737668, by decide⟩ ⟨12, 2, 0, 737668, 93363, 1445, 65536⟩
    (by decide) selected_cut_29196

theorem unmarked_context_11_23340_737669 : frontier 10 ⟨737669, by decide⟩
    (prefixCache 11 23340) (prefixPartial 11 23340) = false := by
  decide +kernel

theorem node_context_11_23340_737669 : EJMOriginalGlobalDAGData.nodes 10 ⟨737669, by decide⟩ =
    .split (coordinate 11) (![⟨737627, by decide⟩,⟨737639, by decide⟩,⟨737649, by decide⟩,⟨737668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23340_737669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23340 ⟨737669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23340
    ⟨737669, by decide⟩ (by decide) (![⟨737627, by decide⟩,⟨737639, by decide⟩,⟨737649, by decide⟩,⟨737668, by decide⟩]) unmarked_context_11_23340_737669 node_context_11_23340_737669
  intro a
  fin_cases a
  · exact context_12_93360_737627
  · exact context_12_93361_737639
  · exact context_12_93362_737649
  · exact context_12_93363_737668

theorem selected_cut_29197 : selected 9 ⟨737685, by decide⟩
    (prefixPartial 12 93364) = some ⟨12, 2, 0, 737685, 93364, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_93364_737685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93364 ⟨737685, by decide⟩ :=
  accepted_of_selected 12 93364 ⟨737685, by decide⟩ ⟨12, 2, 0, 737685, 93364, 1305, 65536⟩
    (by decide) selected_cut_29197

theorem selected_cut_29198 : selected 9 ⟨737702, by decide⟩
    (prefixPartial 12 93365) = some ⟨12, 2, 0, 737702, 93365, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_93365_737702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93365 ⟨737702, by decide⟩ :=
  accepted_of_selected 12 93365 ⟨737702, by decide⟩ ⟨12, 2, 0, 737702, 93365, 1245, 65536⟩
    (by decide) selected_cut_29198

theorem selected_cut_29199 : selected 9 ⟨737720, by decide⟩
    (prefixPartial 12 93366) = some ⟨12, 2, 0, 737720, 93366, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_93366_737720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93366 ⟨737720, by decide⟩ :=
  accepted_of_selected 12 93366 ⟨737720, by decide⟩ ⟨12, 2, 0, 737720, 93366, 1161, 65536⟩
    (by decide) selected_cut_29199

theorem selected_cut_29200 : selected 9 ⟨737744, by decide⟩
    (prefixPartial 12 93367) = some ⟨12, 2, 0, 737744, 93367, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_93367_737744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93367 ⟨737744, by decide⟩ :=
  accepted_of_selected 12 93367 ⟨737744, by decide⟩ ⟨12, 2, 0, 737744, 93367, 1337, 65536⟩
    (by decide) selected_cut_29200

theorem unmarked_context_11_23341_737745 : frontier 10 ⟨737745, by decide⟩
    (prefixCache 11 23341) (prefixPartial 11 23341) = false := by
  decide +kernel

theorem node_context_11_23341_737745 : EJMOriginalGlobalDAGData.nodes 10 ⟨737745, by decide⟩ =
    .split (coordinate 11) (![⟨737685, by decide⟩,⟨737702, by decide⟩,⟨737720, by decide⟩,⟨737744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23341_737745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23341 ⟨737745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23341
    ⟨737745, by decide⟩ (by decide) (![⟨737685, by decide⟩,⟨737702, by decide⟩,⟨737720, by decide⟩,⟨737744, by decide⟩]) unmarked_context_11_23341_737745 node_context_11_23341_737745
  intro a
  fin_cases a
  · exact context_12_93364_737685
  · exact context_12_93365_737702
  · exact context_12_93366_737720
  · exact context_12_93367_737744

theorem selected_cut_29201 : selected 9 ⟨737765, by decide⟩
    (prefixPartial 12 93368) = some ⟨12, 2, 0, 737765, 93368, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_93368_737765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93368 ⟨737765, by decide⟩ :=
  accepted_of_selected 12 93368 ⟨737765, by decide⟩ ⟨12, 2, 0, 737765, 93368, 1297, 65536⟩
    (by decide) selected_cut_29201

theorem selected_cut_29202 : selected 9 ⟨737783, by decide⟩
    (prefixPartial 12 93369) = some ⟨12, 2, 0, 737783, 93369, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_93369_737783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93369 ⟨737783, by decide⟩ :=
  accepted_of_selected 12 93369 ⟨737783, by decide⟩ ⟨12, 2, 0, 737783, 93369, 1269, 65536⟩
    (by decide) selected_cut_29202

theorem selected_cut_29203 : selected 9 ⟨737797, by decide⟩
    (prefixPartial 12 93370) = some ⟨12, 2, 0, 737797, 93370, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_93370_737797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93370 ⟨737797, by decide⟩ :=
  accepted_of_selected 12 93370 ⟨737797, by decide⟩ ⟨12, 2, 0, 737797, 93370, 1053, 65536⟩
    (by decide) selected_cut_29203

theorem selected_cut_29204 : selected 9 ⟨737826, by decide⟩
    (prefixPartial 12 93371) = some ⟨12, 2, 0, 737826, 93371, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_93371_737826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93371 ⟨737826, by decide⟩ :=
  accepted_of_selected 12 93371 ⟨737826, by decide⟩ ⟨12, 2, 0, 737826, 93371, 1293, 65536⟩
    (by decide) selected_cut_29204

theorem unmarked_context_11_23342_737827 : frontier 10 ⟨737827, by decide⟩
    (prefixCache 11 23342) (prefixPartial 11 23342) = false := by
  decide +kernel

theorem node_context_11_23342_737827 : EJMOriginalGlobalDAGData.nodes 10 ⟨737827, by decide⟩ =
    .split (coordinate 11) (![⟨737765, by decide⟩,⟨737783, by decide⟩,⟨737797, by decide⟩,⟨737826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23342_737827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23342 ⟨737827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23342
    ⟨737827, by decide⟩ (by decide) (![⟨737765, by decide⟩,⟨737783, by decide⟩,⟨737797, by decide⟩,⟨737826, by decide⟩]) unmarked_context_11_23342_737827 node_context_11_23342_737827
  intro a
  fin_cases a
  · exact context_12_93368_737765
  · exact context_12_93369_737783
  · exact context_12_93370_737797
  · exact context_12_93371_737826

theorem selected_cut_29205 : selected 10 ⟨737849, by decide⟩
    (prefixPartial 11 23343) = some ⟨11, 2, 0, 737849, 23343, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_23343_737849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23343 ⟨737849, by decide⟩ :=
  accepted_of_selected 11 23343 ⟨737849, by decide⟩ ⟨11, 2, 0, 737849, 23343, 2329, 262144⟩
    (by decide) selected_cut_29205

theorem unmarked_context_10_5835_737850 : frontier 11 ⟨737850, by decide⟩
    (prefixCache 10 5835) (prefixPartial 10 5835) = false := by
  decide +kernel

theorem node_context_10_5835_737850 : EJMOriginalGlobalDAGData.nodes 11 ⟨737850, by decide⟩ =
    .split (coordinate 10) (![⟨737669, by decide⟩,⟨737745, by decide⟩,⟨737827, by decide⟩,⟨737849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5835_737850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5835 ⟨737850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5835
    ⟨737850, by decide⟩ (by decide) (![⟨737669, by decide⟩,⟨737745, by decide⟩,⟨737827, by decide⟩,⟨737849, by decide⟩]) unmarked_context_10_5835_737850 node_context_10_5835_737850
  intro a
  fin_cases a
  · exact context_11_23340_737669
  · exact context_11_23341_737745
  · exact context_11_23342_737827
  · exact context_11_23343_737849

theorem unmarked_context_9_1458_737851 : frontier 12 ⟨737851, by decide⟩
    (prefixCache 9 1458) (prefixPartial 9 1458) = false := by
  decide +kernel

theorem node_context_9_1458_737851 : EJMOriginalGlobalDAGData.nodes 12 ⟨737851, by decide⟩ =
    .split (coordinate 9) (![⟨736565, by decide⟩,⟨737199, by decide⟩,⟨737574, by decide⟩,⟨737850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1458_737851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1458 ⟨737851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1458
    ⟨737851, by decide⟩ (by decide) (![⟨736565, by decide⟩,⟨737199, by decide⟩,⟨737574, by decide⟩,⟨737850, by decide⟩]) unmarked_context_9_1458_737851 node_context_9_1458_737851
  intro a
  fin_cases a
  · exact context_10_5832_736565
  · exact context_10_5833_737199
  · exact context_10_5834_737574
  · exact context_10_5835_737850

theorem selected_cut_29206 : selected 10 ⟨737880, by decide⟩
    (prefixPartial 11 23344) = some ⟨11, 2, 0, 737880, 23344, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_23344_737880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23344 ⟨737880, by decide⟩ :=
  accepted_of_selected 11 23344 ⟨737880, by decide⟩ ⟨11, 2, 0, 737880, 23344, 2493, 262144⟩
    (by decide) selected_cut_29206

theorem selected_cut_29207 : selected 10 ⟨737916, by decide⟩
    (prefixPartial 11 23345) = some ⟨11, 2, 0, 737916, 23345, 2829, 262144⟩ := by
  decide +kernel

theorem context_11_23345_737916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23345 ⟨737916, by decide⟩ :=
  accepted_of_selected 11 23345 ⟨737916, by decide⟩ ⟨11, 2, 0, 737916, 23345, 2829, 262144⟩
    (by decide) selected_cut_29207

theorem selected_cut_29208 : selected 10 ⟨737951, by decide⟩
    (prefixPartial 11 23346) = some ⟨11, 2, 0, 737951, 23346, 3285, 262144⟩ := by
  decide +kernel

theorem context_11_23346_737951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23346 ⟨737951, by decide⟩ :=
  accepted_of_selected 11 23346 ⟨737951, by decide⟩ ⟨11, 2, 0, 737951, 23346, 3285, 262144⟩
    (by decide) selected_cut_29208

theorem selected_cut_29209 : selected 10 ⟨737981, by decide⟩
    (prefixPartial 11 23347) = some ⟨11, 2, 0, 737981, 23347, 2773, 262144⟩ := by
  decide +kernel

theorem context_11_23347_737981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23347 ⟨737981, by decide⟩ :=
  accepted_of_selected 11 23347 ⟨737981, by decide⟩ ⟨11, 2, 0, 737981, 23347, 2773, 262144⟩
    (by decide) selected_cut_29209

theorem unmarked_context_10_5836_737982 : frontier 11 ⟨737982, by decide⟩
    (prefixCache 10 5836) (prefixPartial 10 5836) = false := by
  decide +kernel

theorem node_context_10_5836_737982 : EJMOriginalGlobalDAGData.nodes 11 ⟨737982, by decide⟩ =
    .split (coordinate 10) (![⟨737880, by decide⟩,⟨737916, by decide⟩,⟨737951, by decide⟩,⟨737981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5836_737982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5836 ⟨737982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5836
    ⟨737982, by decide⟩ (by decide) (![⟨737880, by decide⟩,⟨737916, by decide⟩,⟨737951, by decide⟩,⟨737981, by decide⟩]) unmarked_context_10_5836_737982 node_context_10_5836_737982
  intro a
  fin_cases a
  · exact context_11_23344_737880
  · exact context_11_23345_737916
  · exact context_11_23346_737951
  · exact context_11_23347_737981

theorem selected_cut_29210 : selected 10 ⟨738017, by decide⟩
    (prefixPartial 11 23348) = some ⟨11, 2, 0, 738017, 23348, 3065, 262144⟩ := by
  decide +kernel

theorem context_11_23348_738017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23348 ⟨738017, by decide⟩ :=
  accepted_of_selected 11 23348 ⟨738017, by decide⟩ ⟨11, 2, 0, 738017, 23348, 3065, 262144⟩
    (by decide) selected_cut_29210

theorem selected_cut_29211 : selected 10 ⟨738041, by decide⟩
    (prefixPartial 11 23349) = some ⟨11, 2, 0, 738041, 23349, 2373, 262144⟩ := by
  decide +kernel

theorem context_11_23349_738041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23349 ⟨738041, by decide⟩ :=
  accepted_of_selected 11 23349 ⟨738041, by decide⟩ ⟨11, 2, 0, 738041, 23349, 2373, 262144⟩
    (by decide) selected_cut_29211

theorem selected_cut_29212 : selected 10 ⟨738066, by decide⟩
    (prefixPartial 11 23350) = some ⟨11, 2, 0, 738066, 23350, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_23350_738066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23350 ⟨738066, by decide⟩ :=
  accepted_of_selected 11 23350 ⟨738066, by decide⟩ ⟨11, 2, 0, 738066, 23350, 2189, 262144⟩
    (by decide) selected_cut_29212

theorem selected_cut_29213 : selected 10 ⟨738090, by decide⟩
    (prefixPartial 11 23351) = some ⟨11, 2, 0, 738090, 23351, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_23351_738090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23351 ⟨738090, by decide⟩ :=
  accepted_of_selected 11 23351 ⟨738090, by decide⟩ ⟨11, 2, 0, 738090, 23351, 1777, 262144⟩
    (by decide) selected_cut_29213

theorem unmarked_context_10_5837_738091 : frontier 11 ⟨738091, by decide⟩
    (prefixCache 10 5837) (prefixPartial 10 5837) = false := by
  decide +kernel

theorem node_context_10_5837_738091 : EJMOriginalGlobalDAGData.nodes 11 ⟨738091, by decide⟩ =
    .split (coordinate 10) (![⟨738017, by decide⟩,⟨738041, by decide⟩,⟨738066, by decide⟩,⟨738090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5837_738091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5837 ⟨738091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5837
    ⟨738091, by decide⟩ (by decide) (![⟨738017, by decide⟩,⟨738041, by decide⟩,⟨738066, by decide⟩,⟨738090, by decide⟩]) unmarked_context_10_5837_738091 node_context_10_5837_738091
  intro a
  fin_cases a
  · exact context_11_23348_738017
  · exact context_11_23349_738041
  · exact context_11_23350_738066
  · exact context_11_23351_738090

theorem selected_cut_29214 : selected 10 ⟨738109, by decide⟩
    (prefixPartial 11 23352) = some ⟨11, 2, 0, 738109, 23352, 1529, 262144⟩ := by
  decide +kernel

theorem context_11_23352_738109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23352 ⟨738109, by decide⟩ :=
  accepted_of_selected 11 23352 ⟨738109, by decide⟩ ⟨11, 2, 0, 738109, 23352, 1529, 262144⟩
    (by decide) selected_cut_29214

theorem selected_cut_29215 : selected 10 ⟨738126, by decide⟩
    (prefixPartial 11 23353) = some ⟨11, 2, 0, 738126, 23353, 1161, 262144⟩ := by
  decide +kernel

theorem context_11_23353_738126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23353 ⟨738126, by decide⟩ :=
  accepted_of_selected 11 23353 ⟨738126, by decide⟩ ⟨11, 2, 0, 738126, 23353, 1161, 262144⟩
    (by decide) selected_cut_29215

theorem selected_cut_29216 : selected 10 ⟨738138, by decide⟩
    (prefixPartial 11 23354) = some ⟨11, 2, 0, 738138, 23354, 1033, 262144⟩ := by
  decide +kernel

theorem context_11_23354_738138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23354 ⟨738138, by decide⟩ :=
  accepted_of_selected 11 23354 ⟨738138, by decide⟩ ⟨11, 2, 0, 738138, 23354, 1033, 262144⟩
    (by decide) selected_cut_29216

theorem selected_cut_29217 : selected 10 ⟨738153, by decide⟩
    (prefixPartial 11 23355) = some ⟨11, 2, 0, 738153, 23355, 749, 262144⟩ := by
  decide +kernel

theorem context_11_23355_738153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23355 ⟨738153, by decide⟩ :=
  accepted_of_selected 11 23355 ⟨738153, by decide⟩ ⟨11, 2, 0, 738153, 23355, 749, 262144⟩
    (by decide) selected_cut_29217

theorem unmarked_context_10_5838_738154 : frontier 11 ⟨738154, by decide⟩
    (prefixCache 10 5838) (prefixPartial 10 5838) = false := by
  decide +kernel

theorem node_context_10_5838_738154 : EJMOriginalGlobalDAGData.nodes 11 ⟨738154, by decide⟩ =
    .split (coordinate 10) (![⟨738109, by decide⟩,⟨738126, by decide⟩,⟨738138, by decide⟩,⟨738153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5838_738154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5838 ⟨738154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5838
    ⟨738154, by decide⟩ (by decide) (![⟨738109, by decide⟩,⟨738126, by decide⟩,⟨738138, by decide⟩,⟨738153, by decide⟩]) unmarked_context_10_5838_738154 node_context_10_5838_738154
  intro a
  fin_cases a
  · exact context_11_23352_738109
  · exact context_11_23353_738126
  · exact context_11_23354_738138
  · exact context_11_23355_738153

theorem selected_cut_29218 : selected 11 ⟨738181, by decide⟩
    (prefixPartial 10 5839) = some ⟨10, 2, 0, 738181, 5839, 965, 1048576⟩ := by
  decide +kernel

theorem context_10_5839_738181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5839 ⟨738181, by decide⟩ :=
  accepted_of_selected 10 5839 ⟨738181, by decide⟩ ⟨10, 2, 0, 738181, 5839, 965, 1048576⟩
    (by decide) selected_cut_29218

theorem unmarked_context_9_1459_738182 : frontier 12 ⟨738182, by decide⟩
    (prefixCache 9 1459) (prefixPartial 9 1459) = false := by
  decide +kernel

theorem node_context_9_1459_738182 : EJMOriginalGlobalDAGData.nodes 12 ⟨738182, by decide⟩ =
    .split (coordinate 9) (![⟨737982, by decide⟩,⟨738091, by decide⟩,⟨738154, by decide⟩,⟨738181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1459_738182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1459 ⟨738182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1459
    ⟨738182, by decide⟩ (by decide) (![⟨737982, by decide⟩,⟨738091, by decide⟩,⟨738154, by decide⟩,⟨738181, by decide⟩]) unmarked_context_9_1459_738182 node_context_9_1459_738182
  intro a
  fin_cases a
  · exact context_10_5836_737982
  · exact context_10_5837_738091
  · exact context_10_5838_738154
  · exact context_10_5839_738181

theorem unmarked_context_8_364_738183 : frontier 13 ⟨738183, by decide⟩
    (prefixCache 8 364) (prefixPartial 8 364) = false := by
  decide +kernel

theorem node_context_8_364_738183 : EJMOriginalGlobalDAGData.nodes 13 ⟨738183, by decide⟩ =
    .split (coordinate 8) (![⟨733732, by decide⟩,⟨736067, by decide⟩,⟨737851, by decide⟩,⟨738182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_364_738183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 364 ⟨738183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 364
    ⟨738183, by decide⟩ (by decide) (![⟨733732, by decide⟩,⟨736067, by decide⟩,⟨737851, by decide⟩,⟨738182, by decide⟩]) unmarked_context_8_364_738183 node_context_8_364_738183
  intro a
  fin_cases a
  · exact context_9_1456_733732
  · exact context_9_1457_736067
  · exact context_9_1458_737851
  · exact context_9_1459_738182

theorem selected_cut_29219 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23360) = some ⟨11, 1, 0, 434745, 23360, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23360_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23360 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23360 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23360, 1, 262144⟩
    (by decide) selected_cut_29219

theorem selected_cut_29220 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93444) = some ⟨12, 1, 0, 448748, 93444, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93444_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93444 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93444 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93444, 1, 65536⟩
    (by decide) selected_cut_29220

theorem selected_cut_29221 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 93445) = some ⟨12, 1, 0, 34034, 93445, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93445_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93445 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 93445 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 93445, 1, 65536⟩
    (by decide) selected_cut_29221

theorem selected_cut_29222 : selected 8 ⟨738252, by decide⟩
    (prefixPartial 13 373784) = some ⟨13, 2, 0, 738252, 373784, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_373784_738252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373784 ⟨738252, by decide⟩ :=
  accepted_of_selected 13 373784 ⟨738252, by decide⟩ ⟨13, 2, 0, 738252, 373784, 2965, 16384⟩
    (by decide) selected_cut_29222

theorem selected_cut_29223 : selected 8 ⟨738287, by decide⟩
    (prefixPartial 13 373785) = some ⟨13, 2, 0, 738287, 373785, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_373785_738287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373785 ⟨738287, by decide⟩ :=
  accepted_of_selected 13 373785 ⟨738287, by decide⟩ ⟨13, 2, 0, 738287, 373785, 2221, 16384⟩
    (by decide) selected_cut_29223

theorem selected_cut_29224 : selected 8 ⟨738323, by decide⟩
    (prefixPartial 13 373786) = some ⟨13, 2, 0, 738323, 373786, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_373786_738323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373786 ⟨738323, by decide⟩ :=
  accepted_of_selected 13 373786 ⟨738323, by decide⟩ ⟨13, 2, 0, 738323, 373786, 2077, 16384⟩
    (by decide) selected_cut_29224

theorem selected_cut_29225 : selected 8 ⟨738343, by decide⟩
    (prefixPartial 13 373787) = some ⟨13, 2, 0, 738343, 373787, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_373787_738343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373787 ⟨738343, by decide⟩ :=
  accepted_of_selected 13 373787 ⟨738343, by decide⟩ ⟨13, 2, 0, 738343, 373787, 1029, 16384⟩
    (by decide) selected_cut_29225

theorem unmarked_context_12_93446_738344 : frontier 9 ⟨738344, by decide⟩
    (prefixCache 12 93446) (prefixPartial 12 93446) = false := by
  decide +kernel

theorem node_context_12_93446_738344 : EJMOriginalGlobalDAGData.nodes 9 ⟨738344, by decide⟩ =
    .split (coordinate 12) (![⟨738252, by decide⟩,⟨738287, by decide⟩,⟨738323, by decide⟩,⟨738343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93446_738344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93446 ⟨738344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93446
    ⟨738344, by decide⟩ (by decide) (![⟨738252, by decide⟩,⟨738287, by decide⟩,⟨738323, by decide⟩,⟨738343, by decide⟩]) unmarked_context_12_93446_738344 node_context_12_93446_738344
  intro a
  fin_cases a
  · exact context_13_373784_738252
  · exact context_13_373785_738287
  · exact context_13_373786_738323
  · exact context_13_373787_738343

theorem selected_cut_29226 : selected 8 ⟨738409, by decide⟩
    (prefixPartial 13 373788) = some ⟨13, 2, 0, 738409, 373788, 3177, 16384⟩ := by
  decide +kernel

theorem context_13_373788_738409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373788 ⟨738409, by decide⟩ :=
  accepted_of_selected 13 373788 ⟨738409, by decide⟩ ⟨13, 2, 0, 738409, 373788, 3177, 16384⟩
    (by decide) selected_cut_29226

theorem selected_cut_29227 : selected 8 ⟨738435, by decide⟩
    (prefixPartial 13 373789) = some ⟨13, 2, 0, 738435, 373789, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_373789_738435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373789 ⟨738435, by decide⟩ :=
  accepted_of_selected 13 373789 ⟨738435, by decide⟩ ⟨13, 2, 0, 738435, 373789, 2345, 16384⟩
    (by decide) selected_cut_29227

theorem selected_cut_29228 : selected 8 ⟨738475, by decide⟩
    (prefixPartial 13 373790) = some ⟨13, 2, 0, 738475, 373790, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_373790_738475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373790 ⟨738475, by decide⟩ :=
  accepted_of_selected 13 373790 ⟨738475, by decide⟩ ⟨13, 2, 0, 738475, 373790, 2341, 16384⟩
    (by decide) selected_cut_29228

theorem selected_cut_29229 : selected 8 ⟨738484, by decide⟩
    (prefixPartial 13 373791) = some ⟨13, 2, 0, 738484, 373791, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_373791_738484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373791 ⟨738484, by decide⟩ :=
  accepted_of_selected 13 373791 ⟨738484, by decide⟩ ⟨13, 2, 0, 738484, 373791, 1009, 16384⟩
    (by decide) selected_cut_29229

theorem unmarked_context_12_93447_738485 : frontier 9 ⟨738485, by decide⟩
    (prefixCache 12 93447) (prefixPartial 12 93447) = false := by
  decide +kernel

theorem node_context_12_93447_738485 : EJMOriginalGlobalDAGData.nodes 9 ⟨738485, by decide⟩ =
    .split (coordinate 12) (![⟨738409, by decide⟩,⟨738435, by decide⟩,⟨738475, by decide⟩,⟨738484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93447_738485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93447 ⟨738485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93447
    ⟨738485, by decide⟩ (by decide) (![⟨738409, by decide⟩,⟨738435, by decide⟩,⟨738475, by decide⟩,⟨738484, by decide⟩]) unmarked_context_12_93447_738485 node_context_12_93447_738485
  intro a
  fin_cases a
  · exact context_13_373788_738409
  · exact context_13_373789_738435
  · exact context_13_373790_738475
  · exact context_13_373791_738484

theorem unmarked_context_11_23361_738486 : frontier 10 ⟨738486, by decide⟩
    (prefixCache 11 23361) (prefixPartial 11 23361) = false := by
  decide +kernel

theorem node_context_11_23361_738486 : EJMOriginalGlobalDAGData.nodes 10 ⟨738486, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨738344, by decide⟩,⟨738485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23361_738486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23361 ⟨738486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23361
    ⟨738486, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨738344, by decide⟩,⟨738485, by decide⟩]) unmarked_context_11_23361_738486 node_context_11_23361_738486
  intro a
  fin_cases a
  · exact context_12_93444_448748
  · exact context_12_93445_34034
  · exact context_12_93446_738344
  · exact context_12_93447_738485

theorem selected_cut_29230 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93448) = some ⟨12, 1, 0, 448748, 93448, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93448_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93448 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93448 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93448, 1, 65536⟩
    (by decide) selected_cut_29230

theorem selected_cut_29231 : selected 8 ⟨738561, by decide⟩
    (prefixPartial 13 373796) = some ⟨13, 2, 0, 738561, 373796, 3069, 16384⟩ := by
  decide +kernel

theorem context_13_373796_738561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373796 ⟨738561, by decide⟩ :=
  accepted_of_selected 13 373796 ⟨738561, by decide⟩ ⟨13, 2, 0, 738561, 373796, 3069, 16384⟩
    (by decide) selected_cut_29231

theorem selected_cut_29232 : selected 8 ⟨738600, by decide⟩
    (prefixPartial 13 373797) = some ⟨13, 2, 0, 738600, 373797, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_373797_738600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373797 ⟨738600, by decide⟩ :=
  accepted_of_selected 13 373797 ⟨738600, by decide⟩ ⟨13, 2, 0, 738600, 373797, 2137, 16384⟩
    (by decide) selected_cut_29232

theorem selected_cut_29233 : selected 8 ⟨738674, by decide⟩
    (prefixPartial 13 373798) = some ⟨13, 2, 0, 738674, 373798, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_373798_738674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373798 ⟨738674, by decide⟩ :=
  accepted_of_selected 13 373798 ⟨738674, by decide⟩ ⟨13, 2, 0, 738674, 373798, 2437, 16384⟩
    (by decide) selected_cut_29233

theorem selected_cut_29234 : selected 8 ⟨738697, by decide⟩
    (prefixPartial 13 373799) = some ⟨13, 2, 0, 738697, 373799, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_373799_738697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373799 ⟨738697, by decide⟩ :=
  accepted_of_selected 13 373799 ⟨738697, by decide⟩ ⟨13, 2, 0, 738697, 373799, 1097, 16384⟩
    (by decide) selected_cut_29234

theorem unmarked_context_12_93449_738698 : frontier 9 ⟨738698, by decide⟩
    (prefixCache 12 93449) (prefixPartial 12 93449) = false := by
  decide +kernel

theorem node_context_12_93449_738698 : EJMOriginalGlobalDAGData.nodes 9 ⟨738698, by decide⟩ =
    .split (coordinate 12) (![⟨738561, by decide⟩,⟨738600, by decide⟩,⟨738674, by decide⟩,⟨738697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93449_738698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93449 ⟨738698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93449
    ⟨738698, by decide⟩ (by decide) (![⟨738561, by decide⟩,⟨738600, by decide⟩,⟨738674, by decide⟩,⟨738697, by decide⟩]) unmarked_context_12_93449_738698 node_context_12_93449_738698
  intro a
  fin_cases a
  · exact context_13_373796_738561
  · exact context_13_373797_738600
  · exact context_13_373798_738674
  · exact context_13_373799_738697

theorem selected_cut_29235 : selected 8 ⟨738764, by decide⟩
    (prefixPartial 13 373800) = some ⟨13, 2, 0, 738764, 373800, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_373800_738764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373800 ⟨738764, by decide⟩ :=
  accepted_of_selected 13 373800 ⟨738764, by decide⟩ ⟨13, 2, 0, 738764, 373800, 2905, 16384⟩
    (by decide) selected_cut_29235

theorem selected_cut_29236 : selected 8 ⟨738813, by decide⟩
    (prefixPartial 13 373801) = some ⟨13, 2, 0, 738813, 373801, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_373801_738813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373801 ⟨738813, by decide⟩ :=
  accepted_of_selected 13 373801 ⟨738813, by decide⟩ ⟨13, 2, 0, 738813, 373801, 2553, 16384⟩
    (by decide) selected_cut_29236

theorem selected_cut_29237 : selected 8 ⟨738869, by decide⟩
    (prefixPartial 13 373802) = some ⟨13, 2, 0, 738869, 373802, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_373802_738869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373802 ⟨738869, by decide⟩ :=
  accepted_of_selected 13 373802 ⟨738869, by decide⟩ ⟨13, 2, 0, 738869, 373802, 2405, 16384⟩
    (by decide) selected_cut_29237

theorem selected_cut_29238 : selected 8 ⟨738896, by decide⟩
    (prefixPartial 13 373803) = some ⟨13, 2, 0, 738896, 373803, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_373803_738896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373803 ⟨738896, by decide⟩ :=
  accepted_of_selected 13 373803 ⟨738896, by decide⟩ ⟨13, 2, 0, 738896, 373803, 1161, 16384⟩
    (by decide) selected_cut_29238

theorem unmarked_context_12_93450_738897 : frontier 9 ⟨738897, by decide⟩
    (prefixCache 12 93450) (prefixPartial 12 93450) = false := by
  decide +kernel

theorem node_context_12_93450_738897 : EJMOriginalGlobalDAGData.nodes 9 ⟨738897, by decide⟩ =
    .split (coordinate 12) (![⟨738764, by decide⟩,⟨738813, by decide⟩,⟨738869, by decide⟩,⟨738896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93450_738897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93450 ⟨738897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93450
    ⟨738897, by decide⟩ (by decide) (![⟨738764, by decide⟩,⟨738813, by decide⟩,⟨738869, by decide⟩,⟨738896, by decide⟩]) unmarked_context_12_93450_738897 node_context_12_93450_738897
  intro a
  fin_cases a
  · exact context_13_373800_738764
  · exact context_13_373801_738813
  · exact context_13_373802_738869
  · exact context_13_373803_738896

theorem selected_cut_29239 : selected 8 ⟨738956, by decide⟩
    (prefixPartial 13 373804) = some ⟨13, 2, 0, 738956, 373804, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_373804_738956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373804 ⟨738956, by decide⟩ :=
  accepted_of_selected 13 373804 ⟨738956, by decide⟩ ⟨13, 2, 0, 738956, 373804, 3193, 16384⟩
    (by decide) selected_cut_29239

theorem selected_cut_29240 : selected 8 ⟨739013, by decide⟩
    (prefixPartial 13 373805) = some ⟨13, 2, 0, 739013, 373805, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_373805_739013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373805 ⟨739013, by decide⟩ :=
  accepted_of_selected 13 373805 ⟨739013, by decide⟩ ⟨13, 2, 0, 739013, 373805, 2729, 16384⟩
    (by decide) selected_cut_29240

theorem selected_cut_29241 : selected 8 ⟨739079, by decide⟩
    (prefixPartial 13 373806) = some ⟨13, 2, 0, 739079, 373806, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_373806_739079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373806 ⟨739079, by decide⟩ :=
  accepted_of_selected 13 373806 ⟨739079, by decide⟩ ⟨13, 2, 0, 739079, 373806, 2761, 16384⟩
    (by decide) selected_cut_29241

theorem selected_cut_29242 : selected 8 ⟨739113, by decide⟩
    (prefixPartial 13 373807) = some ⟨13, 2, 0, 739113, 373807, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_373807_739113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373807 ⟨739113, by decide⟩ :=
  accepted_of_selected 13 373807 ⟨739113, by decide⟩ ⟨13, 2, 0, 739113, 373807, 1209, 16384⟩
    (by decide) selected_cut_29242

theorem unmarked_context_12_93451_739114 : frontier 9 ⟨739114, by decide⟩
    (prefixCache 12 93451) (prefixPartial 12 93451) = false := by
  decide +kernel

theorem node_context_12_93451_739114 : EJMOriginalGlobalDAGData.nodes 9 ⟨739114, by decide⟩ =
    .split (coordinate 12) (![⟨738956, by decide⟩,⟨739013, by decide⟩,⟨739079, by decide⟩,⟨739113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93451_739114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93451 ⟨739114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93451
    ⟨739114, by decide⟩ (by decide) (![⟨738956, by decide⟩,⟨739013, by decide⟩,⟨739079, by decide⟩,⟨739113, by decide⟩]) unmarked_context_12_93451_739114 node_context_12_93451_739114
  intro a
  fin_cases a
  · exact context_13_373804_738956
  · exact context_13_373805_739013
  · exact context_13_373806_739079
  · exact context_13_373807_739113

theorem unmarked_context_11_23362_739115 : frontier 10 ⟨739115, by decide⟩
    (prefixCache 11 23362) (prefixPartial 11 23362) = false := by
  decide +kernel

theorem node_context_11_23362_739115 : EJMOriginalGlobalDAGData.nodes 10 ⟨739115, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨738698, by decide⟩,⟨738897, by decide⟩,⟨739114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23362_739115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23362 ⟨739115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23362
    ⟨739115, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨738698, by decide⟩,⟨738897, by decide⟩,⟨739114, by decide⟩]) unmarked_context_11_23362_739115 node_context_11_23362_739115
  intro a
  fin_cases a
  · exact context_12_93448_448748
  · exact context_12_93449_738698
  · exact context_12_93450_738897
  · exact context_12_93451_739114

theorem selected_cut_29243 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93452) = some ⟨12, 1, 0, 448748, 93452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93452_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93452 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93452 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93452, 1, 65536⟩
    (by decide) selected_cut_29243

theorem selected_cut_29244 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 93453) = some ⟨12, 1, 0, 390434, 93453, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93453_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93453 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 93453 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 93453, 1, 65536⟩
    (by decide) selected_cut_29244

theorem selected_cut_29245 : selected 8 ⟨739168, by decide⟩
    (prefixPartial 13 373816) = some ⟨13, 2, 0, 739168, 373816, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_373816_739168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373816 ⟨739168, by decide⟩ :=
  accepted_of_selected 13 373816 ⟨739168, by decide⟩ ⟨13, 2, 0, 739168, 373816, 2833, 16384⟩
    (by decide) selected_cut_29245

theorem selected_cut_29246 : selected 8 ⟨739207, by decide⟩
    (prefixPartial 13 373817) = some ⟨13, 2, 0, 739207, 373817, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_373817_739207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373817 ⟨739207, by decide⟩ :=
  accepted_of_selected 13 373817 ⟨739207, by decide⟩ ⟨13, 2, 0, 739207, 373817, 2473, 16384⟩
    (by decide) selected_cut_29246

theorem selected_cut_29247 : selected 8 ⟨739240, by decide⟩
    (prefixPartial 13 373818) = some ⟨13, 2, 0, 739240, 373818, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_373818_739240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373818 ⟨739240, by decide⟩ :=
  accepted_of_selected 13 373818 ⟨739240, by decide⟩ ⟨13, 2, 0, 739240, 373818, 2153, 16384⟩
    (by decide) selected_cut_29247

theorem selected_cut_29248 : selected 8 ⟨739273, by decide⟩
    (prefixPartial 13 373819) = some ⟨13, 2, 0, 739273, 373819, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_373819_739273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373819 ⟨739273, by decide⟩ :=
  accepted_of_selected 13 373819 ⟨739273, by decide⟩ ⟨13, 2, 0, 739273, 373819, 1305, 16384⟩
    (by decide) selected_cut_29248

theorem unmarked_context_12_93454_739274 : frontier 9 ⟨739274, by decide⟩
    (prefixCache 12 93454) (prefixPartial 12 93454) = false := by
  decide +kernel

theorem node_context_12_93454_739274 : EJMOriginalGlobalDAGData.nodes 9 ⟨739274, by decide⟩ =
    .split (coordinate 12) (![⟨739168, by decide⟩,⟨739207, by decide⟩,⟨739240, by decide⟩,⟨739273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93454_739274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93454 ⟨739274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93454
    ⟨739274, by decide⟩ (by decide) (![⟨739168, by decide⟩,⟨739207, by decide⟩,⟨739240, by decide⟩,⟨739273, by decide⟩]) unmarked_context_12_93454_739274 node_context_12_93454_739274
  intro a
  fin_cases a
  · exact context_13_373816_739168
  · exact context_13_373817_739207
  · exact context_13_373818_739240
  · exact context_13_373819_739273

theorem selected_cut_29249 : selected 9 ⟨389061, by decide⟩
    (prefixPartial 12 93455) = some ⟨12, 1, 0, 389061, 93455, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93455_389061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93455 ⟨389061, by decide⟩ :=
  accepted_of_selected 12 93455 ⟨389061, by decide⟩ ⟨12, 1, 0, 389061, 93455, 1, 65536⟩
    (by decide) selected_cut_29249

theorem unmarked_context_11_23363_739275 : frontier 10 ⟨739275, by decide⟩
    (prefixCache 11 23363) (prefixPartial 11 23363) = false := by
  decide +kernel

theorem node_context_11_23363_739275 : EJMOriginalGlobalDAGData.nodes 10 ⟨739275, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨739274, by decide⟩,⟨389061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23363_739275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23363 ⟨739275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23363
    ⟨739275, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨739274, by decide⟩,⟨389061, by decide⟩]) unmarked_context_11_23363_739275 node_context_11_23363_739275
  intro a
  fin_cases a
  · exact context_12_93452_448748
  · exact context_12_93453_390434
  · exact context_12_93454_739274
  · exact context_12_93455_389061

theorem unmarked_context_10_5840_739276 : frontier 11 ⟨739276, by decide⟩
    (prefixCache 10 5840) (prefixPartial 10 5840) = false := by
  decide +kernel

theorem node_context_10_5840_739276 : EJMOriginalGlobalDAGData.nodes 11 ⟨739276, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨738486, by decide⟩,⟨739115, by decide⟩,⟨739275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5840_739276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5840 ⟨739276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5840
    ⟨739276, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨738486, by decide⟩,⟨739115, by decide⟩,⟨739275, by decide⟩]) unmarked_context_10_5840_739276 node_context_10_5840_739276
  intro a
  fin_cases a
  · exact context_11_23360_434745
  · exact context_11_23361_738486
  · exact context_11_23362_739115
  · exact context_11_23363_739275

theorem selected_cut_29250 : selected 8 ⟨739308, by decide⟩
    (prefixPartial 13 373824) = some ⟨13, 2, 0, 739308, 373824, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_373824_739308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373824 ⟨739308, by decide⟩ :=
  accepted_of_selected 13 373824 ⟨739308, by decide⟩ ⟨13, 2, 0, 739308, 373824, 1729, 16384⟩
    (by decide) selected_cut_29250

theorem selected_cut_29251 : selected 8 ⟨739332, by decide⟩
    (prefixPartial 13 373825) = some ⟨13, 2, 0, 739332, 373825, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_373825_739332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373825 ⟨739332, by decide⟩ :=
  accepted_of_selected 13 373825 ⟨739332, by decide⟩ ⟨13, 2, 0, 739332, 373825, 1501, 16384⟩
    (by decide) selected_cut_29251

theorem selected_cut_29252 : selected 8 ⟨739353, by decide⟩
    (prefixPartial 13 373826) = some ⟨13, 2, 0, 739353, 373826, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_373826_739353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373826 ⟨739353, by decide⟩ :=
  accepted_of_selected 13 373826 ⟨739353, by decide⟩ ⟨13, 2, 0, 739353, 373826, 1289, 16384⟩
    (by decide) selected_cut_29252

theorem selected_cut_29253 : selected 8 ⟨739363, by decide⟩
    (prefixPartial 13 373827) = some ⟨13, 2, 0, 739363, 373827, 749, 16384⟩ := by
  decide +kernel

theorem context_13_373827_739363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373827 ⟨739363, by decide⟩ :=
  accepted_of_selected 13 373827 ⟨739363, by decide⟩ ⟨13, 2, 0, 739363, 373827, 749, 16384⟩
    (by decide) selected_cut_29253

theorem unmarked_context_12_93456_739364 : frontier 9 ⟨739364, by decide⟩
    (prefixCache 12 93456) (prefixPartial 12 93456) = false := by
  decide +kernel

theorem node_context_12_93456_739364 : EJMOriginalGlobalDAGData.nodes 9 ⟨739364, by decide⟩ =
    .split (coordinate 12) (![⟨739308, by decide⟩,⟨739332, by decide⟩,⟨739353, by decide⟩,⟨739363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93456_739364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93456 ⟨739364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93456
    ⟨739364, by decide⟩ (by decide) (![⟨739308, by decide⟩,⟨739332, by decide⟩,⟨739353, by decide⟩,⟨739363, by decide⟩]) unmarked_context_12_93456_739364 node_context_12_93456_739364
  intro a
  fin_cases a
  · exact context_13_373824_739308
  · exact context_13_373825_739332
  · exact context_13_373826_739353
  · exact context_13_373827_739363

theorem selected_cut_29254 : selected 8 ⟨739390, by decide⟩
    (prefixPartial 13 373828) = some ⟨13, 2, 0, 739390, 373828, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_373828_739390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373828 ⟨739390, by decide⟩ :=
  accepted_of_selected 13 373828 ⟨739390, by decide⟩ ⟨13, 2, 0, 739390, 373828, 1729, 16384⟩
    (by decide) selected_cut_29254

theorem selected_cut_29255 : selected 8 ⟨739413, by decide⟩
    (prefixPartial 13 373829) = some ⟨13, 2, 0, 739413, 373829, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_373829_739413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373829 ⟨739413, by decide⟩ :=
  accepted_of_selected 13 373829 ⟨739413, by decide⟩ ⟨13, 2, 0, 739413, 373829, 1349, 16384⟩
    (by decide) selected_cut_29255

theorem selected_cut_29256 : selected 8 ⟨739434, by decide⟩
    (prefixPartial 13 373830) = some ⟨13, 2, 0, 739434, 373830, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_373830_739434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373830 ⟨739434, by decide⟩ :=
  accepted_of_selected 13 373830 ⟨739434, by decide⟩ ⟨13, 2, 0, 739434, 373830, 1489, 16384⟩
    (by decide) selected_cut_29256

theorem selected_cut_29257 : selected 8 ⟨739444, by decide⟩
    (prefixPartial 13 373831) = some ⟨13, 2, 0, 739444, 373831, 829, 16384⟩ := by
  decide +kernel

theorem context_13_373831_739444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373831 ⟨739444, by decide⟩ :=
  accepted_of_selected 13 373831 ⟨739444, by decide⟩ ⟨13, 2, 0, 739444, 373831, 829, 16384⟩
    (by decide) selected_cut_29257

theorem unmarked_context_12_93457_739445 : frontier 9 ⟨739445, by decide⟩
    (prefixCache 12 93457) (prefixPartial 12 93457) = false := by
  decide +kernel

theorem node_context_12_93457_739445 : EJMOriginalGlobalDAGData.nodes 9 ⟨739445, by decide⟩ =
    .split (coordinate 12) (![⟨739390, by decide⟩,⟨739413, by decide⟩,⟨739434, by decide⟩,⟨739444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93457_739445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93457 ⟨739445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93457
    ⟨739445, by decide⟩ (by decide) (![⟨739390, by decide⟩,⟨739413, by decide⟩,⟨739434, by decide⟩,⟨739444, by decide⟩]) unmarked_context_12_93457_739445 node_context_12_93457_739445
  intro a
  fin_cases a
  · exact context_13_373828_739390
  · exact context_13_373829_739413
  · exact context_13_373830_739434
  · exact context_13_373831_739444

theorem selected_cut_29258 : selected 8 ⟨739483, by decide⟩
    (prefixPartial 13 373832) = some ⟨13, 2, 0, 739483, 373832, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_373832_739483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373832 ⟨739483, by decide⟩ :=
  accepted_of_selected 13 373832 ⟨739483, by decide⟩ ⟨13, 2, 0, 739483, 373832, 1861, 16384⟩
    (by decide) selected_cut_29258

theorem selected_cut_29259 : selected 8 ⟨739509, by decide⟩
    (prefixPartial 13 373833) = some ⟨13, 2, 0, 739509, 373833, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_373833_739509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373833 ⟨739509, by decide⟩ :=
  accepted_of_selected 13 373833 ⟨739509, by decide⟩ ⟨13, 2, 0, 739509, 373833, 1737, 16384⟩
    (by decide) selected_cut_29259

theorem selected_cut_29260 : selected 8 ⟨739532, by decide⟩
    (prefixPartial 13 373834) = some ⟨13, 2, 0, 739532, 373834, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_373834_739532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373834 ⟨739532, by decide⟩ :=
  accepted_of_selected 13 373834 ⟨739532, by decide⟩ ⟨13, 2, 0, 739532, 373834, 1509, 16384⟩
    (by decide) selected_cut_29260

theorem selected_cut_29261 : selected 8 ⟨739541, by decide⟩
    (prefixPartial 13 373835) = some ⟨13, 2, 0, 739541, 373835, 917, 16384⟩ := by
  decide +kernel

theorem context_13_373835_739541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373835 ⟨739541, by decide⟩ :=
  accepted_of_selected 13 373835 ⟨739541, by decide⟩ ⟨13, 2, 0, 739541, 373835, 917, 16384⟩
    (by decide) selected_cut_29261

theorem unmarked_context_12_93458_739542 : frontier 9 ⟨739542, by decide⟩
    (prefixCache 12 93458) (prefixPartial 12 93458) = false := by
  decide +kernel

theorem node_context_12_93458_739542 : EJMOriginalGlobalDAGData.nodes 9 ⟨739542, by decide⟩ =
    .split (coordinate 12) (![⟨739483, by decide⟩,⟨739509, by decide⟩,⟨739532, by decide⟩,⟨739541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93458_739542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93458 ⟨739542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93458
    ⟨739542, by decide⟩ (by decide) (![⟨739483, by decide⟩,⟨739509, by decide⟩,⟨739532, by decide⟩,⟨739541, by decide⟩]) unmarked_context_12_93458_739542 node_context_12_93458_739542
  intro a
  fin_cases a
  · exact context_13_373832_739483
  · exact context_13_373833_739509
  · exact context_13_373834_739532
  · exact context_13_373835_739541

theorem selected_cut_29262 : selected 8 ⟨739579, by decide⟩
    (prefixPartial 13 373836) = some ⟨13, 2, 0, 739579, 373836, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_373836_739579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373836 ⟨739579, by decide⟩ :=
  accepted_of_selected 13 373836 ⟨739579, by decide⟩ ⟨13, 2, 0, 739579, 373836, 2037, 16384⟩
    (by decide) selected_cut_29262

theorem selected_cut_29263 : selected 8 ⟨739600, by decide⟩
    (prefixPartial 13 373837) = some ⟨13, 2, 0, 739600, 373837, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_373837_739600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373837 ⟨739600, by decide⟩ :=
  accepted_of_selected 13 373837 ⟨739600, by decide⟩ ⟨13, 2, 0, 739600, 373837, 1765, 16384⟩
    (by decide) selected_cut_29263

theorem selected_cut_29264 : selected 8 ⟨739623, by decide⟩
    (prefixPartial 13 373838) = some ⟨13, 2, 0, 739623, 373838, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_373838_739623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373838 ⟨739623, by decide⟩ :=
  accepted_of_selected 13 373838 ⟨739623, by decide⟩ ⟨13, 2, 0, 739623, 373838, 1749, 16384⟩
    (by decide) selected_cut_29264

theorem selected_cut_29265 : selected 8 ⟨739631, by decide⟩
    (prefixPartial 13 373839) = some ⟨13, 2, 0, 739631, 373839, 909, 16384⟩ := by
  decide +kernel

theorem context_13_373839_739631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373839 ⟨739631, by decide⟩ :=
  accepted_of_selected 13 373839 ⟨739631, by decide⟩ ⟨13, 2, 0, 739631, 373839, 909, 16384⟩
    (by decide) selected_cut_29265

theorem unmarked_context_12_93459_739632 : frontier 9 ⟨739632, by decide⟩
    (prefixCache 12 93459) (prefixPartial 12 93459) = false := by
  decide +kernel

theorem node_context_12_93459_739632 : EJMOriginalGlobalDAGData.nodes 9 ⟨739632, by decide⟩ =
    .split (coordinate 12) (![⟨739579, by decide⟩,⟨739600, by decide⟩,⟨739623, by decide⟩,⟨739631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93459_739632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93459 ⟨739632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93459
    ⟨739632, by decide⟩ (by decide) (![⟨739579, by decide⟩,⟨739600, by decide⟩,⟨739623, by decide⟩,⟨739631, by decide⟩]) unmarked_context_12_93459_739632 node_context_12_93459_739632
  intro a
  fin_cases a
  · exact context_13_373836_739579
  · exact context_13_373837_739600
  · exact context_13_373838_739623
  · exact context_13_373839_739631

theorem unmarked_context_11_23364_739633 : frontier 10 ⟨739633, by decide⟩
    (prefixCache 11 23364) (prefixPartial 11 23364) = false := by
  decide +kernel

theorem node_context_11_23364_739633 : EJMOriginalGlobalDAGData.nodes 10 ⟨739633, by decide⟩ =
    .split (coordinate 11) (![⟨739364, by decide⟩,⟨739445, by decide⟩,⟨739542, by decide⟩,⟨739632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23364_739633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23364 ⟨739633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23364
    ⟨739633, by decide⟩ (by decide) (![⟨739364, by decide⟩,⟨739445, by decide⟩,⟨739542, by decide⟩,⟨739632, by decide⟩]) unmarked_context_11_23364_739633 node_context_11_23364_739633
  intro a
  fin_cases a
  · exact context_12_93456_739364
  · exact context_12_93457_739445
  · exact context_12_93458_739542
  · exact context_12_93459_739632

theorem selected_cut_29266 : selected 8 ⟨739654, by decide⟩
    (prefixPartial 13 373840) = some ⟨13, 2, 0, 739654, 373840, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_373840_739654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373840 ⟨739654, by decide⟩ :=
  accepted_of_selected 13 373840 ⟨739654, by decide⟩ ⟨13, 2, 0, 739654, 373840, 1409, 16384⟩
    (by decide) selected_cut_29266

theorem selected_cut_29267 : selected 8 ⟨739675, by decide⟩
    (prefixPartial 13 373841) = some ⟨13, 2, 0, 739675, 373841, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_373841_739675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373841 ⟨739675, by decide⟩ :=
  accepted_of_selected 13 373841 ⟨739675, by decide⟩ ⟨13, 2, 0, 739675, 373841, 1437, 16384⟩
    (by decide) selected_cut_29267

theorem selected_cut_29268 : selected 8 ⟨739696, by decide⟩
    (prefixPartial 13 373842) = some ⟨13, 2, 0, 739696, 373842, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_373842_739696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373842 ⟨739696, by decide⟩ :=
  accepted_of_selected 13 373842 ⟨739696, by decide⟩ ⟨13, 2, 0, 739696, 373842, 1153, 16384⟩
    (by decide) selected_cut_29268

theorem selected_cut_29269 : selected 8 ⟨739704, by decide⟩
    (prefixPartial 13 373843) = some ⟨13, 2, 0, 739704, 373843, 665, 16384⟩ := by
  decide +kernel

theorem context_13_373843_739704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373843 ⟨739704, by decide⟩ :=
  accepted_of_selected 13 373843 ⟨739704, by decide⟩ ⟨13, 2, 0, 739704, 373843, 665, 16384⟩
    (by decide) selected_cut_29269

theorem unmarked_context_12_93460_739705 : frontier 9 ⟨739705, by decide⟩
    (prefixCache 12 93460) (prefixPartial 12 93460) = false := by
  decide +kernel

theorem node_context_12_93460_739705 : EJMOriginalGlobalDAGData.nodes 9 ⟨739705, by decide⟩ =
    .split (coordinate 12) (![⟨739654, by decide⟩,⟨739675, by decide⟩,⟨739696, by decide⟩,⟨739704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93460_739705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93460 ⟨739705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93460
    ⟨739705, by decide⟩ (by decide) (![⟨739654, by decide⟩,⟨739675, by decide⟩,⟨739696, by decide⟩,⟨739704, by decide⟩]) unmarked_context_12_93460_739705 node_context_12_93460_739705
  intro a
  fin_cases a
  · exact context_13_373840_739654
  · exact context_13_373841_739675
  · exact context_13_373842_739696
  · exact context_13_373843_739704

theorem selected_cut_29270 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 93461) = some ⟨12, 1, 0, 439069, 93461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93461_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93461 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 93461 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 93461, 1, 65536⟩
    (by decide) selected_cut_29270

theorem selected_cut_29271 : selected 8 ⟨739731, by decide⟩
    (prefixPartial 13 373848) = some ⟨13, 2, 0, 739731, 373848, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_373848_739731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373848 ⟨739731, by decide⟩ :=
  accepted_of_selected 13 373848 ⟨739731, by decide⟩ ⟨13, 2, 0, 739731, 373848, 1549, 16384⟩
    (by decide) selected_cut_29271

theorem selected_cut_29272 : selected 8 ⟨739752, by decide⟩
    (prefixPartial 13 373849) = some ⟨13, 2, 0, 739752, 373849, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_373849_739752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373849 ⟨739752, by decide⟩ :=
  accepted_of_selected 13 373849 ⟨739752, by decide⟩ ⟨13, 2, 0, 739752, 373849, 1673, 16384⟩
    (by decide) selected_cut_29272

theorem selected_cut_29273 : selected 8 ⟨739771, by decide⟩
    (prefixPartial 13 373850) = some ⟨13, 2, 0, 739771, 373850, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_373850_739771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373850 ⟨739771, by decide⟩ :=
  accepted_of_selected 13 373850 ⟨739771, by decide⟩ ⟨13, 2, 0, 739771, 373850, 1349, 16384⟩
    (by decide) selected_cut_29273

theorem selected_cut_29274 : selected 8 ⟨739778, by decide⟩
    (prefixPartial 13 373851) = some ⟨13, 2, 0, 739778, 373851, 813, 16384⟩ := by
  decide +kernel

theorem context_13_373851_739778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373851 ⟨739778, by decide⟩ :=
  accepted_of_selected 13 373851 ⟨739778, by decide⟩ ⟨13, 2, 0, 739778, 373851, 813, 16384⟩
    (by decide) selected_cut_29274

theorem unmarked_context_12_93462_739779 : frontier 9 ⟨739779, by decide⟩
    (prefixCache 12 93462) (prefixPartial 12 93462) = false := by
  decide +kernel

theorem node_context_12_93462_739779 : EJMOriginalGlobalDAGData.nodes 9 ⟨739779, by decide⟩ =
    .split (coordinate 12) (![⟨739731, by decide⟩,⟨739752, by decide⟩,⟨739771, by decide⟩,⟨739778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93462_739779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93462 ⟨739779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93462
    ⟨739779, by decide⟩ (by decide) (![⟨739731, by decide⟩,⟨739752, by decide⟩,⟨739771, by decide⟩,⟨739778, by decide⟩]) unmarked_context_12_93462_739779 node_context_12_93462_739779
  intro a
  fin_cases a
  · exact context_13_373848_739731
  · exact context_13_373849_739752
  · exact context_13_373850_739771
  · exact context_13_373851_739778

theorem selected_cut_29275 : selected 8 ⟨739807, by decide⟩
    (prefixPartial 13 373852) = some ⟨13, 2, 0, 739807, 373852, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_373852_739807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373852 ⟨739807, by decide⟩ :=
  accepted_of_selected 13 373852 ⟨739807, by decide⟩ ⟨13, 2, 0, 739807, 373852, 1649, 16384⟩
    (by decide) selected_cut_29275

theorem selected_cut_29276 : selected 8 ⟨739833, by decide⟩
    (prefixPartial 13 373853) = some ⟨13, 2, 0, 739833, 373853, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_373853_739833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373853 ⟨739833, by decide⟩ :=
  accepted_of_selected 13 373853 ⟨739833, by decide⟩ ⟨13, 2, 0, 739833, 373853, 1761, 16384⟩
    (by decide) selected_cut_29276

theorem selected_cut_29277 : selected 8 ⟨739855, by decide⟩
    (prefixPartial 13 373854) = some ⟨13, 2, 0, 739855, 373854, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_373854_739855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373854 ⟨739855, by decide⟩ :=
  accepted_of_selected 13 373854 ⟨739855, by decide⟩ ⟨13, 2, 0, 739855, 373854, 1609, 16384⟩
    (by decide) selected_cut_29277

theorem selected_cut_29278 : selected 8 ⟨739862, by decide⟩
    (prefixPartial 13 373855) = some ⟨13, 2, 0, 739862, 373855, 793, 16384⟩ := by
  decide +kernel

theorem context_13_373855_739862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373855 ⟨739862, by decide⟩ :=
  accepted_of_selected 13 373855 ⟨739862, by decide⟩ ⟨13, 2, 0, 739862, 373855, 793, 16384⟩
    (by decide) selected_cut_29278

theorem unmarked_context_12_93463_739863 : frontier 9 ⟨739863, by decide⟩
    (prefixCache 12 93463) (prefixPartial 12 93463) = false := by
  decide +kernel

theorem node_context_12_93463_739863 : EJMOriginalGlobalDAGData.nodes 9 ⟨739863, by decide⟩ =
    .split (coordinate 12) (![⟨739807, by decide⟩,⟨739833, by decide⟩,⟨739855, by decide⟩,⟨739862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93463_739863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93463 ⟨739863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93463
    ⟨739863, by decide⟩ (by decide) (![⟨739807, by decide⟩,⟨739833, by decide⟩,⟨739855, by decide⟩,⟨739862, by decide⟩]) unmarked_context_12_93463_739863 node_context_12_93463_739863
  intro a
  fin_cases a
  · exact context_13_373852_739807
  · exact context_13_373853_739833
  · exact context_13_373854_739855
  · exact context_13_373855_739862

theorem unmarked_context_11_23365_739864 : frontier 10 ⟨739864, by decide⟩
    (prefixCache 11 23365) (prefixPartial 11 23365) = false := by
  decide +kernel

theorem node_context_11_23365_739864 : EJMOriginalGlobalDAGData.nodes 10 ⟨739864, by decide⟩ =
    .split (coordinate 11) (![⟨739705, by decide⟩,⟨439069, by decide⟩,⟨739779, by decide⟩,⟨739863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23365_739864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23365 ⟨739864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23365
    ⟨739864, by decide⟩ (by decide) (![⟨739705, by decide⟩,⟨439069, by decide⟩,⟨739779, by decide⟩,⟨739863, by decide⟩]) unmarked_context_11_23365_739864 node_context_11_23365_739864
  intro a
  fin_cases a
  · exact context_12_93460_739705
  · exact context_12_93461_439069
  · exact context_12_93462_739779
  · exact context_12_93463_739863

theorem selected_cut_29279 : selected 8 ⟨739883, by decide⟩
    (prefixPartial 13 373856) = some ⟨13, 2, 0, 739883, 373856, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_373856_739883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373856 ⟨739883, by decide⟩ :=
  accepted_of_selected 13 373856 ⟨739883, by decide⟩ ⟨13, 2, 0, 739883, 373856, 1305, 16384⟩
    (by decide) selected_cut_29279

theorem selected_cut_29280 : selected 8 ⟨739904, by decide⟩
    (prefixPartial 13 373857) = some ⟨13, 2, 0, 739904, 373857, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_373857_739904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373857 ⟨739904, by decide⟩ :=
  accepted_of_selected 13 373857 ⟨739904, by decide⟩ ⟨13, 2, 0, 739904, 373857, 1433, 16384⟩
    (by decide) selected_cut_29280

theorem selected_cut_29281 : selected 8 ⟨739921, by decide⟩
    (prefixPartial 13 373858) = some ⟨13, 2, 0, 739921, 373858, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_373858_739921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373858 ⟨739921, by decide⟩ :=
  accepted_of_selected 13 373858 ⟨739921, by decide⟩ ⟨13, 2, 0, 739921, 373858, 1365, 16384⟩
    (by decide) selected_cut_29281

theorem selected_cut_29282 : selected 8 ⟨739929, by decide⟩
    (prefixPartial 13 373859) = some ⟨13, 2, 0, 739929, 373859, 757, 16384⟩ := by
  decide +kernel

theorem context_13_373859_739929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373859 ⟨739929, by decide⟩ :=
  accepted_of_selected 13 373859 ⟨739929, by decide⟩ ⟨13, 2, 0, 739929, 373859, 757, 16384⟩
    (by decide) selected_cut_29282

theorem unmarked_context_12_93464_739930 : frontier 9 ⟨739930, by decide⟩
    (prefixCache 12 93464) (prefixPartial 12 93464) = false := by
  decide +kernel

theorem node_context_12_93464_739930 : EJMOriginalGlobalDAGData.nodes 9 ⟨739930, by decide⟩ =
    .split (coordinate 12) (![⟨739883, by decide⟩,⟨739904, by decide⟩,⟨739921, by decide⟩,⟨739929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93464_739930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93464 ⟨739930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93464
    ⟨739930, by decide⟩ (by decide) (![⟨739883, by decide⟩,⟨739904, by decide⟩,⟨739921, by decide⟩,⟨739929, by decide⟩]) unmarked_context_12_93464_739930 node_context_12_93464_739930
  intro a
  fin_cases a
  · exact context_13_373856_739883
  · exact context_13_373857_739904
  · exact context_13_373858_739921
  · exact context_13_373859_739929

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
