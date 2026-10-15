/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover501
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_23472_1351413 : frontier 11 ⟨1351413, by decide⟩
    (prefixCache 10 23472) (prefixPartial 10 23472) = false := by
  decide +kernel

theorem node_context_10_23472_1351413 : EJMOriginalGlobalDAGData.nodes 11 ⟨1351413, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1351165, by decide⟩,⟨1351273, by decide⟩,⟨1351412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23472_1351413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23472 ⟨1351413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23472
    ⟨1351413, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1351165, by decide⟩,⟨1351273, by decide⟩,⟨1351412, by decide⟩]) unmarked_context_10_23472_1351413 node_context_10_23472_1351413
  intro a
  fin_cases a
  · exact context_11_93888_434745
  · exact context_11_93889_1351165
  · exact context_11_93890_1351273
  · exact context_11_93891_1351412

theorem selected_cut_48196 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 375568) = some ⟨12, 1, 0, 1255011, 375568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375568_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375568 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 375568 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 375568, 1, 65536⟩
    (by decide) selected_cut_48196

theorem selected_cut_48197 : selected 9 ⟨1351457, by decide⟩
    (prefixPartial 12 375569) = some ⟨12, 2, 0, 1351457, 375569, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_375569_1351457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375569 ⟨1351457, by decide⟩ :=
  accepted_of_selected 12 375569 ⟨1351457, by decide⟩ ⟨12, 2, 0, 1351457, 375569, 2853, 65536⟩
    (by decide) selected_cut_48197

theorem selected_cut_48198 : selected 9 ⟨1351498, by decide⟩
    (prefixPartial 12 375570) = some ⟨12, 2, 0, 1351498, 375570, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_375570_1351498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375570 ⟨1351498, by decide⟩ :=
  accepted_of_selected 12 375570 ⟨1351498, by decide⟩ ⟨12, 2, 0, 1351498, 375570, 2677, 65536⟩
    (by decide) selected_cut_48198

theorem selected_cut_48199 : selected 9 ⟨1351549, by decide⟩
    (prefixPartial 12 375571) = some ⟨12, 2, 0, 1351549, 375571, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_375571_1351549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375571 ⟨1351549, by decide⟩ :=
  accepted_of_selected 12 375571 ⟨1351549, by decide⟩ ⟨12, 2, 0, 1351549, 375571, 2605, 65536⟩
    (by decide) selected_cut_48199

theorem unmarked_context_11_93892_1351550 : frontier 10 ⟨1351550, by decide⟩
    (prefixCache 11 93892) (prefixPartial 11 93892) = false := by
  decide +kernel

theorem node_context_11_93892_1351550 : EJMOriginalGlobalDAGData.nodes 10 ⟨1351550, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1351457, by decide⟩,⟨1351498, by decide⟩,⟨1351549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93892_1351550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93892 ⟨1351550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93892
    ⟨1351550, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1351457, by decide⟩,⟨1351498, by decide⟩,⟨1351549, by decide⟩]) unmarked_context_11_93892_1351550 node_context_11_93892_1351550
  intro a
  fin_cases a
  · exact context_12_375568_1255011
  · exact context_12_375569_1351457
  · exact context_12_375570_1351498
  · exact context_12_375571_1351549

theorem selected_cut_48200 : selected 9 ⟨1351602, by decide⟩
    (prefixPartial 12 375572) = some ⟨12, 2, 0, 1351602, 375572, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_375572_1351602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375572 ⟨1351602, by decide⟩ :=
  accepted_of_selected 12 375572 ⟨1351602, by decide⟩ ⟨12, 2, 0, 1351602, 375572, 2789, 65536⟩
    (by decide) selected_cut_48200

theorem selected_cut_48201 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 375573) = some ⟨12, 1, 0, 1118965, 375573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375573_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375573 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 375573 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 375573, 1, 65536⟩
    (by decide) selected_cut_48201

theorem selected_cut_48202 : selected 9 ⟨969470, by decide⟩
    (prefixPartial 12 375574) = some ⟨12, 1, 0, 969470, 375574, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375574_969470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375574 ⟨969470, by decide⟩ :=
  accepted_of_selected 12 375574 ⟨969470, by decide⟩ ⟨12, 1, 0, 969470, 375574, 1, 65536⟩
    (by decide) selected_cut_48202

theorem selected_cut_48203 : selected 9 ⟨1351656, by decide⟩
    (prefixPartial 12 375575) = some ⟨12, 2, 0, 1351656, 375575, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_375575_1351656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375575 ⟨1351656, by decide⟩ :=
  accepted_of_selected 12 375575 ⟨1351656, by decide⟩ ⟨12, 2, 0, 1351656, 375575, 2617, 65536⟩
    (by decide) selected_cut_48203

theorem unmarked_context_11_93893_1351657 : frontier 10 ⟨1351657, by decide⟩
    (prefixCache 11 93893) (prefixPartial 11 93893) = false := by
  decide +kernel

theorem node_context_11_93893_1351657 : EJMOriginalGlobalDAGData.nodes 10 ⟨1351657, by decide⟩ =
    .split (coordinate 11) (![⟨1351602, by decide⟩,⟨1118965, by decide⟩,⟨969470, by decide⟩,⟨1351656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93893_1351657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93893 ⟨1351657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93893
    ⟨1351657, by decide⟩ (by decide) (![⟨1351602, by decide⟩,⟨1118965, by decide⟩,⟨969470, by decide⟩,⟨1351656, by decide⟩]) unmarked_context_11_93893_1351657 node_context_11_93893_1351657
  intro a
  fin_cases a
  · exact context_12_375572_1351602
  · exact context_12_375573_1118965
  · exact context_12_375574_969470
  · exact context_12_375575_1351656

theorem selected_cut_48204 : selected 9 ⟨1351696, by decide⟩
    (prefixPartial 12 375576) = some ⟨12, 2, 0, 1351696, 375576, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_375576_1351696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375576 ⟨1351696, by decide⟩ :=
  accepted_of_selected 12 375576 ⟨1351696, by decide⟩ ⟨12, 2, 0, 1351696, 375576, 2349, 65536⟩
    (by decide) selected_cut_48204

theorem selected_cut_48205 : selected 9 ⟨1351732, by decide⟩
    (prefixPartial 12 375577) = some ⟨12, 2, 0, 1351732, 375577, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_375577_1351732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375577 ⟨1351732, by decide⟩ :=
  accepted_of_selected 12 375577 ⟨1351732, by decide⟩ ⟨12, 2, 0, 1351732, 375577, 2505, 65536⟩
    (by decide) selected_cut_48205

theorem selected_cut_48206 : selected 9 ⟨1351768, by decide⟩
    (prefixPartial 12 375578) = some ⟨12, 2, 0, 1351768, 375578, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_375578_1351768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375578 ⟨1351768, by decide⟩ :=
  accepted_of_selected 12 375578 ⟨1351768, by decide⟩ ⟨12, 2, 0, 1351768, 375578, 2261, 65536⟩
    (by decide) selected_cut_48206

theorem selected_cut_48207 : selected 9 ⟨1351811, by decide⟩
    (prefixPartial 12 375579) = some ⟨12, 2, 0, 1351811, 375579, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_375579_1351811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375579 ⟨1351811, by decide⟩ :=
  accepted_of_selected 12 375579 ⟨1351811, by decide⟩ ⟨12, 2, 0, 1351811, 375579, 2297, 65536⟩
    (by decide) selected_cut_48207

theorem unmarked_context_11_93894_1351812 : frontier 10 ⟨1351812, by decide⟩
    (prefixCache 11 93894) (prefixPartial 11 93894) = false := by
  decide +kernel

theorem node_context_11_93894_1351812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1351812, by decide⟩ =
    .split (coordinate 11) (![⟨1351696, by decide⟩,⟨1351732, by decide⟩,⟨1351768, by decide⟩,⟨1351811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93894_1351812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93894 ⟨1351812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93894
    ⟨1351812, by decide⟩ (by decide) (![⟨1351696, by decide⟩,⟨1351732, by decide⟩,⟨1351768, by decide⟩,⟨1351811, by decide⟩]) unmarked_context_11_93894_1351812 node_context_11_93894_1351812
  intro a
  fin_cases a
  · exact context_12_375576_1351696
  · exact context_12_375577_1351732
  · exact context_12_375578_1351768
  · exact context_12_375579_1351811

theorem selected_cut_48208 : selected 9 ⟨1351865, by decide⟩
    (prefixPartial 12 375580) = some ⟨12, 2, 0, 1351865, 375580, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_375580_1351865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375580 ⟨1351865, by decide⟩ :=
  accepted_of_selected 12 375580 ⟨1351865, by decide⟩ ⟨12, 2, 0, 1351865, 375580, 2465, 65536⟩
    (by decide) selected_cut_48208

theorem selected_cut_48209 : selected 9 ⟨1351909, by decide⟩
    (prefixPartial 12 375581) = some ⟨12, 2, 0, 1351909, 375581, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_375581_1351909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375581 ⟨1351909, by decide⟩ :=
  accepted_of_selected 12 375581 ⟨1351909, by decide⟩ ⟨12, 2, 0, 1351909, 375581, 2589, 65536⟩
    (by decide) selected_cut_48209

theorem selected_cut_48210 : selected 9 ⟨1351952, by decide⟩
    (prefixPartial 12 375582) = some ⟨12, 2, 0, 1351952, 375582, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_375582_1351952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375582 ⟨1351952, by decide⟩ :=
  accepted_of_selected 12 375582 ⟨1351952, by decide⟩ ⟨12, 2, 0, 1351952, 375582, 2477, 65536⟩
    (by decide) selected_cut_48210

theorem selected_cut_48211 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 375583) = some ⟨12, 1, 0, 903806, 375583, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375583_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375583 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 375583 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 375583, 1, 65536⟩
    (by decide) selected_cut_48211

theorem unmarked_context_11_93895_1351953 : frontier 10 ⟨1351953, by decide⟩
    (prefixCache 11 93895) (prefixPartial 11 93895) = false := by
  decide +kernel

theorem node_context_11_93895_1351953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1351953, by decide⟩ =
    .split (coordinate 11) (![⟨1351865, by decide⟩,⟨1351909, by decide⟩,⟨1351952, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93895_1351953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93895 ⟨1351953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93895
    ⟨1351953, by decide⟩ (by decide) (![⟨1351865, by decide⟩,⟨1351909, by decide⟩,⟨1351952, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93895_1351953 node_context_11_93895_1351953
  intro a
  fin_cases a
  · exact context_12_375580_1351865
  · exact context_12_375581_1351909
  · exact context_12_375582_1351952
  · exact context_12_375583_903806

theorem unmarked_context_10_23473_1351954 : frontier 11 ⟨1351954, by decide⟩
    (prefixCache 10 23473) (prefixPartial 10 23473) = false := by
  decide +kernel

theorem node_context_10_23473_1351954 : EJMOriginalGlobalDAGData.nodes 11 ⟨1351954, by decide⟩ =
    .split (coordinate 10) (![⟨1351550, by decide⟩,⟨1351657, by decide⟩,⟨1351812, by decide⟩,⟨1351953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23473_1351954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23473 ⟨1351954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23473
    ⟨1351954, by decide⟩ (by decide) (![⟨1351550, by decide⟩,⟨1351657, by decide⟩,⟨1351812, by decide⟩,⟨1351953, by decide⟩]) unmarked_context_10_23473_1351954 node_context_10_23473_1351954
  intro a
  fin_cases a
  · exact context_11_93892_1351550
  · exact context_11_93893_1351657
  · exact context_11_93894_1351812
  · exact context_11_93895_1351953

theorem selected_cut_48212 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375584) = some ⟨12, 1, 0, 435790, 375584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375584_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375584 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375584 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375584, 1, 65536⟩
    (by decide) selected_cut_48212

theorem selected_cut_48213 : selected 9 ⟨1351994, by decide⟩
    (prefixPartial 12 375585) = some ⟨12, 2, 0, 1351994, 375585, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_375585_1351994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375585 ⟨1351994, by decide⟩ :=
  accepted_of_selected 12 375585 ⟨1351994, by decide⟩ ⟨12, 2, 0, 1351994, 375585, 2193, 65536⟩
    (by decide) selected_cut_48213

theorem selected_cut_48214 : selected 9 ⟨1352021, by decide⟩
    (prefixPartial 12 375586) = some ⟨12, 2, 0, 1352021, 375586, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_375586_1352021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375586 ⟨1352021, by decide⟩ :=
  accepted_of_selected 12 375586 ⟨1352021, by decide⟩ ⟨12, 2, 0, 1352021, 375586, 2173, 65536⟩
    (by decide) selected_cut_48214

theorem selected_cut_48215 : selected 9 ⟨1352050, by decide⟩
    (prefixPartial 12 375587) = some ⟨12, 2, 0, 1352050, 375587, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_375587_1352050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375587 ⟨1352050, by decide⟩ :=
  accepted_of_selected 12 375587 ⟨1352050, by decide⟩ ⟨12, 2, 0, 1352050, 375587, 1817, 65536⟩
    (by decide) selected_cut_48215

theorem unmarked_context_11_93896_1352051 : frontier 10 ⟨1352051, by decide⟩
    (prefixCache 11 93896) (prefixPartial 11 93896) = false := by
  decide +kernel

theorem node_context_11_93896_1352051 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352051, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1351994, by decide⟩,⟨1352021, by decide⟩,⟨1352050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93896_1352051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93896 ⟨1352051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93896
    ⟨1352051, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1351994, by decide⟩,⟨1352021, by decide⟩,⟨1352050, by decide⟩]) unmarked_context_11_93896_1352051 node_context_11_93896_1352051
  intro a
  fin_cases a
  · exact context_12_375584_435790
  · exact context_12_375585_1351994
  · exact context_12_375586_1352021
  · exact context_12_375587_1352050

theorem selected_cut_48216 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375588) = some ⟨12, 1, 0, 435790, 375588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375588_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375588 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375588 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375588, 1, 65536⟩
    (by decide) selected_cut_48216

theorem selected_cut_48217 : selected 9 ⟨1352092, by decide⟩
    (prefixPartial 12 375589) = some ⟨12, 2, 0, 1352092, 375589, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_375589_1352092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375589 ⟨1352092, by decide⟩ :=
  accepted_of_selected 12 375589 ⟨1352092, by decide⟩ ⟨12, 2, 0, 1352092, 375589, 2629, 65536⟩
    (by decide) selected_cut_48217

theorem selected_cut_48218 : selected 9 ⟨1352131, by decide⟩
    (prefixPartial 12 375590) = some ⟨12, 2, 0, 1352131, 375590, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_375590_1352131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375590 ⟨1352131, by decide⟩ :=
  accepted_of_selected 12 375590 ⟨1352131, by decide⟩ ⟨12, 2, 0, 1352131, 375590, 2477, 65536⟩
    (by decide) selected_cut_48218

theorem selected_cut_48219 : selected 9 ⟨1352164, by decide⟩
    (prefixPartial 12 375591) = some ⟨12, 2, 0, 1352164, 375591, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_375591_1352164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375591 ⟨1352164, by decide⟩ :=
  accepted_of_selected 12 375591 ⟨1352164, by decide⟩ ⟨12, 2, 0, 1352164, 375591, 2053, 65536⟩
    (by decide) selected_cut_48219

theorem unmarked_context_11_93897_1352165 : frontier 10 ⟨1352165, by decide⟩
    (prefixCache 11 93897) (prefixPartial 11 93897) = false := by
  decide +kernel

theorem node_context_11_93897_1352165 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352165, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1352092, by decide⟩,⟨1352131, by decide⟩,⟨1352164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93897_1352165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93897 ⟨1352165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93897
    ⟨1352165, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1352092, by decide⟩,⟨1352131, by decide⟩,⟨1352164, by decide⟩]) unmarked_context_11_93897_1352165 node_context_11_93897_1352165
  intro a
  fin_cases a
  · exact context_12_375588_435790
  · exact context_12_375589_1352092
  · exact context_12_375590_1352131
  · exact context_12_375591_1352164

theorem selected_cut_48220 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93898) = some ⟨11, 1, 0, 900587, 93898, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93898_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93898 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93898 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93898, 1, 262144⟩
    (by decide) selected_cut_48220

theorem selected_cut_48221 : selected 9 ⟨1352212, by decide⟩
    (prefixPartial 12 375596) = some ⟨12, 2, 0, 1352212, 375596, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_375596_1352212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375596 ⟨1352212, by decide⟩ :=
  accepted_of_selected 12 375596 ⟨1352212, by decide⟩ ⟨12, 2, 0, 1352212, 375596, 2261, 65536⟩
    (by decide) selected_cut_48221

theorem selected_cut_48222 : selected 9 ⟨1352247, by decide⟩
    (prefixPartial 12 375597) = some ⟨12, 2, 0, 1352247, 375597, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_375597_1352247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375597 ⟨1352247, by decide⟩ :=
  accepted_of_selected 12 375597 ⟨1352247, by decide⟩ ⟨12, 2, 0, 1352247, 375597, 2325, 65536⟩
    (by decide) selected_cut_48222

theorem selected_cut_48223 : selected 9 ⟨1352286, by decide⟩
    (prefixPartial 12 375598) = some ⟨12, 2, 0, 1352286, 375598, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_375598_1352286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375598 ⟨1352286, by decide⟩ :=
  accepted_of_selected 12 375598 ⟨1352286, by decide⟩ ⟨12, 2, 0, 1352286, 375598, 2201, 65536⟩
    (by decide) selected_cut_48223

theorem selected_cut_48224 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 375599) = some ⟨12, 1, 0, 903806, 375599, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375599_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375599 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 375599 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 375599, 1, 65536⟩
    (by decide) selected_cut_48224

theorem unmarked_context_11_93899_1352287 : frontier 10 ⟨1352287, by decide⟩
    (prefixCache 11 93899) (prefixPartial 11 93899) = false := by
  decide +kernel

theorem node_context_11_93899_1352287 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352287, by decide⟩ =
    .split (coordinate 11) (![⟨1352212, by decide⟩,⟨1352247, by decide⟩,⟨1352286, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93899_1352287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93899 ⟨1352287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93899
    ⟨1352287, by decide⟩ (by decide) (![⟨1352212, by decide⟩,⟨1352247, by decide⟩,⟨1352286, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93899_1352287 node_context_11_93899_1352287
  intro a
  fin_cases a
  · exact context_12_375596_1352212
  · exact context_12_375597_1352247
  · exact context_12_375598_1352286
  · exact context_12_375599_903806

theorem unmarked_context_10_23474_1352288 : frontier 11 ⟨1352288, by decide⟩
    (prefixCache 10 23474) (prefixPartial 10 23474) = false := by
  decide +kernel

theorem node_context_10_23474_1352288 : EJMOriginalGlobalDAGData.nodes 11 ⟨1352288, by decide⟩ =
    .split (coordinate 10) (![⟨1352051, by decide⟩,⟨1352165, by decide⟩,⟨900587, by decide⟩,⟨1352287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23474_1352288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23474 ⟨1352288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23474
    ⟨1352288, by decide⟩ (by decide) (![⟨1352051, by decide⟩,⟨1352165, by decide⟩,⟨900587, by decide⟩,⟨1352287, by decide⟩]) unmarked_context_10_23474_1352288 node_context_10_23474_1352288
  intro a
  fin_cases a
  · exact context_11_93896_1352051
  · exact context_11_93897_1352165
  · exact context_11_93898_900587
  · exact context_11_93899_1352287

theorem selected_cut_48225 : selected 9 ⟨766630, by decide⟩
    (prefixPartial 12 375600) = some ⟨12, 1, 0, 766630, 375600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375600_766630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375600 ⟨766630, by decide⟩ :=
  accepted_of_selected 12 375600 ⟨766630, by decide⟩ ⟨12, 1, 0, 766630, 375600, 1, 65536⟩
    (by decide) selected_cut_48225

theorem selected_cut_48226 : selected 9 ⟨1352322, by decide⟩
    (prefixPartial 12 375601) = some ⟨12, 2, 0, 1352322, 375601, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_375601_1352322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375601 ⟨1352322, by decide⟩ :=
  accepted_of_selected 12 375601 ⟨1352322, by decide⟩ ⟨12, 2, 0, 1352322, 375601, 2113, 65536⟩
    (by decide) selected_cut_48226

theorem selected_cut_48227 : selected 9 ⟨1352360, by decide⟩
    (prefixPartial 12 375602) = some ⟨12, 2, 0, 1352360, 375602, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_375602_1352360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375602 ⟨1352360, by decide⟩ :=
  accepted_of_selected 12 375602 ⟨1352360, by decide⟩ ⟨12, 2, 0, 1352360, 375602, 2145, 65536⟩
    (by decide) selected_cut_48227

theorem selected_cut_48228 : selected 9 ⟨1352390, by decide⟩
    (prefixPartial 12 375603) = some ⟨12, 2, 0, 1352390, 375603, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_375603_1352390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375603 ⟨1352390, by decide⟩ :=
  accepted_of_selected 12 375603 ⟨1352390, by decide⟩ ⟨12, 2, 0, 1352390, 375603, 1801, 65536⟩
    (by decide) selected_cut_48228

theorem unmarked_context_11_93900_1352391 : frontier 10 ⟨1352391, by decide⟩
    (prefixCache 11 93900) (prefixPartial 11 93900) = false := by
  decide +kernel

theorem node_context_11_93900_1352391 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352391, by decide⟩ =
    .split (coordinate 11) (![⟨766630, by decide⟩,⟨1352322, by decide⟩,⟨1352360, by decide⟩,⟨1352390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93900_1352391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93900 ⟨1352391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93900
    ⟨1352391, by decide⟩ (by decide) (![⟨766630, by decide⟩,⟨1352322, by decide⟩,⟨1352360, by decide⟩,⟨1352390, by decide⟩]) unmarked_context_11_93900_1352391 node_context_11_93900_1352391
  intro a
  fin_cases a
  · exact context_12_375600_766630
  · exact context_12_375601_1352322
  · exact context_12_375602_1352360
  · exact context_12_375603_1352390

theorem selected_cut_48229 : selected 9 ⟨1352434, by decide⟩
    (prefixPartial 12 375604) = some ⟨12, 2, 0, 1352434, 375604, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_375604_1352434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375604 ⟨1352434, by decide⟩ :=
  accepted_of_selected 12 375604 ⟨1352434, by decide⟩ ⟨12, 2, 0, 1352434, 375604, 2289, 65536⟩
    (by decide) selected_cut_48229

theorem selected_cut_48230 : selected 9 ⟨1048050, by decide⟩
    (prefixPartial 12 375605) = some ⟨12, 1, 0, 1048050, 375605, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375605_1048050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375605 ⟨1048050, by decide⟩ :=
  accepted_of_selected 12 375605 ⟨1048050, by decide⟩ ⟨12, 1, 0, 1048050, 375605, 1, 65536⟩
    (by decide) selected_cut_48230

theorem selected_cut_48231 : selected 9 ⟨1352480, by decide⟩
    (prefixPartial 12 375606) = some ⟨12, 2, 0, 1352480, 375606, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_375606_1352480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375606 ⟨1352480, by decide⟩ :=
  accepted_of_selected 12 375606 ⟨1352480, by decide⟩ ⟨12, 2, 0, 1352480, 375606, 2349, 65536⟩
    (by decide) selected_cut_48231

theorem selected_cut_48232 : selected 9 ⟨1352513, by decide⟩
    (prefixPartial 12 375607) = some ⟨12, 2, 0, 1352513, 375607, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_375607_1352513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375607 ⟨1352513, by decide⟩ :=
  accepted_of_selected 12 375607 ⟨1352513, by decide⟩ ⟨12, 2, 0, 1352513, 375607, 1917, 65536⟩
    (by decide) selected_cut_48232

theorem unmarked_context_11_93901_1352514 : frontier 10 ⟨1352514, by decide⟩
    (prefixCache 11 93901) (prefixPartial 11 93901) = false := by
  decide +kernel

theorem node_context_11_93901_1352514 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352514, by decide⟩ =
    .split (coordinate 11) (![⟨1352434, by decide⟩,⟨1048050, by decide⟩,⟨1352480, by decide⟩,⟨1352513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93901_1352514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93901 ⟨1352514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93901
    ⟨1352514, by decide⟩ (by decide) (![⟨1352434, by decide⟩,⟨1048050, by decide⟩,⟨1352480, by decide⟩,⟨1352513, by decide⟩]) unmarked_context_11_93901_1352514 node_context_11_93901_1352514
  intro a
  fin_cases a
  · exact context_12_375604_1352434
  · exact context_12_375605_1048050
  · exact context_12_375606_1352480
  · exact context_12_375607_1352513

theorem selected_cut_48233 : selected 10 ⟨1352566, by decide⟩
    (prefixPartial 11 93902) = some ⟨11, 2, 0, 1352566, 93902, 3393, 262144⟩ := by
  decide +kernel

theorem context_11_93902_1352566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93902 ⟨1352566, by decide⟩ :=
  accepted_of_selected 11 93902 ⟨1352566, by decide⟩ ⟨11, 2, 0, 1352566, 93902, 3393, 262144⟩
    (by decide) selected_cut_48233

theorem selected_cut_48234 : selected 10 ⟨1352632, by decide⟩
    (prefixPartial 11 93903) = some ⟨11, 2, 0, 1352632, 93903, 3681, 262144⟩ := by
  decide +kernel

theorem context_11_93903_1352632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93903 ⟨1352632, by decide⟩ :=
  accepted_of_selected 11 93903 ⟨1352632, by decide⟩ ⟨11, 2, 0, 1352632, 93903, 3681, 262144⟩
    (by decide) selected_cut_48234

theorem unmarked_context_10_23475_1352633 : frontier 11 ⟨1352633, by decide⟩
    (prefixCache 10 23475) (prefixPartial 10 23475) = false := by
  decide +kernel

theorem node_context_10_23475_1352633 : EJMOriginalGlobalDAGData.nodes 11 ⟨1352633, by decide⟩ =
    .split (coordinate 10) (![⟨1352391, by decide⟩,⟨1352514, by decide⟩,⟨1352566, by decide⟩,⟨1352632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23475_1352633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23475 ⟨1352633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23475
    ⟨1352633, by decide⟩ (by decide) (![⟨1352391, by decide⟩,⟨1352514, by decide⟩,⟨1352566, by decide⟩,⟨1352632, by decide⟩]) unmarked_context_10_23475_1352633 node_context_10_23475_1352633
  intro a
  fin_cases a
  · exact context_11_93900_1352391
  · exact context_11_93901_1352514
  · exact context_11_93902_1352566
  · exact context_11_93903_1352632

theorem unmarked_context_9_5868_1352634 : frontier 12 ⟨1352634, by decide⟩
    (prefixCache 9 5868) (prefixPartial 9 5868) = false := by
  decide +kernel

theorem node_context_9_5868_1352634 : EJMOriginalGlobalDAGData.nodes 12 ⟨1352634, by decide⟩ =
    .split (coordinate 9) (![⟨1351413, by decide⟩,⟨1351954, by decide⟩,⟨1352288, by decide⟩,⟨1352633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5868_1352634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5868 ⟨1352634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5868
    ⟨1352634, by decide⟩ (by decide) (![⟨1351413, by decide⟩,⟨1351954, by decide⟩,⟨1352288, by decide⟩,⟨1352633, by decide⟩]) unmarked_context_9_5868_1352634 node_context_9_5868_1352634
  intro a
  fin_cases a
  · exact context_10_23472_1351413
  · exact context_10_23473_1351954
  · exact context_10_23474_1352288
  · exact context_10_23475_1352633

theorem selected_cut_48235 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 375616) = some ⟨12, 1, 0, 1120586, 375616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375616_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375616 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 375616 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 375616, 1, 65536⟩
    (by decide) selected_cut_48235

theorem selected_cut_48236 : selected 9 ⟨1352655, by decide⟩
    (prefixPartial 12 375617) = some ⟨12, 2, 0, 1352655, 375617, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_375617_1352655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375617 ⟨1352655, by decide⟩ :=
  accepted_of_selected 12 375617 ⟨1352655, by decide⟩ ⟨12, 2, 0, 1352655, 375617, 1585, 65536⟩
    (by decide) selected_cut_48236

theorem selected_cut_48237 : selected 9 ⟨1352687, by decide⟩
    (prefixPartial 12 375618) = some ⟨12, 2, 0, 1352687, 375618, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_375618_1352687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375618 ⟨1352687, by decide⟩ :=
  accepted_of_selected 12 375618 ⟨1352687, by decide⟩ ⟨12, 2, 0, 1352687, 375618, 1793, 65536⟩
    (by decide) selected_cut_48237

theorem selected_cut_48238 : selected 9 ⟨1352712, by decide⟩
    (prefixPartial 12 375619) = some ⟨12, 2, 0, 1352712, 375619, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_375619_1352712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375619 ⟨1352712, by decide⟩ :=
  accepted_of_selected 12 375619 ⟨1352712, by decide⟩ ⟨12, 2, 0, 1352712, 375619, 1541, 65536⟩
    (by decide) selected_cut_48238

theorem unmarked_context_11_93904_1352713 : frontier 10 ⟨1352713, by decide⟩
    (prefixCache 11 93904) (prefixPartial 11 93904) = false := by
  decide +kernel

theorem node_context_11_93904_1352713 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352713, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨1352655, by decide⟩,⟨1352687, by decide⟩,⟨1352712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93904_1352713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93904 ⟨1352713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93904
    ⟨1352713, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨1352655, by decide⟩,⟨1352687, by decide⟩,⟨1352712, by decide⟩]) unmarked_context_11_93904_1352713 node_context_11_93904_1352713
  intro a
  fin_cases a
  · exact context_12_375616_1120586
  · exact context_12_375617_1352655
  · exact context_12_375618_1352687
  · exact context_12_375619_1352712

theorem selected_cut_48239 : selected 9 ⟨1352767, by decide⟩
    (prefixPartial 12 375620) = some ⟨12, 2, 0, 1352767, 375620, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_375620_1352767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375620 ⟨1352767, by decide⟩ :=
  accepted_of_selected 12 375620 ⟨1352767, by decide⟩ ⟨12, 2, 0, 1352767, 375620, 1989, 65536⟩
    (by decide) selected_cut_48239

theorem selected_cut_48240 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 375621) = some ⟨12, 1, 0, 1257136, 375621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375621_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375621 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 375621 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 375621, 1, 65536⟩
    (by decide) selected_cut_48240

theorem selected_cut_48241 : selected 9 ⟨1352812, by decide⟩
    (prefixPartial 12 375622) = some ⟨12, 2, 0, 1352812, 375622, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_375622_1352812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375622 ⟨1352812, by decide⟩ :=
  accepted_of_selected 12 375622 ⟨1352812, by decide⟩ ⟨12, 2, 0, 1352812, 375622, 1877, 65536⟩
    (by decide) selected_cut_48241

theorem selected_cut_48242 : selected 9 ⟨1352850, by decide⟩
    (prefixPartial 12 375623) = some ⟨12, 2, 0, 1352850, 375623, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_375623_1352850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375623 ⟨1352850, by decide⟩ :=
  accepted_of_selected 12 375623 ⟨1352850, by decide⟩ ⟨12, 2, 0, 1352850, 375623, 1649, 65536⟩
    (by decide) selected_cut_48242

theorem unmarked_context_11_93905_1352851 : frontier 10 ⟨1352851, by decide⟩
    (prefixCache 11 93905) (prefixPartial 11 93905) = false := by
  decide +kernel

theorem node_context_11_93905_1352851 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352851, by decide⟩ =
    .split (coordinate 11) (![⟨1352767, by decide⟩,⟨1257136, by decide⟩,⟨1352812, by decide⟩,⟨1352850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93905_1352851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93905 ⟨1352851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93905
    ⟨1352851, by decide⟩ (by decide) (![⟨1352767, by decide⟩,⟨1257136, by decide⟩,⟨1352812, by decide⟩,⟨1352850, by decide⟩]) unmarked_context_11_93905_1352851 node_context_11_93905_1352851
  intro a
  fin_cases a
  · exact context_12_375620_1352767
  · exact context_12_375621_1257136
  · exact context_12_375622_1352812
  · exact context_12_375623_1352850

theorem selected_cut_48243 : selected 9 ⟨1352878, by decide⟩
    (prefixPartial 12 375624) = some ⟨12, 2, 0, 1352878, 375624, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_375624_1352878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375624 ⟨1352878, by decide⟩ :=
  accepted_of_selected 12 375624 ⟨1352878, by decide⟩ ⟨12, 2, 0, 1352878, 375624, 1593, 65536⟩
    (by decide) selected_cut_48243

theorem selected_cut_48244 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 375625) = some ⟨12, 1, 0, 1025817, 375625, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375625_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375625 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 375625 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 375625, 1, 65536⟩
    (by decide) selected_cut_48244

theorem selected_cut_48245 : selected 9 ⟨1352906, by decide⟩
    (prefixPartial 12 375626) = some ⟨12, 2, 0, 1352906, 375626, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_375626_1352906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375626 ⟨1352906, by decide⟩ :=
  accepted_of_selected 12 375626 ⟨1352906, by decide⟩ ⟨12, 2, 0, 1352906, 375626, 1533, 65536⟩
    (by decide) selected_cut_48245

theorem selected_cut_48246 : selected 9 ⟨1352927, by decide⟩
    (prefixPartial 12 375627) = some ⟨12, 2, 0, 1352927, 375627, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_375627_1352927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375627 ⟨1352927, by decide⟩ :=
  accepted_of_selected 12 375627 ⟨1352927, by decide⟩ ⟨12, 2, 0, 1352927, 375627, 1365, 65536⟩
    (by decide) selected_cut_48246

theorem unmarked_context_11_93906_1352928 : frontier 10 ⟨1352928, by decide⟩
    (prefixCache 11 93906) (prefixPartial 11 93906) = false := by
  decide +kernel

theorem node_context_11_93906_1352928 : EJMOriginalGlobalDAGData.nodes 10 ⟨1352928, by decide⟩ =
    .split (coordinate 11) (![⟨1352878, by decide⟩,⟨1025817, by decide⟩,⟨1352906, by decide⟩,⟨1352927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93906_1352928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93906 ⟨1352928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93906
    ⟨1352928, by decide⟩ (by decide) (![⟨1352878, by decide⟩,⟨1025817, by decide⟩,⟨1352906, by decide⟩,⟨1352927, by decide⟩]) unmarked_context_11_93906_1352928 node_context_11_93906_1352928
  intro a
  fin_cases a
  · exact context_12_375624_1352878
  · exact context_12_375625_1025817
  · exact context_12_375626_1352906
  · exact context_12_375627_1352927

theorem selected_cut_48247 : selected 9 ⟨1352961, by decide⟩
    (prefixPartial 12 375628) = some ⟨12, 2, 0, 1352961, 375628, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_375628_1352961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375628 ⟨1352961, by decide⟩ :=
  accepted_of_selected 12 375628 ⟨1352961, by decide⟩ ⟨12, 2, 0, 1352961, 375628, 1689, 65536⟩
    (by decide) selected_cut_48247

theorem selected_cut_48248 : selected 9 ⟨1352986, by decide⟩
    (prefixPartial 12 375629) = some ⟨12, 2, 0, 1352986, 375629, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_375629_1352986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375629 ⟨1352986, by decide⟩ :=
  accepted_of_selected 12 375629 ⟨1352986, by decide⟩ ⟨12, 2, 0, 1352986, 375629, 1461, 65536⟩
    (by decide) selected_cut_48248

theorem selected_cut_48249 : selected 9 ⟨1353019, by decide⟩
    (prefixPartial 12 375630) = some ⟨12, 2, 0, 1353019, 375630, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_375630_1353019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375630 ⟨1353019, by decide⟩ :=
  accepted_of_selected 12 375630 ⟨1353019, by decide⟩ ⟨12, 2, 0, 1353019, 375630, 1593, 65536⟩
    (by decide) selected_cut_48249

theorem selected_cut_48250 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 375631) = some ⟨12, 1, 0, 903806, 375631, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375631_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375631 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 375631 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 375631, 1, 65536⟩
    (by decide) selected_cut_48250

theorem unmarked_context_11_93907_1353020 : frontier 10 ⟨1353020, by decide⟩
    (prefixCache 11 93907) (prefixPartial 11 93907) = false := by
  decide +kernel

theorem node_context_11_93907_1353020 : EJMOriginalGlobalDAGData.nodes 10 ⟨1353020, by decide⟩ =
    .split (coordinate 11) (![⟨1352961, by decide⟩,⟨1352986, by decide⟩,⟨1353019, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93907_1353020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93907 ⟨1353020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93907
    ⟨1353020, by decide⟩ (by decide) (![⟨1352961, by decide⟩,⟨1352986, by decide⟩,⟨1353019, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93907_1353020 node_context_11_93907_1353020
  intro a
  fin_cases a
  · exact context_12_375628_1352961
  · exact context_12_375629_1352986
  · exact context_12_375630_1353019
  · exact context_12_375631_903806

theorem unmarked_context_10_23476_1353021 : frontier 11 ⟨1353021, by decide⟩
    (prefixCache 10 23476) (prefixPartial 10 23476) = false := by
  decide +kernel

theorem node_context_10_23476_1353021 : EJMOriginalGlobalDAGData.nodes 11 ⟨1353021, by decide⟩ =
    .split (coordinate 10) (![⟨1352713, by decide⟩,⟨1352851, by decide⟩,⟨1352928, by decide⟩,⟨1353020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23476_1353021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23476 ⟨1353021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23476
    ⟨1353021, by decide⟩ (by decide) (![⟨1352713, by decide⟩,⟨1352851, by decide⟩,⟨1352928, by decide⟩,⟨1353020, by decide⟩]) unmarked_context_10_23476_1353021 node_context_10_23476_1353021
  intro a
  fin_cases a
  · exact context_11_93904_1352713
  · exact context_11_93905_1352851
  · exact context_11_93906_1352928
  · exact context_11_93907_1353020

theorem selected_cut_48251 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23477) = some ⟨10, 1, 0, 893098, 23477, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23477_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23477 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23477 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23477, 1, 1048576⟩
    (by decide) selected_cut_48251

theorem selected_cut_48252 : selected 10 ⟨1353082, by decide⟩
    (prefixPartial 11 93912) = some ⟨11, 2, 0, 1353082, 93912, 3349, 262144⟩ := by
  decide +kernel

theorem context_11_93912_1353082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93912 ⟨1353082, by decide⟩ :=
  accepted_of_selected 11 93912 ⟨1353082, by decide⟩ ⟨11, 2, 0, 1353082, 93912, 3349, 262144⟩
    (by decide) selected_cut_48252

theorem selected_cut_48253 : selected 10 ⟨1353149, by decide⟩
    (prefixPartial 11 93913) = some ⟨11, 2, 0, 1353149, 93913, 3425, 262144⟩ := by
  decide +kernel

theorem context_11_93913_1353149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93913 ⟨1353149, by decide⟩ :=
  accepted_of_selected 11 93913 ⟨1353149, by decide⟩ ⟨11, 2, 0, 1353149, 93913, 3425, 262144⟩
    (by decide) selected_cut_48253

theorem selected_cut_48254 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93914) = some ⟨11, 1, 0, 900587, 93914, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93914_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93914 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93914 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93914, 1, 262144⟩
    (by decide) selected_cut_48254

theorem selected_cut_48255 : selected 10 ⟨1353192, by decide⟩
    (prefixPartial 11 93915) = some ⟨11, 2, 0, 1353192, 93915, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_93915_1353192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93915 ⟨1353192, by decide⟩ :=
  accepted_of_selected 11 93915 ⟨1353192, by decide⟩ ⟨11, 2, 0, 1353192, 93915, 2009, 262144⟩
    (by decide) selected_cut_48255

theorem unmarked_context_10_23478_1353193 : frontier 11 ⟨1353193, by decide⟩
    (prefixCache 10 23478) (prefixPartial 10 23478) = false := by
  decide +kernel

theorem node_context_10_23478_1353193 : EJMOriginalGlobalDAGData.nodes 11 ⟨1353193, by decide⟩ =
    .split (coordinate 10) (![⟨1353082, by decide⟩,⟨1353149, by decide⟩,⟨900587, by decide⟩,⟨1353192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23478_1353193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23478 ⟨1353193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23478
    ⟨1353193, by decide⟩ (by decide) (![⟨1353082, by decide⟩,⟨1353149, by decide⟩,⟨900587, by decide⟩,⟨1353192, by decide⟩]) unmarked_context_10_23478_1353193 node_context_10_23478_1353193
  intro a
  fin_cases a
  · exact context_11_93912_1353082
  · exact context_11_93913_1353149
  · exact context_11_93914_900587
  · exact context_11_93915_1353192

theorem selected_cut_48256 : selected 10 ⟨1353283, by decide⟩
    (prefixPartial 11 93916) = some ⟨11, 2, 0, 1353283, 93916, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_93916_1353283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93916 ⟨1353283, by decide⟩ :=
  accepted_of_selected 11 93916 ⟨1353283, by decide⟩ ⟨11, 2, 0, 1353283, 93916, 3537, 262144⟩
    (by decide) selected_cut_48256

theorem selected_cut_48257 : selected 10 ⟨1353338, by decide⟩
    (prefixPartial 11 93917) = some ⟨11, 2, 0, 1353338, 93917, 3213, 262144⟩ := by
  decide +kernel

theorem context_11_93917_1353338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93917 ⟨1353338, by decide⟩ :=
  accepted_of_selected 11 93917 ⟨1353338, by decide⟩ ⟨11, 2, 0, 1353338, 93917, 3213, 262144⟩
    (by decide) selected_cut_48257

theorem selected_cut_48258 : selected 10 ⟨1353363, by decide⟩
    (prefixPartial 11 93918) = some ⟨11, 2, 0, 1353363, 93918, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_93918_1353363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93918 ⟨1353363, by decide⟩ :=
  accepted_of_selected 11 93918 ⟨1353363, by decide⟩ ⟨11, 2, 0, 1353363, 93918, 1705, 262144⟩
    (by decide) selected_cut_48258

theorem selected_cut_48259 : selected 10 ⟨1353387, by decide⟩
    (prefixPartial 11 93919) = some ⟨11, 2, 0, 1353387, 93919, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_93919_1353387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93919 ⟨1353387, by decide⟩ :=
  accepted_of_selected 11 93919 ⟨1353387, by decide⟩ ⟨11, 2, 0, 1353387, 93919, 1661, 262144⟩
    (by decide) selected_cut_48259

theorem unmarked_context_10_23479_1353388 : frontier 11 ⟨1353388, by decide⟩
    (prefixCache 10 23479) (prefixPartial 10 23479) = false := by
  decide +kernel

theorem node_context_10_23479_1353388 : EJMOriginalGlobalDAGData.nodes 11 ⟨1353388, by decide⟩ =
    .split (coordinate 10) (![⟨1353283, by decide⟩,⟨1353338, by decide⟩,⟨1353363, by decide⟩,⟨1353387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23479_1353388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23479 ⟨1353388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23479
    ⟨1353388, by decide⟩ (by decide) (![⟨1353283, by decide⟩,⟨1353338, by decide⟩,⟨1353363, by decide⟩,⟨1353387, by decide⟩]) unmarked_context_10_23479_1353388 node_context_10_23479_1353388
  intro a
  fin_cases a
  · exact context_11_93916_1353283
  · exact context_11_93917_1353338
  · exact context_11_93918_1353363
  · exact context_11_93919_1353387

theorem unmarked_context_9_5869_1353389 : frontier 12 ⟨1353389, by decide⟩
    (prefixCache 9 5869) (prefixPartial 9 5869) = false := by
  decide +kernel

theorem node_context_9_5869_1353389 : EJMOriginalGlobalDAGData.nodes 12 ⟨1353389, by decide⟩ =
    .split (coordinate 9) (![⟨1353021, by decide⟩,⟨893098, by decide⟩,⟨1353193, by decide⟩,⟨1353388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5869_1353389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5869 ⟨1353389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5869
    ⟨1353389, by decide⟩ (by decide) (![⟨1353021, by decide⟩,⟨893098, by decide⟩,⟨1353193, by decide⟩,⟨1353388, by decide⟩]) unmarked_context_9_5869_1353389 node_context_9_5869_1353389
  intro a
  fin_cases a
  · exact context_10_23476_1353021
  · exact context_10_23477_893098
  · exact context_10_23478_1353193
  · exact context_10_23479_1353388

theorem selected_cut_48260 : selected 10 ⟨1353402, by decide⟩
    (prefixPartial 11 93920) = some ⟨11, 2, 0, 1353402, 93920, 789, 262144⟩ := by
  decide +kernel

theorem context_11_93920_1353402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93920 ⟨1353402, by decide⟩ :=
  accepted_of_selected 11 93920 ⟨1353402, by decide⟩ ⟨11, 2, 0, 1353402, 93920, 789, 262144⟩
    (by decide) selected_cut_48260

theorem selected_cut_48261 : selected 10 ⟨1353446, by decide⟩
    (prefixPartial 11 93921) = some ⟨11, 2, 0, 1353446, 93921, 2677, 262144⟩ := by
  decide +kernel

theorem context_11_93921_1353446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93921 ⟨1353446, by decide⟩ :=
  accepted_of_selected 11 93921 ⟨1353446, by decide⟩ ⟨11, 2, 0, 1353446, 93921, 2677, 262144⟩
    (by decide) selected_cut_48261

theorem selected_cut_48262 : selected 10 ⟨1353475, by decide⟩
    (prefixPartial 11 93922) = some ⟨11, 2, 0, 1353475, 93922, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_93922_1353475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93922 ⟨1353475, by decide⟩ :=
  accepted_of_selected 11 93922 ⟨1353475, by decide⟩ ⟨11, 2, 0, 1353475, 93922, 2205, 262144⟩
    (by decide) selected_cut_48262

theorem selected_cut_48263 : selected 10 ⟨1353503, by decide⟩
    (prefixPartial 11 93923) = some ⟨11, 2, 0, 1353503, 93923, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_93923_1353503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93923 ⟨1353503, by decide⟩ :=
  accepted_of_selected 11 93923 ⟨1353503, by decide⟩ ⟨11, 2, 0, 1353503, 93923, 1417, 262144⟩
    (by decide) selected_cut_48263

theorem unmarked_context_10_23480_1353504 : frontier 11 ⟨1353504, by decide⟩
    (prefixCache 10 23480) (prefixPartial 10 23480) = false := by
  decide +kernel

theorem node_context_10_23480_1353504 : EJMOriginalGlobalDAGData.nodes 11 ⟨1353504, by decide⟩ =
    .split (coordinate 10) (![⟨1353402, by decide⟩,⟨1353446, by decide⟩,⟨1353475, by decide⟩,⟨1353503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23480_1353504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23480 ⟨1353504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23480
    ⟨1353504, by decide⟩ (by decide) (![⟨1353402, by decide⟩,⟨1353446, by decide⟩,⟨1353475, by decide⟩,⟨1353503, by decide⟩]) unmarked_context_10_23480_1353504 node_context_10_23480_1353504
  intro a
  fin_cases a
  · exact context_11_93920_1353402
  · exact context_11_93921_1353446
  · exact context_11_93922_1353475
  · exact context_11_93923_1353503

theorem selected_cut_48264 : selected 10 ⟨1353529, by decide⟩
    (prefixPartial 11 93924) = some ⟨11, 2, 0, 1353529, 93924, 1833, 262144⟩ := by
  decide +kernel

theorem context_11_93924_1353529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93924 ⟨1353529, by decide⟩ :=
  accepted_of_selected 11 93924 ⟨1353529, by decide⟩ ⟨11, 2, 0, 1353529, 93924, 1833, 262144⟩
    (by decide) selected_cut_48264

theorem selected_cut_48265 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 93925) = some ⟨11, 1, 0, 1192826, 93925, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93925_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93925 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 93925 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 93925, 1, 262144⟩
    (by decide) selected_cut_48265

theorem selected_cut_48266 : selected 10 ⟨1353552, by decide⟩
    (prefixPartial 11 93926) = some ⟨11, 2, 0, 1353552, 93926, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_93926_1353552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93926 ⟨1353552, by decide⟩ :=
  accepted_of_selected 11 93926 ⟨1353552, by decide⟩ ⟨11, 2, 0, 1353552, 93926, 1653, 262144⟩
    (by decide) selected_cut_48266

theorem selected_cut_48267 : selected 10 ⟨1353564, by decide⟩
    (prefixPartial 11 93927) = some ⟨11, 2, 0, 1353564, 93927, 1085, 262144⟩ := by
  decide +kernel

theorem context_11_93927_1353564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93927 ⟨1353564, by decide⟩ :=
  accepted_of_selected 11 93927 ⟨1353564, by decide⟩ ⟨11, 2, 0, 1353564, 93927, 1085, 262144⟩
    (by decide) selected_cut_48267

theorem unmarked_context_10_23481_1353565 : frontier 11 ⟨1353565, by decide⟩
    (prefixCache 10 23481) (prefixPartial 10 23481) = false := by
  decide +kernel

theorem node_context_10_23481_1353565 : EJMOriginalGlobalDAGData.nodes 11 ⟨1353565, by decide⟩ =
    .split (coordinate 10) (![⟨1353529, by decide⟩,⟨1192826, by decide⟩,⟨1353552, by decide⟩,⟨1353564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23481_1353565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23481 ⟨1353565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23481
    ⟨1353565, by decide⟩ (by decide) (![⟨1353529, by decide⟩,⟨1192826, by decide⟩,⟨1353552, by decide⟩,⟨1353564, by decide⟩]) unmarked_context_10_23481_1353565 node_context_10_23481_1353565
  intro a
  fin_cases a
  · exact context_11_93924_1353529
  · exact context_11_93925_1192826
  · exact context_11_93926_1353552
  · exact context_11_93927_1353564

theorem selected_cut_48268 : selected 11 ⟨1353594, by decide⟩
    (prefixPartial 10 23482) = some ⟨10, 2, 0, 1353594, 23482, 1405, 1048576⟩ := by
  decide +kernel

theorem context_10_23482_1353594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23482 ⟨1353594, by decide⟩ :=
  accepted_of_selected 10 23482 ⟨1353594, by decide⟩ ⟨10, 2, 0, 1353594, 23482, 1405, 1048576⟩
    (by decide) selected_cut_48268

theorem selected_cut_48269 : selected 11 ⟨1353663, by decide⟩
    (prefixPartial 10 23483) = some ⟨10, 2, 0, 1353663, 23483, 3381, 1048576⟩ := by
  decide +kernel

theorem context_10_23483_1353663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23483 ⟨1353663, by decide⟩ :=
  accepted_of_selected 10 23483 ⟨1353663, by decide⟩ ⟨10, 2, 0, 1353663, 23483, 3381, 1048576⟩
    (by decide) selected_cut_48269

theorem unmarked_context_9_5870_1353664 : frontier 12 ⟨1353664, by decide⟩
    (prefixCache 9 5870) (prefixPartial 9 5870) = false := by
  decide +kernel

theorem node_context_9_5870_1353664 : EJMOriginalGlobalDAGData.nodes 12 ⟨1353664, by decide⟩ =
    .split (coordinate 9) (![⟨1353504, by decide⟩,⟨1353565, by decide⟩,⟨1353594, by decide⟩,⟨1353663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5870_1353664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5870 ⟨1353664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5870
    ⟨1353664, by decide⟩ (by decide) (![⟨1353504, by decide⟩,⟨1353565, by decide⟩,⟨1353594, by decide⟩,⟨1353663, by decide⟩]) unmarked_context_9_5870_1353664 node_context_9_5870_1353664
  intro a
  fin_cases a
  · exact context_10_23480_1353504
  · exact context_10_23481_1353565
  · exact context_10_23482_1353594
  · exact context_10_23483_1353663

theorem selected_cut_48270 : selected 11 ⟨1353732, by decide⟩
    (prefixPartial 10 23484) = some ⟨10, 2, 0, 1353732, 23484, 3369, 1048576⟩ := by
  decide +kernel

theorem context_10_23484_1353732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23484 ⟨1353732, by decide⟩ :=
  accepted_of_selected 10 23484 ⟨1353732, by decide⟩ ⟨10, 2, 0, 1353732, 23484, 3369, 1048576⟩
    (by decide) selected_cut_48270

theorem selected_cut_48271 : selected 11 ⟨1353776, by decide⟩
    (prefixPartial 10 23485) = some ⟨10, 2, 0, 1353776, 23485, 1949, 1048576⟩ := by
  decide +kernel

theorem context_10_23485_1353776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23485 ⟨1353776, by decide⟩ :=
  accepted_of_selected 10 23485 ⟨1353776, by decide⟩ ⟨10, 2, 0, 1353776, 23485, 1949, 1048576⟩
    (by decide) selected_cut_48271

theorem selected_cut_48272 : selected 11 ⟨1353800, by decide⟩
    (prefixPartial 10 23486) = some ⟨10, 2, 0, 1353800, 23486, 745, 1048576⟩ := by
  decide +kernel

theorem context_10_23486_1353800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23486 ⟨1353800, by decide⟩ :=
  accepted_of_selected 10 23486 ⟨1353800, by decide⟩ ⟨10, 2, 0, 1353800, 23486, 745, 1048576⟩
    (by decide) selected_cut_48272

theorem selected_cut_48273 : selected 11 ⟨1353810, by decide⟩
    (prefixPartial 10 23487) = some ⟨10, 2, 0, 1353810, 23487, 89, 1048576⟩ := by
  decide +kernel

theorem context_10_23487_1353810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23487 ⟨1353810, by decide⟩ :=
  accepted_of_selected 10 23487 ⟨1353810, by decide⟩ ⟨10, 2, 0, 1353810, 23487, 89, 1048576⟩
    (by decide) selected_cut_48273

theorem unmarked_context_9_5871_1353811 : frontier 12 ⟨1353811, by decide⟩
    (prefixCache 9 5871) (prefixPartial 9 5871) = false := by
  decide +kernel

theorem node_context_9_5871_1353811 : EJMOriginalGlobalDAGData.nodes 12 ⟨1353811, by decide⟩ =
    .split (coordinate 9) (![⟨1353732, by decide⟩,⟨1353776, by decide⟩,⟨1353800, by decide⟩,⟨1353810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5871_1353811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5871 ⟨1353811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5871
    ⟨1353811, by decide⟩ (by decide) (![⟨1353732, by decide⟩,⟨1353776, by decide⟩,⟨1353800, by decide⟩,⟨1353810, by decide⟩]) unmarked_context_9_5871_1353811 node_context_9_5871_1353811
  intro a
  fin_cases a
  · exact context_10_23484_1353732
  · exact context_10_23485_1353776
  · exact context_10_23486_1353800
  · exact context_10_23487_1353810

theorem unmarked_context_8_1467_1353812 : frontier 13 ⟨1353812, by decide⟩
    (prefixCache 8 1467) (prefixPartial 8 1467) = false := by
  decide +kernel

theorem node_context_8_1467_1353812 : EJMOriginalGlobalDAGData.nodes 13 ⟨1353812, by decide⟩ =
    .split (coordinate 8) (![⟨1352634, by decide⟩,⟨1353389, by decide⟩,⟨1353664, by decide⟩,⟨1353811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1467_1353812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1467 ⟨1353812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1467
    ⟨1353812, by decide⟩ (by decide) (![⟨1352634, by decide⟩,⟨1353389, by decide⟩,⟨1353664, by decide⟩,⟨1353811, by decide⟩]) unmarked_context_8_1467_1353812 node_context_8_1467_1353812
  intro a
  fin_cases a
  · exact context_9_5868_1352634
  · exact context_9_5869_1353389
  · exact context_9_5870_1353664
  · exact context_9_5871_1353811

theorem unmarked_context_7_366_1353813 : frontier 14 ⟨1353813, by decide⟩
    (prefixCache 7 366) (prefixPartial 7 366) = false := by
  decide +kernel

theorem node_context_7_366_1353813 : EJMOriginalGlobalDAGData.nodes 14 ⟨1353813, by decide⟩ =
    .split (coordinate 7) (![⟨1345142, by decide⟩,⟨1347941, by decide⟩,⟨1351107, by decide⟩,⟨1353812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_366_1353813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 366 ⟨1353813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 366
    ⟨1353813, by decide⟩ (by decide) (![⟨1345142, by decide⟩,⟨1347941, by decide⟩,⟨1351107, by decide⟩,⟨1353812, by decide⟩]) unmarked_context_7_366_1353813 node_context_7_366_1353813
  intro a
  fin_cases a
  · exact context_8_1464_1345142
  · exact context_8_1465_1347941
  · exact context_8_1466_1351107
  · exact context_8_1467_1353812

theorem selected_cut_48274 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93952) = some ⟨11, 1, 0, 434745, 93952, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93952_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93952 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93952 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93952, 1, 262144⟩
    (by decide) selected_cut_48274

theorem selected_cut_48275 : selected 10 ⟨1353877, by decide⟩
    (prefixPartial 11 93953) = some ⟨11, 2, 0, 1353877, 93953, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_93953_1353877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93953 ⟨1353877, by decide⟩ :=
  accepted_of_selected 11 93953 ⟨1353877, by decide⟩ ⟨11, 2, 0, 1353877, 93953, 2009, 262144⟩
    (by decide) selected_cut_48275

theorem selected_cut_48276 : selected 10 ⟨1353947, by decide⟩
    (prefixPartial 11 93954) = some ⟨11, 2, 0, 1353947, 93954, 3029, 262144⟩ := by
  decide +kernel

theorem context_11_93954_1353947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93954 ⟨1353947, by decide⟩ :=
  accepted_of_selected 11 93954 ⟨1353947, by decide⟩ ⟨11, 2, 0, 1353947, 93954, 3029, 262144⟩
    (by decide) selected_cut_48276

theorem selected_cut_48277 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 375820) = some ⟨12, 1, 0, 448748, 375820, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375820_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375820 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 375820 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 375820, 1, 65536⟩
    (by decide) selected_cut_48277

theorem selected_cut_48278 : selected 9 ⟨1354008, by decide⟩
    (prefixPartial 12 375821) = some ⟨12, 2, 0, 1354008, 375821, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_375821_1354008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375821 ⟨1354008, by decide⟩ :=
  accepted_of_selected 12 375821 ⟨1354008, by decide⟩ ⟨12, 2, 0, 1354008, 375821, 2901, 65536⟩
    (by decide) selected_cut_48278

theorem selected_cut_48279 : selected 9 ⟨1354062, by decide⟩
    (prefixPartial 12 375822) = some ⟨12, 2, 0, 1354062, 375822, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_375822_1354062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375822 ⟨1354062, by decide⟩ :=
  accepted_of_selected 12 375822 ⟨1354062, by decide⟩ ⟨12, 2, 0, 1354062, 375822, 3005, 65536⟩
    (by decide) selected_cut_48279

theorem selected_cut_48280 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 375823) = some ⟨12, 1, 0, 760511, 375823, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375823_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375823 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 375823 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 375823, 1, 65536⟩
    (by decide) selected_cut_48280

theorem unmarked_context_11_93955_1354063 : frontier 10 ⟨1354063, by decide⟩
    (prefixCache 11 93955) (prefixPartial 11 93955) = false := by
  decide +kernel

theorem node_context_11_93955_1354063 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354063, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1354008, by decide⟩,⟨1354062, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93955_1354063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93955 ⟨1354063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93955
    ⟨1354063, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1354008, by decide⟩,⟨1354062, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_93955_1354063 node_context_11_93955_1354063
  intro a
  fin_cases a
  · exact context_12_375820_448748
  · exact context_12_375821_1354008
  · exact context_12_375822_1354062
  · exact context_12_375823_760511

theorem unmarked_context_10_23488_1354064 : frontier 11 ⟨1354064, by decide⟩
    (prefixCache 10 23488) (prefixPartial 10 23488) = false := by
  decide +kernel

theorem node_context_10_23488_1354064 : EJMOriginalGlobalDAGData.nodes 11 ⟨1354064, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1353877, by decide⟩,⟨1353947, by decide⟩,⟨1354063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23488_1354064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23488 ⟨1354064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23488
    ⟨1354064, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1353877, by decide⟩,⟨1353947, by decide⟩,⟨1354063, by decide⟩]) unmarked_context_10_23488_1354064 node_context_10_23488_1354064
  intro a
  fin_cases a
  · exact context_11_93952_434745
  · exact context_11_93953_1353877
  · exact context_11_93954_1353947
  · exact context_11_93955_1354063

theorem selected_cut_48281 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 375824) = some ⟨12, 1, 0, 985390, 375824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375824_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375824 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 375824 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 375824, 1, 65536⟩
    (by decide) selected_cut_48281

theorem selected_cut_48282 : selected 9 ⟨1354115, by decide⟩
    (prefixPartial 12 375825) = some ⟨12, 2, 0, 1354115, 375825, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_375825_1354115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375825 ⟨1354115, by decide⟩ :=
  accepted_of_selected 12 375825 ⟨1354115, by decide⟩ ⟨12, 2, 0, 1354115, 375825, 2557, 65536⟩
    (by decide) selected_cut_48282

theorem selected_cut_48283 : selected 9 ⟨1354163, by decide⟩
    (prefixPartial 12 375826) = some ⟨12, 2, 0, 1354163, 375826, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_375826_1354163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375826 ⟨1354163, by decide⟩ :=
  accepted_of_selected 12 375826 ⟨1354163, by decide⟩ ⟨12, 2, 0, 1354163, 375826, 2393, 65536⟩
    (by decide) selected_cut_48283

theorem selected_cut_48284 : selected 9 ⟨1354214, by decide⟩
    (prefixPartial 12 375827) = some ⟨12, 2, 0, 1354214, 375827, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_375827_1354214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375827 ⟨1354214, by decide⟩ :=
  accepted_of_selected 12 375827 ⟨1354214, by decide⟩ ⟨12, 2, 0, 1354214, 375827, 2621, 65536⟩
    (by decide) selected_cut_48284

theorem unmarked_context_11_93956_1354215 : frontier 10 ⟨1354215, by decide⟩
    (prefixCache 11 93956) (prefixPartial 11 93956) = false := by
  decide +kernel

theorem node_context_11_93956_1354215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354215, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1354115, by decide⟩,⟨1354163, by decide⟩,⟨1354214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93956_1354215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93956 ⟨1354215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93956
    ⟨1354215, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1354115, by decide⟩,⟨1354163, by decide⟩,⟨1354214, by decide⟩]) unmarked_context_11_93956_1354215 node_context_11_93956_1354215
  intro a
  fin_cases a
  · exact context_12_375824_985390
  · exact context_12_375825_1354115
  · exact context_12_375826_1354163
  · exact context_12_375827_1354214

theorem selected_cut_48285 : selected 9 ⟨1354272, by decide⟩
    (prefixPartial 12 375828) = some ⟨12, 2, 0, 1354272, 375828, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_375828_1354272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375828 ⟨1354272, by decide⟩ :=
  accepted_of_selected 12 375828 ⟨1354272, by decide⟩ ⟨12, 2, 0, 1354272, 375828, 2969, 65536⟩
    (by decide) selected_cut_48285

theorem selected_cut_48286 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 375829) = some ⟨12, 1, 0, 1172003, 375829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375829_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375829 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 375829 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 375829, 1, 65536⟩
    (by decide) selected_cut_48286

theorem selected_cut_48287 : selected 9 ⟨1354335, by decide⟩
    (prefixPartial 12 375830) = some ⟨12, 2, 0, 1354335, 375830, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_375830_1354335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375830 ⟨1354335, by decide⟩ :=
  accepted_of_selected 12 375830 ⟨1354335, by decide⟩ ⟨12, 2, 0, 1354335, 375830, 2933, 65536⟩
    (by decide) selected_cut_48287

theorem selected_cut_48288 : selected 9 ⟨347235, by decide⟩
    (prefixPartial 12 375831) = some ⟨12, 1, 0, 347235, 375831, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375831_347235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375831 ⟨347235, by decide⟩ :=
  accepted_of_selected 12 375831 ⟨347235, by decide⟩ ⟨12, 1, 0, 347235, 375831, 1, 65536⟩
    (by decide) selected_cut_48288

theorem unmarked_context_11_93957_1354336 : frontier 10 ⟨1354336, by decide⟩
    (prefixCache 11 93957) (prefixPartial 11 93957) = false := by
  decide +kernel

theorem node_context_11_93957_1354336 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354336, by decide⟩ =
    .split (coordinate 11) (![⟨1354272, by decide⟩,⟨1172003, by decide⟩,⟨1354335, by decide⟩,⟨347235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93957_1354336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93957 ⟨1354336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93957
    ⟨1354336, by decide⟩ (by decide) (![⟨1354272, by decide⟩,⟨1172003, by decide⟩,⟨1354335, by decide⟩,⟨347235, by decide⟩]) unmarked_context_11_93957_1354336 node_context_11_93957_1354336
  intro a
  fin_cases a
  · exact context_12_375828_1354272
  · exact context_12_375829_1172003
  · exact context_12_375830_1354335
  · exact context_12_375831_347235

theorem selected_cut_48289 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 375832) = some ⟨12, 1, 0, 994572, 375832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375832_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375832 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 375832 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 375832, 1, 65536⟩
    (by decide) selected_cut_48289

theorem selected_cut_48290 : selected 9 ⟨1354384, by decide⟩
    (prefixPartial 12 375833) = some ⟨12, 2, 0, 1354384, 375833, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_375833_1354384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375833 ⟨1354384, by decide⟩ :=
  accepted_of_selected 12 375833 ⟨1354384, by decide⟩ ⟨12, 2, 0, 1354384, 375833, 2629, 65536⟩
    (by decide) selected_cut_48290

theorem selected_cut_48291 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 375834) = some ⟨12, 1, 0, 806997, 375834, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375834_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375834 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 375834 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 375834, 1, 65536⟩
    (by decide) selected_cut_48291

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
