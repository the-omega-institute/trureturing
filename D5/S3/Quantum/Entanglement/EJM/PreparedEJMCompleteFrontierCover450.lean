/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover449
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_84888_1181274 : frontier 10 ⟨1181274, by decide⟩
    (prefixCache 11 84888) (prefixPartial 11 84888) = false := by
  decide +kernel

theorem node_context_11_84888_1181274 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181274, by decide⟩ =
    .split (coordinate 11) (![⟨1181170, by decide⟩,⟨1181198, by decide⟩,⟨1181233, by decide⟩,⟨1181273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84888_1181274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84888 ⟨1181274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84888
    ⟨1181274, by decide⟩ (by decide) (![⟨1181170, by decide⟩,⟨1181198, by decide⟩,⟨1181233, by decide⟩,⟨1181273, by decide⟩]) unmarked_context_11_84888_1181274 node_context_11_84888_1181274
  intro a
  fin_cases a
  · exact context_12_339552_1181170
  · exact context_12_339553_1181198
  · exact context_12_339554_1181233
  · exact context_12_339555_1181273

theorem selected_cut_43204 : selected 9 ⟨1181305, by decide⟩
    (prefixPartial 12 339556) = some ⟨12, 2, 0, 1181305, 339556, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_339556_1181305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339556 ⟨1181305, by decide⟩ :=
  accepted_of_selected 12 339556 ⟨1181305, by decide⟩ ⟨12, 2, 0, 1181305, 339556, 1897, 65536⟩
    (by decide) selected_cut_43204

theorem selected_cut_43205 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 339557) = some ⟨12, 1, 0, 642794, 339557, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339557_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339557 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 339557 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 339557, 1, 65536⟩
    (by decide) selected_cut_43205

theorem selected_cut_43206 : selected 9 ⟨1181335, by decide⟩
    (prefixPartial 12 339558) = some ⟨12, 2, 0, 1181335, 339558, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_339558_1181335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339558 ⟨1181335, by decide⟩ :=
  accepted_of_selected 12 339558 ⟨1181335, by decide⟩ ⟨12, 2, 0, 1181335, 339558, 1861, 65536⟩
    (by decide) selected_cut_43206

theorem selected_cut_43207 : selected 9 ⟨1181370, by decide⟩
    (prefixPartial 12 339559) = some ⟨12, 2, 0, 1181370, 339559, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_339559_1181370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339559 ⟨1181370, by decide⟩ :=
  accepted_of_selected 12 339559 ⟨1181370, by decide⟩ ⟨12, 2, 0, 1181370, 339559, 2121, 65536⟩
    (by decide) selected_cut_43207

theorem unmarked_context_11_84889_1181371 : frontier 10 ⟨1181371, by decide⟩
    (prefixCache 11 84889) (prefixPartial 11 84889) = false := by
  decide +kernel

theorem node_context_11_84889_1181371 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181371, by decide⟩ =
    .split (coordinate 11) (![⟨1181305, by decide⟩,⟨642794, by decide⟩,⟨1181335, by decide⟩,⟨1181370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84889_1181371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84889 ⟨1181371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84889
    ⟨1181371, by decide⟩ (by decide) (![⟨1181305, by decide⟩,⟨642794, by decide⟩,⟨1181335, by decide⟩,⟨1181370, by decide⟩]) unmarked_context_11_84889_1181371 node_context_11_84889_1181371
  intro a
  fin_cases a
  · exact context_12_339556_1181305
  · exact context_12_339557_642794
  · exact context_12_339558_1181335
  · exact context_12_339559_1181370

theorem selected_cut_43208 : selected 10 ⟨1181424, by decide⟩
    (prefixPartial 11 84890) = some ⟨11, 2, 0, 1181424, 84890, 3177, 262144⟩ := by
  decide +kernel

theorem context_11_84890_1181424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84890 ⟨1181424, by decide⟩ :=
  accepted_of_selected 11 84890 ⟨1181424, by decide⟩ ⟨11, 2, 0, 1181424, 84890, 3177, 262144⟩
    (by decide) selected_cut_43208

theorem selected_cut_43209 : selected 9 ⟨1181443, by decide⟩
    (prefixPartial 12 339564) = some ⟨12, 2, 0, 1181443, 339564, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_339564_1181443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339564 ⟨1181443, by decide⟩ :=
  accepted_of_selected 12 339564 ⟨1181443, by decide⟩ ⟨12, 2, 0, 1181443, 339564, 1365, 65536⟩
    (by decide) selected_cut_43209

theorem selected_cut_43210 : selected 9 ⟨1181464, by decide⟩
    (prefixPartial 12 339565) = some ⟨12, 2, 0, 1181464, 339565, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_339565_1181464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339565 ⟨1181464, by decide⟩ :=
  accepted_of_selected 12 339565 ⟨1181464, by decide⟩ ⟨12, 2, 0, 1181464, 339565, 1393, 65536⟩
    (by decide) selected_cut_43210

theorem selected_cut_43211 : selected 9 ⟨1181486, by decide⟩
    (prefixPartial 12 339566) = some ⟨12, 2, 0, 1181486, 339566, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_339566_1181486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339566 ⟨1181486, by decide⟩ :=
  accepted_of_selected 12 339566 ⟨1181486, by decide⟩ ⟨12, 2, 0, 1181486, 339566, 1321, 65536⟩
    (by decide) selected_cut_43211

theorem selected_cut_43212 : selected 9 ⟨1181541, by decide⟩
    (prefixPartial 12 339567) = some ⟨12, 2, 0, 1181541, 339567, 681, 65536⟩ := by
  decide +kernel

theorem context_12_339567_1181541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339567 ⟨1181541, by decide⟩ :=
  accepted_of_selected 12 339567 ⟨1181541, by decide⟩ ⟨12, 2, 0, 1181541, 339567, 681, 65536⟩
    (by decide) selected_cut_43212

theorem unmarked_context_11_84891_1181542 : frontier 10 ⟨1181542, by decide⟩
    (prefixCache 11 84891) (prefixPartial 11 84891) = false := by
  decide +kernel

theorem node_context_11_84891_1181542 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181542, by decide⟩ =
    .split (coordinate 11) (![⟨1181443, by decide⟩,⟨1181464, by decide⟩,⟨1181486, by decide⟩,⟨1181541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84891_1181542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84891 ⟨1181542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84891
    ⟨1181542, by decide⟩ (by decide) (![⟨1181443, by decide⟩,⟨1181464, by decide⟩,⟨1181486, by decide⟩,⟨1181541, by decide⟩]) unmarked_context_11_84891_1181542 node_context_11_84891_1181542
  intro a
  fin_cases a
  · exact context_12_339564_1181443
  · exact context_12_339565_1181464
  · exact context_12_339566_1181486
  · exact context_12_339567_1181541

theorem unmarked_context_10_21222_1181543 : frontier 11 ⟨1181543, by decide⟩
    (prefixCache 10 21222) (prefixPartial 10 21222) = false := by
  decide +kernel

theorem node_context_10_21222_1181543 : EJMOriginalGlobalDAGData.nodes 11 ⟨1181543, by decide⟩ =
    .split (coordinate 10) (![⟨1181274, by decide⟩,⟨1181371, by decide⟩,⟨1181424, by decide⟩,⟨1181542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21222_1181543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21222 ⟨1181543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21222
    ⟨1181543, by decide⟩ (by decide) (![⟨1181274, by decide⟩,⟨1181371, by decide⟩,⟨1181424, by decide⟩,⟨1181542, by decide⟩]) unmarked_context_10_21222_1181543 node_context_10_21222_1181543
  intro a
  fin_cases a
  · exact context_11_84888_1181274
  · exact context_11_84889_1181371
  · exact context_11_84890_1181424
  · exact context_11_84891_1181542

theorem selected_cut_43213 : selected 9 ⟨1181568, by decide⟩
    (prefixPartial 12 339568) = some ⟨12, 2, 0, 1181568, 339568, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_339568_1181568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339568 ⟨1181568, by decide⟩ :=
  accepted_of_selected 12 339568 ⟨1181568, by decide⟩ ⟨12, 2, 0, 1181568, 339568, 1485, 65536⟩
    (by decide) selected_cut_43213

theorem selected_cut_43214 : selected 9 ⟨1181592, by decide⟩
    (prefixPartial 12 339569) = some ⟨12, 2, 0, 1181592, 339569, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_339569_1181592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339569 ⟨1181592, by decide⟩ :=
  accepted_of_selected 12 339569 ⟨1181592, by decide⟩ ⟨12, 2, 0, 1181592, 339569, 1465, 65536⟩
    (by decide) selected_cut_43214

theorem selected_cut_43215 : selected 9 ⟨1181616, by decide⟩
    (prefixPartial 12 339570) = some ⟨12, 2, 0, 1181616, 339570, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_339570_1181616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339570 ⟨1181616, by decide⟩ :=
  accepted_of_selected 12 339570 ⟨1181616, by decide⟩ ⟨12, 2, 0, 1181616, 339570, 1393, 65536⟩
    (by decide) selected_cut_43215

theorem selected_cut_43216 : selected 9 ⟨1181644, by decide⟩
    (prefixPartial 12 339571) = some ⟨12, 2, 0, 1181644, 339571, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_339571_1181644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339571 ⟨1181644, by decide⟩ :=
  accepted_of_selected 12 339571 ⟨1181644, by decide⟩ ⟨12, 2, 0, 1181644, 339571, 1657, 65536⟩
    (by decide) selected_cut_43216

theorem unmarked_context_11_84892_1181645 : frontier 10 ⟨1181645, by decide⟩
    (prefixCache 11 84892) (prefixPartial 11 84892) = false := by
  decide +kernel

theorem node_context_11_84892_1181645 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181645, by decide⟩ =
    .split (coordinate 11) (![⟨1181568, by decide⟩,⟨1181592, by decide⟩,⟨1181616, by decide⟩,⟨1181644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84892_1181645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84892 ⟨1181645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84892
    ⟨1181645, by decide⟩ (by decide) (![⟨1181568, by decide⟩,⟨1181592, by decide⟩,⟨1181616, by decide⟩,⟨1181644, by decide⟩]) unmarked_context_11_84892_1181645 node_context_11_84892_1181645
  intro a
  fin_cases a
  · exact context_12_339568_1181568
  · exact context_12_339569_1181592
  · exact context_12_339570_1181616
  · exact context_12_339571_1181644

theorem selected_cut_43217 : selected 9 ⟨1181669, by decide⟩
    (prefixPartial 12 339572) = some ⟨12, 2, 0, 1181669, 339572, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_339572_1181669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339572 ⟨1181669, by decide⟩ :=
  accepted_of_selected 12 339572 ⟨1181669, by decide⟩ ⟨12, 2, 0, 1181669, 339572, 1357, 65536⟩
    (by decide) selected_cut_43217

theorem selected_cut_43218 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 339573) = some ⟨12, 1, 0, 642794, 339573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339573_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339573 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 339573 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 339573, 1, 65536⟩
    (by decide) selected_cut_43218

theorem selected_cut_43219 : selected 9 ⟨1181694, by decide⟩
    (prefixPartial 12 339574) = some ⟨12, 2, 0, 1181694, 339574, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_339574_1181694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339574 ⟨1181694, by decide⟩ :=
  accepted_of_selected 12 339574 ⟨1181694, by decide⟩ ⟨12, 2, 0, 1181694, 339574, 1377, 65536⟩
    (by decide) selected_cut_43219

theorem selected_cut_43220 : selected 9 ⟨1181721, by decide⟩
    (prefixPartial 12 339575) = some ⟨12, 2, 0, 1181721, 339575, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_339575_1181721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339575 ⟨1181721, by decide⟩ :=
  accepted_of_selected 12 339575 ⟨1181721, by decide⟩ ⟨12, 2, 0, 1181721, 339575, 1533, 65536⟩
    (by decide) selected_cut_43220

theorem unmarked_context_11_84893_1181722 : frontier 10 ⟨1181722, by decide⟩
    (prefixCache 11 84893) (prefixPartial 11 84893) = false := by
  decide +kernel

theorem node_context_11_84893_1181722 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181722, by decide⟩ =
    .split (coordinate 11) (![⟨1181669, by decide⟩,⟨642794, by decide⟩,⟨1181694, by decide⟩,⟨1181721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84893_1181722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84893 ⟨1181722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84893
    ⟨1181722, by decide⟩ (by decide) (![⟨1181669, by decide⟩,⟨642794, by decide⟩,⟨1181694, by decide⟩,⟨1181721, by decide⟩]) unmarked_context_11_84893_1181722 node_context_11_84893_1181722
  intro a
  fin_cases a
  · exact context_12_339572_1181669
  · exact context_12_339573_642794
  · exact context_12_339574_1181694
  · exact context_12_339575_1181721

theorem selected_cut_43221 : selected 10 ⟨1181778, by decide⟩
    (prefixPartial 11 84894) = some ⟨11, 2, 0, 1181778, 84894, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_84894_1181778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84894 ⟨1181778, by decide⟩ :=
  accepted_of_selected 11 84894 ⟨1181778, by decide⟩ ⟨11, 2, 0, 1181778, 84894, 3469, 262144⟩
    (by decide) selected_cut_43221

theorem selected_cut_43222 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84895) = some ⟨11, 1, 0, 977886, 84895, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84895_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84895 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84895 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84895, 1, 262144⟩
    (by decide) selected_cut_43222

theorem unmarked_context_10_21223_1181779 : frontier 11 ⟨1181779, by decide⟩
    (prefixCache 10 21223) (prefixPartial 10 21223) = false := by
  decide +kernel

theorem node_context_10_21223_1181779 : EJMOriginalGlobalDAGData.nodes 11 ⟨1181779, by decide⟩ =
    .split (coordinate 10) (![⟨1181645, by decide⟩,⟨1181722, by decide⟩,⟨1181778, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21223_1181779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21223 ⟨1181779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21223
    ⟨1181779, by decide⟩ (by decide) (![⟨1181645, by decide⟩,⟨1181722, by decide⟩,⟨1181778, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21223_1181779 node_context_10_21223_1181779
  intro a
  fin_cases a
  · exact context_11_84892_1181645
  · exact context_11_84893_1181722
  · exact context_11_84894_1181778
  · exact context_11_84895_977886

theorem unmarked_context_9_5305_1181780 : frontier 12 ⟨1181780, by decide⟩
    (prefixCache 9 5305) (prefixPartial 9 5305) = false := by
  decide +kernel

theorem node_context_9_5305_1181780 : EJMOriginalGlobalDAGData.nodes 12 ⟨1181780, by decide⟩ =
    .split (coordinate 9) (![⟨1181136, by decide⟩,⟨893098, by decide⟩,⟨1181543, by decide⟩,⟨1181779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5305_1181780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5305 ⟨1181780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5305
    ⟨1181780, by decide⟩ (by decide) (![⟨1181136, by decide⟩,⟨893098, by decide⟩,⟨1181543, by decide⟩,⟨1181779, by decide⟩]) unmarked_context_9_5305_1181780 node_context_9_5305_1181780
  intro a
  fin_cases a
  · exact context_10_21220_1181136
  · exact context_10_21221_893098
  · exact context_10_21222_1181543
  · exact context_10_21223_1181779

theorem selected_cut_43223 : selected 10 ⟨1181843, by decide⟩
    (prefixPartial 11 84896) = some ⟨11, 2, 0, 1181843, 84896, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_84896_1181843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84896 ⟨1181843, by decide⟩ :=
  accepted_of_selected 11 84896 ⟨1181843, by decide⟩ ⟨11, 2, 0, 1181843, 84896, 3169, 262144⟩
    (by decide) selected_cut_43223

theorem selected_cut_43224 : selected 9 ⟨1181872, by decide⟩
    (prefixPartial 12 339588) = some ⟨12, 2, 0, 1181872, 339588, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_339588_1181872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339588 ⟨1181872, by decide⟩ :=
  accepted_of_selected 12 339588 ⟨1181872, by decide⟩ ⟨12, 2, 0, 1181872, 339588, 1409, 65536⟩
    (by decide) selected_cut_43224

theorem selected_cut_43225 : selected 9 ⟨1181890, by decide⟩
    (prefixPartial 12 339589) = some ⟨12, 2, 0, 1181890, 339589, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_339589_1181890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339589 ⟨1181890, by decide⟩ :=
  accepted_of_selected 12 339589 ⟨1181890, by decide⟩ ⟨12, 2, 0, 1181890, 339589, 1417, 65536⟩
    (by decide) selected_cut_43225

theorem selected_cut_43226 : selected 9 ⟨1181913, by decide⟩
    (prefixPartial 12 339590) = some ⟨12, 2, 0, 1181913, 339590, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_339590_1181913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339590 ⟨1181913, by decide⟩ :=
  accepted_of_selected 12 339590 ⟨1181913, by decide⟩ ⟨12, 2, 0, 1181913, 339590, 1365, 65536⟩
    (by decide) selected_cut_43226

theorem selected_cut_43227 : selected 9 ⟨1181949, by decide⟩
    (prefixPartial 12 339591) = some ⟨12, 2, 0, 1181949, 339591, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_339591_1181949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339591 ⟨1181949, by decide⟩ :=
  accepted_of_selected 12 339591 ⟨1181949, by decide⟩ ⟨12, 2, 0, 1181949, 339591, 1625, 65536⟩
    (by decide) selected_cut_43227

theorem unmarked_context_11_84897_1181950 : frontier 10 ⟨1181950, by decide⟩
    (prefixCache 11 84897) (prefixPartial 11 84897) = false := by
  decide +kernel

theorem node_context_11_84897_1181950 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181950, by decide⟩ =
    .split (coordinate 11) (![⟨1181872, by decide⟩,⟨1181890, by decide⟩,⟨1181913, by decide⟩,⟨1181949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84897_1181950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84897 ⟨1181950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84897
    ⟨1181950, by decide⟩ (by decide) (![⟨1181872, by decide⟩,⟨1181890, by decide⟩,⟨1181913, by decide⟩,⟨1181949, by decide⟩]) unmarked_context_11_84897_1181950 node_context_11_84897_1181950
  intro a
  fin_cases a
  · exact context_12_339588_1181872
  · exact context_12_339589_1181890
  · exact context_12_339590_1181913
  · exact context_12_339591_1181949

theorem selected_cut_43228 : selected 10 ⟨1182011, by decide⟩
    (prefixPartial 11 84898) = some ⟨11, 2, 0, 1182011, 84898, 3889, 262144⟩ := by
  decide +kernel

theorem context_11_84898_1182011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84898 ⟨1182011, by decide⟩ :=
  accepted_of_selected 11 84898 ⟨1182011, by decide⟩ ⟨11, 2, 0, 1182011, 84898, 3889, 262144⟩
    (by decide) selected_cut_43228

theorem selected_cut_43229 : selected 9 ⟨1182027, by decide⟩
    (prefixPartial 12 339596) = some ⟨12, 2, 0, 1182027, 339596, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_339596_1182027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339596 ⟨1182027, by decide⟩ :=
  accepted_of_selected 12 339596 ⟨1182027, by decide⟩ ⟨12, 2, 0, 1182027, 339596, 1077, 65536⟩
    (by decide) selected_cut_43229

theorem selected_cut_43230 : selected 9 ⟨1182042, by decide⟩
    (prefixPartial 12 339597) = some ⟨12, 2, 0, 1182042, 339597, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_339597_1182042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339597 ⟨1182042, by decide⟩ :=
  accepted_of_selected 12 339597 ⟨1182042, by decide⟩ ⟨12, 2, 0, 1182042, 339597, 1185, 65536⟩
    (by decide) selected_cut_43230

theorem selected_cut_43231 : selected 9 ⟨1182067, by decide⟩
    (prefixPartial 12 339598) = some ⟨12, 2, 0, 1182067, 339598, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_339598_1182067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339598 ⟨1182067, by decide⟩ :=
  accepted_of_selected 12 339598 ⟨1182067, by decide⟩ ⟨12, 2, 0, 1182067, 339598, 1105, 65536⟩
    (by decide) selected_cut_43231

theorem selected_cut_43232 : selected 9 ⟨1182094, by decide⟩
    (prefixPartial 12 339599) = some ⟨12, 2, 0, 1182094, 339599, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_339599_1182094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339599 ⟨1182094, by decide⟩ :=
  accepted_of_selected 12 339599 ⟨1182094, by decide⟩ ⟨12, 2, 0, 1182094, 339599, 1317, 65536⟩
    (by decide) selected_cut_43232

theorem unmarked_context_11_84899_1182095 : frontier 10 ⟨1182095, by decide⟩
    (prefixCache 11 84899) (prefixPartial 11 84899) = false := by
  decide +kernel

theorem node_context_11_84899_1182095 : EJMOriginalGlobalDAGData.nodes 10 ⟨1182095, by decide⟩ =
    .split (coordinate 11) (![⟨1182027, by decide⟩,⟨1182042, by decide⟩,⟨1182067, by decide⟩,⟨1182094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84899_1182095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84899 ⟨1182095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84899
    ⟨1182095, by decide⟩ (by decide) (![⟨1182027, by decide⟩,⟨1182042, by decide⟩,⟨1182067, by decide⟩,⟨1182094, by decide⟩]) unmarked_context_11_84899_1182095 node_context_11_84899_1182095
  intro a
  fin_cases a
  · exact context_12_339596_1182027
  · exact context_12_339597_1182042
  · exact context_12_339598_1182067
  · exact context_12_339599_1182094

theorem unmarked_context_10_21224_1182096 : frontier 11 ⟨1182096, by decide⟩
    (prefixCache 10 21224) (prefixPartial 10 21224) = false := by
  decide +kernel

theorem node_context_10_21224_1182096 : EJMOriginalGlobalDAGData.nodes 11 ⟨1182096, by decide⟩ =
    .split (coordinate 10) (![⟨1181843, by decide⟩,⟨1181950, by decide⟩,⟨1182011, by decide⟩,⟨1182095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21224_1182096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21224 ⟨1182096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21224
    ⟨1182096, by decide⟩ (by decide) (![⟨1181843, by decide⟩,⟨1181950, by decide⟩,⟨1182011, by decide⟩,⟨1182095, by decide⟩]) unmarked_context_10_21224_1182096 node_context_10_21224_1182096
  intro a
  fin_cases a
  · exact context_11_84896_1181843
  · exact context_11_84897_1181950
  · exact context_11_84898_1182011
  · exact context_11_84899_1182095

theorem selected_cut_43233 : selected 10 ⟨1182162, by decide⟩
    (prefixPartial 11 84900) = some ⟨11, 2, 0, 1182162, 84900, 2741, 262144⟩ := by
  decide +kernel

theorem context_11_84900_1182162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84900 ⟨1182162, by decide⟩ :=
  accepted_of_selected 11 84900 ⟨1182162, by decide⟩ ⟨11, 2, 0, 1182162, 84900, 2741, 262144⟩
    (by decide) selected_cut_43233

theorem selected_cut_43234 : selected 10 ⟨1182224, by decide⟩
    (prefixPartial 11 84901) = some ⟨11, 2, 0, 1182224, 84901, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_84901_1182224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84901 ⟨1182224, by decide⟩ :=
  accepted_of_selected 11 84901 ⟨1182224, by decide⟩ ⟨11, 2, 0, 1182224, 84901, 3273, 262144⟩
    (by decide) selected_cut_43234

theorem selected_cut_43235 : selected 10 ⟨1182279, by decide⟩
    (prefixPartial 11 84902) = some ⟨11, 2, 0, 1182279, 84902, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_84902_1182279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84902 ⟨1182279, by decide⟩ :=
  accepted_of_selected 11 84902 ⟨1182279, by decide⟩ ⟨11, 2, 0, 1182279, 84902, 2885, 262144⟩
    (by decide) selected_cut_43235

theorem selected_cut_43236 : selected 10 ⟨1182345, by decide⟩
    (prefixPartial 11 84903) = some ⟨11, 2, 0, 1182345, 84903, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_84903_1182345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84903 ⟨1182345, by decide⟩ :=
  accepted_of_selected 11 84903 ⟨1182345, by decide⟩ ⟨11, 2, 0, 1182345, 84903, 3537, 262144⟩
    (by decide) selected_cut_43236

theorem unmarked_context_10_21225_1182346 : frontier 11 ⟨1182346, by decide⟩
    (prefixCache 10 21225) (prefixPartial 10 21225) = false := by
  decide +kernel

theorem node_context_10_21225_1182346 : EJMOriginalGlobalDAGData.nodes 11 ⟨1182346, by decide⟩ =
    .split (coordinate 10) (![⟨1182162, by decide⟩,⟨1182224, by decide⟩,⟨1182279, by decide⟩,⟨1182345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21225_1182346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21225 ⟨1182346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21225
    ⟨1182346, by decide⟩ (by decide) (![⟨1182162, by decide⟩,⟨1182224, by decide⟩,⟨1182279, by decide⟩,⟨1182345, by decide⟩]) unmarked_context_10_21225_1182346 node_context_10_21225_1182346
  intro a
  fin_cases a
  · exact context_11_84900_1182162
  · exact context_11_84901_1182224
  · exact context_11_84902_1182279
  · exact context_11_84903_1182345

theorem selected_cut_43237 : selected 10 ⟨1182381, by decide⟩
    (prefixPartial 11 84904) = some ⟨11, 2, 0, 1182381, 84904, 1913, 262144⟩ := by
  decide +kernel

theorem context_11_84904_1182381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84904 ⟨1182381, by decide⟩ :=
  accepted_of_selected 11 84904 ⟨1182381, by decide⟩ ⟨11, 2, 0, 1182381, 84904, 1913, 262144⟩
    (by decide) selected_cut_43237

theorem selected_cut_43238 : selected 10 ⟨1182435, by decide⟩
    (prefixPartial 11 84905) = some ⟨11, 2, 0, 1182435, 84905, 2921, 262144⟩ := by
  decide +kernel

theorem context_11_84905_1182435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84905 ⟨1182435, by decide⟩ :=
  accepted_of_selected 11 84905 ⟨1182435, by decide⟩ ⟨11, 2, 0, 1182435, 84905, 2921, 262144⟩
    (by decide) selected_cut_43238

theorem selected_cut_43239 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84906) = some ⟨11, 1, 0, 1109453, 84906, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84906_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84906 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84906 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84906, 1, 262144⟩
    (by decide) selected_cut_43239

theorem selected_cut_43240 : selected 10 ⟨1182463, by decide⟩
    (prefixPartial 11 84907) = some ⟨11, 2, 0, 1182463, 84907, 1409, 262144⟩ := by
  decide +kernel

theorem context_11_84907_1182463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84907 ⟨1182463, by decide⟩ :=
  accepted_of_selected 11 84907 ⟨1182463, by decide⟩ ⟨11, 2, 0, 1182463, 84907, 1409, 262144⟩
    (by decide) selected_cut_43240

theorem unmarked_context_10_21226_1182464 : frontier 11 ⟨1182464, by decide⟩
    (prefixCache 10 21226) (prefixPartial 10 21226) = false := by
  decide +kernel

theorem node_context_10_21226_1182464 : EJMOriginalGlobalDAGData.nodes 11 ⟨1182464, by decide⟩ =
    .split (coordinate 10) (![⟨1182381, by decide⟩,⟨1182435, by decide⟩,⟨1109453, by decide⟩,⟨1182463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21226_1182464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21226 ⟨1182464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21226
    ⟨1182464, by decide⟩ (by decide) (![⟨1182381, by decide⟩,⟨1182435, by decide⟩,⟨1109453, by decide⟩,⟨1182463, by decide⟩]) unmarked_context_10_21226_1182464 node_context_10_21226_1182464
  intro a
  fin_cases a
  · exact context_11_84904_1182381
  · exact context_11_84905_1182435
  · exact context_11_84906_1109453
  · exact context_11_84907_1182463

theorem selected_cut_43241 : selected 10 ⟨1182508, by decide⟩
    (prefixPartial 11 84908) = some ⟨11, 2, 0, 1182508, 84908, 1789, 262144⟩ := by
  decide +kernel

theorem context_11_84908_1182508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84908 ⟨1182508, by decide⟩ :=
  accepted_of_selected 11 84908 ⟨1182508, by decide⟩ ⟨11, 2, 0, 1182508, 84908, 1789, 262144⟩
    (by decide) selected_cut_43241

theorem selected_cut_43242 : selected 10 ⟨1182556, by decide⟩
    (prefixPartial 11 84909) = some ⟨11, 2, 0, 1182556, 84909, 2529, 262144⟩ := by
  decide +kernel

theorem context_11_84909_1182556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84909 ⟨1182556, by decide⟩ :=
  accepted_of_selected 11 84909 ⟨1182556, by decide⟩ ⟨11, 2, 0, 1182556, 84909, 2529, 262144⟩
    (by decide) selected_cut_43242

theorem selected_cut_43243 : selected 10 ⟨1182585, by decide⟩
    (prefixPartial 11 84910) = some ⟨11, 2, 0, 1182585, 84910, 1565, 262144⟩ := by
  decide +kernel

theorem context_11_84910_1182585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84910 ⟨1182585, by decide⟩ :=
  accepted_of_selected 11 84910 ⟨1182585, by decide⟩ ⟨11, 2, 0, 1182585, 84910, 1565, 262144⟩
    (by decide) selected_cut_43243

theorem selected_cut_43244 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84911) = some ⟨11, 1, 0, 977886, 84911, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84911_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84911 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84911 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84911, 1, 262144⟩
    (by decide) selected_cut_43244

theorem unmarked_context_10_21227_1182586 : frontier 11 ⟨1182586, by decide⟩
    (prefixCache 10 21227) (prefixPartial 10 21227) = false := by
  decide +kernel

theorem node_context_10_21227_1182586 : EJMOriginalGlobalDAGData.nodes 11 ⟨1182586, by decide⟩ =
    .split (coordinate 10) (![⟨1182508, by decide⟩,⟨1182556, by decide⟩,⟨1182585, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21227_1182586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21227 ⟨1182586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21227
    ⟨1182586, by decide⟩ (by decide) (![⟨1182508, by decide⟩,⟨1182556, by decide⟩,⟨1182585, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21227_1182586 node_context_10_21227_1182586
  intro a
  fin_cases a
  · exact context_11_84908_1182508
  · exact context_11_84909_1182556
  · exact context_11_84910_1182585
  · exact context_11_84911_977886

theorem unmarked_context_9_5306_1182587 : frontier 12 ⟨1182587, by decide⟩
    (prefixCache 9 5306) (prefixPartial 9 5306) = false := by
  decide +kernel

theorem node_context_9_5306_1182587 : EJMOriginalGlobalDAGData.nodes 12 ⟨1182587, by decide⟩ =
    .split (coordinate 9) (![⟨1182096, by decide⟩,⟨1182346, by decide⟩,⟨1182464, by decide⟩,⟨1182586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5306_1182587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5306 ⟨1182587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5306
    ⟨1182587, by decide⟩ (by decide) (![⟨1182096, by decide⟩,⟨1182346, by decide⟩,⟨1182464, by decide⟩,⟨1182586, by decide⟩]) unmarked_context_9_5306_1182587 node_context_9_5306_1182587
  intro a
  fin_cases a
  · exact context_10_21224_1182096
  · exact context_10_21225_1182346
  · exact context_10_21226_1182464
  · exact context_10_21227_1182586

theorem selected_cut_43245 : selected 10 ⟨1182621, by decide⟩
    (prefixPartial 11 84912) = some ⟨11, 2, 0, 1182621, 84912, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_84912_1182621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84912 ⟨1182621, by decide⟩ :=
  accepted_of_selected 11 84912 ⟨1182621, by decide⟩ ⟨11, 2, 0, 1182621, 84912, 1961, 262144⟩
    (by decide) selected_cut_43245

theorem selected_cut_43246 : selected 10 ⟨1182661, by decide⟩
    (prefixPartial 11 84913) = some ⟨11, 2, 0, 1182661, 84913, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_84913_1182661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84913 ⟨1182661, by decide⟩ :=
  accepted_of_selected 11 84913 ⟨1182661, by decide⟩ ⟨11, 2, 0, 1182661, 84913, 2165, 262144⟩
    (by decide) selected_cut_43246

theorem selected_cut_43247 : selected 10 ⟨1182685, by decide⟩
    (prefixPartial 11 84914) = some ⟨11, 2, 0, 1182685, 84914, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_84914_1182685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84914 ⟨1182685, by decide⟩ :=
  accepted_of_selected 11 84914 ⟨1182685, by decide⟩ ⟨11, 2, 0, 1182685, 84914, 1353, 262144⟩
    (by decide) selected_cut_43247

theorem selected_cut_43248 : selected 10 ⟨1182703, by decide⟩
    (prefixPartial 11 84915) = some ⟨11, 2, 0, 1182703, 84915, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_84915_1182703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84915 ⟨1182703, by decide⟩ :=
  accepted_of_selected 11 84915 ⟨1182703, by decide⟩ ⟨11, 2, 0, 1182703, 84915, 1049, 262144⟩
    (by decide) selected_cut_43248

theorem unmarked_context_10_21228_1182704 : frontier 11 ⟨1182704, by decide⟩
    (prefixCache 10 21228) (prefixPartial 10 21228) = false := by
  decide +kernel

theorem node_context_10_21228_1182704 : EJMOriginalGlobalDAGData.nodes 11 ⟨1182704, by decide⟩ =
    .split (coordinate 10) (![⟨1182621, by decide⟩,⟨1182661, by decide⟩,⟨1182685, by decide⟩,⟨1182703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21228_1182704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21228 ⟨1182704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21228
    ⟨1182704, by decide⟩ (by decide) (![⟨1182621, by decide⟩,⟨1182661, by decide⟩,⟨1182685, by decide⟩,⟨1182703, by decide⟩]) unmarked_context_10_21228_1182704 node_context_10_21228_1182704
  intro a
  fin_cases a
  · exact context_11_84912_1182621
  · exact context_11_84913_1182661
  · exact context_11_84914_1182685
  · exact context_11_84915_1182703

theorem selected_cut_43249 : selected 11 ⟨1182751, by decide⟩
    (prefixPartial 10 21229) = some ⟨10, 2, 0, 1182751, 21229, 2745, 1048576⟩ := by
  decide +kernel

theorem context_10_21229_1182751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21229 ⟨1182751, by decide⟩ :=
  accepted_of_selected 10 21229 ⟨1182751, by decide⟩ ⟨10, 2, 0, 1182751, 21229, 2745, 1048576⟩
    (by decide) selected_cut_43249

theorem selected_cut_43250 : selected 11 ⟨1182800, by decide⟩
    (prefixPartial 10 21230) = some ⟨10, 2, 0, 1182800, 21230, 1941, 1048576⟩ := by
  decide +kernel

theorem context_10_21230_1182800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21230 ⟨1182800, by decide⟩ :=
  accepted_of_selected 10 21230 ⟨1182800, by decide⟩ ⟨10, 2, 0, 1182800, 21230, 1941, 1048576⟩
    (by decide) selected_cut_43250

theorem selected_cut_43251 : selected 11 ⟨1182811, by decide⟩
    (prefixPartial 10 21231) = some ⟨10, 2, 0, 1182811, 21231, 253, 1048576⟩ := by
  decide +kernel

theorem context_10_21231_1182811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21231 ⟨1182811, by decide⟩ :=
  accepted_of_selected 10 21231 ⟨1182811, by decide⟩ ⟨10, 2, 0, 1182811, 21231, 253, 1048576⟩
    (by decide) selected_cut_43251

theorem unmarked_context_9_5307_1182812 : frontier 12 ⟨1182812, by decide⟩
    (prefixCache 9 5307) (prefixPartial 9 5307) = false := by
  decide +kernel

theorem node_context_9_5307_1182812 : EJMOriginalGlobalDAGData.nodes 12 ⟨1182812, by decide⟩ =
    .split (coordinate 9) (![⟨1182704, by decide⟩,⟨1182751, by decide⟩,⟨1182800, by decide⟩,⟨1182811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5307_1182812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5307 ⟨1182812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5307
    ⟨1182812, by decide⟩ (by decide) (![⟨1182704, by decide⟩,⟨1182751, by decide⟩,⟨1182800, by decide⟩,⟨1182811, by decide⟩]) unmarked_context_9_5307_1182812 node_context_9_5307_1182812
  intro a
  fin_cases a
  · exact context_10_21228_1182704
  · exact context_10_21229_1182751
  · exact context_10_21230_1182800
  · exact context_10_21231_1182811

theorem unmarked_context_8_1326_1182813 : frontier 13 ⟨1182813, by decide⟩
    (prefixCache 8 1326) (prefixPartial 8 1326) = false := by
  decide +kernel

theorem node_context_8_1326_1182813 : EJMOriginalGlobalDAGData.nodes 13 ⟨1182813, by decide⟩ =
    .split (coordinate 8) (![⟨1180755, by decide⟩,⟨1181780, by decide⟩,⟨1182587, by decide⟩,⟨1182812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1326_1182813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1326 ⟨1182813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1326
    ⟨1182813, by decide⟩ (by decide) (![⟨1180755, by decide⟩,⟨1181780, by decide⟩,⟨1182587, by decide⟩,⟨1182812, by decide⟩]) unmarked_context_8_1326_1182813 node_context_8_1326_1182813
  intro a
  fin_cases a
  · exact context_9_5304_1180755
  · exact context_9_5305_1181780
  · exact context_9_5306_1182587
  · exact context_9_5307_1182812

theorem selected_cut_43252 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84928) = some ⟨11, 1, 0, 434745, 84928, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84928_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84928 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84928 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84928, 1, 262144⟩
    (by decide) selected_cut_43252

theorem selected_cut_43253 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339716) = some ⟨12, 1, 0, 448748, 339716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339716_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339716 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339716 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339716, 1, 65536⟩
    (by decide) selected_cut_43253

theorem selected_cut_43254 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 339717) = some ⟨12, 1, 0, 34034, 339717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339717_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339717 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 339717 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 339717, 1, 65536⟩
    (by decide) selected_cut_43254

theorem selected_cut_43255 : selected 9 ⟨1182897, by decide⟩
    (prefixPartial 12 339718) = some ⟨12, 2, 0, 1182897, 339718, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_339718_1182897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339718 ⟨1182897, by decide⟩ :=
  accepted_of_selected 12 339718 ⟨1182897, by decide⟩ ⟨12, 2, 0, 1182897, 339718, 3181, 65536⟩
    (by decide) selected_cut_43255

theorem selected_cut_43256 : selected 9 ⟨1182975, by decide⟩
    (prefixPartial 12 339719) = some ⟨12, 2, 0, 1182975, 339719, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_339719_1182975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339719 ⟨1182975, by decide⟩ :=
  accepted_of_selected 12 339719 ⟨1182975, by decide⟩ ⟨12, 2, 0, 1182975, 339719, 3629, 65536⟩
    (by decide) selected_cut_43256

theorem unmarked_context_11_84929_1182976 : frontier 10 ⟨1182976, by decide⟩
    (prefixCache 11 84929) (prefixPartial 11 84929) = false := by
  decide +kernel

theorem node_context_11_84929_1182976 : EJMOriginalGlobalDAGData.nodes 10 ⟨1182976, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1182897, by decide⟩,⟨1182975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84929_1182976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84929 ⟨1182976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84929
    ⟨1182976, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1182897, by decide⟩,⟨1182975, by decide⟩]) unmarked_context_11_84929_1182976 node_context_11_84929_1182976
  intro a
  fin_cases a
  · exact context_12_339716_448748
  · exact context_12_339717_34034
  · exact context_12_339718_1182897
  · exact context_12_339719_1182975

theorem selected_cut_43257 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339720) = some ⟨12, 1, 0, 448748, 339720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339720_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339720 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339720 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339720, 1, 65536⟩
    (by decide) selected_cut_43257

theorem selected_cut_43258 : selected 9 ⟨1183078, by decide⟩
    (prefixPartial 12 339721) = some ⟨12, 2, 0, 1183078, 339721, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_339721_1183078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339721 ⟨1183078, by decide⟩ :=
  accepted_of_selected 12 339721 ⟨1183078, by decide⟩ ⟨12, 2, 0, 1183078, 339721, 3673, 65536⟩
    (by decide) selected_cut_43258

theorem selected_cut_43259 : selected 9 ⟨1183139, by decide⟩
    (prefixPartial 12 339722) = some ⟨12, 2, 0, 1183139, 339722, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_339722_1183139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339722 ⟨1183139, by decide⟩ :=
  accepted_of_selected 12 339722 ⟨1183139, by decide⟩ ⟨12, 2, 0, 1183139, 339722, 3065, 65536⟩
    (by decide) selected_cut_43259

theorem selected_cut_43260 : selected 9 ⟨1183207, by decide⟩
    (prefixPartial 12 339723) = some ⟨12, 2, 0, 1183207, 339723, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_339723_1183207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339723 ⟨1183207, by decide⟩ :=
  accepted_of_selected 12 339723 ⟨1183207, by decide⟩ ⟨12, 2, 0, 1183207, 339723, 3633, 65536⟩
    (by decide) selected_cut_43260

theorem unmarked_context_11_84930_1183208 : frontier 10 ⟨1183208, by decide⟩
    (prefixCache 11 84930) (prefixPartial 11 84930) = false := by
  decide +kernel

theorem node_context_11_84930_1183208 : EJMOriginalGlobalDAGData.nodes 10 ⟨1183208, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1183078, by decide⟩,⟨1183139, by decide⟩,⟨1183207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84930_1183208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84930 ⟨1183208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84930
    ⟨1183208, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1183078, by decide⟩,⟨1183139, by decide⟩,⟨1183207, by decide⟩]) unmarked_context_11_84930_1183208 node_context_11_84930_1183208
  intro a
  fin_cases a
  · exact context_12_339720_448748
  · exact context_12_339721_1183078
  · exact context_12_339722_1183139
  · exact context_12_339723_1183207

theorem selected_cut_43261 : selected 10 ⟨1183265, by decide⟩
    (prefixPartial 11 84931) = some ⟨11, 2, 0, 1183265, 84931, 2757, 262144⟩ := by
  decide +kernel

theorem context_11_84931_1183265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84931 ⟨1183265, by decide⟩ :=
  accepted_of_selected 11 84931 ⟨1183265, by decide⟩ ⟨11, 2, 0, 1183265, 84931, 2757, 262144⟩
    (by decide) selected_cut_43261

theorem unmarked_context_10_21232_1183266 : frontier 11 ⟨1183266, by decide⟩
    (prefixCache 10 21232) (prefixPartial 10 21232) = false := by
  decide +kernel

theorem node_context_10_21232_1183266 : EJMOriginalGlobalDAGData.nodes 11 ⟨1183266, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1182976, by decide⟩,⟨1183208, by decide⟩,⟨1183265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21232_1183266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21232 ⟨1183266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21232
    ⟨1183266, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1182976, by decide⟩,⟨1183208, by decide⟩,⟨1183265, by decide⟩]) unmarked_context_10_21232_1183266 node_context_10_21232_1183266
  intro a
  fin_cases a
  · exact context_11_84928_434745
  · exact context_11_84929_1182976
  · exact context_11_84930_1183208
  · exact context_11_84931_1183265

theorem selected_cut_43262 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339728) = some ⟨12, 1, 0, 1108174, 339728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339728_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339728 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339728 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339728, 1, 65536⟩
    (by decide) selected_cut_43262

theorem selected_cut_43263 : selected 9 ⟨1183338, by decide⟩
    (prefixPartial 12 339729) = some ⟨12, 2, 0, 1183338, 339729, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_339729_1183338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339729 ⟨1183338, by decide⟩ :=
  accepted_of_selected 12 339729 ⟨1183338, by decide⟩ ⟨12, 2, 0, 1183338, 339729, 3529, 65536⟩
    (by decide) selected_cut_43263

theorem selected_cut_43264 : selected 9 ⟨1183413, by decide⟩
    (prefixPartial 12 339730) = some ⟨12, 2, 0, 1183413, 339730, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_339730_1183413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339730 ⟨1183413, by decide⟩ :=
  accepted_of_selected 12 339730 ⟨1183413, by decide⟩ ⟨12, 2, 0, 1183413, 339730, 3609, 65536⟩
    (by decide) selected_cut_43264

theorem selected_cut_43265 : selected 9 ⟨1183492, by decide⟩
    (prefixPartial 12 339731) = some ⟨12, 2, 0, 1183492, 339731, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_339731_1183492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339731 ⟨1183492, by decide⟩ :=
  accepted_of_selected 12 339731 ⟨1183492, by decide⟩ ⟨12, 2, 0, 1183492, 339731, 3817, 65536⟩
    (by decide) selected_cut_43265

theorem unmarked_context_11_84932_1183493 : frontier 10 ⟨1183493, by decide⟩
    (prefixCache 11 84932) (prefixPartial 11 84932) = false := by
  decide +kernel

theorem node_context_11_84932_1183493 : EJMOriginalGlobalDAGData.nodes 10 ⟨1183493, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1183338, by decide⟩,⟨1183413, by decide⟩,⟨1183492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84932_1183493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84932 ⟨1183493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84932
    ⟨1183493, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1183338, by decide⟩,⟨1183413, by decide⟩,⟨1183492, by decide⟩]) unmarked_context_11_84932_1183493 node_context_11_84932_1183493
  intro a
  fin_cases a
  · exact context_12_339728_1108174
  · exact context_12_339729_1183338
  · exact context_12_339730_1183413
  · exact context_12_339731_1183492

theorem selected_cut_43266 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339732) = some ⟨12, 1, 0, 1108174, 339732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339732_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339732 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339732 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339732, 1, 65536⟩
    (by decide) selected_cut_43266

theorem selected_cut_43267 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 339733) = some ⟨12, 1, 0, 1172003, 339733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339733_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339733 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 339733 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 339733, 1, 65536⟩
    (by decide) selected_cut_43267

theorem selected_cut_43268 : selected 9 ⟨1183574, by decide⟩
    (prefixPartial 12 339734) = some ⟨12, 2, 0, 1183574, 339734, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_339734_1183574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339734 ⟨1183574, by decide⟩ :=
  accepted_of_selected 12 339734 ⟨1183574, by decide⟩ ⟨12, 2, 0, 1183574, 339734, 3537, 65536⟩
    (by decide) selected_cut_43268

theorem selected_cut_43269 : selected 9 ⟨1183649, by decide⟩
    (prefixPartial 12 339735) = some ⟨12, 2, 0, 1183649, 339735, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_339735_1183649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339735 ⟨1183649, by decide⟩ :=
  accepted_of_selected 12 339735 ⟨1183649, by decide⟩ ⟨12, 2, 0, 1183649, 339735, 3777, 65536⟩
    (by decide) selected_cut_43269

theorem unmarked_context_11_84933_1183650 : frontier 10 ⟨1183650, by decide⟩
    (prefixCache 11 84933) (prefixPartial 11 84933) = false := by
  decide +kernel

theorem node_context_11_84933_1183650 : EJMOriginalGlobalDAGData.nodes 10 ⟨1183650, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172003, by decide⟩,⟨1183574, by decide⟩,⟨1183649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84933_1183650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84933 ⟨1183650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84933
    ⟨1183650, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172003, by decide⟩,⟨1183574, by decide⟩,⟨1183649, by decide⟩]) unmarked_context_11_84933_1183650 node_context_11_84933_1183650
  intro a
  fin_cases a
  · exact context_12_339732_1108174
  · exact context_12_339733_1172003
  · exact context_12_339734_1183574
  · exact context_12_339735_1183649

theorem selected_cut_43270 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339736) = some ⟨12, 1, 0, 1108174, 339736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339736_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339736 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339736 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339736, 1, 65536⟩
    (by decide) selected_cut_43270

theorem selected_cut_43271 : selected 9 ⟨1183714, by decide⟩
    (prefixPartial 12 339737) = some ⟨12, 2, 0, 1183714, 339737, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_339737_1183714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339737 ⟨1183714, by decide⟩ :=
  accepted_of_selected 12 339737 ⟨1183714, by decide⟩ ⟨12, 2, 0, 1183714, 339737, 3105, 65536⟩
    (by decide) selected_cut_43271

theorem selected_cut_43272 : selected 9 ⟨1183762, by decide⟩
    (prefixPartial 12 339738) = some ⟨12, 2, 0, 1183762, 339738, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_339738_1183762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339738 ⟨1183762, by decide⟩ :=
  accepted_of_selected 12 339738 ⟨1183762, by decide⟩ ⟨12, 2, 0, 1183762, 339738, 2989, 65536⟩
    (by decide) selected_cut_43272

theorem selected_cut_43273 : selected 9 ⟨1183824, by decide⟩
    (prefixPartial 12 339739) = some ⟨12, 2, 0, 1183824, 339739, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_339739_1183824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339739 ⟨1183824, by decide⟩ :=
  accepted_of_selected 12 339739 ⟨1183824, by decide⟩ ⟨12, 2, 0, 1183824, 339739, 3381, 65536⟩
    (by decide) selected_cut_43273

theorem unmarked_context_11_84934_1183825 : frontier 10 ⟨1183825, by decide⟩
    (prefixCache 11 84934) (prefixPartial 11 84934) = false := by
  decide +kernel

theorem node_context_11_84934_1183825 : EJMOriginalGlobalDAGData.nodes 10 ⟨1183825, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1183714, by decide⟩,⟨1183762, by decide⟩,⟨1183824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84934_1183825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84934 ⟨1183825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84934
    ⟨1183825, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1183714, by decide⟩,⟨1183762, by decide⟩,⟨1183824, by decide⟩]) unmarked_context_11_84934_1183825 node_context_11_84934_1183825
  intro a
  fin_cases a
  · exact context_12_339736_1108174
  · exact context_12_339737_1183714
  · exact context_12_339738_1183762
  · exact context_12_339739_1183824

theorem selected_cut_43274 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339740) = some ⟨12, 1, 0, 1108174, 339740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339740_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339740 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339740 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339740, 1, 65536⟩
    (by decide) selected_cut_43274

theorem selected_cut_43275 : selected 9 ⟨1183872, by decide⟩
    (prefixPartial 12 339741) = some ⟨12, 2, 0, 1183872, 339741, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_339741_1183872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339741 ⟨1183872, by decide⟩ :=
  accepted_of_selected 12 339741 ⟨1183872, by decide⟩ ⟨12, 2, 0, 1183872, 339741, 2681, 65536⟩
    (by decide) selected_cut_43275

theorem selected_cut_43276 : selected 9 ⟨1183923, by decide⟩
    (prefixPartial 12 339742) = some ⟨12, 2, 0, 1183923, 339742, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_339742_1183923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339742 ⟨1183923, by decide⟩ :=
  accepted_of_selected 12 339742 ⟨1183923, by decide⟩ ⟨12, 2, 0, 1183923, 339742, 2905, 65536⟩
    (by decide) selected_cut_43276

theorem selected_cut_43277 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 339743) = some ⟨12, 1, 0, 903806, 339743, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339743_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339743 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 339743 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 339743, 1, 65536⟩
    (by decide) selected_cut_43277

theorem unmarked_context_11_84935_1183924 : frontier 10 ⟨1183924, by decide⟩
    (prefixCache 11 84935) (prefixPartial 11 84935) = false := by
  decide +kernel

theorem node_context_11_84935_1183924 : EJMOriginalGlobalDAGData.nodes 10 ⟨1183924, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1183872, by decide⟩,⟨1183923, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84935_1183924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84935 ⟨1183924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84935
    ⟨1183924, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1183872, by decide⟩,⟨1183923, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84935_1183924 node_context_11_84935_1183924
  intro a
  fin_cases a
  · exact context_12_339740_1108174
  · exact context_12_339741_1183872
  · exact context_12_339742_1183923
  · exact context_12_339743_903806

theorem unmarked_context_10_21233_1183925 : frontier 11 ⟨1183925, by decide⟩
    (prefixCache 10 21233) (prefixPartial 10 21233) = false := by
  decide +kernel

theorem node_context_10_21233_1183925 : EJMOriginalGlobalDAGData.nodes 11 ⟨1183925, by decide⟩ =
    .split (coordinate 10) (![⟨1183493, by decide⟩,⟨1183650, by decide⟩,⟨1183825, by decide⟩,⟨1183924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21233_1183925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21233 ⟨1183925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21233
    ⟨1183925, by decide⟩ (by decide) (![⟨1183493, by decide⟩,⟨1183650, by decide⟩,⟨1183825, by decide⟩,⟨1183924, by decide⟩]) unmarked_context_10_21233_1183925 node_context_10_21233_1183925
  intro a
  fin_cases a
  · exact context_11_84932_1183493
  · exact context_11_84933_1183650
  · exact context_11_84934_1183825
  · exact context_11_84935_1183924

theorem selected_cut_43278 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339744) = some ⟨12, 1, 0, 1108174, 339744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339744_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339744 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339744 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339744, 1, 65536⟩
    (by decide) selected_cut_43278

theorem selected_cut_43279 : selected 9 ⟨1184001, by decide⟩
    (prefixPartial 12 339745) = some ⟨12, 2, 0, 1184001, 339745, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_339745_1184001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339745 ⟨1184001, by decide⟩ :=
  accepted_of_selected 12 339745 ⟨1184001, by decide⟩ ⟨12, 2, 0, 1184001, 339745, 3341, 65536⟩
    (by decide) selected_cut_43279

theorem selected_cut_43280 : selected 9 ⟨1184063, by decide⟩
    (prefixPartial 12 339746) = some ⟨12, 2, 0, 1184063, 339746, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_339746_1184063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339746 ⟨1184063, by decide⟩ :=
  accepted_of_selected 12 339746 ⟨1184063, by decide⟩ ⟨12, 2, 0, 1184063, 339746, 3109, 65536⟩
    (by decide) selected_cut_43280

theorem selected_cut_43281 : selected 9 ⟨1184134, by decide⟩
    (prefixPartial 12 339747) = some ⟨12, 2, 0, 1184134, 339747, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_339747_1184134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339747 ⟨1184134, by decide⟩ :=
  accepted_of_selected 12 339747 ⟨1184134, by decide⟩ ⟨12, 2, 0, 1184134, 339747, 3469, 65536⟩
    (by decide) selected_cut_43281

theorem unmarked_context_11_84936_1184135 : frontier 10 ⟨1184135, by decide⟩
    (prefixCache 11 84936) (prefixPartial 11 84936) = false := by
  decide +kernel

theorem node_context_11_84936_1184135 : EJMOriginalGlobalDAGData.nodes 10 ⟨1184135, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184001, by decide⟩,⟨1184063, by decide⟩,⟨1184134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84936_1184135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84936 ⟨1184135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84936
    ⟨1184135, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184001, by decide⟩,⟨1184063, by decide⟩,⟨1184134, by decide⟩]) unmarked_context_11_84936_1184135 node_context_11_84936_1184135
  intro a
  fin_cases a
  · exact context_12_339744_1108174
  · exact context_12_339745_1184001
  · exact context_12_339746_1184063
  · exact context_12_339747_1184134

theorem selected_cut_43282 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339748) = some ⟨12, 1, 0, 1108174, 339748, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339748_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339748 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339748 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339748, 1, 65536⟩
    (by decide) selected_cut_43282

theorem selected_cut_43283 : selected 9 ⟨1184203, by decide⟩
    (prefixPartial 12 339749) = some ⟨12, 2, 0, 1184203, 339749, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_339749_1184203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339749 ⟨1184203, by decide⟩ :=
  accepted_of_selected 12 339749 ⟨1184203, by decide⟩ ⟨12, 2, 0, 1184203, 339749, 3101, 65536⟩
    (by decide) selected_cut_43283

theorem selected_cut_43284 : selected 9 ⟨1184263, by decide⟩
    (prefixPartial 12 339750) = some ⟨12, 2, 0, 1184263, 339750, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_339750_1184263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339750 ⟨1184263, by decide⟩ :=
  accepted_of_selected 12 339750 ⟨1184263, by decide⟩ ⟨12, 2, 0, 1184263, 339750, 2913, 65536⟩
    (by decide) selected_cut_43284

theorem selected_cut_43285 : selected 9 ⟨1184333, by decide⟩
    (prefixPartial 12 339751) = some ⟨12, 2, 0, 1184333, 339751, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_339751_1184333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339751 ⟨1184333, by decide⟩ :=
  accepted_of_selected 12 339751 ⟨1184333, by decide⟩ ⟨12, 2, 0, 1184333, 339751, 3433, 65536⟩
    (by decide) selected_cut_43285

theorem unmarked_context_11_84937_1184334 : frontier 10 ⟨1184334, by decide⟩
    (prefixCache 11 84937) (prefixPartial 11 84937) = false := by
  decide +kernel

theorem node_context_11_84937_1184334 : EJMOriginalGlobalDAGData.nodes 10 ⟨1184334, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184203, by decide⟩,⟨1184263, by decide⟩,⟨1184333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84937_1184334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84937 ⟨1184334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84937
    ⟨1184334, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184203, by decide⟩,⟨1184263, by decide⟩,⟨1184333, by decide⟩]) unmarked_context_11_84937_1184334 node_context_11_84937_1184334
  intro a
  fin_cases a
  · exact context_12_339748_1108174
  · exact context_12_339749_1184203
  · exact context_12_339750_1184263
  · exact context_12_339751_1184333

theorem selected_cut_43286 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339752) = some ⟨12, 1, 0, 1108174, 339752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339752_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339752 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339752 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339752, 1, 65536⟩
    (by decide) selected_cut_43286

theorem selected_cut_43287 : selected 9 ⟨1184393, by decide⟩
    (prefixPartial 12 339753) = some ⟨12, 2, 0, 1184393, 339753, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_339753_1184393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339753 ⟨1184393, by decide⟩ :=
  accepted_of_selected 12 339753 ⟨1184393, by decide⟩ ⟨12, 2, 0, 1184393, 339753, 2929, 65536⟩
    (by decide) selected_cut_43287

theorem selected_cut_43288 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 339754) = some ⟨12, 1, 0, 1172910, 339754, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339754_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339754 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 339754 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 339754, 1, 65536⟩
    (by decide) selected_cut_43288

theorem selected_cut_43289 : selected 9 ⟨1184445, by decide⟩
    (prefixPartial 12 339755) = some ⟨12, 2, 0, 1184445, 339755, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_339755_1184445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339755 ⟨1184445, by decide⟩ :=
  accepted_of_selected 12 339755 ⟨1184445, by decide⟩ ⟨12, 2, 0, 1184445, 339755, 3153, 65536⟩
    (by decide) selected_cut_43289

theorem unmarked_context_11_84938_1184446 : frontier 10 ⟨1184446, by decide⟩
    (prefixCache 11 84938) (prefixPartial 11 84938) = false := by
  decide +kernel

theorem node_context_11_84938_1184446 : EJMOriginalGlobalDAGData.nodes 10 ⟨1184446, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184393, by decide⟩,⟨1172910, by decide⟩,⟨1184445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84938_1184446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84938 ⟨1184446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84938
    ⟨1184446, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184393, by decide⟩,⟨1172910, by decide⟩,⟨1184445, by decide⟩]) unmarked_context_11_84938_1184446 node_context_11_84938_1184446
  intro a
  fin_cases a
  · exact context_12_339752_1108174
  · exact context_12_339753_1184393
  · exact context_12_339754_1172910
  · exact context_12_339755_1184445

theorem selected_cut_43290 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339756) = some ⟨12, 1, 0, 1108174, 339756, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339756_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339756 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339756 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339756, 1, 65536⟩
    (by decide) selected_cut_43290

theorem selected_cut_43291 : selected 9 ⟨1184495, by decide⟩
    (prefixPartial 12 339757) = some ⟨12, 2, 0, 1184495, 339757, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_339757_1184495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339757 ⟨1184495, by decide⟩ :=
  accepted_of_selected 12 339757 ⟨1184495, by decide⟩ ⟨12, 2, 0, 1184495, 339757, 2493, 65536⟩
    (by decide) selected_cut_43291

theorem selected_cut_43292 : selected 9 ⟨1184544, by decide⟩
    (prefixPartial 12 339758) = some ⟨12, 2, 0, 1184544, 339758, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_339758_1184544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339758 ⟨1184544, by decide⟩ :=
  accepted_of_selected 12 339758 ⟨1184544, by decide⟩ ⟨12, 2, 0, 1184544, 339758, 2477, 65536⟩
    (by decide) selected_cut_43292

theorem selected_cut_43293 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 339759) = some ⟨12, 1, 0, 903806, 339759, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339759_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339759 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 339759 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 339759, 1, 65536⟩
    (by decide) selected_cut_43293

theorem unmarked_context_11_84939_1184545 : frontier 10 ⟨1184545, by decide⟩
    (prefixCache 11 84939) (prefixPartial 11 84939) = false := by
  decide +kernel

theorem node_context_11_84939_1184545 : EJMOriginalGlobalDAGData.nodes 10 ⟨1184545, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184495, by decide⟩,⟨1184544, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84939_1184545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84939 ⟨1184545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84939
    ⟨1184545, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184495, by decide⟩,⟨1184544, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84939_1184545 node_context_11_84939_1184545
  intro a
  fin_cases a
  · exact context_12_339756_1108174
  · exact context_12_339757_1184495
  · exact context_12_339758_1184544
  · exact context_12_339759_903806

theorem unmarked_context_10_21234_1184546 : frontier 11 ⟨1184546, by decide⟩
    (prefixCache 10 21234) (prefixPartial 10 21234) = false := by
  decide +kernel

theorem node_context_10_21234_1184546 : EJMOriginalGlobalDAGData.nodes 11 ⟨1184546, by decide⟩ =
    .split (coordinate 10) (![⟨1184135, by decide⟩,⟨1184334, by decide⟩,⟨1184446, by decide⟩,⟨1184545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21234_1184546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21234 ⟨1184546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21234
    ⟨1184546, by decide⟩ (by decide) (![⟨1184135, by decide⟩,⟨1184334, by decide⟩,⟨1184446, by decide⟩,⟨1184545, by decide⟩]) unmarked_context_10_21234_1184546 node_context_10_21234_1184546
  intro a
  fin_cases a
  · exact context_11_84936_1184135
  · exact context_11_84937_1184334
  · exact context_11_84938_1184446
  · exact context_11_84939_1184545

theorem selected_cut_43294 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339760) = some ⟨12, 1, 0, 1108174, 339760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339760_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339760 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339760 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339760, 1, 65536⟩
    (by decide) selected_cut_43294

theorem selected_cut_43295 : selected 9 ⟨1184606, by decide⟩
    (prefixPartial 12 339761) = some ⟨12, 2, 0, 1184606, 339761, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_339761_1184606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339761 ⟨1184606, by decide⟩ :=
  accepted_of_selected 12 339761 ⟨1184606, by decide⟩ ⟨12, 2, 0, 1184606, 339761, 3001, 65536⟩
    (by decide) selected_cut_43295

theorem selected_cut_43296 : selected 9 ⟨1184669, by decide⟩
    (prefixPartial 12 339762) = some ⟨12, 2, 0, 1184669, 339762, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_339762_1184669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339762 ⟨1184669, by decide⟩ :=
  accepted_of_selected 12 339762 ⟨1184669, by decide⟩ ⟨12, 2, 0, 1184669, 339762, 2989, 65536⟩
    (by decide) selected_cut_43296

theorem selected_cut_43297 : selected 9 ⟨1184730, by decide⟩
    (prefixPartial 12 339763) = some ⟨12, 2, 0, 1184730, 339763, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_339763_1184730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339763 ⟨1184730, by decide⟩ :=
  accepted_of_selected 12 339763 ⟨1184730, by decide⟩ ⟨12, 2, 0, 1184730, 339763, 3189, 65536⟩
    (by decide) selected_cut_43297

theorem unmarked_context_11_84940_1184731 : frontier 10 ⟨1184731, by decide⟩
    (prefixCache 11 84940) (prefixPartial 11 84940) = false := by
  decide +kernel

theorem node_context_11_84940_1184731 : EJMOriginalGlobalDAGData.nodes 10 ⟨1184731, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184606, by decide⟩,⟨1184669, by decide⟩,⟨1184730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84940_1184731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84940 ⟨1184731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84940
    ⟨1184731, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184606, by decide⟩,⟨1184669, by decide⟩,⟨1184730, by decide⟩]) unmarked_context_11_84940_1184731 node_context_11_84940_1184731
  intro a
  fin_cases a
  · exact context_12_339760_1108174
  · exact context_12_339761_1184606
  · exact context_12_339762_1184669
  · exact context_12_339763_1184730

theorem selected_cut_43298 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339764) = some ⟨12, 1, 0, 1108174, 339764, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339764_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339764 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339764 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339764, 1, 65536⟩
    (by decide) selected_cut_43298

theorem selected_cut_43299 : selected 9 ⟨1184778, by decide⟩
    (prefixPartial 12 339765) = some ⟨12, 2, 0, 1184778, 339765, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_339765_1184778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339765 ⟨1184778, by decide⟩ :=
  accepted_of_selected 12 339765 ⟨1184778, by decide⟩ ⟨12, 2, 0, 1184778, 339765, 2633, 65536⟩
    (by decide) selected_cut_43299

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
