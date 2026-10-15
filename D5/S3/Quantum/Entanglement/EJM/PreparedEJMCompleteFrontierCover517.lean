/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover516
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49636 : selected 10 ⟨1405656, by decide⟩
    (prefixPartial 11 102094) = some ⟨11, 2, 0, 1405656, 102094, 2721, 262144⟩ := by
  decide +kernel

theorem context_11_102094_1405656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102094 ⟨1405656, by decide⟩ :=
  accepted_of_selected 11 102094 ⟨1405656, by decide⟩ ⟨11, 2, 0, 1405656, 102094, 2721, 262144⟩
    (by decide) selected_cut_49636

theorem selected_cut_49637 : selected 10 ⟨1405714, by decide⟩
    (prefixPartial 11 102095) = some ⟨11, 2, 0, 1405714, 102095, 697, 262144⟩ := by
  decide +kernel

theorem context_11_102095_1405714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102095 ⟨1405714, by decide⟩ :=
  accepted_of_selected 11 102095 ⟨1405714, by decide⟩ ⟨11, 2, 0, 1405714, 102095, 697, 262144⟩
    (by decide) selected_cut_49637

theorem unmarked_context_10_25523_1405715 : frontier 11 ⟨1405715, by decide⟩
    (prefixCache 10 25523) (prefixPartial 10 25523) = false := by
  decide +kernel

theorem node_context_10_25523_1405715 : EJMOriginalGlobalDAGData.nodes 11 ⟨1405715, by decide⟩ =
    .split (coordinate 10) (![⟨1405541, by decide⟩,⟨1405604, by decide⟩,⟨1405656, by decide⟩,⟨1405714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25523_1405715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25523 ⟨1405715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25523
    ⟨1405715, by decide⟩ (by decide) (![⟨1405541, by decide⟩,⟨1405604, by decide⟩,⟨1405656, by decide⟩,⟨1405714, by decide⟩]) unmarked_context_10_25523_1405715 node_context_10_25523_1405715
  intro a
  fin_cases a
  · exact context_11_102092_1405541
  · exact context_11_102093_1405604
  · exact context_11_102094_1405656
  · exact context_11_102095_1405714

theorem unmarked_context_9_6380_1405716 : frontier 12 ⟨1405716, by decide⟩
    (prefixCache 9 6380) (prefixPartial 9 6380) = false := by
  decide +kernel

theorem node_context_9_6380_1405716 : EJMOriginalGlobalDAGData.nodes 12 ⟨1405716, by decide⟩ =
    .split (coordinate 9) (![⟨1404758, by decide⟩,⟨1405150, by decide⟩,⟨1405430, by decide⟩,⟨1405715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6380_1405716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6380 ⟨1405716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6380
    ⟨1405716, by decide⟩ (by decide) (![⟨1404758, by decide⟩,⟨1405150, by decide⟩,⟨1405430, by decide⟩,⟨1405715, by decide⟩]) unmarked_context_9_6380_1405716 node_context_9_6380_1405716
  intro a
  fin_cases a
  · exact context_10_25520_1404758
  · exact context_10_25521_1405150
  · exact context_10_25522_1405430
  · exact context_10_25523_1405715

theorem selected_cut_49638 : selected 10 ⟨1405769, by decide⟩
    (prefixPartial 11 102096) = some ⟨11, 2, 0, 1405769, 102096, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_102096_1405769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102096 ⟨1405769, by decide⟩ :=
  accepted_of_selected 11 102096 ⟨1405769, by decide⟩ ⟨11, 2, 0, 1405769, 102096, 1685, 262144⟩
    (by decide) selected_cut_49638

theorem selected_cut_49639 : selected 9 ⟨1405799, by decide⟩
    (prefixPartial 12 408388) = some ⟨12, 2, 0, 1405799, 408388, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_408388_1405799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408388 ⟨1405799, by decide⟩ :=
  accepted_of_selected 12 408388 ⟨1405799, by decide⟩ ⟨12, 2, 0, 1405799, 408388, 1377, 65536⟩
    (by decide) selected_cut_49639

theorem selected_cut_49640 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 408389) = some ⟨12, 1, 0, 642341, 408389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408389_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408389 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 408389 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 408389, 1, 65536⟩
    (by decide) selected_cut_49640

theorem selected_cut_49641 : selected 9 ⟨1405834, by decide⟩
    (prefixPartial 12 408390) = some ⟨12, 2, 0, 1405834, 408390, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_408390_1405834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408390 ⟨1405834, by decide⟩ :=
  accepted_of_selected 12 408390 ⟨1405834, by decide⟩ ⟨12, 2, 0, 1405834, 408390, 1557, 65536⟩
    (by decide) selected_cut_49641

theorem selected_cut_49642 : selected 9 ⟨1405863, by decide⟩
    (prefixPartial 12 408391) = some ⟨12, 2, 0, 1405863, 408391, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_408391_1405863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408391 ⟨1405863, by decide⟩ :=
  accepted_of_selected 12 408391 ⟨1405863, by decide⟩ ⟨12, 2, 0, 1405863, 408391, 1405, 65536⟩
    (by decide) selected_cut_49642

theorem unmarked_context_11_102097_1405864 : frontier 10 ⟨1405864, by decide⟩
    (prefixCache 11 102097) (prefixPartial 11 102097) = false := by
  decide +kernel

theorem node_context_11_102097_1405864 : EJMOriginalGlobalDAGData.nodes 10 ⟨1405864, by decide⟩ =
    .split (coordinate 11) (![⟨1405799, by decide⟩,⟨642341, by decide⟩,⟨1405834, by decide⟩,⟨1405863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102097_1405864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102097 ⟨1405864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102097
    ⟨1405864, by decide⟩ (by decide) (![⟨1405799, by decide⟩,⟨642341, by decide⟩,⟨1405834, by decide⟩,⟨1405863, by decide⟩]) unmarked_context_11_102097_1405864 node_context_11_102097_1405864
  intro a
  fin_cases a
  · exact context_12_408388_1405799
  · exact context_12_408389_642341
  · exact context_12_408390_1405834
  · exact context_12_408391_1405863

theorem selected_cut_49643 : selected 10 ⟨1405968, by decide⟩
    (prefixPartial 11 102098) = some ⟨11, 2, 0, 1405968, 102098, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_102098_1405968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102098 ⟨1405968, by decide⟩ :=
  accepted_of_selected 11 102098 ⟨1405968, by decide⟩ ⟨11, 2, 0, 1405968, 102098, 2985, 262144⟩
    (by decide) selected_cut_49643

theorem selected_cut_49644 : selected 10 ⟨1406029, by decide⟩
    (prefixPartial 11 102099) = some ⟨11, 2, 0, 1406029, 102099, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_102099_1406029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102099 ⟨1406029, by decide⟩ :=
  accepted_of_selected 11 102099 ⟨1406029, by decide⟩ ⟨11, 2, 0, 1406029, 102099, 2777, 262144⟩
    (by decide) selected_cut_49644

theorem unmarked_context_10_25524_1406030 : frontier 11 ⟨1406030, by decide⟩
    (prefixCache 10 25524) (prefixPartial 10 25524) = false := by
  decide +kernel

theorem node_context_10_25524_1406030 : EJMOriginalGlobalDAGData.nodes 11 ⟨1406030, by decide⟩ =
    .split (coordinate 10) (![⟨1405769, by decide⟩,⟨1405864, by decide⟩,⟨1405968, by decide⟩,⟨1406029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25524_1406030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25524 ⟨1406030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25524
    ⟨1406030, by decide⟩ (by decide) (![⟨1405769, by decide⟩,⟨1405864, by decide⟩,⟨1405968, by decide⟩,⟨1406029, by decide⟩]) unmarked_context_10_25524_1406030 node_context_10_25524_1406030
  intro a
  fin_cases a
  · exact context_11_102096_1405769
  · exact context_11_102097_1405864
  · exact context_11_102098_1405968
  · exact context_11_102099_1406029

theorem selected_cut_49645 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25525) = some ⟨10, 1, 0, 893098, 25525, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25525_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25525 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25525 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25525, 1, 1048576⟩
    (by decide) selected_cut_49645

theorem selected_cut_49646 : selected 10 ⟨1406109, by decide⟩
    (prefixPartial 11 102104) = some ⟨11, 2, 0, 1406109, 102104, 3573, 262144⟩ := by
  decide +kernel

theorem context_11_102104_1406109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102104 ⟨1406109, by decide⟩ :=
  accepted_of_selected 11 102104 ⟨1406109, by decide⟩ ⟨11, 2, 0, 1406109, 102104, 3573, 262144⟩
    (by decide) selected_cut_49646

theorem selected_cut_49647 : selected 10 ⟨1406169, by decide⟩
    (prefixPartial 11 102105) = some ⟨11, 2, 0, 1406169, 102105, 3153, 262144⟩ := by
  decide +kernel

theorem context_11_102105_1406169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102105 ⟨1406169, by decide⟩ :=
  accepted_of_selected 11 102105 ⟨1406169, by decide⟩ ⟨11, 2, 0, 1406169, 102105, 3153, 262144⟩
    (by decide) selected_cut_49647

theorem selected_cut_49648 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 102106) = some ⟨11, 1, 0, 900587, 102106, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102106_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102106 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 102106 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 102106, 1, 262144⟩
    (by decide) selected_cut_49648

theorem selected_cut_49649 : selected 10 ⟨1406221, by decide⟩
    (prefixPartial 11 102107) = some ⟨11, 2, 0, 1406221, 102107, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_102107_1406221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102107 ⟨1406221, by decide⟩ :=
  accepted_of_selected 11 102107 ⟨1406221, by decide⟩ ⟨11, 2, 0, 1406221, 102107, 2857, 262144⟩
    (by decide) selected_cut_49649

theorem unmarked_context_10_25526_1406222 : frontier 11 ⟨1406222, by decide⟩
    (prefixCache 10 25526) (prefixPartial 10 25526) = false := by
  decide +kernel

theorem node_context_10_25526_1406222 : EJMOriginalGlobalDAGData.nodes 11 ⟨1406222, by decide⟩ =
    .split (coordinate 10) (![⟨1406109, by decide⟩,⟨1406169, by decide⟩,⟨900587, by decide⟩,⟨1406221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25526_1406222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25526 ⟨1406222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25526
    ⟨1406222, by decide⟩ (by decide) (![⟨1406109, by decide⟩,⟨1406169, by decide⟩,⟨900587, by decide⟩,⟨1406221, by decide⟩]) unmarked_context_10_25526_1406222 node_context_10_25526_1406222
  intro a
  fin_cases a
  · exact context_11_102104_1406109
  · exact context_11_102105_1406169
  · exact context_11_102106_900587
  · exact context_11_102107_1406221

theorem selected_cut_49650 : selected 10 ⟨1406271, by decide⟩
    (prefixPartial 11 102108) = some ⟨11, 2, 0, 1406271, 102108, 2201, 262144⟩ := by
  decide +kernel

theorem context_11_102108_1406271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102108 ⟨1406271, by decide⟩ :=
  accepted_of_selected 11 102108 ⟨1406271, by decide⟩ ⟨11, 2, 0, 1406271, 102108, 2201, 262144⟩
    (by decide) selected_cut_49650

theorem selected_cut_49651 : selected 10 ⟨1406324, by decide⟩
    (prefixPartial 11 102109) = some ⟨11, 2, 0, 1406324, 102109, 2969, 262144⟩ := by
  decide +kernel

theorem context_11_102109_1406324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102109 ⟨1406324, by decide⟩ :=
  accepted_of_selected 11 102109 ⟨1406324, by decide⟩ ⟨11, 2, 0, 1406324, 102109, 2969, 262144⟩
    (by decide) selected_cut_49651

theorem selected_cut_49652 : selected 10 ⟨1406363, by decide⟩
    (prefixPartial 11 102110) = some ⟨11, 2, 0, 1406363, 102110, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_102110_1406363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102110 ⟨1406363, by decide⟩ :=
  accepted_of_selected 11 102110 ⟨1406363, by decide⟩ ⟨11, 2, 0, 1406363, 102110, 1953, 262144⟩
    (by decide) selected_cut_49652

theorem selected_cut_49653 : selected 10 ⟨1406374, by decide⟩
    (prefixPartial 11 102111) = some ⟨11, 2, 0, 1406374, 102111, 805, 262144⟩ := by
  decide +kernel

theorem context_11_102111_1406374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102111 ⟨1406374, by decide⟩ :=
  accepted_of_selected 11 102111 ⟨1406374, by decide⟩ ⟨11, 2, 0, 1406374, 102111, 805, 262144⟩
    (by decide) selected_cut_49653

theorem unmarked_context_10_25527_1406375 : frontier 11 ⟨1406375, by decide⟩
    (prefixCache 10 25527) (prefixPartial 10 25527) = false := by
  decide +kernel

theorem node_context_10_25527_1406375 : EJMOriginalGlobalDAGData.nodes 11 ⟨1406375, by decide⟩ =
    .split (coordinate 10) (![⟨1406271, by decide⟩,⟨1406324, by decide⟩,⟨1406363, by decide⟩,⟨1406374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25527_1406375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25527 ⟨1406375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25527
    ⟨1406375, by decide⟩ (by decide) (![⟨1406271, by decide⟩,⟨1406324, by decide⟩,⟨1406363, by decide⟩,⟨1406374, by decide⟩]) unmarked_context_10_25527_1406375 node_context_10_25527_1406375
  intro a
  fin_cases a
  · exact context_11_102108_1406271
  · exact context_11_102109_1406324
  · exact context_11_102110_1406363
  · exact context_11_102111_1406374

theorem unmarked_context_9_6381_1406376 : frontier 12 ⟨1406376, by decide⟩
    (prefixCache 9 6381) (prefixPartial 9 6381) = false := by
  decide +kernel

theorem node_context_9_6381_1406376 : EJMOriginalGlobalDAGData.nodes 12 ⟨1406376, by decide⟩ =
    .split (coordinate 9) (![⟨1406030, by decide⟩,⟨893098, by decide⟩,⟨1406222, by decide⟩,⟨1406375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6381_1406376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6381 ⟨1406376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6381
    ⟨1406376, by decide⟩ (by decide) (![⟨1406030, by decide⟩,⟨893098, by decide⟩,⟨1406222, by decide⟩,⟨1406375, by decide⟩]) unmarked_context_9_6381_1406376 node_context_9_6381_1406376
  intro a
  fin_cases a
  · exact context_10_25524_1406030
  · exact context_10_25525_893098
  · exact context_10_25526_1406222
  · exact context_10_25527_1406375

theorem selected_cut_49654 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 102112) = some ⟨11, 1, 0, 1375697, 102112, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102112_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102112 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 102112 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 102112, 1, 262144⟩
    (by decide) selected_cut_49654

theorem selected_cut_49655 : selected 10 ⟨1406445, by decide⟩
    (prefixPartial 11 102113) = some ⟨11, 2, 0, 1406445, 102113, 2797, 262144⟩ := by
  decide +kernel

theorem context_11_102113_1406445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102113 ⟨1406445, by decide⟩ :=
  accepted_of_selected 11 102113 ⟨1406445, by decide⟩ ⟨11, 2, 0, 1406445, 102113, 2797, 262144⟩
    (by decide) selected_cut_49655

theorem selected_cut_49656 : selected 10 ⟨1406492, by decide⟩
    (prefixPartial 11 102114) = some ⟨11, 2, 0, 1406492, 102114, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_102114_1406492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102114 ⟨1406492, by decide⟩ :=
  accepted_of_selected 11 102114 ⟨1406492, by decide⟩ ⟨11, 2, 0, 1406492, 102114, 2097, 262144⟩
    (by decide) selected_cut_49656

theorem selected_cut_49657 : selected 10 ⟨1406520, by decide⟩
    (prefixPartial 11 102115) = some ⟨11, 2, 0, 1406520, 102115, 1477, 262144⟩ := by
  decide +kernel

theorem context_11_102115_1406520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102115 ⟨1406520, by decide⟩ :=
  accepted_of_selected 11 102115 ⟨1406520, by decide⟩ ⟨11, 2, 0, 1406520, 102115, 1477, 262144⟩
    (by decide) selected_cut_49657

theorem unmarked_context_10_25528_1406521 : frontier 11 ⟨1406521, by decide⟩
    (prefixCache 10 25528) (prefixPartial 10 25528) = false := by
  decide +kernel

theorem node_context_10_25528_1406521 : EJMOriginalGlobalDAGData.nodes 11 ⟨1406521, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1406445, by decide⟩,⟨1406492, by decide⟩,⟨1406520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25528_1406521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25528 ⟨1406521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25528
    ⟨1406521, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1406445, by decide⟩,⟨1406492, by decide⟩,⟨1406520, by decide⟩]) unmarked_context_10_25528_1406521 node_context_10_25528_1406521
  intro a
  fin_cases a
  · exact context_11_102112_1375697
  · exact context_11_102113_1406445
  · exact context_11_102114_1406492
  · exact context_11_102115_1406520

theorem selected_cut_49658 : selected 10 ⟨1406576, by decide⟩
    (prefixPartial 11 102116) = some ⟨11, 2, 0, 1406576, 102116, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_102116_1406576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102116 ⟨1406576, by decide⟩ :=
  accepted_of_selected 11 102116 ⟨1406576, by decide⟩ ⟨11, 2, 0, 1406576, 102116, 1777, 262144⟩
    (by decide) selected_cut_49658

theorem selected_cut_49659 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 102117) = some ⟨11, 1, 0, 1378525, 102117, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102117_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102117 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 102117 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 102117, 1, 262144⟩
    (by decide) selected_cut_49659

theorem selected_cut_49660 : selected 10 ⟨1406608, by decide⟩
    (prefixPartial 11 102118) = some ⟨11, 2, 0, 1406608, 102118, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_102118_1406608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102118 ⟨1406608, by decide⟩ :=
  accepted_of_selected 11 102118 ⟨1406608, by decide⟩ ⟨11, 2, 0, 1406608, 102118, 1613, 262144⟩
    (by decide) selected_cut_49660

theorem selected_cut_49661 : selected 10 ⟨1406638, by decide⟩
    (prefixPartial 11 102119) = some ⟨11, 2, 0, 1406638, 102119, 1501, 262144⟩ := by
  decide +kernel

theorem context_11_102119_1406638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102119 ⟨1406638, by decide⟩ :=
  accepted_of_selected 11 102119 ⟨1406638, by decide⟩ ⟨11, 2, 0, 1406638, 102119, 1501, 262144⟩
    (by decide) selected_cut_49661

theorem unmarked_context_10_25529_1406639 : frontier 11 ⟨1406639, by decide⟩
    (prefixCache 10 25529) (prefixPartial 10 25529) = false := by
  decide +kernel

theorem node_context_10_25529_1406639 : EJMOriginalGlobalDAGData.nodes 11 ⟨1406639, by decide⟩ =
    .split (coordinate 10) (![⟨1406576, by decide⟩,⟨1378525, by decide⟩,⟨1406608, by decide⟩,⟨1406638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25529_1406639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25529 ⟨1406639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25529
    ⟨1406639, by decide⟩ (by decide) (![⟨1406576, by decide⟩,⟨1378525, by decide⟩,⟨1406608, by decide⟩,⟨1406638, by decide⟩]) unmarked_context_10_25529_1406639 node_context_10_25529_1406639
  intro a
  fin_cases a
  · exact context_11_102116_1406576
  · exact context_11_102117_1378525
  · exact context_11_102118_1406608
  · exact context_11_102119_1406638

theorem selected_cut_49662 : selected 11 ⟨1406663, by decide⟩
    (prefixPartial 10 25530) = some ⟨10, 2, 0, 1406663, 25530, 617, 1048576⟩ := by
  decide +kernel

theorem context_10_25530_1406663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25530 ⟨1406663, by decide⟩ :=
  accepted_of_selected 10 25530 ⟨1406663, by decide⟩ ⟨10, 2, 0, 1406663, 25530, 617, 1048576⟩
    (by decide) selected_cut_49662

theorem selected_cut_49663 : selected 11 ⟨1406759, by decide⟩
    (prefixPartial 10 25531) = some ⟨10, 2, 0, 1406759, 25531, 3909, 1048576⟩ := by
  decide +kernel

theorem context_10_25531_1406759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25531 ⟨1406759, by decide⟩ :=
  accepted_of_selected 10 25531 ⟨1406759, by decide⟩ ⟨10, 2, 0, 1406759, 25531, 3909, 1048576⟩
    (by decide) selected_cut_49663

theorem unmarked_context_9_6382_1406760 : frontier 12 ⟨1406760, by decide⟩
    (prefixCache 9 6382) (prefixPartial 9 6382) = false := by
  decide +kernel

theorem node_context_9_6382_1406760 : EJMOriginalGlobalDAGData.nodes 12 ⟨1406760, by decide⟩ =
    .split (coordinate 9) (![⟨1406521, by decide⟩,⟨1406639, by decide⟩,⟨1406663, by decide⟩,⟨1406759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6382_1406760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6382 ⟨1406760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6382
    ⟨1406760, by decide⟩ (by decide) (![⟨1406521, by decide⟩,⟨1406639, by decide⟩,⟨1406663, by decide⟩,⟨1406759, by decide⟩]) unmarked_context_9_6382_1406760 node_context_9_6382_1406760
  intro a
  fin_cases a
  · exact context_10_25528_1406521
  · exact context_10_25529_1406639
  · exact context_10_25530_1406663
  · exact context_10_25531_1406759

theorem selected_cut_49664 : selected 11 ⟨1406809, by decide⟩
    (prefixPartial 10 25532) = some ⟨10, 2, 0, 1406809, 25532, 2249, 1048576⟩ := by
  decide +kernel

theorem context_10_25532_1406809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25532 ⟨1406809, by decide⟩ :=
  accepted_of_selected 10 25532 ⟨1406809, by decide⟩ ⟨10, 2, 0, 1406809, 25532, 2249, 1048576⟩
    (by decide) selected_cut_49664

theorem selected_cut_49665 : selected 11 ⟨1406848, by decide⟩
    (prefixPartial 10 25533) = some ⟨10, 2, 0, 1406848, 25533, 1289, 1048576⟩ := by
  decide +kernel

theorem context_10_25533_1406848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25533 ⟨1406848, by decide⟩ :=
  accepted_of_selected 10 25533 ⟨1406848, by decide⟩ ⟨10, 2, 0, 1406848, 25533, 1289, 1048576⟩
    (by decide) selected_cut_49665

theorem selected_cut_49666 : selected 11 ⟨1406874, by decide⟩
    (prefixPartial 10 25534) = some ⟨10, 2, 0, 1406874, 25534, 641, 1048576⟩ := by
  decide +kernel

theorem context_10_25534_1406874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25534 ⟨1406874, by decide⟩ :=
  accepted_of_selected 10 25534 ⟨1406874, by decide⟩ ⟨10, 2, 0, 1406874, 25534, 641, 1048576⟩
    (by decide) selected_cut_49666

theorem selected_cut_49667 : selected 11 ⟨1406879, by decide⟩
    (prefixPartial 10 25535) = some ⟨10, 2, 0, 1406879, 25535, 77, 1048576⟩ := by
  decide +kernel

theorem context_10_25535_1406879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25535 ⟨1406879, by decide⟩ :=
  accepted_of_selected 10 25535 ⟨1406879, by decide⟩ ⟨10, 2, 0, 1406879, 25535, 77, 1048576⟩
    (by decide) selected_cut_49667

theorem unmarked_context_9_6383_1406880 : frontier 12 ⟨1406880, by decide⟩
    (prefixCache 9 6383) (prefixPartial 9 6383) = false := by
  decide +kernel

theorem node_context_9_6383_1406880 : EJMOriginalGlobalDAGData.nodes 12 ⟨1406880, by decide⟩ =
    .split (coordinate 9) (![⟨1406809, by decide⟩,⟨1406848, by decide⟩,⟨1406874, by decide⟩,⟨1406879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6383_1406880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6383 ⟨1406880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6383
    ⟨1406880, by decide⟩ (by decide) (![⟨1406809, by decide⟩,⟨1406848, by decide⟩,⟨1406874, by decide⟩,⟨1406879, by decide⟩]) unmarked_context_9_6383_1406880 node_context_9_6383_1406880
  intro a
  fin_cases a
  · exact context_10_25532_1406809
  · exact context_10_25533_1406848
  · exact context_10_25534_1406874
  · exact context_10_25535_1406879

theorem unmarked_context_8_1595_1406881 : frontier 13 ⟨1406881, by decide⟩
    (prefixCache 8 1595) (prefixPartial 8 1595) = false := by
  decide +kernel

theorem node_context_8_1595_1406881 : EJMOriginalGlobalDAGData.nodes 13 ⟨1406881, by decide⟩ =
    .split (coordinate 8) (![⟨1405716, by decide⟩,⟨1406376, by decide⟩,⟨1406760, by decide⟩,⟨1406880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1595_1406881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1595 ⟨1406881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1595
    ⟨1406881, by decide⟩ (by decide) (![⟨1405716, by decide⟩,⟨1406376, by decide⟩,⟨1406760, by decide⟩,⟨1406880, by decide⟩]) unmarked_context_8_1595_1406881 node_context_8_1595_1406881
  intro a
  fin_cases a
  · exact context_9_6380_1405716
  · exact context_9_6381_1406376
  · exact context_9_6382_1406760
  · exact context_9_6383_1406880

theorem unmarked_context_7_398_1406882 : frontier 14 ⟨1406882, by decide⟩
    (prefixCache 7 398) (prefixPartial 7 398) = false := by
  decide +kernel

theorem node_context_7_398_1406882 : EJMOriginalGlobalDAGData.nodes 14 ⟨1406882, by decide⟩ =
    .split (coordinate 7) (![⟨1400443, by decide⟩,⟨1402376, by decide⟩,⟨1404657, by decide⟩,⟨1406881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_398_1406882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 398 ⟨1406882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 398
    ⟨1406882, by decide⟩ (by decide) (![⟨1400443, by decide⟩,⟨1402376, by decide⟩,⟨1404657, by decide⟩,⟨1406881, by decide⟩]) unmarked_context_7_398_1406882 node_context_7_398_1406882
  intro a
  fin_cases a
  · exact context_8_1592_1400443
  · exact context_8_1593_1402376
  · exact context_8_1594_1404657
  · exact context_8_1595_1406881

theorem selected_cut_49668 : selected 11 ⟨1406950, by decide⟩
    (prefixPartial 10 25536) = some ⟨10, 2, 0, 1406950, 25536, 2081, 1048576⟩ := by
  decide +kernel

theorem context_10_25536_1406950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25536 ⟨1406950, by decide⟩ :=
  accepted_of_selected 10 25536 ⟨1406950, by decide⟩ ⟨10, 2, 0, 1406950, 25536, 2081, 1048576⟩
    (by decide) selected_cut_49668

theorem selected_cut_49669 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408592) = some ⟨12, 1, 0, 1108174, 408592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408592_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408592 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408592 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408592, 1, 65536⟩
    (by decide) selected_cut_49669

theorem selected_cut_49670 : selected 9 ⟨1407015, by decide⟩
    (prefixPartial 12 408593) = some ⟨12, 2, 0, 1407015, 408593, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_408593_1407015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408593 ⟨1407015, by decide⟩ :=
  accepted_of_selected 12 408593 ⟨1407015, by decide⟩ ⟨12, 2, 0, 1407015, 408593, 2241, 65536⟩
    (by decide) selected_cut_49670

theorem selected_cut_49671 : selected 9 ⟨1407076, by decide⟩
    (prefixPartial 12 408594) = some ⟨12, 2, 0, 1407076, 408594, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_408594_1407076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408594 ⟨1407076, by decide⟩ :=
  accepted_of_selected 12 408594 ⟨1407076, by decide⟩ ⟨12, 2, 0, 1407076, 408594, 2249, 65536⟩
    (by decide) selected_cut_49671

theorem selected_cut_49672 : selected 9 ⟨1407131, by decide⟩
    (prefixPartial 12 408595) = some ⟨12, 2, 0, 1407131, 408595, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_408595_1407131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408595 ⟨1407131, by decide⟩ :=
  accepted_of_selected 12 408595 ⟨1407131, by decide⟩ ⟨12, 2, 0, 1407131, 408595, 2133, 65536⟩
    (by decide) selected_cut_49672

theorem unmarked_context_11_102148_1407132 : frontier 10 ⟨1407132, by decide⟩
    (prefixCache 11 102148) (prefixPartial 11 102148) = false := by
  decide +kernel

theorem node_context_11_102148_1407132 : EJMOriginalGlobalDAGData.nodes 10 ⟨1407132, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1407015, by decide⟩,⟨1407076, by decide⟩,⟨1407131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102148_1407132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102148 ⟨1407132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102148
    ⟨1407132, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1407015, by decide⟩,⟨1407076, by decide⟩,⟨1407131, by decide⟩]) unmarked_context_11_102148_1407132 node_context_11_102148_1407132
  intro a
  fin_cases a
  · exact context_12_408592_1108174
  · exact context_12_408593_1407015
  · exact context_12_408594_1407076
  · exact context_12_408595_1407131

theorem selected_cut_49673 : selected 10 ⟨1407133, by decide⟩
    (prefixPartial 11 102149) = some ⟨11, 2, 0, 1407133, 102149, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102149_1407133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102149 ⟨1407133, by decide⟩ :=
  accepted_of_selected 11 102149 ⟨1407133, by decide⟩ ⟨11, 2, 0, 1407133, 102149, 5, 262144⟩
    (by decide) selected_cut_49673

theorem selected_cut_49674 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408600) = some ⟨12, 1, 0, 1108174, 408600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408600_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408600 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408600 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408600, 1, 65536⟩
    (by decide) selected_cut_49674

theorem selected_cut_49675 : selected 9 ⟨1407189, by decide⟩
    (prefixPartial 12 408601) = some ⟨12, 2, 0, 1407189, 408601, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_408601_1407189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408601 ⟨1407189, by decide⟩ :=
  accepted_of_selected 12 408601 ⟨1407189, by decide⟩ ⟨12, 2, 0, 1407189, 408601, 2113, 65536⟩
    (by decide) selected_cut_49675

theorem selected_cut_49676 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 408602) = some ⟨12, 1, 0, 448662, 408602, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408602_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408602 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 408602 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 408602, 1, 65536⟩
    (by decide) selected_cut_49676

theorem selected_cut_49677 : selected 9 ⟨1407248, by decide⟩
    (prefixPartial 12 408603) = some ⟨12, 2, 0, 1407248, 408603, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_408603_1407248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408603 ⟨1407248, by decide⟩ :=
  accepted_of_selected 12 408603 ⟨1407248, by decide⟩ ⟨12, 2, 0, 1407248, 408603, 2221, 65536⟩
    (by decide) selected_cut_49677

theorem unmarked_context_11_102150_1407249 : frontier 10 ⟨1407249, by decide⟩
    (prefixCache 11 102150) (prefixPartial 11 102150) = false := by
  decide +kernel

theorem node_context_11_102150_1407249 : EJMOriginalGlobalDAGData.nodes 10 ⟨1407249, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1407189, by decide⟩,⟨448662, by decide⟩,⟨1407248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102150_1407249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102150 ⟨1407249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102150
    ⟨1407249, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1407189, by decide⟩,⟨448662, by decide⟩,⟨1407248, by decide⟩]) unmarked_context_11_102150_1407249 node_context_11_102150_1407249
  intro a
  fin_cases a
  · exact context_12_408600_1108174
  · exact context_12_408601_1407189
  · exact context_12_408602_448662
  · exact context_12_408603_1407248

theorem selected_cut_49678 : selected 10 ⟨1407344, by decide⟩
    (prefixPartial 11 102151) = some ⟨11, 2, 0, 1407344, 102151, 3921, 262144⟩ := by
  decide +kernel

theorem context_11_102151_1407344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102151 ⟨1407344, by decide⟩ :=
  accepted_of_selected 11 102151 ⟨1407344, by decide⟩ ⟨11, 2, 0, 1407344, 102151, 3921, 262144⟩
    (by decide) selected_cut_49678

theorem unmarked_context_10_25537_1407345 : frontier 11 ⟨1407345, by decide⟩
    (prefixCache 10 25537) (prefixPartial 10 25537) = false := by
  decide +kernel

theorem node_context_10_25537_1407345 : EJMOriginalGlobalDAGData.nodes 11 ⟨1407345, by decide⟩ =
    .split (coordinate 10) (![⟨1407132, by decide⟩,⟨1407133, by decide⟩,⟨1407249, by decide⟩,⟨1407344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25537_1407345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25537 ⟨1407345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25537
    ⟨1407345, by decide⟩ (by decide) (![⟨1407132, by decide⟩,⟨1407133, by decide⟩,⟨1407249, by decide⟩,⟨1407344, by decide⟩]) unmarked_context_10_25537_1407345 node_context_10_25537_1407345
  intro a
  fin_cases a
  · exact context_11_102148_1407132
  · exact context_11_102149_1407133
  · exact context_11_102150_1407249
  · exact context_11_102151_1407344

theorem selected_cut_49679 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408608) = some ⟨12, 1, 0, 1108174, 408608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408608_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408608 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408608 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408608, 1, 65536⟩
    (by decide) selected_cut_49679

theorem selected_cut_49680 : selected 9 ⟨1407389, by decide⟩
    (prefixPartial 12 408609) = some ⟨12, 2, 0, 1407389, 408609, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_408609_1407389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408609 ⟨1407389, by decide⟩ :=
  accepted_of_selected 12 408609 ⟨1407389, by decide⟩ ⟨12, 2, 0, 1407389, 408609, 2049, 65536⟩
    (by decide) selected_cut_49680

theorem selected_cut_49681 : selected 9 ⟨1407440, by decide⟩
    (prefixPartial 12 408610) = some ⟨12, 2, 0, 1407440, 408610, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_408610_1407440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408610 ⟨1407440, by decide⟩ :=
  accepted_of_selected 12 408610 ⟨1407440, by decide⟩ ⟨12, 2, 0, 1407440, 408610, 2125, 65536⟩
    (by decide) selected_cut_49681

theorem selected_cut_49682 : selected 9 ⟨1407489, by decide⟩
    (prefixPartial 12 408611) = some ⟨12, 2, 0, 1407489, 408611, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_408611_1407489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408611 ⟨1407489, by decide⟩ :=
  accepted_of_selected 12 408611 ⟨1407489, by decide⟩ ⟨12, 2, 0, 1407489, 408611, 1873, 65536⟩
    (by decide) selected_cut_49682

theorem unmarked_context_11_102152_1407490 : frontier 10 ⟨1407490, by decide⟩
    (prefixCache 11 102152) (prefixPartial 11 102152) = false := by
  decide +kernel

theorem node_context_11_102152_1407490 : EJMOriginalGlobalDAGData.nodes 10 ⟨1407490, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1407389, by decide⟩,⟨1407440, by decide⟩,⟨1407489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102152_1407490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102152 ⟨1407490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102152
    ⟨1407490, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1407389, by decide⟩,⟨1407440, by decide⟩,⟨1407489, by decide⟩]) unmarked_context_11_102152_1407490 node_context_11_102152_1407490
  intro a
  fin_cases a
  · exact context_12_408608_1108174
  · exact context_12_408609_1407389
  · exact context_12_408610_1407440
  · exact context_12_408611_1407489

theorem selected_cut_49683 : selected 10 ⟨1407578, by decide⟩
    (prefixPartial 11 102153) = some ⟨11, 2, 0, 1407578, 102153, 3965, 262144⟩ := by
  decide +kernel

theorem context_11_102153_1407578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102153 ⟨1407578, by decide⟩ :=
  accepted_of_selected 11 102153 ⟨1407578, by decide⟩ ⟨11, 2, 0, 1407578, 102153, 3965, 262144⟩
    (by decide) selected_cut_49683

theorem selected_cut_49684 : selected 10 ⟨1407622, by decide⟩
    (prefixPartial 11 102154) = some ⟨11, 2, 0, 1407622, 102154, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_102154_1407622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102154 ⟨1407622, by decide⟩ :=
  accepted_of_selected 11 102154 ⟨1407622, by decide⟩ ⟨11, 2, 0, 1407622, 102154, 1801, 262144⟩
    (by decide) selected_cut_49684

theorem selected_cut_49685 : selected 10 ⟨1407693, by decide⟩
    (prefixPartial 11 102155) = some ⟨11, 2, 0, 1407693, 102155, 3333, 262144⟩ := by
  decide +kernel

theorem context_11_102155_1407693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102155 ⟨1407693, by decide⟩ :=
  accepted_of_selected 11 102155 ⟨1407693, by decide⟩ ⟨11, 2, 0, 1407693, 102155, 3333, 262144⟩
    (by decide) selected_cut_49685

theorem unmarked_context_10_25538_1407694 : frontier 11 ⟨1407694, by decide⟩
    (prefixCache 10 25538) (prefixPartial 10 25538) = false := by
  decide +kernel

theorem node_context_10_25538_1407694 : EJMOriginalGlobalDAGData.nodes 11 ⟨1407694, by decide⟩ =
    .split (coordinate 10) (![⟨1407490, by decide⟩,⟨1407578, by decide⟩,⟨1407622, by decide⟩,⟨1407693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25538_1407694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25538 ⟨1407694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25538
    ⟨1407694, by decide⟩ (by decide) (![⟨1407490, by decide⟩,⟨1407578, by decide⟩,⟨1407622, by decide⟩,⟨1407693, by decide⟩]) unmarked_context_10_25538_1407694 node_context_10_25538_1407694
  intro a
  fin_cases a
  · exact context_11_102152_1407490
  · exact context_11_102153_1407578
  · exact context_11_102154_1407622
  · exact context_11_102155_1407693

theorem selected_cut_49686 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408624) = some ⟨12, 1, 0, 1108174, 408624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408624_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408624 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408624 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408624, 1, 65536⟩
    (by decide) selected_cut_49686

theorem selected_cut_49687 : selected 9 ⟨1407733, by decide⟩
    (prefixPartial 12 408625) = some ⟨12, 2, 0, 1407733, 408625, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_408625_1407733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408625 ⟨1407733, by decide⟩ :=
  accepted_of_selected 12 408625 ⟨1407733, by decide⟩ ⟨12, 2, 0, 1407733, 408625, 1537, 65536⟩
    (by decide) selected_cut_49687

theorem selected_cut_49688 : selected 9 ⟨1407773, by decide⟩
    (prefixPartial 12 408626) = some ⟨12, 2, 0, 1407773, 408626, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_408626_1407773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408626 ⟨1407773, by decide⟩ :=
  accepted_of_selected 12 408626 ⟨1407773, by decide⟩ ⟨12, 2, 0, 1407773, 408626, 1481, 65536⟩
    (by decide) selected_cut_49688

theorem selected_cut_49689 : selected 9 ⟨1407806, by decide⟩
    (prefixPartial 12 408627) = some ⟨12, 2, 0, 1407806, 408627, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_408627_1407806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408627 ⟨1407806, by decide⟩ :=
  accepted_of_selected 12 408627 ⟨1407806, by decide⟩ ⟨12, 2, 0, 1407806, 408627, 1401, 65536⟩
    (by decide) selected_cut_49689

theorem unmarked_context_11_102156_1407807 : frontier 10 ⟨1407807, by decide⟩
    (prefixCache 11 102156) (prefixPartial 11 102156) = false := by
  decide +kernel

theorem node_context_11_102156_1407807 : EJMOriginalGlobalDAGData.nodes 10 ⟨1407807, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1407733, by decide⟩,⟨1407773, by decide⟩,⟨1407806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102156_1407807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102156 ⟨1407807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102156
    ⟨1407807, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1407733, by decide⟩,⟨1407773, by decide⟩,⟨1407806, by decide⟩]) unmarked_context_11_102156_1407807 node_context_11_102156_1407807
  intro a
  fin_cases a
  · exact context_12_408624_1108174
  · exact context_12_408625_1407733
  · exact context_12_408626_1407773
  · exact context_12_408627_1407806

theorem selected_cut_49690 : selected 10 ⟨1407883, by decide⟩
    (prefixPartial 11 102157) = some ⟨11, 2, 0, 1407883, 102157, 3189, 262144⟩ := by
  decide +kernel

theorem context_11_102157_1407883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102157 ⟨1407883, by decide⟩ :=
  accepted_of_selected 11 102157 ⟨1407883, by decide⟩ ⟨11, 2, 0, 1407883, 102157, 3189, 262144⟩
    (by decide) selected_cut_49690

theorem selected_cut_49691 : selected 10 ⟨1407933, by decide⟩
    (prefixPartial 11 102158) = some ⟨11, 2, 0, 1407933, 102158, 2693, 262144⟩ := by
  decide +kernel

theorem context_11_102158_1407933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102158 ⟨1407933, by decide⟩ :=
  accepted_of_selected 11 102158 ⟨1407933, by decide⟩ ⟨11, 2, 0, 1407933, 102158, 2693, 262144⟩
    (by decide) selected_cut_49691

theorem selected_cut_49692 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102159) = some ⟨11, 1, 0, 977886, 102159, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102159_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102159 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102159 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102159, 1, 262144⟩
    (by decide) selected_cut_49692

theorem unmarked_context_10_25539_1407934 : frontier 11 ⟨1407934, by decide⟩
    (prefixCache 10 25539) (prefixPartial 10 25539) = false := by
  decide +kernel

theorem node_context_10_25539_1407934 : EJMOriginalGlobalDAGData.nodes 11 ⟨1407934, by decide⟩ =
    .split (coordinate 10) (![⟨1407807, by decide⟩,⟨1407883, by decide⟩,⟨1407933, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25539_1407934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25539 ⟨1407934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25539
    ⟨1407934, by decide⟩ (by decide) (![⟨1407807, by decide⟩,⟨1407883, by decide⟩,⟨1407933, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25539_1407934 node_context_10_25539_1407934
  intro a
  fin_cases a
  · exact context_11_102156_1407807
  · exact context_11_102157_1407883
  · exact context_11_102158_1407933
  · exact context_11_102159_977886

theorem unmarked_context_9_6384_1407935 : frontier 12 ⟨1407935, by decide⟩
    (prefixCache 9 6384) (prefixPartial 9 6384) = false := by
  decide +kernel

theorem node_context_9_6384_1407935 : EJMOriginalGlobalDAGData.nodes 12 ⟨1407935, by decide⟩ =
    .split (coordinate 9) (![⟨1406950, by decide⟩,⟨1407345, by decide⟩,⟨1407694, by decide⟩,⟨1407934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6384_1407935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6384 ⟨1407935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6384
    ⟨1407935, by decide⟩ (by decide) (![⟨1406950, by decide⟩,⟨1407345, by decide⟩,⟨1407694, by decide⟩,⟨1407934, by decide⟩]) unmarked_context_9_6384_1407935 node_context_9_6384_1407935
  intro a
  fin_cases a
  · exact context_10_25536_1406950
  · exact context_10_25537_1407345
  · exact context_10_25538_1407694
  · exact context_10_25539_1407934

theorem selected_cut_49693 : selected 10 ⟨1407994, by decide⟩
    (prefixPartial 11 102160) = some ⟨11, 2, 0, 1407994, 102160, 765, 262144⟩ := by
  decide +kernel

theorem context_11_102160_1407994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102160 ⟨1407994, by decide⟩ :=
  accepted_of_selected 11 102160 ⟨1407994, by decide⟩ ⟨11, 2, 0, 1407994, 102160, 765, 262144⟩
    (by decide) selected_cut_49693

theorem selected_cut_49694 : selected 10 ⟨1408052, by decide⟩
    (prefixPartial 11 102161) = some ⟨11, 2, 0, 1408052, 102161, 3729, 262144⟩ := by
  decide +kernel

theorem context_11_102161_1408052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102161 ⟨1408052, by decide⟩ :=
  accepted_of_selected 11 102161 ⟨1408052, by decide⟩ ⟨11, 2, 0, 1408052, 102161, 3729, 262144⟩
    (by decide) selected_cut_49694

theorem selected_cut_49695 : selected 10 ⟨1408091, by decide⟩
    (prefixPartial 11 102162) = some ⟨11, 2, 0, 1408091, 102162, 2229, 262144⟩ := by
  decide +kernel

theorem context_11_102162_1408091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102162 ⟨1408091, by decide⟩ :=
  accepted_of_selected 11 102162 ⟨1408091, by decide⟩ ⟨11, 2, 0, 1408091, 102162, 2229, 262144⟩
    (by decide) selected_cut_49695

theorem selected_cut_49696 : selected 10 ⟨1408127, by decide⟩
    (prefixPartial 11 102163) = some ⟨11, 2, 0, 1408127, 102163, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_102163_1408127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102163 ⟨1408127, by decide⟩ :=
  accepted_of_selected 11 102163 ⟨1408127, by decide⟩ ⟨11, 2, 0, 1408127, 102163, 2013, 262144⟩
    (by decide) selected_cut_49696

theorem unmarked_context_10_25540_1408128 : frontier 11 ⟨1408128, by decide⟩
    (prefixCache 10 25540) (prefixPartial 10 25540) = false := by
  decide +kernel

theorem node_context_10_25540_1408128 : EJMOriginalGlobalDAGData.nodes 11 ⟨1408128, by decide⟩ =
    .split (coordinate 10) (![⟨1407994, by decide⟩,⟨1408052, by decide⟩,⟨1408091, by decide⟩,⟨1408127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25540_1408128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25540 ⟨1408128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25540
    ⟨1408128, by decide⟩ (by decide) (![⟨1407994, by decide⟩,⟨1408052, by decide⟩,⟨1408091, by decide⟩,⟨1408127, by decide⟩]) unmarked_context_10_25540_1408128 node_context_10_25540_1408128
  intro a
  fin_cases a
  · exact context_11_102160_1407994
  · exact context_11_102161_1408052
  · exact context_11_102162_1408091
  · exact context_11_102163_1408127

theorem selected_cut_49697 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25541) = some ⟨10, 1, 0, 893098, 25541, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25541_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25541 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25541 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25541, 1, 1048576⟩
    (by decide) selected_cut_49697

theorem selected_cut_49698 : selected 10 ⟨1408188, by decide⟩
    (prefixPartial 11 102168) = some ⟨11, 2, 0, 1408188, 102168, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_102168_1408188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102168 ⟨1408188, by decide⟩ :=
  accepted_of_selected 11 102168 ⟨1408188, by decide⟩ ⟨11, 2, 0, 1408188, 102168, 2625, 262144⟩
    (by decide) selected_cut_49698

theorem selected_cut_49699 : selected 10 ⟨1408263, by decide⟩
    (prefixPartial 11 102169) = some ⟨11, 2, 0, 1408263, 102169, 3585, 262144⟩ := by
  decide +kernel

theorem context_11_102169_1408263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102169 ⟨1408263, by decide⟩ :=
  accepted_of_selected 11 102169 ⟨1408263, by decide⟩ ⟨11, 2, 0, 1408263, 102169, 3585, 262144⟩
    (by decide) selected_cut_49699

theorem selected_cut_49700 : selected 10 ⟨1408279, by decide⟩
    (prefixPartial 11 102170) = some ⟨11, 2, 0, 1408279, 102170, 969, 262144⟩ := by
  decide +kernel

theorem context_11_102170_1408279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102170 ⟨1408279, by decide⟩ :=
  accepted_of_selected 11 102170 ⟨1408279, by decide⟩ ⟨11, 2, 0, 1408279, 102170, 969, 262144⟩
    (by decide) selected_cut_49700

theorem selected_cut_49701 : selected 10 ⟨1408310, by decide⟩
    (prefixPartial 11 102171) = some ⟨11, 2, 0, 1408310, 102171, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_102171_1408310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102171 ⟨1408310, by decide⟩ :=
  accepted_of_selected 11 102171 ⟨1408310, by decide⟩ ⟨11, 2, 0, 1408310, 102171, 1849, 262144⟩
    (by decide) selected_cut_49701

theorem unmarked_context_10_25542_1408311 : frontier 11 ⟨1408311, by decide⟩
    (prefixCache 10 25542) (prefixPartial 10 25542) = false := by
  decide +kernel

theorem node_context_10_25542_1408311 : EJMOriginalGlobalDAGData.nodes 11 ⟨1408311, by decide⟩ =
    .split (coordinate 10) (![⟨1408188, by decide⟩,⟨1408263, by decide⟩,⟨1408279, by decide⟩,⟨1408310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25542_1408311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25542 ⟨1408311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25542
    ⟨1408311, by decide⟩ (by decide) (![⟨1408188, by decide⟩,⟨1408263, by decide⟩,⟨1408279, by decide⟩,⟨1408310, by decide⟩]) unmarked_context_10_25542_1408311 node_context_10_25542_1408311
  intro a
  fin_cases a
  · exact context_11_102168_1408188
  · exact context_11_102169_1408263
  · exact context_11_102170_1408279
  · exact context_11_102171_1408310

theorem selected_cut_49702 : selected 10 ⟨1408343, by decide⟩
    (prefixPartial 11 102172) = some ⟨11, 2, 0, 1408343, 102172, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_102172_1408343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102172 ⟨1408343, by decide⟩ :=
  accepted_of_selected 11 102172 ⟨1408343, by decide⟩ ⟨11, 2, 0, 1408343, 102172, 1733, 262144⟩
    (by decide) selected_cut_49702

theorem selected_cut_49703 : selected 10 ⟨1408398, by decide⟩
    (prefixPartial 11 102173) = some ⟨11, 2, 0, 1408398, 102173, 2601, 262144⟩ := by
  decide +kernel

theorem context_11_102173_1408398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102173 ⟨1408398, by decide⟩ :=
  accepted_of_selected 11 102173 ⟨1408398, by decide⟩ ⟨11, 2, 0, 1408398, 102173, 2601, 262144⟩
    (by decide) selected_cut_49703

theorem selected_cut_49704 : selected 10 ⟨1408431, by decide⟩
    (prefixPartial 11 102174) = some ⟨11, 2, 0, 1408431, 102174, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_102174_1408431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102174 ⟨1408431, by decide⟩ :=
  accepted_of_selected 11 102174 ⟨1408431, by decide⟩ ⟨11, 2, 0, 1408431, 102174, 2225, 262144⟩
    (by decide) selected_cut_49704

theorem selected_cut_49705 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102175) = some ⟨11, 1, 0, 977886, 102175, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102175_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102175 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102175 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102175, 1, 262144⟩
    (by decide) selected_cut_49705

theorem unmarked_context_10_25543_1408432 : frontier 11 ⟨1408432, by decide⟩
    (prefixCache 10 25543) (prefixPartial 10 25543) = false := by
  decide +kernel

theorem node_context_10_25543_1408432 : EJMOriginalGlobalDAGData.nodes 11 ⟨1408432, by decide⟩ =
    .split (coordinate 10) (![⟨1408343, by decide⟩,⟨1408398, by decide⟩,⟨1408431, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25543_1408432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25543 ⟨1408432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25543
    ⟨1408432, by decide⟩ (by decide) (![⟨1408343, by decide⟩,⟨1408398, by decide⟩,⟨1408431, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25543_1408432 node_context_10_25543_1408432
  intro a
  fin_cases a
  · exact context_11_102172_1408343
  · exact context_11_102173_1408398
  · exact context_11_102174_1408431
  · exact context_11_102175_977886

theorem unmarked_context_9_6385_1408433 : frontier 12 ⟨1408433, by decide⟩
    (prefixCache 9 6385) (prefixPartial 9 6385) = false := by
  decide +kernel

theorem node_context_9_6385_1408433 : EJMOriginalGlobalDAGData.nodes 12 ⟨1408433, by decide⟩ =
    .split (coordinate 9) (![⟨1408128, by decide⟩,⟨893098, by decide⟩,⟨1408311, by decide⟩,⟨1408432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6385_1408433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6385 ⟨1408433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6385
    ⟨1408433, by decide⟩ (by decide) (![⟨1408128, by decide⟩,⟨893098, by decide⟩,⟨1408311, by decide⟩,⟨1408432, by decide⟩]) unmarked_context_9_6385_1408433 node_context_9_6385_1408433
  intro a
  fin_cases a
  · exact context_10_25540_1408128
  · exact context_10_25541_893098
  · exact context_10_25542_1408311
  · exact context_10_25543_1408432

theorem selected_cut_49706 : selected 10 ⟨1408434, by decide⟩
    (prefixPartial 11 102176) = some ⟨11, 2, 0, 1408434, 102176, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102176_1408434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102176 ⟨1408434, by decide⟩ :=
  accepted_of_selected 11 102176 ⟨1408434, by decide⟩ ⟨11, 2, 0, 1408434, 102176, 5, 262144⟩
    (by decide) selected_cut_49706

theorem selected_cut_49707 : selected 10 ⟨1408458, by decide⟩
    (prefixPartial 11 102177) = some ⟨11, 2, 0, 1408458, 102177, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_102177_1408458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102177 ⟨1408458, by decide⟩ :=
  accepted_of_selected 11 102177 ⟨1408458, by decide⟩ ⟨11, 2, 0, 1408458, 102177, 1369, 262144⟩
    (by decide) selected_cut_49707

theorem selected_cut_49708 : selected 10 ⟨1408504, by decide⟩
    (prefixPartial 11 102178) = some ⟨11, 2, 0, 1408504, 102178, 2181, 262144⟩ := by
  decide +kernel

theorem context_11_102178_1408504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102178 ⟨1408504, by decide⟩ :=
  accepted_of_selected 11 102178 ⟨1408504, by decide⟩ ⟨11, 2, 0, 1408504, 102178, 2181, 262144⟩
    (by decide) selected_cut_49708

theorem selected_cut_49709 : selected 10 ⟨1408523, by decide⟩
    (prefixPartial 11 102179) = some ⟨11, 2, 0, 1408523, 102179, 1229, 262144⟩ := by
  decide +kernel

theorem context_11_102179_1408523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102179 ⟨1408523, by decide⟩ :=
  accepted_of_selected 11 102179 ⟨1408523, by decide⟩ ⟨11, 2, 0, 1408523, 102179, 1229, 262144⟩
    (by decide) selected_cut_49709

theorem unmarked_context_10_25544_1408524 : frontier 11 ⟨1408524, by decide⟩
    (prefixCache 10 25544) (prefixPartial 10 25544) = false := by
  decide +kernel

theorem node_context_10_25544_1408524 : EJMOriginalGlobalDAGData.nodes 11 ⟨1408524, by decide⟩ =
    .split (coordinate 10) (![⟨1408434, by decide⟩,⟨1408458, by decide⟩,⟨1408504, by decide⟩,⟨1408523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25544_1408524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25544 ⟨1408524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25544
    ⟨1408524, by decide⟩ (by decide) (![⟨1408434, by decide⟩,⟨1408458, by decide⟩,⟨1408504, by decide⟩,⟨1408523, by decide⟩]) unmarked_context_10_25544_1408524 node_context_10_25544_1408524
  intro a
  fin_cases a
  · exact context_11_102176_1408434
  · exact context_11_102177_1408458
  · exact context_11_102178_1408504
  · exact context_11_102179_1408523

theorem selected_cut_49710 : selected 10 ⟨1408568, by decide⟩
    (prefixPartial 11 102180) = some ⟨11, 2, 0, 1408568, 102180, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_102180_1408568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102180 ⟨1408568, by decide⟩ :=
  accepted_of_selected 11 102180 ⟨1408568, by decide⟩ ⟨11, 2, 0, 1408568, 102180, 1661, 262144⟩
    (by decide) selected_cut_49710

theorem selected_cut_49711 : selected 10 ⟨1408581, by decide⟩
    (prefixPartial 11 102181) = some ⟨11, 2, 0, 1408581, 102181, 609, 262144⟩ := by
  decide +kernel

theorem context_11_102181_1408581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102181 ⟨1408581, by decide⟩ :=
  accepted_of_selected 11 102181 ⟨1408581, by decide⟩ ⟨11, 2, 0, 1408581, 102181, 609, 262144⟩
    (by decide) selected_cut_49711

theorem selected_cut_49712 : selected 10 ⟨1408627, by decide⟩
    (prefixPartial 11 102182) = some ⟨11, 2, 0, 1408627, 102182, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_102182_1408627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102182 ⟨1408627, by decide⟩ :=
  accepted_of_selected 11 102182 ⟨1408627, by decide⟩ ⟨11, 2, 0, 1408627, 102182, 1925, 262144⟩
    (by decide) selected_cut_49712

theorem selected_cut_49713 : selected 10 ⟨1408661, by decide⟩
    (prefixPartial 11 102183) = some ⟨11, 2, 0, 1408661, 102183, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_102183_1408661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102183 ⟨1408661, by decide⟩ :=
  accepted_of_selected 11 102183 ⟨1408661, by decide⟩ ⟨11, 2, 0, 1408661, 102183, 1493, 262144⟩
    (by decide) selected_cut_49713

theorem unmarked_context_10_25545_1408662 : frontier 11 ⟨1408662, by decide⟩
    (prefixCache 10 25545) (prefixPartial 10 25545) = false := by
  decide +kernel

theorem node_context_10_25545_1408662 : EJMOriginalGlobalDAGData.nodes 11 ⟨1408662, by decide⟩ =
    .split (coordinate 10) (![⟨1408568, by decide⟩,⟨1408581, by decide⟩,⟨1408627, by decide⟩,⟨1408661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25545_1408662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25545 ⟨1408662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25545
    ⟨1408662, by decide⟩ (by decide) (![⟨1408568, by decide⟩,⟨1408581, by decide⟩,⟨1408627, by decide⟩,⟨1408661, by decide⟩]) unmarked_context_10_25545_1408662 node_context_10_25545_1408662
  intro a
  fin_cases a
  · exact context_11_102180_1408568
  · exact context_11_102181_1408581
  · exact context_11_102182_1408627
  · exact context_11_102183_1408661

theorem selected_cut_49714 : selected 11 ⟨1408691, by decide⟩
    (prefixPartial 10 25546) = some ⟨10, 2, 0, 1408691, 25546, 1033, 1048576⟩ := by
  decide +kernel

theorem context_10_25546_1408691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25546 ⟨1408691, by decide⟩ :=
  accepted_of_selected 10 25546 ⟨1408691, by decide⟩ ⟨10, 2, 0, 1408691, 25546, 1033, 1048576⟩
    (by decide) selected_cut_49714

theorem selected_cut_49715 : selected 11 ⟨1408756, by decide⟩
    (prefixPartial 10 25547) = some ⟨10, 2, 0, 1408756, 25547, 3289, 1048576⟩ := by
  decide +kernel

theorem context_10_25547_1408756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25547 ⟨1408756, by decide⟩ :=
  accepted_of_selected 10 25547 ⟨1408756, by decide⟩ ⟨10, 2, 0, 1408756, 25547, 3289, 1048576⟩
    (by decide) selected_cut_49715

theorem unmarked_context_9_6386_1408757 : frontier 12 ⟨1408757, by decide⟩
    (prefixCache 9 6386) (prefixPartial 9 6386) = false := by
  decide +kernel

theorem node_context_9_6386_1408757 : EJMOriginalGlobalDAGData.nodes 12 ⟨1408757, by decide⟩ =
    .split (coordinate 9) (![⟨1408524, by decide⟩,⟨1408662, by decide⟩,⟨1408691, by decide⟩,⟨1408756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6386_1408757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6386 ⟨1408757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6386
    ⟨1408757, by decide⟩ (by decide) (![⟨1408524, by decide⟩,⟨1408662, by decide⟩,⟨1408691, by decide⟩,⟨1408756, by decide⟩]) unmarked_context_9_6386_1408757 node_context_9_6386_1408757
  intro a
  fin_cases a
  · exact context_10_25544_1408524
  · exact context_10_25545_1408662
  · exact context_10_25546_1408691
  · exact context_10_25547_1408756

theorem selected_cut_49716 : selected 11 ⟨1408791, by decide⟩
    (prefixPartial 10 25548) = some ⟨10, 2, 0, 1408791, 25548, 1757, 1048576⟩ := by
  decide +kernel

theorem context_10_25548_1408791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25548 ⟨1408791, by decide⟩ :=
  accepted_of_selected 10 25548 ⟨1408791, by decide⟩ ⟨10, 2, 0, 1408791, 25548, 1757, 1048576⟩
    (by decide) selected_cut_49716

theorem selected_cut_49717 : selected 11 ⟨1408836, by decide⟩
    (prefixPartial 10 25549) = some ⟨10, 2, 0, 1408836, 25549, 1729, 1048576⟩ := by
  decide +kernel

theorem context_10_25549_1408836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25549 ⟨1408836, by decide⟩ :=
  accepted_of_selected 10 25549 ⟨1408836, by decide⟩ ⟨10, 2, 0, 1408836, 25549, 1729, 1048576⟩
    (by decide) selected_cut_49717

theorem selected_cut_49718 : selected 11 ⟨1408876, by decide⟩
    (prefixPartial 10 25550) = some ⟨10, 2, 0, 1408876, 25550, 817, 1048576⟩ := by
  decide +kernel

theorem context_10_25550_1408876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25550 ⟨1408876, by decide⟩ :=
  accepted_of_selected 10 25550 ⟨1408876, by decide⟩ ⟨10, 2, 0, 1408876, 25550, 817, 1048576⟩
    (by decide) selected_cut_49718

theorem selected_cut_49719 : selected 11 ⟨1408882, by decide⟩
    (prefixPartial 10 25551) = some ⟨10, 2, 0, 1408882, 25551, 33, 1048576⟩ := by
  decide +kernel

theorem context_10_25551_1408882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25551 ⟨1408882, by decide⟩ :=
  accepted_of_selected 10 25551 ⟨1408882, by decide⟩ ⟨10, 2, 0, 1408882, 25551, 33, 1048576⟩
    (by decide) selected_cut_49719

theorem unmarked_context_9_6387_1408883 : frontier 12 ⟨1408883, by decide⟩
    (prefixCache 9 6387) (prefixPartial 9 6387) = false := by
  decide +kernel

theorem node_context_9_6387_1408883 : EJMOriginalGlobalDAGData.nodes 12 ⟨1408883, by decide⟩ =
    .split (coordinate 9) (![⟨1408791, by decide⟩,⟨1408836, by decide⟩,⟨1408876, by decide⟩,⟨1408882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6387_1408883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6387 ⟨1408883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6387
    ⟨1408883, by decide⟩ (by decide) (![⟨1408791, by decide⟩,⟨1408836, by decide⟩,⟨1408876, by decide⟩,⟨1408882, by decide⟩]) unmarked_context_9_6387_1408883 node_context_9_6387_1408883
  intro a
  fin_cases a
  · exact context_10_25548_1408791
  · exact context_10_25549_1408836
  · exact context_10_25550_1408876
  · exact context_10_25551_1408882

theorem unmarked_context_8_1596_1408884 : frontier 13 ⟨1408884, by decide⟩
    (prefixCache 8 1596) (prefixPartial 8 1596) = false := by
  decide +kernel

theorem node_context_8_1596_1408884 : EJMOriginalGlobalDAGData.nodes 13 ⟨1408884, by decide⟩ =
    .split (coordinate 8) (![⟨1407935, by decide⟩,⟨1408433, by decide⟩,⟨1408757, by decide⟩,⟨1408883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1596_1408884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1596 ⟨1408884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1596
    ⟨1408884, by decide⟩ (by decide) (![⟨1407935, by decide⟩,⟨1408433, by decide⟩,⟨1408757, by decide⟩,⟨1408883, by decide⟩]) unmarked_context_8_1596_1408884 node_context_8_1596_1408884
  intro a
  fin_cases a
  · exact context_9_6384_1407935
  · exact context_9_6385_1408433
  · exact context_9_6386_1408757
  · exact context_9_6387_1408883

theorem selected_cut_49720 : selected 11 ⟨1408944, by decide⟩
    (prefixPartial 10 25552) = some ⟨10, 2, 0, 1408944, 25552, 2017, 1048576⟩ := by
  decide +kernel

theorem context_10_25552_1408944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25552 ⟨1408944, by decide⟩ :=
  accepted_of_selected 10 25552 ⟨1408944, by decide⟩ ⟨10, 2, 0, 1408944, 25552, 2017, 1048576⟩
    (by decide) selected_cut_49720

theorem selected_cut_49721 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408848) = some ⟨12, 1, 0, 1108174, 408848, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408848_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408848 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408848 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408848, 1, 65536⟩
    (by decide) selected_cut_49721

theorem selected_cut_49722 : selected 9 ⟨1409009, by decide⟩
    (prefixPartial 12 408849) = some ⟨12, 2, 0, 1409009, 408849, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_408849_1409009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408849 ⟨1409009, by decide⟩ :=
  accepted_of_selected 12 408849 ⟨1409009, by decide⟩ ⟨12, 2, 0, 1409009, 408849, 2229, 65536⟩
    (by decide) selected_cut_49722

theorem selected_cut_49723 : selected 9 ⟨1409066, by decide⟩
    (prefixPartial 12 408850) = some ⟨12, 2, 0, 1409066, 408850, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_408850_1409066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408850 ⟨1409066, by decide⟩ :=
  accepted_of_selected 12 408850 ⟨1409066, by decide⟩ ⟨12, 2, 0, 1409066, 408850, 2349, 65536⟩
    (by decide) selected_cut_49723

theorem selected_cut_49724 : selected 9 ⟨1409116, by decide⟩
    (prefixPartial 12 408851) = some ⟨12, 2, 0, 1409116, 408851, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_408851_1409116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408851 ⟨1409116, by decide⟩ :=
  accepted_of_selected 12 408851 ⟨1409116, by decide⟩ ⟨12, 2, 0, 1409116, 408851, 2273, 65536⟩
    (by decide) selected_cut_49724

theorem unmarked_context_11_102212_1409117 : frontier 10 ⟨1409117, by decide⟩
    (prefixCache 11 102212) (prefixPartial 11 102212) = false := by
  decide +kernel

theorem node_context_11_102212_1409117 : EJMOriginalGlobalDAGData.nodes 10 ⟨1409117, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1409009, by decide⟩,⟨1409066, by decide⟩,⟨1409116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102212_1409117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102212 ⟨1409117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102212
    ⟨1409117, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1409009, by decide⟩,⟨1409066, by decide⟩,⟨1409116, by decide⟩]) unmarked_context_11_102212_1409117 node_context_11_102212_1409117
  intro a
  fin_cases a
  · exact context_12_408848_1108174
  · exact context_12_408849_1409009
  · exact context_12_408850_1409066
  · exact context_12_408851_1409116

theorem selected_cut_49725 : selected 10 ⟨1407133, by decide⟩
    (prefixPartial 11 102213) = some ⟨11, 2, 0, 1407133, 102213, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102213_1407133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102213 ⟨1407133, by decide⟩ :=
  accepted_of_selected 11 102213 ⟨1407133, by decide⟩ ⟨11, 2, 0, 1407133, 102213, 5, 262144⟩
    (by decide) selected_cut_49725

theorem selected_cut_49726 : selected 10 ⟨1409195, by decide⟩
    (prefixPartial 11 102214) = some ⟨11, 2, 0, 1409195, 102214, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_102214_1409195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102214 ⟨1409195, by decide⟩ :=
  accepted_of_selected 11 102214 ⟨1409195, by decide⟩ ⟨11, 2, 0, 1409195, 102214, 3517, 262144⟩
    (by decide) selected_cut_49726

theorem selected_cut_49727 : selected 10 ⟨1409259, by decide⟩
    (prefixPartial 11 102215) = some ⟨11, 2, 0, 1409259, 102215, 3497, 262144⟩ := by
  decide +kernel

theorem context_11_102215_1409259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102215 ⟨1409259, by decide⟩ :=
  accepted_of_selected 11 102215 ⟨1409259, by decide⟩ ⟨11, 2, 0, 1409259, 102215, 3497, 262144⟩
    (by decide) selected_cut_49727

theorem unmarked_context_10_25553_1409260 : frontier 11 ⟨1409260, by decide⟩
    (prefixCache 10 25553) (prefixPartial 10 25553) = false := by
  decide +kernel

theorem node_context_10_25553_1409260 : EJMOriginalGlobalDAGData.nodes 11 ⟨1409260, by decide⟩ =
    .split (coordinate 10) (![⟨1409117, by decide⟩,⟨1407133, by decide⟩,⟨1409195, by decide⟩,⟨1409259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25553_1409260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25553 ⟨1409260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25553
    ⟨1409260, by decide⟩ (by decide) (![⟨1409117, by decide⟩,⟨1407133, by decide⟩,⟨1409195, by decide⟩,⟨1409259, by decide⟩]) unmarked_context_10_25553_1409260 node_context_10_25553_1409260
  intro a
  fin_cases a
  · exact context_11_102212_1409117
  · exact context_11_102213_1407133
  · exact context_11_102214_1409195
  · exact context_11_102215_1409259

theorem selected_cut_49728 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408864) = some ⟨12, 1, 0, 1108174, 408864, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408864_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408864 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408864 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408864, 1, 65536⟩
    (by decide) selected_cut_49728

theorem selected_cut_49729 : selected 9 ⟨1409323, by decide⟩
    (prefixPartial 12 408865) = some ⟨12, 2, 0, 1409323, 408865, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_408865_1409323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408865 ⟨1409323, by decide⟩ :=
  accepted_of_selected 12 408865 ⟨1409323, by decide⟩ ⟨12, 2, 0, 1409323, 408865, 2205, 65536⟩
    (by decide) selected_cut_49729

theorem selected_cut_49730 : selected 9 ⟨1409387, by decide⟩
    (prefixPartial 12 408866) = some ⟨12, 2, 0, 1409387, 408866, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_408866_1409387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408866 ⟨1409387, by decide⟩ :=
  accepted_of_selected 12 408866 ⟨1409387, by decide⟩ ⟨12, 2, 0, 1409387, 408866, 2249, 65536⟩
    (by decide) selected_cut_49730

theorem selected_cut_49731 : selected 9 ⟨1409426, by decide⟩
    (prefixPartial 12 408867) = some ⟨12, 2, 0, 1409426, 408867, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_408867_1409426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408867 ⟨1409426, by decide⟩ :=
  accepted_of_selected 12 408867 ⟨1409426, by decide⟩ ⟨12, 2, 0, 1409426, 408867, 1909, 65536⟩
    (by decide) selected_cut_49731

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
