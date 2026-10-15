/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover464
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44643 : selected 10 ⟨1229238, by decide⟩
    (prefixPartial 11 88665) = some ⟨11, 2, 0, 1229238, 88665, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_88665_1229238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88665 ⟨1229238, by decide⟩ :=
  accepted_of_selected 11 88665 ⟨1229238, by decide⟩ ⟨11, 2, 0, 1229238, 88665, 3117, 262144⟩
    (by decide) selected_cut_44643

theorem selected_cut_44644 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88666) = some ⟨11, 1, 0, 900587, 88666, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88666_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88666 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88666 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88666, 1, 262144⟩
    (by decide) selected_cut_44644

theorem selected_cut_44645 : selected 10 ⟨1229293, by decide⟩
    (prefixPartial 11 88667) = some ⟨11, 2, 0, 1229293, 88667, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_88667_1229293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88667 ⟨1229293, by decide⟩ :=
  accepted_of_selected 11 88667 ⟨1229293, by decide⟩ ⟨11, 2, 0, 1229293, 88667, 2897, 262144⟩
    (by decide) selected_cut_44645

theorem unmarked_context_10_22166_1229294 : frontier 11 ⟨1229294, by decide⟩
    (prefixCache 10 22166) (prefixPartial 10 22166) = false := by
  decide +kernel

theorem node_context_10_22166_1229294 : EJMOriginalGlobalDAGData.nodes 11 ⟨1229294, by decide⟩ =
    .split (coordinate 10) (![⟨1229181, by decide⟩,⟨1229238, by decide⟩,⟨900587, by decide⟩,⟨1229293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22166_1229294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22166 ⟨1229294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22166
    ⟨1229294, by decide⟩ (by decide) (![⟨1229181, by decide⟩,⟨1229238, by decide⟩,⟨900587, by decide⟩,⟨1229293, by decide⟩]) unmarked_context_10_22166_1229294 node_context_10_22166_1229294
  intro a
  fin_cases a
  · exact context_11_88664_1229181
  · exact context_11_88665_1229238
  · exact context_11_88666_900587
  · exact context_11_88667_1229293

theorem selected_cut_44646 : selected 10 ⟨1229363, by decide⟩
    (prefixPartial 11 88668) = some ⟨11, 2, 0, 1229363, 88668, 3945, 262144⟩ := by
  decide +kernel

theorem context_11_88668_1229363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88668 ⟨1229363, by decide⟩ :=
  accepted_of_selected 11 88668 ⟨1229363, by decide⟩ ⟨11, 2, 0, 1229363, 88668, 3945, 262144⟩
    (by decide) selected_cut_44646

theorem selected_cut_44647 : selected 10 ⟨1229413, by decide⟩
    (prefixPartial 11 88669) = some ⟨11, 2, 0, 1229413, 88669, 3089, 262144⟩ := by
  decide +kernel

theorem context_11_88669_1229413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88669 ⟨1229413, by decide⟩ :=
  accepted_of_selected 11 88669 ⟨1229413, by decide⟩ ⟨11, 2, 0, 1229413, 88669, 3089, 262144⟩
    (by decide) selected_cut_44647

theorem selected_cut_44648 : selected 10 ⟨1229447, by decide⟩
    (prefixPartial 11 88670) = some ⟨11, 2, 0, 1229447, 88670, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_88670_1229447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88670 ⟨1229447, by decide⟩ :=
  accepted_of_selected 11 88670 ⟨1229447, by decide⟩ ⟨11, 2, 0, 1229447, 88670, 2205, 262144⟩
    (by decide) selected_cut_44648

theorem selected_cut_44649 : selected 10 ⟨1229479, by decide⟩
    (prefixPartial 11 88671) = some ⟨11, 2, 0, 1229479, 88671, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_88671_1229479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88671 ⟨1229479, by decide⟩ :=
  accepted_of_selected 11 88671 ⟨1229479, by decide⟩ ⟨11, 2, 0, 1229479, 88671, 2113, 262144⟩
    (by decide) selected_cut_44649

theorem unmarked_context_10_22167_1229480 : frontier 11 ⟨1229480, by decide⟩
    (prefixCache 10 22167) (prefixPartial 10 22167) = false := by
  decide +kernel

theorem node_context_10_22167_1229480 : EJMOriginalGlobalDAGData.nodes 11 ⟨1229480, by decide⟩ =
    .split (coordinate 10) (![⟨1229363, by decide⟩,⟨1229413, by decide⟩,⟨1229447, by decide⟩,⟨1229479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22167_1229480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22167 ⟨1229480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22167
    ⟨1229480, by decide⟩ (by decide) (![⟨1229363, by decide⟩,⟨1229413, by decide⟩,⟨1229447, by decide⟩,⟨1229479, by decide⟩]) unmarked_context_10_22167_1229480 node_context_10_22167_1229480
  intro a
  fin_cases a
  · exact context_11_88668_1229363
  · exact context_11_88669_1229413
  · exact context_11_88670_1229447
  · exact context_11_88671_1229479

theorem unmarked_context_9_5541_1229481 : frontier 12 ⟨1229481, by decide⟩
    (prefixCache 9 5541) (prefixPartial 9 5541) = false := by
  decide +kernel

theorem node_context_9_5541_1229481 : EJMOriginalGlobalDAGData.nodes 12 ⟨1229481, by decide⟩ =
    .split (coordinate 9) (![⟨1229120, by decide⟩,⟨893098, by decide⟩,⟨1229294, by decide⟩,⟨1229480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5541_1229481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5541 ⟨1229481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5541
    ⟨1229481, by decide⟩ (by decide) (![⟨1229120, by decide⟩,⟨893098, by decide⟩,⟨1229294, by decide⟩,⟨1229480, by decide⟩]) unmarked_context_9_5541_1229481 node_context_9_5541_1229481
  intro a
  fin_cases a
  · exact context_10_22164_1229120
  · exact context_10_22165_893098
  · exact context_10_22166_1229294
  · exact context_10_22167_1229480

theorem selected_cut_44650 : selected 10 ⟨1229523, by decide⟩
    (prefixPartial 11 88672) = some ⟨11, 2, 0, 1229523, 88672, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_88672_1229523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88672 ⟨1229523, by decide⟩ :=
  accepted_of_selected 11 88672 ⟨1229523, by decide⟩ ⟨11, 2, 0, 1229523, 88672, 3233, 262144⟩
    (by decide) selected_cut_44650

theorem selected_cut_44651 : selected 10 ⟨1229555, by decide⟩
    (prefixPartial 11 88673) = some ⟨11, 2, 0, 1229555, 88673, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_88673_1229555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88673 ⟨1229555, by decide⟩ :=
  accepted_of_selected 11 88673 ⟨1229555, by decide⟩ ⟨11, 2, 0, 1229555, 88673, 2141, 262144⟩
    (by decide) selected_cut_44651

theorem selected_cut_44652 : selected 10 ⟨1229615, by decide⟩
    (prefixPartial 11 88674) = some ⟨11, 2, 0, 1229615, 88674, 3245, 262144⟩ := by
  decide +kernel

theorem context_11_88674_1229615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88674 ⟨1229615, by decide⟩ :=
  accepted_of_selected 11 88674 ⟨1229615, by decide⟩ ⟨11, 2, 0, 1229615, 88674, 3245, 262144⟩
    (by decide) selected_cut_44652

theorem selected_cut_44653 : selected 10 ⟨1229674, by decide⟩
    (prefixPartial 11 88675) = some ⟨11, 2, 0, 1229674, 88675, 3993, 262144⟩ := by
  decide +kernel

theorem context_11_88675_1229674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88675 ⟨1229674, by decide⟩ :=
  accepted_of_selected 11 88675 ⟨1229674, by decide⟩ ⟨11, 2, 0, 1229674, 88675, 3993, 262144⟩
    (by decide) selected_cut_44653

theorem unmarked_context_10_22168_1229675 : frontier 11 ⟨1229675, by decide⟩
    (prefixCache 10 22168) (prefixPartial 10 22168) = false := by
  decide +kernel

theorem node_context_10_22168_1229675 : EJMOriginalGlobalDAGData.nodes 11 ⟨1229675, by decide⟩ =
    .split (coordinate 10) (![⟨1229523, by decide⟩,⟨1229555, by decide⟩,⟨1229615, by decide⟩,⟨1229674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22168_1229675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22168 ⟨1229675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22168
    ⟨1229675, by decide⟩ (by decide) (![⟨1229523, by decide⟩,⟨1229555, by decide⟩,⟨1229615, by decide⟩,⟨1229674, by decide⟩]) unmarked_context_10_22168_1229675 node_context_10_22168_1229675
  intro a
  fin_cases a
  · exact context_11_88672_1229523
  · exact context_11_88673_1229555
  · exact context_11_88674_1229615
  · exact context_11_88675_1229674

theorem selected_cut_44654 : selected 10 ⟨1229713, by decide⟩
    (prefixPartial 11 88676) = some ⟨11, 2, 0, 1229713, 88676, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_88676_1229713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88676 ⟨1229713, by decide⟩ :=
  accepted_of_selected 11 88676 ⟨1229713, by decide⟩ ⟨11, 2, 0, 1229713, 88676, 2465, 262144⟩
    (by decide) selected_cut_44654

theorem selected_cut_44655 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 88677) = some ⟨11, 1, 0, 1192826, 88677, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88677_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88677 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 88677 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 88677, 1, 262144⟩
    (by decide) selected_cut_44655

theorem selected_cut_44656 : selected 10 ⟨1229751, by decide⟩
    (prefixPartial 11 88678) = some ⟨11, 2, 0, 1229751, 88678, 2245, 262144⟩ := by
  decide +kernel

theorem context_11_88678_1229751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88678 ⟨1229751, by decide⟩ :=
  accepted_of_selected 11 88678 ⟨1229751, by decide⟩ ⟨11, 2, 0, 1229751, 88678, 2245, 262144⟩
    (by decide) selected_cut_44656

theorem selected_cut_44657 : selected 10 ⟨1229780, by decide⟩
    (prefixPartial 11 88679) = some ⟨11, 2, 0, 1229780, 88679, 2105, 262144⟩ := by
  decide +kernel

theorem context_11_88679_1229780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88679 ⟨1229780, by decide⟩ :=
  accepted_of_selected 11 88679 ⟨1229780, by decide⟩ ⟨11, 2, 0, 1229780, 88679, 2105, 262144⟩
    (by decide) selected_cut_44657

theorem unmarked_context_10_22169_1229781 : frontier 11 ⟨1229781, by decide⟩
    (prefixCache 10 22169) (prefixPartial 10 22169) = false := by
  decide +kernel

theorem node_context_10_22169_1229781 : EJMOriginalGlobalDAGData.nodes 11 ⟨1229781, by decide⟩ =
    .split (coordinate 10) (![⟨1229713, by decide⟩,⟨1192826, by decide⟩,⟨1229751, by decide⟩,⟨1229780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22169_1229781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22169 ⟨1229781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22169
    ⟨1229781, by decide⟩ (by decide) (![⟨1229713, by decide⟩,⟨1192826, by decide⟩,⟨1229751, by decide⟩,⟨1229780, by decide⟩]) unmarked_context_10_22169_1229781 node_context_10_22169_1229781
  intro a
  fin_cases a
  · exact context_11_88676_1229713
  · exact context_11_88677_1192826
  · exact context_11_88678_1229751
  · exact context_11_88679_1229780

theorem selected_cut_44658 : selected 11 ⟨1229828, by decide⟩
    (prefixPartial 10 22170) = some ⟨10, 2, 0, 1229828, 22170, 2793, 1048576⟩ := by
  decide +kernel

theorem context_10_22170_1229828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22170 ⟨1229828, by decide⟩ :=
  accepted_of_selected 10 22170 ⟨1229828, by decide⟩ ⟨10, 2, 0, 1229828, 22170, 2793, 1048576⟩
    (by decide) selected_cut_44658

theorem selected_cut_44659 : selected 10 ⟨1229882, by decide⟩
    (prefixPartial 11 88684) = some ⟨11, 2, 0, 1229882, 88684, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_88684_1229882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88684 ⟨1229882, by decide⟩ :=
  accepted_of_selected 11 88684 ⟨1229882, by decide⟩ ⟨11, 2, 0, 1229882, 88684, 2717, 262144⟩
    (by decide) selected_cut_44659

theorem selected_cut_44660 : selected 10 ⟨1229904, by decide⟩
    (prefixPartial 11 88685) = some ⟨11, 2, 0, 1229904, 88685, 1109, 262144⟩ := by
  decide +kernel

theorem context_11_88685_1229904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88685 ⟨1229904, by decide⟩ :=
  accepted_of_selected 11 88685 ⟨1229904, by decide⟩ ⟨11, 2, 0, 1229904, 88685, 1109, 262144⟩
    (by decide) selected_cut_44660

theorem selected_cut_44661 : selected 10 ⟨1229932, by decide⟩
    (prefixPartial 11 88686) = some ⟨11, 2, 0, 1229932, 88686, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_88686_1229932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88686 ⟨1229932, by decide⟩ :=
  accepted_of_selected 11 88686 ⟨1229932, by decide⟩ ⟨11, 2, 0, 1229932, 88686, 1641, 262144⟩
    (by decide) selected_cut_44661

theorem selected_cut_44662 : selected 10 ⟨1229968, by decide⟩
    (prefixPartial 11 88687) = some ⟨11, 2, 0, 1229968, 88687, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_88687_1229968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88687 ⟨1229968, by decide⟩ :=
  accepted_of_selected 11 88687 ⟨1229968, by decide⟩ ⟨11, 2, 0, 1229968, 88687, 1669, 262144⟩
    (by decide) selected_cut_44662

theorem unmarked_context_10_22171_1229969 : frontier 11 ⟨1229969, by decide⟩
    (prefixCache 10 22171) (prefixPartial 10 22171) = false := by
  decide +kernel

theorem node_context_10_22171_1229969 : EJMOriginalGlobalDAGData.nodes 11 ⟨1229969, by decide⟩ =
    .split (coordinate 10) (![⟨1229882, by decide⟩,⟨1229904, by decide⟩,⟨1229932, by decide⟩,⟨1229968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22171_1229969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22171 ⟨1229969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22171
    ⟨1229969, by decide⟩ (by decide) (![⟨1229882, by decide⟩,⟨1229904, by decide⟩,⟨1229932, by decide⟩,⟨1229968, by decide⟩]) unmarked_context_10_22171_1229969 node_context_10_22171_1229969
  intro a
  fin_cases a
  · exact context_11_88684_1229882
  · exact context_11_88685_1229904
  · exact context_11_88686_1229932
  · exact context_11_88687_1229968

theorem unmarked_context_9_5542_1229970 : frontier 12 ⟨1229970, by decide⟩
    (prefixCache 9 5542) (prefixPartial 9 5542) = false := by
  decide +kernel

theorem node_context_9_5542_1229970 : EJMOriginalGlobalDAGData.nodes 12 ⟨1229970, by decide⟩ =
    .split (coordinate 9) (![⟨1229675, by decide⟩,⟨1229781, by decide⟩,⟨1229828, by decide⟩,⟨1229969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5542_1229970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5542 ⟨1229970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5542
    ⟨1229970, by decide⟩ (by decide) (![⟨1229675, by decide⟩,⟨1229781, by decide⟩,⟨1229828, by decide⟩,⟨1229969, by decide⟩]) unmarked_context_9_5542_1229970 node_context_9_5542_1229970
  intro a
  fin_cases a
  · exact context_10_22168_1229675
  · exact context_10_22169_1229781
  · exact context_10_22170_1229828
  · exact context_10_22171_1229969

theorem selected_cut_44663 : selected 10 ⟨1229992, by decide⟩
    (prefixPartial 11 88688) = some ⟨11, 2, 0, 1229992, 88688, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_88688_1229992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88688 ⟨1229992, by decide⟩ :=
  accepted_of_selected 11 88688 ⟨1229992, by decide⟩ ⟨11, 2, 0, 1229992, 88688, 1381, 262144⟩
    (by decide) selected_cut_44663

theorem selected_cut_44664 : selected 10 ⟨1230009, by decide⟩
    (prefixPartial 11 88689) = some ⟨11, 2, 0, 1230009, 88689, 889, 262144⟩ := by
  decide +kernel

theorem context_11_88689_1230009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88689 ⟨1230009, by decide⟩ :=
  accepted_of_selected 11 88689 ⟨1230009, by decide⟩ ⟨11, 2, 0, 1230009, 88689, 889, 262144⟩
    (by decide) selected_cut_44664

theorem selected_cut_44665 : selected 10 ⟨1230036, by decide⟩
    (prefixPartial 11 88690) = some ⟨11, 2, 0, 1230036, 88690, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_88690_1230036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88690 ⟨1230036, by decide⟩ :=
  accepted_of_selected 11 88690 ⟨1230036, by decide⟩ ⟨11, 2, 0, 1230036, 88690, 1613, 262144⟩
    (by decide) selected_cut_44665

theorem selected_cut_44666 : selected 10 ⟨1230058, by decide⟩
    (prefixPartial 11 88691) = some ⟨11, 2, 0, 1230058, 88691, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_88691_1230058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88691 ⟨1230058, by decide⟩ :=
  accepted_of_selected 11 88691 ⟨1230058, by decide⟩ ⟨11, 2, 0, 1230058, 88691, 1149, 262144⟩
    (by decide) selected_cut_44666

theorem unmarked_context_10_22172_1230059 : frontier 11 ⟨1230059, by decide⟩
    (prefixCache 10 22172) (prefixPartial 10 22172) = false := by
  decide +kernel

theorem node_context_10_22172_1230059 : EJMOriginalGlobalDAGData.nodes 11 ⟨1230059, by decide⟩ =
    .split (coordinate 10) (![⟨1229992, by decide⟩,⟨1230009, by decide⟩,⟨1230036, by decide⟩,⟨1230058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22172_1230059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22172 ⟨1230059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22172
    ⟨1230059, by decide⟩ (by decide) (![⟨1229992, by decide⟩,⟨1230009, by decide⟩,⟨1230036, by decide⟩,⟨1230058, by decide⟩]) unmarked_context_10_22172_1230059 node_context_10_22172_1230059
  intro a
  fin_cases a
  · exact context_11_88688_1229992
  · exact context_11_88689_1230009
  · exact context_11_88690_1230036
  · exact context_11_88691_1230058

theorem selected_cut_44667 : selected 11 ⟨1230099, by decide⟩
    (prefixPartial 10 22173) = some ⟨10, 2, 0, 1230099, 22173, 2337, 1048576⟩ := by
  decide +kernel

theorem context_10_22173_1230099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22173 ⟨1230099, by decide⟩ :=
  accepted_of_selected 10 22173 ⟨1230099, by decide⟩ ⟨10, 2, 0, 1230099, 22173, 2337, 1048576⟩
    (by decide) selected_cut_44667

theorem selected_cut_44668 : selected 11 ⟨1230131, by decide⟩
    (prefixPartial 10 22174) = some ⟨10, 2, 0, 1230131, 22174, 1341, 1048576⟩ := by
  decide +kernel

theorem context_10_22174_1230131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22174 ⟨1230131, by decide⟩ :=
  accepted_of_selected 10 22174 ⟨1230131, by decide⟩ ⟨10, 2, 0, 1230131, 22174, 1341, 1048576⟩
    (by decide) selected_cut_44668

theorem selected_cut_44669 : selected 11 ⟨1230152, by decide⟩
    (prefixPartial 10 22175) = some ⟨10, 2, 0, 1230152, 22175, 393, 1048576⟩ := by
  decide +kernel

theorem context_10_22175_1230152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22175 ⟨1230152, by decide⟩ :=
  accepted_of_selected 10 22175 ⟨1230152, by decide⟩ ⟨10, 2, 0, 1230152, 22175, 393, 1048576⟩
    (by decide) selected_cut_44669

theorem unmarked_context_9_5543_1230153 : frontier 12 ⟨1230153, by decide⟩
    (prefixCache 9 5543) (prefixPartial 9 5543) = false := by
  decide +kernel

theorem node_context_9_5543_1230153 : EJMOriginalGlobalDAGData.nodes 12 ⟨1230153, by decide⟩ =
    .split (coordinate 9) (![⟨1230059, by decide⟩,⟨1230099, by decide⟩,⟨1230131, by decide⟩,⟨1230152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5543_1230153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5543 ⟨1230153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5543
    ⟨1230153, by decide⟩ (by decide) (![⟨1230059, by decide⟩,⟨1230099, by decide⟩,⟨1230131, by decide⟩,⟨1230152, by decide⟩]) unmarked_context_9_5543_1230153 node_context_9_5543_1230153
  intro a
  fin_cases a
  · exact context_10_22172_1230059
  · exact context_10_22173_1230099
  · exact context_10_22174_1230131
  · exact context_10_22175_1230152

theorem unmarked_context_8_1385_1230154 : frontier 13 ⟨1230154, by decide⟩
    (prefixCache 8 1385) (prefixPartial 8 1385) = false := by
  decide +kernel

theorem node_context_8_1385_1230154 : EJMOriginalGlobalDAGData.nodes 13 ⟨1230154, by decide⟩ =
    .split (coordinate 8) (![⟨1228926, by decide⟩,⟨1229481, by decide⟩,⟨1229970, by decide⟩,⟨1230153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1385_1230154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1385 ⟨1230154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1385
    ⟨1230154, by decide⟩ (by decide) (![⟨1228926, by decide⟩,⟨1229481, by decide⟩,⟨1229970, by decide⟩,⟨1230153, by decide⟩]) unmarked_context_8_1385_1230154 node_context_8_1385_1230154
  intro a
  fin_cases a
  · exact context_9_5540_1228926
  · exact context_9_5541_1229481
  · exact context_9_5542_1229970
  · exact context_9_5543_1230153

theorem selected_cut_44670 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88704) = some ⟨11, 1, 0, 434745, 88704, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88704_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88704 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88704 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88704, 1, 262144⟩
    (by decide) selected_cut_44670

theorem selected_cut_44671 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354820) = some ⟨12, 1, 0, 448748, 354820, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354820_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354820 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354820 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354820, 1, 65536⟩
    (by decide) selected_cut_44671

theorem selected_cut_44672 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 354821) = some ⟨12, 1, 0, 34034, 354821, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354821_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354821 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 354821 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 354821, 1, 65536⟩
    (by decide) selected_cut_44672

theorem selected_cut_44673 : selected 9 ⟨1230209, by decide⟩
    (prefixPartial 12 354822) = some ⟨12, 2, 0, 1230209, 354822, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_354822_1230209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354822 ⟨1230209, by decide⟩ :=
  accepted_of_selected 12 354822 ⟨1230209, by decide⟩ ⟨12, 2, 0, 1230209, 354822, 2813, 65536⟩
    (by decide) selected_cut_44673

theorem selected_cut_44674 : selected 9 ⟨1230275, by decide⟩
    (prefixPartial 12 354823) = some ⟨12, 2, 0, 1230275, 354823, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_354823_1230275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354823 ⟨1230275, by decide⟩ :=
  accepted_of_selected 12 354823 ⟨1230275, by decide⟩ ⟨12, 2, 0, 1230275, 354823, 3449, 65536⟩
    (by decide) selected_cut_44674

theorem unmarked_context_11_88705_1230276 : frontier 10 ⟨1230276, by decide⟩
    (prefixCache 11 88705) (prefixPartial 11 88705) = false := by
  decide +kernel

theorem node_context_11_88705_1230276 : EJMOriginalGlobalDAGData.nodes 10 ⟨1230276, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1230209, by decide⟩,⟨1230275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88705_1230276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88705 ⟨1230276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88705
    ⟨1230276, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1230209, by decide⟩,⟨1230275, by decide⟩]) unmarked_context_11_88705_1230276 node_context_11_88705_1230276
  intro a
  fin_cases a
  · exact context_12_354820_448748
  · exact context_12_354821_34034
  · exact context_12_354822_1230209
  · exact context_12_354823_1230275

theorem selected_cut_44675 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354824) = some ⟨12, 1, 0, 448748, 354824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354824_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354824 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354824 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354824, 1, 65536⟩
    (by decide) selected_cut_44675

theorem selected_cut_44676 : selected 9 ⟨1230335, by decide⟩
    (prefixPartial 12 354825) = some ⟨12, 2, 0, 1230335, 354825, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_354825_1230335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354825 ⟨1230335, by decide⟩ :=
  accepted_of_selected 12 354825 ⟨1230335, by decide⟩ ⟨12, 2, 0, 1230335, 354825, 3005, 65536⟩
    (by decide) selected_cut_44676

theorem selected_cut_44677 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 354826) = some ⟨12, 1, 0, 893903, 354826, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354826_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354826 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 354826 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 354826, 1, 65536⟩
    (by decide) selected_cut_44677

theorem selected_cut_44678 : selected 9 ⟨1230410, by decide⟩
    (prefixPartial 12 354827) = some ⟨12, 2, 0, 1230410, 354827, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_354827_1230410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354827 ⟨1230410, by decide⟩ :=
  accepted_of_selected 12 354827 ⟨1230410, by decide⟩ ⟨12, 2, 0, 1230410, 354827, 3565, 65536⟩
    (by decide) selected_cut_44678

theorem unmarked_context_11_88706_1230411 : frontier 10 ⟨1230411, by decide⟩
    (prefixCache 11 88706) (prefixPartial 11 88706) = false := by
  decide +kernel

theorem node_context_11_88706_1230411 : EJMOriginalGlobalDAGData.nodes 10 ⟨1230411, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1230335, by decide⟩,⟨893903, by decide⟩,⟨1230410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88706_1230411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88706 ⟨1230411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88706
    ⟨1230411, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1230335, by decide⟩,⟨893903, by decide⟩,⟨1230410, by decide⟩]) unmarked_context_11_88706_1230411 node_context_11_88706_1230411
  intro a
  fin_cases a
  · exact context_12_354824_448748
  · exact context_12_354825_1230335
  · exact context_12_354826_893903
  · exact context_12_354827_1230410

theorem selected_cut_44679 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354828) = some ⟨12, 1, 0, 448748, 354828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354828_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354828 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354828 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354828, 1, 65536⟩
    (by decide) selected_cut_44679

theorem selected_cut_44680 : selected 9 ⟨1230459, by decide⟩
    (prefixPartial 12 354829) = some ⟨12, 2, 0, 1230459, 354829, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_354829_1230459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354829 ⟨1230459, by decide⟩ :=
  accepted_of_selected 12 354829 ⟨1230459, by decide⟩ ⟨12, 2, 0, 1230459, 354829, 2981, 65536⟩
    (by decide) selected_cut_44680

theorem selected_cut_44681 : selected 9 ⟨1230513, by decide⟩
    (prefixPartial 12 354830) = some ⟨12, 2, 0, 1230513, 354830, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_354830_1230513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354830 ⟨1230513, by decide⟩ :=
  accepted_of_selected 12 354830 ⟨1230513, by decide⟩ ⟨12, 2, 0, 1230513, 354830, 3169, 65536⟩
    (by decide) selected_cut_44681

theorem selected_cut_44682 : selected 9 ⟨1230571, by decide⟩
    (prefixPartial 12 354831) = some ⟨12, 2, 0, 1230571, 354831, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_354831_1230571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354831 ⟨1230571, by decide⟩ :=
  accepted_of_selected 12 354831 ⟨1230571, by decide⟩ ⟨12, 2, 0, 1230571, 354831, 3409, 65536⟩
    (by decide) selected_cut_44682

theorem unmarked_context_11_88707_1230572 : frontier 10 ⟨1230572, by decide⟩
    (prefixCache 11 88707) (prefixPartial 11 88707) = false := by
  decide +kernel

theorem node_context_11_88707_1230572 : EJMOriginalGlobalDAGData.nodes 10 ⟨1230572, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1230459, by decide⟩,⟨1230513, by decide⟩,⟨1230571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88707_1230572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88707 ⟨1230572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88707
    ⟨1230572, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1230459, by decide⟩,⟨1230513, by decide⟩,⟨1230571, by decide⟩]) unmarked_context_11_88707_1230572 node_context_11_88707_1230572
  intro a
  fin_cases a
  · exact context_12_354828_448748
  · exact context_12_354829_1230459
  · exact context_12_354830_1230513
  · exact context_12_354831_1230571

theorem unmarked_context_10_22176_1230573 : frontier 11 ⟨1230573, by decide⟩
    (prefixCache 10 22176) (prefixPartial 10 22176) = false := by
  decide +kernel

theorem node_context_10_22176_1230573 : EJMOriginalGlobalDAGData.nodes 11 ⟨1230573, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1230276, by decide⟩,⟨1230411, by decide⟩,⟨1230572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22176_1230573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22176 ⟨1230573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22176
    ⟨1230573, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1230276, by decide⟩,⟨1230411, by decide⟩,⟨1230572, by decide⟩]) unmarked_context_10_22176_1230573 node_context_10_22176_1230573
  intro a
  fin_cases a
  · exact context_11_88704_434745
  · exact context_11_88705_1230276
  · exact context_11_88706_1230411
  · exact context_11_88707_1230572

theorem selected_cut_44683 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 354832) = some ⟨12, 1, 0, 435160, 354832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354832_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354832 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 354832 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 354832, 1, 65536⟩
    (by decide) selected_cut_44683

theorem selected_cut_44684 : selected 9 ⟨1230627, by decide⟩
    (prefixPartial 12 354833) = some ⟨12, 2, 0, 1230627, 354833, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_354833_1230627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354833 ⟨1230627, by decide⟩ :=
  accepted_of_selected 12 354833 ⟨1230627, by decide⟩ ⟨12, 2, 0, 1230627, 354833, 2929, 65536⟩
    (by decide) selected_cut_44684

theorem selected_cut_44685 : selected 9 ⟨1230685, by decide⟩
    (prefixPartial 12 354834) = some ⟨12, 2, 0, 1230685, 354834, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_354834_1230685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354834 ⟨1230685, by decide⟩ :=
  accepted_of_selected 12 354834 ⟨1230685, by decide⟩ ⟨12, 2, 0, 1230685, 354834, 3237, 65536⟩
    (by decide) selected_cut_44685

theorem selected_cut_44686 : selected 9 ⟨1230757, by decide⟩
    (prefixPartial 12 354835) = some ⟨12, 2, 0, 1230757, 354835, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_354835_1230757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354835 ⟨1230757, by decide⟩ :=
  accepted_of_selected 12 354835 ⟨1230757, by decide⟩ ⟨12, 2, 0, 1230757, 354835, 3765, 65536⟩
    (by decide) selected_cut_44686

theorem unmarked_context_11_88708_1230758 : frontier 10 ⟨1230758, by decide⟩
    (prefixCache 11 88708) (prefixPartial 11 88708) = false := by
  decide +kernel

theorem node_context_11_88708_1230758 : EJMOriginalGlobalDAGData.nodes 10 ⟨1230758, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1230627, by decide⟩,⟨1230685, by decide⟩,⟨1230757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88708_1230758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88708 ⟨1230758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88708
    ⟨1230758, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1230627, by decide⟩,⟨1230685, by decide⟩,⟨1230757, by decide⟩]) unmarked_context_11_88708_1230758 node_context_11_88708_1230758
  intro a
  fin_cases a
  · exact context_12_354832_435160
  · exact context_12_354833_1230627
  · exact context_12_354834_1230685
  · exact context_12_354835_1230757

theorem selected_cut_44687 : selected 10 ⟨1230825, by decide⟩
    (prefixPartial 11 88709) = some ⟨11, 2, 0, 1230825, 88709, 3637, 262144⟩ := by
  decide +kernel

theorem context_11_88709_1230825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88709 ⟨1230825, by decide⟩ :=
  accepted_of_selected 11 88709 ⟨1230825, by decide⟩ ⟨11, 2, 0, 1230825, 88709, 3637, 262144⟩
    (by decide) selected_cut_44687

theorem selected_cut_44688 : selected 9 ⟨1230872, by decide⟩
    (prefixPartial 12 354840) = some ⟨12, 2, 0, 1230872, 354840, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_354840_1230872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354840 ⟨1230872, by decide⟩ :=
  accepted_of_selected 12 354840 ⟨1230872, by decide⟩ ⟨12, 2, 0, 1230872, 354840, 1753, 65536⟩
    (by decide) selected_cut_44688

theorem selected_cut_44689 : selected 9 ⟨1230921, by decide⟩
    (prefixPartial 12 354841) = some ⟨12, 2, 0, 1230921, 354841, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_354841_1230921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354841 ⟨1230921, by decide⟩ :=
  accepted_of_selected 12 354841 ⟨1230921, by decide⟩ ⟨12, 2, 0, 1230921, 354841, 2641, 65536⟩
    (by decide) selected_cut_44689

theorem selected_cut_44690 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 354842) = some ⟨12, 1, 0, 893903, 354842, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354842_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354842 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 354842 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 354842, 1, 65536⟩
    (by decide) selected_cut_44690

theorem selected_cut_44691 : selected 9 ⟨1230981, by decide⟩
    (prefixPartial 12 354843) = some ⟨12, 2, 0, 1230981, 354843, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_354843_1230981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354843 ⟨1230981, by decide⟩ :=
  accepted_of_selected 12 354843 ⟨1230981, by decide⟩ ⟨12, 2, 0, 1230981, 354843, 3333, 65536⟩
    (by decide) selected_cut_44691

theorem unmarked_context_11_88710_1230982 : frontier 10 ⟨1230982, by decide⟩
    (prefixCache 11 88710) (prefixPartial 11 88710) = false := by
  decide +kernel

theorem node_context_11_88710_1230982 : EJMOriginalGlobalDAGData.nodes 10 ⟨1230982, by decide⟩ =
    .split (coordinate 11) (![⟨1230872, by decide⟩,⟨1230921, by decide⟩,⟨893903, by decide⟩,⟨1230981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88710_1230982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88710 ⟨1230982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88710
    ⟨1230982, by decide⟩ (by decide) (![⟨1230872, by decide⟩,⟨1230921, by decide⟩,⟨893903, by decide⟩,⟨1230981, by decide⟩]) unmarked_context_11_88710_1230982 node_context_11_88710_1230982
  intro a
  fin_cases a
  · exact context_12_354840_1230872
  · exact context_12_354841_1230921
  · exact context_12_354842_893903
  · exact context_12_354843_1230981

theorem selected_cut_44692 : selected 9 ⟨1231033, by decide⟩
    (prefixPartial 12 354844) = some ⟨12, 2, 0, 1231033, 354844, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_354844_1231033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354844 ⟨1231033, by decide⟩ :=
  accepted_of_selected 12 354844 ⟨1231033, by decide⟩ ⟨12, 2, 0, 1231033, 354844, 2913, 65536⟩
    (by decide) selected_cut_44692

theorem selected_cut_44693 : selected 9 ⟨1231074, by decide⟩
    (prefixPartial 12 354845) = some ⟨12, 2, 0, 1231074, 354845, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_354845_1231074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354845 ⟨1231074, by decide⟩ :=
  accepted_of_selected 12 354845 ⟨1231074, by decide⟩ ⟨12, 2, 0, 1231074, 354845, 2693, 65536⟩
    (by decide) selected_cut_44693

theorem selected_cut_44694 : selected 9 ⟨1231122, by decide⟩
    (prefixPartial 12 354846) = some ⟨12, 2, 0, 1231122, 354846, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_354846_1231122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354846 ⟨1231122, by decide⟩ :=
  accepted_of_selected 12 354846 ⟨1231122, by decide⟩ ⟨12, 2, 0, 1231122, 354846, 2945, 65536⟩
    (by decide) selected_cut_44694

theorem selected_cut_44695 : selected 9 ⟨1231173, by decide⟩
    (prefixPartial 12 354847) = some ⟨12, 2, 0, 1231173, 354847, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_354847_1231173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354847 ⟨1231173, by decide⟩ :=
  accepted_of_selected 12 354847 ⟨1231173, by decide⟩ ⟨12, 2, 0, 1231173, 354847, 3205, 65536⟩
    (by decide) selected_cut_44695

theorem unmarked_context_11_88711_1231174 : frontier 10 ⟨1231174, by decide⟩
    (prefixCache 11 88711) (prefixPartial 11 88711) = false := by
  decide +kernel

theorem node_context_11_88711_1231174 : EJMOriginalGlobalDAGData.nodes 10 ⟨1231174, by decide⟩ =
    .split (coordinate 11) (![⟨1231033, by decide⟩,⟨1231074, by decide⟩,⟨1231122, by decide⟩,⟨1231173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88711_1231174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88711 ⟨1231174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88711
    ⟨1231174, by decide⟩ (by decide) (![⟨1231033, by decide⟩,⟨1231074, by decide⟩,⟨1231122, by decide⟩,⟨1231173, by decide⟩]) unmarked_context_11_88711_1231174 node_context_11_88711_1231174
  intro a
  fin_cases a
  · exact context_12_354844_1231033
  · exact context_12_354845_1231074
  · exact context_12_354846_1231122
  · exact context_12_354847_1231173

theorem unmarked_context_10_22177_1231175 : frontier 11 ⟨1231175, by decide⟩
    (prefixCache 10 22177) (prefixPartial 10 22177) = false := by
  decide +kernel

theorem node_context_10_22177_1231175 : EJMOriginalGlobalDAGData.nodes 11 ⟨1231175, by decide⟩ =
    .split (coordinate 10) (![⟨1230758, by decide⟩,⟨1230825, by decide⟩,⟨1230982, by decide⟩,⟨1231174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22177_1231175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22177 ⟨1231175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22177
    ⟨1231175, by decide⟩ (by decide) (![⟨1230758, by decide⟩,⟨1230825, by decide⟩,⟨1230982, by decide⟩,⟨1231174, by decide⟩]) unmarked_context_10_22177_1231175 node_context_10_22177_1231175
  intro a
  fin_cases a
  · exact context_11_88708_1230758
  · exact context_11_88709_1230825
  · exact context_11_88710_1230982
  · exact context_11_88711_1231174

theorem selected_cut_44696 : selected 9 ⟨355612, by decide⟩
    (prefixPartial 12 354848) = some ⟨12, 1, 0, 355612, 354848, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354848_355612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354848 ⟨355612, by decide⟩ :=
  accepted_of_selected 12 354848 ⟨355612, by decide⟩ ⟨12, 1, 0, 355612, 354848, 1, 65536⟩
    (by decide) selected_cut_44696

theorem selected_cut_44697 : selected 9 ⟨1231216, by decide⟩
    (prefixPartial 12 354849) = some ⟨12, 2, 0, 1231216, 354849, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_354849_1231216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354849 ⟨1231216, by decide⟩ :=
  accepted_of_selected 12 354849 ⟨1231216, by decide⟩ ⟨12, 2, 0, 1231216, 354849, 2253, 65536⟩
    (by decide) selected_cut_44697

theorem selected_cut_44698 : selected 9 ⟨1231255, by decide⟩
    (prefixPartial 12 354850) = some ⟨12, 2, 0, 1231255, 354850, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_354850_1231255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354850 ⟨1231255, by decide⟩ :=
  accepted_of_selected 12 354850 ⟨1231255, by decide⟩ ⟨12, 2, 0, 1231255, 354850, 2209, 65536⟩
    (by decide) selected_cut_44698

theorem selected_cut_44699 : selected 9 ⟨1231317, by decide⟩
    (prefixPartial 12 354851) = some ⟨12, 2, 0, 1231317, 354851, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_354851_1231317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354851 ⟨1231317, by decide⟩ :=
  accepted_of_selected 12 354851 ⟨1231317, by decide⟩ ⟨12, 2, 0, 1231317, 354851, 2945, 65536⟩
    (by decide) selected_cut_44699

theorem unmarked_context_11_88712_1231318 : frontier 10 ⟨1231318, by decide⟩
    (prefixCache 11 88712) (prefixPartial 11 88712) = false := by
  decide +kernel

theorem node_context_11_88712_1231318 : EJMOriginalGlobalDAGData.nodes 10 ⟨1231318, by decide⟩ =
    .split (coordinate 11) (![⟨355612, by decide⟩,⟨1231216, by decide⟩,⟨1231255, by decide⟩,⟨1231317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88712_1231318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88712 ⟨1231318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88712
    ⟨1231318, by decide⟩ (by decide) (![⟨355612, by decide⟩,⟨1231216, by decide⟩,⟨1231255, by decide⟩,⟨1231317, by decide⟩]) unmarked_context_11_88712_1231318 node_context_11_88712_1231318
  intro a
  fin_cases a
  · exact context_12_354848_355612
  · exact context_12_354849_1231216
  · exact context_12_354850_1231255
  · exact context_12_354851_1231317

theorem selected_cut_44700 : selected 9 ⟨1231375, by decide⟩
    (prefixPartial 12 354852) = some ⟨12, 2, 0, 1231375, 354852, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_354852_1231375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354852 ⟨1231375, by decide⟩ :=
  accepted_of_selected 12 354852 ⟨1231375, by decide⟩ ⟨12, 2, 0, 1231375, 354852, 2593, 65536⟩
    (by decide) selected_cut_44700

theorem selected_cut_44701 : selected 9 ⟨234650, by decide⟩
    (prefixPartial 12 354853) = some ⟨12, 1, 0, 234650, 354853, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354853_234650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354853 ⟨234650, by decide⟩ :=
  accepted_of_selected 12 354853 ⟨234650, by decide⟩ ⟨12, 1, 0, 234650, 354853, 1, 65536⟩
    (by decide) selected_cut_44701

theorem selected_cut_44702 : selected 9 ⟨1231405, by decide⟩
    (prefixPartial 12 354854) = some ⟨12, 2, 0, 1231405, 354854, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_354854_1231405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354854 ⟨1231405, by decide⟩ :=
  accepted_of_selected 12 354854 ⟨1231405, by decide⟩ ⟨12, 2, 0, 1231405, 354854, 2037, 65536⟩
    (by decide) selected_cut_44702

theorem selected_cut_44703 : selected 9 ⟨1231460, by decide⟩
    (prefixPartial 12 354855) = some ⟨12, 2, 0, 1231460, 354855, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_354855_1231460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354855 ⟨1231460, by decide⟩ :=
  accepted_of_selected 12 354855 ⟨1231460, by decide⟩ ⟨12, 2, 0, 1231460, 354855, 2789, 65536⟩
    (by decide) selected_cut_44703

theorem unmarked_context_11_88713_1231461 : frontier 10 ⟨1231461, by decide⟩
    (prefixCache 11 88713) (prefixPartial 11 88713) = false := by
  decide +kernel

theorem node_context_11_88713_1231461 : EJMOriginalGlobalDAGData.nodes 10 ⟨1231461, by decide⟩ =
    .split (coordinate 11) (![⟨1231375, by decide⟩,⟨234650, by decide⟩,⟨1231405, by decide⟩,⟨1231460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88713_1231461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88713 ⟨1231461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88713
    ⟨1231461, by decide⟩ (by decide) (![⟨1231375, by decide⟩,⟨234650, by decide⟩,⟨1231405, by decide⟩,⟨1231460, by decide⟩]) unmarked_context_11_88713_1231461 node_context_11_88713_1231461
  intro a
  fin_cases a
  · exact context_12_354852_1231375
  · exact context_12_354853_234650
  · exact context_12_354854_1231405
  · exact context_12_354855_1231460

theorem selected_cut_44704 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88714) = some ⟨11, 1, 0, 900587, 88714, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88714_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88714 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88714 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88714, 1, 262144⟩
    (by decide) selected_cut_44704

theorem selected_cut_44705 : selected 9 ⟨1231514, by decide⟩
    (prefixPartial 12 354860) = some ⟨12, 2, 0, 1231514, 354860, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_354860_1231514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354860 ⟨1231514, by decide⟩ :=
  accepted_of_selected 12 354860 ⟨1231514, by decide⟩ ⟨12, 2, 0, 1231514, 354860, 2661, 65536⟩
    (by decide) selected_cut_44705

theorem selected_cut_44706 : selected 9 ⟨1231556, by decide⟩
    (prefixPartial 12 354861) = some ⟨12, 2, 0, 1231556, 354861, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_354861_1231556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354861 ⟨1231556, by decide⟩ :=
  accepted_of_selected 12 354861 ⟨1231556, by decide⟩ ⟨12, 2, 0, 1231556, 354861, 2157, 65536⟩
    (by decide) selected_cut_44706

theorem selected_cut_44707 : selected 9 ⟨1231594, by decide⟩
    (prefixPartial 12 354862) = some ⟨12, 2, 0, 1231594, 354862, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_354862_1231594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354862 ⟨1231594, by decide⟩ :=
  accepted_of_selected 12 354862 ⟨1231594, by decide⟩ ⟨12, 2, 0, 1231594, 354862, 2165, 65536⟩
    (by decide) selected_cut_44707

theorem selected_cut_44708 : selected 9 ⟨1231645, by decide⟩
    (prefixPartial 12 354863) = some ⟨12, 2, 0, 1231645, 354863, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_354863_1231645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354863 ⟨1231645, by decide⟩ :=
  accepted_of_selected 12 354863 ⟨1231645, by decide⟩ ⟨12, 2, 0, 1231645, 354863, 2581, 65536⟩
    (by decide) selected_cut_44708

theorem unmarked_context_11_88715_1231646 : frontier 10 ⟨1231646, by decide⟩
    (prefixCache 11 88715) (prefixPartial 11 88715) = false := by
  decide +kernel

theorem node_context_11_88715_1231646 : EJMOriginalGlobalDAGData.nodes 10 ⟨1231646, by decide⟩ =
    .split (coordinate 11) (![⟨1231514, by decide⟩,⟨1231556, by decide⟩,⟨1231594, by decide⟩,⟨1231645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88715_1231646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88715 ⟨1231646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88715
    ⟨1231646, by decide⟩ (by decide) (![⟨1231514, by decide⟩,⟨1231556, by decide⟩,⟨1231594, by decide⟩,⟨1231645, by decide⟩]) unmarked_context_11_88715_1231646 node_context_11_88715_1231646
  intro a
  fin_cases a
  · exact context_12_354860_1231514
  · exact context_12_354861_1231556
  · exact context_12_354862_1231594
  · exact context_12_354863_1231645

theorem unmarked_context_10_22178_1231647 : frontier 11 ⟨1231647, by decide⟩
    (prefixCache 10 22178) (prefixPartial 10 22178) = false := by
  decide +kernel

theorem node_context_10_22178_1231647 : EJMOriginalGlobalDAGData.nodes 11 ⟨1231647, by decide⟩ =
    .split (coordinate 10) (![⟨1231318, by decide⟩,⟨1231461, by decide⟩,⟨900587, by decide⟩,⟨1231646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22178_1231647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22178 ⟨1231647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22178
    ⟨1231647, by decide⟩ (by decide) (![⟨1231318, by decide⟩,⟨1231461, by decide⟩,⟨900587, by decide⟩,⟨1231646, by decide⟩]) unmarked_context_10_22178_1231647 node_context_10_22178_1231647
  intro a
  fin_cases a
  · exact context_11_88712_1231318
  · exact context_11_88713_1231461
  · exact context_11_88714_900587
  · exact context_11_88715_1231646

theorem selected_cut_44709 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 354864) = some ⟨12, 1, 0, 1187656, 354864, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354864_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354864 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 354864 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 354864, 1, 65536⟩
    (by decide) selected_cut_44709

theorem selected_cut_44710 : selected 9 ⟨1231690, by decide⟩
    (prefixPartial 12 354865) = some ⟨12, 2, 0, 1231690, 354865, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_354865_1231690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354865 ⟨1231690, by decide⟩ :=
  accepted_of_selected 12 354865 ⟨1231690, by decide⟩ ⟨12, 2, 0, 1231690, 354865, 2405, 65536⟩
    (by decide) selected_cut_44710

theorem selected_cut_44711 : selected 9 ⟨1231735, by decide⟩
    (prefixPartial 12 354866) = some ⟨12, 2, 0, 1231735, 354866, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_354866_1231735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354866 ⟨1231735, by decide⟩ :=
  accepted_of_selected 12 354866 ⟨1231735, by decide⟩ ⟨12, 2, 0, 1231735, 354866, 2505, 65536⟩
    (by decide) selected_cut_44711

theorem selected_cut_44712 : selected 9 ⟨1231796, by decide⟩
    (prefixPartial 12 354867) = some ⟨12, 2, 0, 1231796, 354867, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_354867_1231796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354867 ⟨1231796, by decide⟩ :=
  accepted_of_selected 12 354867 ⟨1231796, by decide⟩ ⟨12, 2, 0, 1231796, 354867, 2905, 65536⟩
    (by decide) selected_cut_44712

theorem unmarked_context_11_88716_1231797 : frontier 10 ⟨1231797, by decide⟩
    (prefixCache 11 88716) (prefixPartial 11 88716) = false := by
  decide +kernel

theorem node_context_11_88716_1231797 : EJMOriginalGlobalDAGData.nodes 10 ⟨1231797, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1231690, by decide⟩,⟨1231735, by decide⟩,⟨1231796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88716_1231797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88716 ⟨1231797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88716
    ⟨1231797, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1231690, by decide⟩,⟨1231735, by decide⟩,⟨1231796, by decide⟩]) unmarked_context_11_88716_1231797 node_context_11_88716_1231797
  intro a
  fin_cases a
  · exact context_12_354864_1187656
  · exact context_12_354865_1231690
  · exact context_12_354866_1231735
  · exact context_12_354867_1231796

theorem selected_cut_44713 : selected 9 ⟨1231840, by decide⟩
    (prefixPartial 12 354868) = some ⟨12, 2, 0, 1231840, 354868, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_354868_1231840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354868 ⟨1231840, by decide⟩ :=
  accepted_of_selected 12 354868 ⟨1231840, by decide⟩ ⟨12, 2, 0, 1231840, 354868, 2449, 65536⟩
    (by decide) selected_cut_44713

theorem selected_cut_44714 : selected 9 ⟨1231868, by decide⟩
    (prefixPartial 12 354869) = some ⟨12, 2, 0, 1231868, 354869, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_354869_1231868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354869 ⟨1231868, by decide⟩ :=
  accepted_of_selected 12 354869 ⟨1231868, by decide⟩ ⟨12, 2, 0, 1231868, 354869, 2109, 65536⟩
    (by decide) selected_cut_44714

theorem selected_cut_44715 : selected 9 ⟨1231910, by decide⟩
    (prefixPartial 12 354870) = some ⟨12, 2, 0, 1231910, 354870, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_354870_1231910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354870 ⟨1231910, by decide⟩ :=
  accepted_of_selected 12 354870 ⟨1231910, by decide⟩ ⟨12, 2, 0, 1231910, 354870, 2169, 65536⟩
    (by decide) selected_cut_44715

theorem selected_cut_44716 : selected 9 ⟨1231952, by decide⟩
    (prefixPartial 12 354871) = some ⟨12, 2, 0, 1231952, 354871, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_354871_1231952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354871 ⟨1231952, by decide⟩ :=
  accepted_of_selected 12 354871 ⟨1231952, by decide⟩ ⟨12, 2, 0, 1231952, 354871, 2417, 65536⟩
    (by decide) selected_cut_44716

theorem unmarked_context_11_88717_1231953 : frontier 10 ⟨1231953, by decide⟩
    (prefixCache 11 88717) (prefixPartial 11 88717) = false := by
  decide +kernel

theorem node_context_11_88717_1231953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1231953, by decide⟩ =
    .split (coordinate 11) (![⟨1231840, by decide⟩,⟨1231868, by decide⟩,⟨1231910, by decide⟩,⟨1231952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88717_1231953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88717 ⟨1231953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88717
    ⟨1231953, by decide⟩ (by decide) (![⟨1231840, by decide⟩,⟨1231868, by decide⟩,⟨1231910, by decide⟩,⟨1231952, by decide⟩]) unmarked_context_11_88717_1231953 node_context_11_88717_1231953
  intro a
  fin_cases a
  · exact context_12_354868_1231840
  · exact context_12_354869_1231868
  · exact context_12_354870_1231910
  · exact context_12_354871_1231952

theorem selected_cut_44717 : selected 9 ⟨1231994, by decide⟩
    (prefixPartial 12 354872) = some ⟨12, 2, 0, 1231994, 354872, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_354872_1231994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354872 ⟨1231994, by decide⟩ :=
  accepted_of_selected 12 354872 ⟨1231994, by decide⟩ ⟨12, 2, 0, 1231994, 354872, 2413, 65536⟩
    (by decide) selected_cut_44717

theorem selected_cut_44718 : selected 9 ⟨1232031, by decide⟩
    (prefixPartial 12 354873) = some ⟨12, 2, 0, 1232031, 354873, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_354873_1232031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354873 ⟨1232031, by decide⟩ :=
  accepted_of_selected 12 354873 ⟨1232031, by decide⟩ ⟨12, 2, 0, 1232031, 354873, 2173, 65536⟩
    (by decide) selected_cut_44718

theorem selected_cut_44719 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 354874) = some ⟨12, 1, 0, 893903, 354874, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354874_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354874 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 354874 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 354874, 1, 65536⟩
    (by decide) selected_cut_44719

theorem selected_cut_44720 : selected 9 ⟨1232085, by decide⟩
    (prefixPartial 12 354875) = some ⟨12, 2, 0, 1232085, 354875, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_354875_1232085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354875 ⟨1232085, by decide⟩ :=
  accepted_of_selected 12 354875 ⟨1232085, by decide⟩ ⟨12, 2, 0, 1232085, 354875, 2561, 65536⟩
    (by decide) selected_cut_44720

theorem unmarked_context_11_88718_1232086 : frontier 10 ⟨1232086, by decide⟩
    (prefixCache 11 88718) (prefixPartial 11 88718) = false := by
  decide +kernel

theorem node_context_11_88718_1232086 : EJMOriginalGlobalDAGData.nodes 10 ⟨1232086, by decide⟩ =
    .split (coordinate 11) (![⟨1231994, by decide⟩,⟨1232031, by decide⟩,⟨893903, by decide⟩,⟨1232085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88718_1232086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88718 ⟨1232086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88718
    ⟨1232086, by decide⟩ (by decide) (![⟨1231994, by decide⟩,⟨1232031, by decide⟩,⟨893903, by decide⟩,⟨1232085, by decide⟩]) unmarked_context_11_88718_1232086 node_context_11_88718_1232086
  intro a
  fin_cases a
  · exact context_12_354872_1231994
  · exact context_12_354873_1232031
  · exact context_12_354874_893903
  · exact context_12_354875_1232085

theorem selected_cut_44721 : selected 9 ⟨1232134, by decide⟩
    (prefixPartial 12 354876) = some ⟨12, 2, 0, 1232134, 354876, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_354876_1232134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354876 ⟨1232134, by decide⟩ :=
  accepted_of_selected 12 354876 ⟨1232134, by decide⟩ ⟨12, 2, 0, 1232134, 354876, 2305, 65536⟩
    (by decide) selected_cut_44721

theorem selected_cut_44722 : selected 9 ⟨1232167, by decide⟩
    (prefixPartial 12 354877) = some ⟨12, 2, 0, 1232167, 354877, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_354877_1232167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354877 ⟨1232167, by decide⟩ :=
  accepted_of_selected 12 354877 ⟨1232167, by decide⟩ ⟨12, 2, 0, 1232167, 354877, 1913, 65536⟩
    (by decide) selected_cut_44722

theorem selected_cut_44723 : selected 9 ⟨1232209, by decide⟩
    (prefixPartial 12 354878) = some ⟨12, 2, 0, 1232209, 354878, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_354878_1232209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354878 ⟨1232209, by decide⟩ :=
  accepted_of_selected 12 354878 ⟨1232209, by decide⟩ ⟨12, 2, 0, 1232209, 354878, 2109, 65536⟩
    (by decide) selected_cut_44723

theorem selected_cut_44724 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 354879) = some ⟨12, 1, 0, 1120582, 354879, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354879_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354879 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 354879 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 354879, 1, 65536⟩
    (by decide) selected_cut_44724

theorem unmarked_context_11_88719_1232210 : frontier 10 ⟨1232210, by decide⟩
    (prefixCache 11 88719) (prefixPartial 11 88719) = false := by
  decide +kernel

theorem node_context_11_88719_1232210 : EJMOriginalGlobalDAGData.nodes 10 ⟨1232210, by decide⟩ =
    .split (coordinate 11) (![⟨1232134, by decide⟩,⟨1232167, by decide⟩,⟨1232209, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88719_1232210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88719 ⟨1232210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88719
    ⟨1232210, by decide⟩ (by decide) (![⟨1232134, by decide⟩,⟨1232167, by decide⟩,⟨1232209, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_88719_1232210 node_context_11_88719_1232210
  intro a
  fin_cases a
  · exact context_12_354876_1232134
  · exact context_12_354877_1232167
  · exact context_12_354878_1232209
  · exact context_12_354879_1120582

theorem unmarked_context_10_22179_1232211 : frontier 11 ⟨1232211, by decide⟩
    (prefixCache 10 22179) (prefixPartial 10 22179) = false := by
  decide +kernel

theorem node_context_10_22179_1232211 : EJMOriginalGlobalDAGData.nodes 11 ⟨1232211, by decide⟩ =
    .split (coordinate 10) (![⟨1231797, by decide⟩,⟨1231953, by decide⟩,⟨1232086, by decide⟩,⟨1232210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22179_1232211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22179 ⟨1232211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22179
    ⟨1232211, by decide⟩ (by decide) (![⟨1231797, by decide⟩,⟨1231953, by decide⟩,⟨1232086, by decide⟩,⟨1232210, by decide⟩]) unmarked_context_10_22179_1232211 node_context_10_22179_1232211
  intro a
  fin_cases a
  · exact context_11_88716_1231797
  · exact context_11_88717_1231953
  · exact context_11_88718_1232086
  · exact context_11_88719_1232210

theorem unmarked_context_9_5544_1232212 : frontier 12 ⟨1232212, by decide⟩
    (prefixCache 9 5544) (prefixPartial 9 5544) = false := by
  decide +kernel

theorem node_context_9_5544_1232212 : EJMOriginalGlobalDAGData.nodes 12 ⟨1232212, by decide⟩ =
    .split (coordinate 9) (![⟨1230573, by decide⟩,⟨1231175, by decide⟩,⟨1231647, by decide⟩,⟨1232211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5544_1232212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5544 ⟨1232212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5544
    ⟨1232212, by decide⟩ (by decide) (![⟨1230573, by decide⟩,⟨1231175, by decide⟩,⟨1231647, by decide⟩,⟨1232211, by decide⟩]) unmarked_context_9_5544_1232212 node_context_9_5544_1232212
  intro a
  fin_cases a
  · exact context_10_22176_1230573
  · exact context_10_22177_1231175
  · exact context_10_22178_1231647
  · exact context_10_22179_1232211

theorem selected_cut_44725 : selected 10 ⟨1232311, by decide⟩
    (prefixPartial 11 88720) = some ⟨11, 2, 0, 1232311, 88720, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_88720_1232311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88720 ⟨1232311, by decide⟩ :=
  accepted_of_selected 11 88720 ⟨1232311, by decide⟩ ⟨11, 2, 0, 1232311, 88720, 2645, 262144⟩
    (by decide) selected_cut_44725

theorem selected_cut_44726 : selected 9 ⟨1232343, by decide⟩
    (prefixPartial 12 354884) = some ⟨12, 2, 0, 1232343, 354884, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_354884_1232343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354884 ⟨1232343, by decide⟩ :=
  accepted_of_selected 12 354884 ⟨1232343, by decide⟩ ⟨12, 2, 0, 1232343, 354884, 1677, 65536⟩
    (by decide) selected_cut_44726

theorem selected_cut_44727 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354885) = some ⟨12, 1, 0, 896706, 354885, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354885_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354885 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354885 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354885, 1, 65536⟩
    (by decide) selected_cut_44727

theorem selected_cut_44728 : selected 9 ⟨1232371, by decide⟩
    (prefixPartial 12 354886) = some ⟨12, 2, 0, 1232371, 354886, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_354886_1232371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354886 ⟨1232371, by decide⟩ :=
  accepted_of_selected 12 354886 ⟨1232371, by decide⟩ ⟨12, 2, 0, 1232371, 354886, 1505, 65536⟩
    (by decide) selected_cut_44728

theorem selected_cut_44729 : selected 9 ⟨1232410, by decide⟩
    (prefixPartial 12 354887) = some ⟨12, 2, 0, 1232410, 354887, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_354887_1232410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354887 ⟨1232410, by decide⟩ :=
  accepted_of_selected 12 354887 ⟨1232410, by decide⟩ ⟨12, 2, 0, 1232410, 354887, 1761, 65536⟩
    (by decide) selected_cut_44729

theorem unmarked_context_11_88721_1232411 : frontier 10 ⟨1232411, by decide⟩
    (prefixCache 11 88721) (prefixPartial 11 88721) = false := by
  decide +kernel

theorem node_context_11_88721_1232411 : EJMOriginalGlobalDAGData.nodes 10 ⟨1232411, by decide⟩ =
    .split (coordinate 11) (![⟨1232343, by decide⟩,⟨896706, by decide⟩,⟨1232371, by decide⟩,⟨1232410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88721_1232411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88721 ⟨1232411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88721
    ⟨1232411, by decide⟩ (by decide) (![⟨1232343, by decide⟩,⟨896706, by decide⟩,⟨1232371, by decide⟩,⟨1232410, by decide⟩]) unmarked_context_11_88721_1232411 node_context_11_88721_1232411
  intro a
  fin_cases a
  · exact context_12_354884_1232343
  · exact context_12_354885_896706
  · exact context_12_354886_1232371
  · exact context_12_354887_1232410

theorem selected_cut_44730 : selected 10 ⟨1232479, by decide⟩
    (prefixPartial 11 88722) = some ⟨11, 2, 0, 1232479, 88722, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_88722_1232479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88722 ⟨1232479, by decide⟩ :=
  accepted_of_selected 11 88722 ⟨1232479, by decide⟩ ⟨11, 2, 0, 1232479, 88722, 3409, 262144⟩
    (by decide) selected_cut_44730

theorem selected_cut_44731 : selected 9 ⟨1232505, by decide⟩
    (prefixPartial 12 354892) = some ⟨12, 2, 0, 1232505, 354892, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_354892_1232505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354892 ⟨1232505, by decide⟩ :=
  accepted_of_selected 12 354892 ⟨1232505, by decide⟩ ⟨12, 2, 0, 1232505, 354892, 1509, 65536⟩
    (by decide) selected_cut_44731

theorem selected_cut_44732 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354893) = some ⟨12, 1, 0, 896706, 354893, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354893_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354893 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354893 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354893, 1, 65536⟩
    (by decide) selected_cut_44732

theorem selected_cut_44733 : selected 9 ⟨1232528, by decide⟩
    (prefixPartial 12 354894) = some ⟨12, 2, 0, 1232528, 354894, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_354894_1232528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354894 ⟨1232528, by decide⟩ :=
  accepted_of_selected 12 354894 ⟨1232528, by decide⟩ ⟨12, 2, 0, 1232528, 354894, 1405, 65536⟩
    (by decide) selected_cut_44733

theorem selected_cut_44734 : selected 9 ⟨1232563, by decide⟩
    (prefixPartial 12 354895) = some ⟨12, 2, 0, 1232563, 354895, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_354895_1232563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354895 ⟨1232563, by decide⟩ :=
  accepted_of_selected 12 354895 ⟨1232563, by decide⟩ ⟨12, 2, 0, 1232563, 354895, 1433, 65536⟩
    (by decide) selected_cut_44734

theorem unmarked_context_11_88723_1232564 : frontier 10 ⟨1232564, by decide⟩
    (prefixCache 11 88723) (prefixPartial 11 88723) = false := by
  decide +kernel

theorem node_context_11_88723_1232564 : EJMOriginalGlobalDAGData.nodes 10 ⟨1232564, by decide⟩ =
    .split (coordinate 11) (![⟨1232505, by decide⟩,⟨896706, by decide⟩,⟨1232528, by decide⟩,⟨1232563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88723_1232564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88723 ⟨1232564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88723
    ⟨1232564, by decide⟩ (by decide) (![⟨1232505, by decide⟩,⟨896706, by decide⟩,⟨1232528, by decide⟩,⟨1232563, by decide⟩]) unmarked_context_11_88723_1232564 node_context_11_88723_1232564
  intro a
  fin_cases a
  · exact context_12_354892_1232505
  · exact context_12_354893_896706
  · exact context_12_354894_1232528
  · exact context_12_354895_1232563

theorem unmarked_context_10_22180_1232565 : frontier 11 ⟨1232565, by decide⟩
    (prefixCache 10 22180) (prefixPartial 10 22180) = false := by
  decide +kernel

theorem node_context_10_22180_1232565 : EJMOriginalGlobalDAGData.nodes 11 ⟨1232565, by decide⟩ =
    .split (coordinate 10) (![⟨1232311, by decide⟩,⟨1232411, by decide⟩,⟨1232479, by decide⟩,⟨1232564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22180_1232565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22180 ⟨1232565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22180
    ⟨1232565, by decide⟩ (by decide) (![⟨1232311, by decide⟩,⟨1232411, by decide⟩,⟨1232479, by decide⟩,⟨1232564, by decide⟩]) unmarked_context_10_22180_1232565 node_context_10_22180_1232565
  intro a
  fin_cases a
  · exact context_11_88720_1232311
  · exact context_11_88721_1232411
  · exact context_11_88722_1232479
  · exact context_11_88723_1232564

theorem selected_cut_44735 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22181) = some ⟨10, 1, 0, 893098, 22181, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22181_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22181 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22181 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22181, 1, 1048576⟩
    (by decide) selected_cut_44735

theorem selected_cut_44736 : selected 10 ⟨1232669, by decide⟩
    (prefixPartial 11 88728) = some ⟨11, 2, 0, 1232669, 88728, 3157, 262144⟩ := by
  decide +kernel

theorem context_11_88728_1232669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88728 ⟨1232669, by decide⟩ :=
  accepted_of_selected 11 88728 ⟨1232669, by decide⟩ ⟨11, 2, 0, 1232669, 88728, 3157, 262144⟩
    (by decide) selected_cut_44736

theorem selected_cut_44737 : selected 10 ⟨1232728, by decide⟩
    (prefixPartial 11 88729) = some ⟨11, 2, 0, 1232728, 88729, 3817, 262144⟩ := by
  decide +kernel

theorem context_11_88729_1232728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88729 ⟨1232728, by decide⟩ :=
  accepted_of_selected 11 88729 ⟨1232728, by decide⟩ ⟨11, 2, 0, 1232728, 88729, 3817, 262144⟩
    (by decide) selected_cut_44737

theorem selected_cut_44738 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88730) = some ⟨11, 1, 0, 900587, 88730, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88730_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88730 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88730 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88730, 1, 262144⟩
    (by decide) selected_cut_44738

theorem selected_cut_44739 : selected 10 ⟨1232788, by decide⟩
    (prefixPartial 11 88731) = some ⟨11, 2, 0, 1232788, 88731, 2709, 262144⟩ := by
  decide +kernel

theorem context_11_88731_1232788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88731 ⟨1232788, by decide⟩ :=
  accepted_of_selected 11 88731 ⟨1232788, by decide⟩ ⟨11, 2, 0, 1232788, 88731, 2709, 262144⟩
    (by decide) selected_cut_44739

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
