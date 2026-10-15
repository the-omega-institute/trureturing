/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover183
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17666 : selected 8 ⟨450143, by decide⟩
    (prefixPartial 13 282764) = some ⟨13, 2, 0, 450143, 282764, 785, 16384⟩ := by
  decide +kernel

theorem context_13_282764_450143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282764 ⟨450143, by decide⟩ :=
  accepted_of_selected 13 282764 ⟨450143, by decide⟩ ⟨13, 2, 0, 450143, 282764, 785, 16384⟩
    (by decide) selected_cut_17666

theorem selected_cut_17667 : selected 8 ⟨450168, by decide⟩
    (prefixPartial 13 282765) = some ⟨13, 2, 0, 450168, 282765, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_282765_450168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282765 ⟨450168, by decide⟩ :=
  accepted_of_selected 13 282765 ⟨450168, by decide⟩ ⟨13, 2, 0, 450168, 282765, 2105, 16384⟩
    (by decide) selected_cut_17667

theorem selected_cut_17668 : selected 8 ⟨450188, by decide⟩
    (prefixPartial 13 282766) = some ⟨13, 2, 0, 450188, 282766, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_282766_450188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282766 ⟨450188, by decide⟩ :=
  accepted_of_selected 13 282766 ⟨450188, by decide⟩ ⟨13, 2, 0, 450188, 282766, 1257, 16384⟩
    (by decide) selected_cut_17668

theorem selected_cut_17669 : selected 8 ⟨450193, by decide⟩
    (prefixPartial 13 282767) = some ⟨13, 2, 0, 450193, 282767, 629, 16384⟩ := by
  decide +kernel

theorem context_13_282767_450193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282767 ⟨450193, by decide⟩ :=
  accepted_of_selected 13 282767 ⟨450193, by decide⟩ ⟨13, 2, 0, 450193, 282767, 629, 16384⟩
    (by decide) selected_cut_17669

theorem unmarked_context_12_70691_450194 : frontier 9 ⟨450194, by decide⟩
    (prefixCache 12 70691) (prefixPartial 12 70691) = false := by
  decide +kernel

theorem node_context_12_70691_450194 : EJMOriginalGlobalDAGData.nodes 9 ⟨450194, by decide⟩ =
    .split (coordinate 12) (![⟨450143, by decide⟩,⟨450168, by decide⟩,⟨450188, by decide⟩,⟨450193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70691_450194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70691 ⟨450194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70691
    ⟨450194, by decide⟩ (by decide) (![⟨450143, by decide⟩,⟨450168, by decide⟩,⟨450188, by decide⟩,⟨450193, by decide⟩]) unmarked_context_12_70691_450194 node_context_12_70691_450194
  intro a
  fin_cases a
  · exact context_13_282764_450143
  · exact context_13_282765_450168
  · exact context_13_282766_450188
  · exact context_13_282767_450193

theorem unmarked_context_11_17672_450195 : frontier 10 ⟨450195, by decide⟩
    (prefixCache 11 17672) (prefixPartial 11 17672) = false := by
  decide +kernel

theorem node_context_11_17672_450195 : EJMOriginalGlobalDAGData.nodes 10 ⟨450195, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨450047, by decide⟩,⟨450124, by decide⟩,⟨450194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17672_450195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17672 ⟨450195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17672
    ⟨450195, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨450047, by decide⟩,⟨450124, by decide⟩,⟨450194, by decide⟩]) unmarked_context_11_17672_450195 node_context_11_17672_450195
  intro a
  fin_cases a
  · exact context_12_70688_435790
  · exact context_12_70689_450047
  · exact context_12_70690_450124
  · exact context_12_70691_450194

theorem selected_cut_17670 : selected 8 ⟨450219, by decide⟩
    (prefixPartial 13 282768) = some ⟨13, 2, 0, 450219, 282768, 865, 16384⟩ := by
  decide +kernel

theorem context_13_282768_450219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282768 ⟨450219, by decide⟩ :=
  accepted_of_selected 13 282768 ⟨450219, by decide⟩ ⟨13, 2, 0, 450219, 282768, 865, 16384⟩
    (by decide) selected_cut_17670

theorem selected_cut_17671 : selected 8 ⟨450253, by decide⟩
    (prefixPartial 13 282769) = some ⟨13, 2, 0, 450253, 282769, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_282769_450253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282769 ⟨450253, by decide⟩ :=
  accepted_of_selected 13 282769 ⟨450253, by decide⟩ ⟨13, 2, 0, 450253, 282769, 2677, 16384⟩
    (by decide) selected_cut_17671

theorem selected_cut_17672 : selected 8 ⟨450275, by decide⟩
    (prefixPartial 13 282770) = some ⟨13, 2, 0, 450275, 282770, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_282770_450275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282770 ⟨450275, by decide⟩ :=
  accepted_of_selected 13 282770 ⟨450275, by decide⟩ ⟨13, 2, 0, 450275, 282770, 1657, 16384⟩
    (by decide) selected_cut_17672

theorem selected_cut_17673 : selected 8 ⟨450285, by decide⟩
    (prefixPartial 13 282771) = some ⟨13, 2, 0, 450285, 282771, 941, 16384⟩ := by
  decide +kernel

theorem context_13_282771_450285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282771 ⟨450285, by decide⟩ :=
  accepted_of_selected 13 282771 ⟨450285, by decide⟩ ⟨13, 2, 0, 450285, 282771, 941, 16384⟩
    (by decide) selected_cut_17673

theorem unmarked_context_12_70692_450286 : frontier 9 ⟨450286, by decide⟩
    (prefixCache 12 70692) (prefixPartial 12 70692) = false := by
  decide +kernel

theorem node_context_12_70692_450286 : EJMOriginalGlobalDAGData.nodes 9 ⟨450286, by decide⟩ =
    .split (coordinate 12) (![⟨450219, by decide⟩,⟨450253, by decide⟩,⟨450275, by decide⟩,⟨450285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70692_450286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70692 ⟨450286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70692
    ⟨450286, by decide⟩ (by decide) (![⟨450219, by decide⟩,⟨450253, by decide⟩,⟨450275, by decide⟩,⟨450285, by decide⟩]) unmarked_context_12_70692_450286 node_context_12_70692_450286
  intro a
  fin_cases a
  · exact context_13_282768_450219
  · exact context_13_282769_450253
  · exact context_13_282770_450275
  · exact context_13_282771_450285

theorem selected_cut_17674 : selected 9 ⟨450341, by decide⟩
    (prefixPartial 12 70693) = some ⟨12, 2, 0, 450341, 70693, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_70693_450341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70693 ⟨450341, by decide⟩ :=
  accepted_of_selected 12 70693 ⟨450341, by decide⟩ ⟨12, 2, 0, 450341, 70693, 3973, 65536⟩
    (by decide) selected_cut_17674

theorem selected_cut_17675 : selected 8 ⟨450365, by decide⟩
    (prefixPartial 13 282776) = some ⟨13, 2, 0, 450365, 282776, 841, 16384⟩ := by
  decide +kernel

theorem context_13_282776_450365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282776 ⟨450365, by decide⟩ :=
  accepted_of_selected 13 282776 ⟨450365, by decide⟩ ⟨13, 2, 0, 450365, 282776, 841, 16384⟩
    (by decide) selected_cut_17675

theorem selected_cut_17676 : selected 8 ⟨450394, by decide⟩
    (prefixPartial 13 282777) = some ⟨13, 2, 0, 450394, 282777, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_282777_450394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282777 ⟨450394, by decide⟩ :=
  accepted_of_selected 13 282777 ⟨450394, by decide⟩ ⟨13, 2, 0, 450394, 282777, 2205, 16384⟩
    (by decide) selected_cut_17676

theorem selected_cut_17677 : selected 8 ⟨450412, by decide⟩
    (prefixPartial 13 282778) = some ⟨13, 2, 0, 450412, 282778, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_282778_450412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282778 ⟨450412, by decide⟩ :=
  accepted_of_selected 13 282778 ⟨450412, by decide⟩ ⟨13, 2, 0, 450412, 282778, 1281, 16384⟩
    (by decide) selected_cut_17677

theorem selected_cut_17678 : selected 8 ⟨450419, by decide⟩
    (prefixPartial 13 282779) = some ⟨13, 2, 0, 450419, 282779, 781, 16384⟩ := by
  decide +kernel

theorem context_13_282779_450419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282779 ⟨450419, by decide⟩ :=
  accepted_of_selected 13 282779 ⟨450419, by decide⟩ ⟨13, 2, 0, 450419, 282779, 781, 16384⟩
    (by decide) selected_cut_17678

theorem unmarked_context_12_70694_450420 : frontier 9 ⟨450420, by decide⟩
    (prefixCache 12 70694) (prefixPartial 12 70694) = false := by
  decide +kernel

theorem node_context_12_70694_450420 : EJMOriginalGlobalDAGData.nodes 9 ⟨450420, by decide⟩ =
    .split (coordinate 12) (![⟨450365, by decide⟩,⟨450394, by decide⟩,⟨450412, by decide⟩,⟨450419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70694_450420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70694 ⟨450420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70694
    ⟨450420, by decide⟩ (by decide) (![⟨450365, by decide⟩,⟨450394, by decide⟩,⟨450412, by decide⟩,⟨450419, by decide⟩]) unmarked_context_12_70694_450420 node_context_12_70694_450420
  intro a
  fin_cases a
  · exact context_13_282776_450365
  · exact context_13_282777_450394
  · exact context_13_282778_450412
  · exact context_13_282779_450419

theorem selected_cut_17679 : selected 8 ⟨450441, by decide⟩
    (prefixPartial 13 282780) = some ⟨13, 2, 0, 450441, 282780, 717, 16384⟩ := by
  decide +kernel

theorem context_13_282780_450441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282780 ⟨450441, by decide⟩ :=
  accepted_of_selected 13 282780 ⟨450441, by decide⟩ ⟨13, 2, 0, 450441, 282780, 717, 16384⟩
    (by decide) selected_cut_17679

theorem selected_cut_17680 : selected 8 ⟨450470, by decide⟩
    (prefixPartial 13 282781) = some ⟨13, 2, 0, 450470, 282781, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_282781_450470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282781 ⟨450470, by decide⟩ :=
  accepted_of_selected 13 282781 ⟨450470, by decide⟩ ⟨13, 2, 0, 450470, 282781, 2237, 16384⟩
    (by decide) selected_cut_17680

theorem selected_cut_17681 : selected 8 ⟨450489, by decide⟩
    (prefixPartial 13 282782) = some ⟨13, 2, 0, 450489, 282782, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_282782_450489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282782 ⟨450489, by decide⟩ :=
  accepted_of_selected 13 282782 ⟨450489, by decide⟩ ⟨13, 2, 0, 450489, 282782, 1345, 16384⟩
    (by decide) selected_cut_17681

theorem selected_cut_17682 : selected 8 ⟨450495, by decide⟩
    (prefixPartial 13 282783) = some ⟨13, 2, 0, 450495, 282783, 665, 16384⟩ := by
  decide +kernel

theorem context_13_282783_450495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282783 ⟨450495, by decide⟩ :=
  accepted_of_selected 13 282783 ⟨450495, by decide⟩ ⟨13, 2, 0, 450495, 282783, 665, 16384⟩
    (by decide) selected_cut_17682

theorem unmarked_context_12_70695_450496 : frontier 9 ⟨450496, by decide⟩
    (prefixCache 12 70695) (prefixPartial 12 70695) = false := by
  decide +kernel

theorem node_context_12_70695_450496 : EJMOriginalGlobalDAGData.nodes 9 ⟨450496, by decide⟩ =
    .split (coordinate 12) (![⟨450441, by decide⟩,⟨450470, by decide⟩,⟨450489, by decide⟩,⟨450495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70695_450496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70695 ⟨450496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70695
    ⟨450496, by decide⟩ (by decide) (![⟨450441, by decide⟩,⟨450470, by decide⟩,⟨450489, by decide⟩,⟨450495, by decide⟩]) unmarked_context_12_70695_450496 node_context_12_70695_450496
  intro a
  fin_cases a
  · exact context_13_282780_450441
  · exact context_13_282781_450470
  · exact context_13_282782_450489
  · exact context_13_282783_450495

theorem unmarked_context_11_17673_450497 : frontier 10 ⟨450497, by decide⟩
    (prefixCache 11 17673) (prefixPartial 11 17673) = false := by
  decide +kernel

theorem node_context_11_17673_450497 : EJMOriginalGlobalDAGData.nodes 10 ⟨450497, by decide⟩ =
    .split (coordinate 11) (![⟨450286, by decide⟩,⟨450341, by decide⟩,⟨450420, by decide⟩,⟨450496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17673_450497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17673 ⟨450497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17673
    ⟨450497, by decide⟩ (by decide) (![⟨450286, by decide⟩,⟨450341, by decide⟩,⟨450420, by decide⟩,⟨450496, by decide⟩]) unmarked_context_11_17673_450497 node_context_11_17673_450497
  intro a
  fin_cases a
  · exact context_12_70692_450286
  · exact context_12_70693_450341
  · exact context_12_70694_450420
  · exact context_12_70695_450496

theorem selected_cut_17683 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 70696) = some ⟨12, 1, 0, 450498, 70696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70696_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70696 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 70696 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 70696, 1, 65536⟩
    (by decide) selected_cut_17683

theorem selected_cut_17684 : selected 8 ⟨450510, by decide⟩
    (prefixPartial 13 282788) = some ⟨13, 2, 0, 450510, 282788, 465, 16384⟩ := by
  decide +kernel

theorem context_13_282788_450510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282788 ⟨450510, by decide⟩ :=
  accepted_of_selected 13 282788 ⟨450510, by decide⟩ ⟨13, 2, 0, 450510, 282788, 465, 16384⟩
    (by decide) selected_cut_17684

theorem selected_cut_17685 : selected 8 ⟨450536, by decide⟩
    (prefixPartial 13 282789) = some ⟨13, 2, 0, 450536, 282789, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_282789_450536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282789 ⟨450536, by decide⟩ :=
  accepted_of_selected 13 282789 ⟨450536, by decide⟩ ⟨13, 2, 0, 450536, 282789, 2261, 16384⟩
    (by decide) selected_cut_17685

theorem selected_cut_17686 : selected 8 ⟨450551, by decide⟩
    (prefixPartial 13 282790) = some ⟨13, 2, 0, 450551, 282790, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_282790_450551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282790 ⟨450551, by decide⟩ :=
  accepted_of_selected 13 282790 ⟨450551, by decide⟩ ⟨13, 2, 0, 450551, 282790, 1237, 16384⟩
    (by decide) selected_cut_17686

theorem selected_cut_17687 : selected 8 ⟨450556, by decide⟩
    (prefixPartial 13 282791) = some ⟨13, 2, 0, 450556, 282791, 761, 16384⟩ := by
  decide +kernel

theorem context_13_282791_450556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282791 ⟨450556, by decide⟩ :=
  accepted_of_selected 13 282791 ⟨450556, by decide⟩ ⟨13, 2, 0, 450556, 282791, 761, 16384⟩
    (by decide) selected_cut_17687

theorem unmarked_context_12_70697_450557 : frontier 9 ⟨450557, by decide⟩
    (prefixCache 12 70697) (prefixPartial 12 70697) = false := by
  decide +kernel

theorem node_context_12_70697_450557 : EJMOriginalGlobalDAGData.nodes 9 ⟨450557, by decide⟩ =
    .split (coordinate 12) (![⟨450510, by decide⟩,⟨450536, by decide⟩,⟨450551, by decide⟩,⟨450556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70697_450557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70697 ⟨450557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70697
    ⟨450557, by decide⟩ (by decide) (![⟨450510, by decide⟩,⟨450536, by decide⟩,⟨450551, by decide⟩,⟨450556, by decide⟩]) unmarked_context_12_70697_450557 node_context_12_70697_450557
  intro a
  fin_cases a
  · exact context_13_282788_450510
  · exact context_13_282789_450536
  · exact context_13_282790_450551
  · exact context_13_282791_450556

theorem selected_cut_17688 : selected 8 ⟨450570, by decide⟩
    (prefixPartial 13 282792) = some ⟨13, 2, 0, 450570, 282792, 433, 16384⟩ := by
  decide +kernel

theorem context_13_282792_450570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282792 ⟨450570, by decide⟩ :=
  accepted_of_selected 13 282792 ⟨450570, by decide⟩ ⟨13, 2, 0, 450570, 282792, 433, 16384⟩
    (by decide) selected_cut_17688

theorem selected_cut_17689 : selected 8 ⟨450601, by decide⟩
    (prefixPartial 13 282793) = some ⟨13, 2, 0, 450601, 282793, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_282793_450601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282793 ⟨450601, by decide⟩ :=
  accepted_of_selected 13 282793 ⟨450601, by decide⟩ ⟨13, 2, 0, 450601, 282793, 2373, 16384⟩
    (by decide) selected_cut_17689

theorem selected_cut_17690 : selected 8 ⟨450617, by decide⟩
    (prefixPartial 13 282794) = some ⟨13, 2, 0, 450617, 282794, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_282794_450617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282794 ⟨450617, by decide⟩ :=
  accepted_of_selected 13 282794 ⟨450617, by decide⟩ ⟨13, 2, 0, 450617, 282794, 1217, 16384⟩
    (by decide) selected_cut_17690

theorem selected_cut_17691 : selected 8 ⟨450622, by decide⟩
    (prefixPartial 13 282795) = some ⟨13, 2, 0, 450622, 282795, 865, 16384⟩ := by
  decide +kernel

theorem context_13_282795_450622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282795 ⟨450622, by decide⟩ :=
  accepted_of_selected 13 282795 ⟨450622, by decide⟩ ⟨13, 2, 0, 450622, 282795, 865, 16384⟩
    (by decide) selected_cut_17691

theorem unmarked_context_12_70698_450623 : frontier 9 ⟨450623, by decide⟩
    (prefixCache 12 70698) (prefixPartial 12 70698) = false := by
  decide +kernel

theorem node_context_12_70698_450623 : EJMOriginalGlobalDAGData.nodes 9 ⟨450623, by decide⟩ =
    .split (coordinate 12) (![⟨450570, by decide⟩,⟨450601, by decide⟩,⟨450617, by decide⟩,⟨450622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70698_450623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70698 ⟨450623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70698
    ⟨450623, by decide⟩ (by decide) (![⟨450570, by decide⟩,⟨450601, by decide⟩,⟨450617, by decide⟩,⟨450622, by decide⟩]) unmarked_context_12_70698_450623 node_context_12_70698_450623
  intro a
  fin_cases a
  · exact context_13_282792_450570
  · exact context_13_282793_450601
  · exact context_13_282794_450617
  · exact context_13_282795_450622

theorem selected_cut_17692 : selected 8 ⟨450637, by decide⟩
    (prefixPartial 13 282796) = some ⟨13, 2, 0, 450637, 282796, 441, 16384⟩ := by
  decide +kernel

theorem context_13_282796_450637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282796 ⟨450637, by decide⟩ :=
  accepted_of_selected 13 282796 ⟨450637, by decide⟩ ⟨13, 2, 0, 450637, 282796, 441, 16384⟩
    (by decide) selected_cut_17692

theorem selected_cut_17693 : selected 8 ⟨450667, by decide⟩
    (prefixPartial 13 282797) = some ⟨13, 2, 0, 450667, 282797, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_282797_450667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282797 ⟨450667, by decide⟩ :=
  accepted_of_selected 13 282797 ⟨450667, by decide⟩ ⟨13, 2, 0, 450667, 282797, 2637, 16384⟩
    (by decide) selected_cut_17693

theorem selected_cut_17694 : selected 8 ⟨450687, by decide⟩
    (prefixPartial 13 282798) = some ⟨13, 2, 0, 450687, 282798, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_282798_450687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282798 ⟨450687, by decide⟩ :=
  accepted_of_selected 13 282798 ⟨450687, by decide⟩ ⟨13, 2, 0, 450687, 282798, 1397, 16384⟩
    (by decide) selected_cut_17694

theorem selected_cut_17695 : selected 8 ⟨450693, by decide⟩
    (prefixPartial 13 282799) = some ⟨13, 2, 0, 450693, 282799, 781, 16384⟩ := by
  decide +kernel

theorem context_13_282799_450693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282799 ⟨450693, by decide⟩ :=
  accepted_of_selected 13 282799 ⟨450693, by decide⟩ ⟨13, 2, 0, 450693, 282799, 781, 16384⟩
    (by decide) selected_cut_17695

theorem unmarked_context_12_70699_450694 : frontier 9 ⟨450694, by decide⟩
    (prefixCache 12 70699) (prefixPartial 12 70699) = false := by
  decide +kernel

theorem node_context_12_70699_450694 : EJMOriginalGlobalDAGData.nodes 9 ⟨450694, by decide⟩ =
    .split (coordinate 12) (![⟨450637, by decide⟩,⟨450667, by decide⟩,⟨450687, by decide⟩,⟨450693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70699_450694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70699 ⟨450694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70699
    ⟨450694, by decide⟩ (by decide) (![⟨450637, by decide⟩,⟨450667, by decide⟩,⟨450687, by decide⟩,⟨450693, by decide⟩]) unmarked_context_12_70699_450694 node_context_12_70699_450694
  intro a
  fin_cases a
  · exact context_13_282796_450637
  · exact context_13_282797_450667
  · exact context_13_282798_450687
  · exact context_13_282799_450693

theorem unmarked_context_11_17674_450695 : frontier 10 ⟨450695, by decide⟩
    (prefixCache 11 17674) (prefixPartial 11 17674) = false := by
  decide +kernel

theorem node_context_11_17674_450695 : EJMOriginalGlobalDAGData.nodes 10 ⟨450695, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨450557, by decide⟩,⟨450623, by decide⟩,⟨450694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17674_450695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17674 ⟨450695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17674
    ⟨450695, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨450557, by decide⟩,⟨450623, by decide⟩,⟨450694, by decide⟩]) unmarked_context_11_17674_450695 node_context_11_17674_450695
  intro a
  fin_cases a
  · exact context_12_70696_450498
  · exact context_12_70697_450557
  · exact context_12_70698_450623
  · exact context_12_70699_450694

theorem selected_cut_17696 : selected 8 ⟨450704, by decide⟩
    (prefixPartial 13 282800) = some ⟨13, 2, 0, 450704, 282800, 337, 16384⟩ := by
  decide +kernel

theorem context_13_282800_450704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282800 ⟨450704, by decide⟩ :=
  accepted_of_selected 13 282800 ⟨450704, by decide⟩ ⟨13, 2, 0, 450704, 282800, 337, 16384⟩
    (by decide) selected_cut_17696

theorem selected_cut_17697 : selected 8 ⟨450751, by decide⟩
    (prefixPartial 13 282801) = some ⟨13, 2, 0, 450751, 282801, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_282801_450751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282801 ⟨450751, by decide⟩ :=
  accepted_of_selected 13 282801 ⟨450751, by decide⟩ ⟨13, 2, 0, 450751, 282801, 3245, 16384⟩
    (by decide) selected_cut_17697

theorem selected_cut_17698 : selected 8 ⟨450772, by decide⟩
    (prefixPartial 13 282802) = some ⟨13, 2, 0, 450772, 282802, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_282802_450772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282802 ⟨450772, by decide⟩ :=
  accepted_of_selected 13 282802 ⟨450772, by decide⟩ ⟨13, 2, 0, 450772, 282802, 1925, 16384⟩
    (by decide) selected_cut_17698

theorem selected_cut_17699 : selected 8 ⟨450781, by decide⟩
    (prefixPartial 13 282803) = some ⟨13, 2, 0, 450781, 282803, 909, 16384⟩ := by
  decide +kernel

theorem context_13_282803_450781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282803 ⟨450781, by decide⟩ :=
  accepted_of_selected 13 282803 ⟨450781, by decide⟩ ⟨13, 2, 0, 450781, 282803, 909, 16384⟩
    (by decide) selected_cut_17699

theorem unmarked_context_12_70700_450782 : frontier 9 ⟨450782, by decide⟩
    (prefixCache 12 70700) (prefixPartial 12 70700) = false := by
  decide +kernel

theorem node_context_12_70700_450782 : EJMOriginalGlobalDAGData.nodes 9 ⟨450782, by decide⟩ =
    .split (coordinate 12) (![⟨450704, by decide⟩,⟨450751, by decide⟩,⟨450772, by decide⟩,⟨450781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70700_450782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70700 ⟨450782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70700
    ⟨450782, by decide⟩ (by decide) (![⟨450704, by decide⟩,⟨450751, by decide⟩,⟨450772, by decide⟩,⟨450781, by decide⟩]) unmarked_context_12_70700_450782 node_context_12_70700_450782
  intro a
  fin_cases a
  · exact context_13_282800_450704
  · exact context_13_282801_450751
  · exact context_13_282802_450772
  · exact context_13_282803_450781

theorem selected_cut_17700 : selected 8 ⟨450791, by decide⟩
    (prefixPartial 13 282804) = some ⟨13, 2, 0, 450791, 282804, 217, 16384⟩ := by
  decide +kernel

theorem context_13_282804_450791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282804 ⟨450791, by decide⟩ :=
  accepted_of_selected 13 282804 ⟨450791, by decide⟩ ⟨13, 2, 0, 450791, 282804, 217, 16384⟩
    (by decide) selected_cut_17700

theorem selected_cut_17701 : selected 8 ⟨450820, by decide⟩
    (prefixPartial 13 282805) = some ⟨13, 2, 0, 450820, 282805, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_282805_450820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282805 ⟨450820, by decide⟩ :=
  accepted_of_selected 13 282805 ⟨450820, by decide⟩ ⟨13, 2, 0, 450820, 282805, 2401, 16384⟩
    (by decide) selected_cut_17701

theorem selected_cut_17702 : selected 8 ⟨450840, by decide⟩
    (prefixPartial 13 282806) = some ⟨13, 2, 0, 450840, 282806, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_282806_450840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282806 ⟨450840, by decide⟩ :=
  accepted_of_selected 13 282806 ⟨450840, by decide⟩ ⟨13, 2, 0, 450840, 282806, 1441, 16384⟩
    (by decide) selected_cut_17702

theorem selected_cut_17703 : selected 8 ⟨450846, by decide⟩
    (prefixPartial 13 282807) = some ⟨13, 2, 0, 450846, 282807, 741, 16384⟩ := by
  decide +kernel

theorem context_13_282807_450846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282807 ⟨450846, by decide⟩ :=
  accepted_of_selected 13 282807 ⟨450846, by decide⟩ ⟨13, 2, 0, 450846, 282807, 741, 16384⟩
    (by decide) selected_cut_17703

theorem unmarked_context_12_70701_450847 : frontier 9 ⟨450847, by decide⟩
    (prefixCache 12 70701) (prefixPartial 12 70701) = false := by
  decide +kernel

theorem node_context_12_70701_450847 : EJMOriginalGlobalDAGData.nodes 9 ⟨450847, by decide⟩ =
    .split (coordinate 12) (![⟨450791, by decide⟩,⟨450820, by decide⟩,⟨450840, by decide⟩,⟨450846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70701_450847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70701 ⟨450847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70701
    ⟨450847, by decide⟩ (by decide) (![⟨450791, by decide⟩,⟨450820, by decide⟩,⟨450840, by decide⟩,⟨450846, by decide⟩]) unmarked_context_12_70701_450847 node_context_12_70701_450847
  intro a
  fin_cases a
  · exact context_13_282804_450791
  · exact context_13_282805_450820
  · exact context_13_282806_450840
  · exact context_13_282807_450846

theorem selected_cut_17704 : selected 8 ⟨450855, by decide⟩
    (prefixPartial 13 282808) = some ⟨13, 2, 0, 450855, 282808, 185, 16384⟩ := by
  decide +kernel

theorem context_13_282808_450855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282808 ⟨450855, by decide⟩ :=
  accepted_of_selected 13 282808 ⟨450855, by decide⟩ ⟨13, 2, 0, 450855, 282808, 185, 16384⟩
    (by decide) selected_cut_17704

theorem selected_cut_17705 : selected 8 ⟨450887, by decide⟩
    (prefixPartial 13 282809) = some ⟨13, 2, 0, 450887, 282809, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_282809_450887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282809 ⟨450887, by decide⟩ :=
  accepted_of_selected 13 282809 ⟨450887, by decide⟩ ⟨13, 2, 0, 450887, 282809, 2761, 16384⟩
    (by decide) selected_cut_17705

theorem selected_cut_17706 : selected 8 ⟨450907, by decide⟩
    (prefixPartial 13 282810) = some ⟨13, 2, 0, 450907, 282810, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_282810_450907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282810 ⟨450907, by decide⟩ :=
  accepted_of_selected 13 282810 ⟨450907, by decide⟩ ⟨13, 2, 0, 450907, 282810, 1649, 16384⟩
    (by decide) selected_cut_17706

theorem selected_cut_17707 : selected 8 ⟨450913, by decide⟩
    (prefixPartial 13 282811) = some ⟨13, 2, 0, 450913, 282811, 761, 16384⟩ := by
  decide +kernel

theorem context_13_282811_450913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282811 ⟨450913, by decide⟩ :=
  accepted_of_selected 13 282811 ⟨450913, by decide⟩ ⟨13, 2, 0, 450913, 282811, 761, 16384⟩
    (by decide) selected_cut_17707

theorem unmarked_context_12_70702_450914 : frontier 9 ⟨450914, by decide⟩
    (prefixCache 12 70702) (prefixPartial 12 70702) = false := by
  decide +kernel

theorem node_context_12_70702_450914 : EJMOriginalGlobalDAGData.nodes 9 ⟨450914, by decide⟩ =
    .split (coordinate 12) (![⟨450855, by decide⟩,⟨450887, by decide⟩,⟨450907, by decide⟩,⟨450913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70702_450914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70702 ⟨450914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70702
    ⟨450914, by decide⟩ (by decide) (![⟨450855, by decide⟩,⟨450887, by decide⟩,⟨450907, by decide⟩,⟨450913, by decide⟩]) unmarked_context_12_70702_450914 node_context_12_70702_450914
  intro a
  fin_cases a
  · exact context_13_282808_450855
  · exact context_13_282809_450887
  · exact context_13_282810_450907
  · exact context_13_282811_450913

theorem selected_cut_17708 : selected 8 ⟨450920, by decide⟩
    (prefixPartial 13 282812) = some ⟨13, 2, 0, 450920, 282812, 85, 16384⟩ := by
  decide +kernel

theorem context_13_282812_450920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282812 ⟨450920, by decide⟩ :=
  accepted_of_selected 13 282812 ⟨450920, by decide⟩ ⟨13, 2, 0, 450920, 282812, 85, 16384⟩
    (by decide) selected_cut_17708

theorem selected_cut_17709 : selected 8 ⟨450951, by decide⟩
    (prefixPartial 13 282813) = some ⟨13, 2, 0, 450951, 282813, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_282813_450951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282813 ⟨450951, by decide⟩ :=
  accepted_of_selected 13 282813 ⟨450951, by decide⟩ ⟨13, 2, 0, 450951, 282813, 2629, 16384⟩
    (by decide) selected_cut_17709

theorem selected_cut_17710 : selected 8 ⟨450973, by decide⟩
    (prefixPartial 13 282814) = some ⟨13, 2, 0, 450973, 282814, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_282814_450973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282814 ⟨450973, by decide⟩ :=
  accepted_of_selected 13 282814 ⟨450973, by decide⟩ ⟨13, 2, 0, 450973, 282814, 1585, 16384⟩
    (by decide) selected_cut_17710

theorem selected_cut_17711 : selected 8 ⟨450977, by decide⟩
    (prefixPartial 13 282815) = some ⟨13, 2, 0, 450977, 282815, 665, 16384⟩ := by
  decide +kernel

theorem context_13_282815_450977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282815 ⟨450977, by decide⟩ :=
  accepted_of_selected 13 282815 ⟨450977, by decide⟩ ⟨13, 2, 0, 450977, 282815, 665, 16384⟩
    (by decide) selected_cut_17711

theorem unmarked_context_12_70703_450978 : frontier 9 ⟨450978, by decide⟩
    (prefixCache 12 70703) (prefixPartial 12 70703) = false := by
  decide +kernel

theorem node_context_12_70703_450978 : EJMOriginalGlobalDAGData.nodes 9 ⟨450978, by decide⟩ =
    .split (coordinate 12) (![⟨450920, by decide⟩,⟨450951, by decide⟩,⟨450973, by decide⟩,⟨450977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70703_450978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70703 ⟨450978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70703
    ⟨450978, by decide⟩ (by decide) (![⟨450920, by decide⟩,⟨450951, by decide⟩,⟨450973, by decide⟩,⟨450977, by decide⟩]) unmarked_context_12_70703_450978 node_context_12_70703_450978
  intro a
  fin_cases a
  · exact context_13_282812_450920
  · exact context_13_282813_450951
  · exact context_13_282814_450973
  · exact context_13_282815_450977

theorem unmarked_context_11_17675_450979 : frontier 10 ⟨450979, by decide⟩
    (prefixCache 11 17675) (prefixPartial 11 17675) = false := by
  decide +kernel

theorem node_context_11_17675_450979 : EJMOriginalGlobalDAGData.nodes 10 ⟨450979, by decide⟩ =
    .split (coordinate 11) (![⟨450782, by decide⟩,⟨450847, by decide⟩,⟨450914, by decide⟩,⟨450978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17675_450979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17675 ⟨450979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17675
    ⟨450979, by decide⟩ (by decide) (![⟨450782, by decide⟩,⟨450847, by decide⟩,⟨450914, by decide⟩,⟨450978, by decide⟩]) unmarked_context_11_17675_450979 node_context_11_17675_450979
  intro a
  fin_cases a
  · exact context_12_70700_450782
  · exact context_12_70701_450847
  · exact context_12_70702_450914
  · exact context_12_70703_450978

theorem unmarked_context_10_4418_450980 : frontier 11 ⟨450980, by decide⟩
    (prefixCache 10 4418) (prefixPartial 10 4418) = false := by
  decide +kernel

theorem node_context_10_4418_450980 : EJMOriginalGlobalDAGData.nodes 11 ⟨450980, by decide⟩ =
    .split (coordinate 10) (![⟨450195, by decide⟩,⟨450497, by decide⟩,⟨450695, by decide⟩,⟨450979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4418_450980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4418 ⟨450980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4418
    ⟨450980, by decide⟩ (by decide) (![⟨450195, by decide⟩,⟨450497, by decide⟩,⟨450695, by decide⟩,⟨450979, by decide⟩]) unmarked_context_10_4418_450980 node_context_10_4418_450980
  intro a
  fin_cases a
  · exact context_11_17672_450195
  · exact context_11_17673_450497
  · exact context_11_17674_450695
  · exact context_11_17675_450979

theorem selected_cut_17712 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4419) = some ⟨10, 1, 0, 3440, 4419, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4419_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4419 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4419 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4419, 1, 1048576⟩
    (by decide) selected_cut_17712

theorem unmarked_context_9_1104_450981 : frontier 12 ⟨450981, by decide⟩
    (prefixCache 9 1104) (prefixPartial 9 1104) = false := by
  decide +kernel

theorem node_context_9_1104_450981 : EJMOriginalGlobalDAGData.nodes 12 ⟨450981, by decide⟩ =
    .split (coordinate 9) (![⟨449392, by decide⟩,⟨449977, by decide⟩,⟨450980, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1104_450981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1104 ⟨450981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1104
    ⟨450981, by decide⟩ (by decide) (![⟨449392, by decide⟩,⟨449977, by decide⟩,⟨450980, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1104_450981 node_context_9_1104_450981
  intro a
  fin_cases a
  · exact context_10_4416_449392
  · exact context_10_4417_449977
  · exact context_10_4418_450980
  · exact context_10_4419_3440

theorem selected_cut_17713 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 70720) = some ⟨12, 1, 0, 450982, 70720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70720_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70720 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 70720 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 70720, 1, 65536⟩
    (by decide) selected_cut_17713

theorem selected_cut_17714 : selected 9 ⟨451021, by decide⟩
    (prefixPartial 12 70721) = some ⟨12, 2, 0, 451021, 70721, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_70721_451021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70721 ⟨451021, by decide⟩ :=
  accepted_of_selected 12 70721 ⟨451021, by decide⟩ ⟨12, 2, 0, 451021, 70721, 1729, 65536⟩
    (by decide) selected_cut_17714

theorem selected_cut_17715 : selected 9 ⟨451073, by decide⟩
    (prefixPartial 12 70722) = some ⟨12, 2, 0, 451073, 70722, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_70722_451073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70722 ⟨451073, by decide⟩ :=
  accepted_of_selected 12 70722 ⟨451073, by decide⟩ ⟨12, 2, 0, 451073, 70722, 3425, 65536⟩
    (by decide) selected_cut_17715

theorem selected_cut_17716 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70723) = some ⟨12, 1, 0, 893, 70723, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70723_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70723 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70723 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70723, 1, 65536⟩
    (by decide) selected_cut_17716

theorem unmarked_context_11_17680_451074 : frontier 10 ⟨451074, by decide⟩
    (prefixCache 11 17680) (prefixPartial 11 17680) = false := by
  decide +kernel

theorem node_context_11_17680_451074 : EJMOriginalGlobalDAGData.nodes 10 ⟨451074, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨451021, by decide⟩,⟨451073, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17680_451074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17680 ⟨451074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17680
    ⟨451074, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨451021, by decide⟩,⟨451073, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17680_451074 node_context_11_17680_451074
  intro a
  fin_cases a
  · exact context_12_70720_450982
  · exact context_12_70721_451021
  · exact context_12_70722_451073
  · exact context_12_70723_893

theorem selected_cut_17717 : selected 9 ⟨451108, by decide⟩
    (prefixPartial 12 70724) = some ⟨12, 2, 0, 451108, 70724, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_70724_451108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70724 ⟨451108, by decide⟩ :=
  accepted_of_selected 12 70724 ⟨451108, by decide⟩ ⟨12, 2, 0, 451108, 70724, 1513, 65536⟩
    (by decide) selected_cut_17717

theorem selected_cut_17718 : selected 9 ⟨451145, by decide⟩
    (prefixPartial 12 70725) = some ⟨12, 2, 0, 451145, 70725, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_70725_451145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70725 ⟨451145, by decide⟩ :=
  accepted_of_selected 12 70725 ⟨451145, by decide⟩ ⟨12, 2, 0, 451145, 70725, 1661, 65536⟩
    (by decide) selected_cut_17718

theorem selected_cut_17719 : selected 9 ⟨451207, by decide⟩
    (prefixPartial 12 70726) = some ⟨12, 2, 0, 451207, 70726, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_70726_451207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70726 ⟨451207, by decide⟩ :=
  accepted_of_selected 12 70726 ⟨451207, by decide⟩ ⟨12, 2, 0, 451207, 70726, 3601, 65536⟩
    (by decide) selected_cut_17719

theorem selected_cut_17720 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70727) = some ⟨12, 1, 0, 893, 70727, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70727_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70727 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70727 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70727, 1, 65536⟩
    (by decide) selected_cut_17720

theorem unmarked_context_11_17681_451208 : frontier 10 ⟨451208, by decide⟩
    (prefixCache 11 17681) (prefixPartial 11 17681) = false := by
  decide +kernel

theorem node_context_11_17681_451208 : EJMOriginalGlobalDAGData.nodes 10 ⟨451208, by decide⟩ =
    .split (coordinate 11) (![⟨451108, by decide⟩,⟨451145, by decide⟩,⟨451207, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17681_451208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17681 ⟨451208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17681
    ⟨451208, by decide⟩ (by decide) (![⟨451108, by decide⟩,⟨451145, by decide⟩,⟨451207, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17681_451208 node_context_11_17681_451208
  intro a
  fin_cases a
  · exact context_12_70724_451108
  · exact context_12_70725_451145
  · exact context_12_70726_451207
  · exact context_12_70727_893

theorem selected_cut_17721 : selected 9 ⟨451250, by decide⟩
    (prefixPartial 12 70728) = some ⟨12, 2, 0, 451250, 70728, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_70728_451250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70728 ⟨451250, by decide⟩ :=
  accepted_of_selected 12 70728 ⟨451250, by decide⟩ ⟨12, 2, 0, 451250, 70728, 3157, 65536⟩
    (by decide) selected_cut_17721

theorem selected_cut_17722 : selected 9 ⟨451301, by decide⟩
    (prefixPartial 12 70729) = some ⟨12, 2, 0, 451301, 70729, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_70729_451301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70729 ⟨451301, by decide⟩ :=
  accepted_of_selected 12 70729 ⟨451301, by decide⟩ ⟨12, 2, 0, 451301, 70729, 3741, 65536⟩
    (by decide) selected_cut_17722

theorem selected_cut_17723 : selected 9 ⟨451355, by decide⟩
    (prefixPartial 12 70730) = some ⟨12, 2, 0, 451355, 70730, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_70730_451355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70730 ⟨451355, by decide⟩ :=
  accepted_of_selected 12 70730 ⟨451355, by decide⟩ ⟨12, 2, 0, 451355, 70730, 3737, 65536⟩
    (by decide) selected_cut_17723

theorem selected_cut_17724 : selected 9 ⟨451410, by decide⟩
    (prefixPartial 12 70731) = some ⟨12, 2, 0, 451410, 70731, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_70731_451410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70731 ⟨451410, by decide⟩ :=
  accepted_of_selected 12 70731 ⟨451410, by decide⟩ ⟨12, 2, 0, 451410, 70731, 3889, 65536⟩
    (by decide) selected_cut_17724

theorem unmarked_context_11_17682_451411 : frontier 10 ⟨451411, by decide⟩
    (prefixCache 11 17682) (prefixPartial 11 17682) = false := by
  decide +kernel

theorem node_context_11_17682_451411 : EJMOriginalGlobalDAGData.nodes 10 ⟨451411, by decide⟩ =
    .split (coordinate 11) (![⟨451250, by decide⟩,⟨451301, by decide⟩,⟨451355, by decide⟩,⟨451410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17682_451411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17682 ⟨451411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17682
    ⟨451411, by decide⟩ (by decide) (![⟨451250, by decide⟩,⟨451301, by decide⟩,⟨451355, by decide⟩,⟨451410, by decide⟩]) unmarked_context_11_17682_451411 node_context_11_17682_451411
  intro a
  fin_cases a
  · exact context_12_70728_451250
  · exact context_12_70729_451301
  · exact context_12_70730_451355
  · exact context_12_70731_451410

theorem selected_cut_17725 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17683) = some ⟨11, 1, 0, 1736, 17683, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17683_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17683 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17683 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17683, 1, 262144⟩
    (by decide) selected_cut_17725

theorem unmarked_context_10_4420_451412 : frontier 11 ⟨451412, by decide⟩
    (prefixCache 10 4420) (prefixPartial 10 4420) = false := by
  decide +kernel

theorem node_context_10_4420_451412 : EJMOriginalGlobalDAGData.nodes 11 ⟨451412, by decide⟩ =
    .split (coordinate 10) (![⟨451074, by decide⟩,⟨451208, by decide⟩,⟨451411, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4420_451412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4420 ⟨451412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4420
    ⟨451412, by decide⟩ (by decide) (![⟨451074, by decide⟩,⟨451208, by decide⟩,⟨451411, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4420_451412 node_context_10_4420_451412
  intro a
  fin_cases a
  · exact context_11_17680_451074
  · exact context_11_17681_451208
  · exact context_11_17682_451411
  · exact context_11_17683_1736

theorem selected_cut_17726 : selected 9 ⟨451460, by decide⟩
    (prefixPartial 12 70736) = some ⟨12, 2, 0, 451460, 70736, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_70736_451460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70736 ⟨451460, by decide⟩ :=
  accepted_of_selected 12 70736 ⟨451460, by decide⟩ ⟨12, 2, 0, 451460, 70736, 1521, 65536⟩
    (by decide) selected_cut_17726

theorem selected_cut_17727 : selected 9 ⟨451494, by decide⟩
    (prefixPartial 12 70737) = some ⟨12, 2, 0, 451494, 70737, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_70737_451494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70737 ⟨451494, by decide⟩ :=
  accepted_of_selected 12 70737 ⟨451494, by decide⟩ ⟨12, 2, 0, 451494, 70737, 1789, 65536⟩
    (by decide) selected_cut_17727

theorem selected_cut_17728 : selected 9 ⟨451539, by decide⟩
    (prefixPartial 12 70738) = some ⟨12, 2, 0, 451539, 70738, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_70738_451539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70738 ⟨451539, by decide⟩ :=
  accepted_of_selected 12 70738 ⟨451539, by decide⟩ ⟨12, 2, 0, 451539, 70738, 4001, 65536⟩
    (by decide) selected_cut_17728

theorem selected_cut_17729 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70739) = some ⟨12, 1, 0, 893, 70739, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70739_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70739 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70739 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70739, 1, 65536⟩
    (by decide) selected_cut_17729

theorem unmarked_context_11_17684_451540 : frontier 10 ⟨451540, by decide⟩
    (prefixCache 11 17684) (prefixPartial 11 17684) = false := by
  decide +kernel

theorem node_context_11_17684_451540 : EJMOriginalGlobalDAGData.nodes 10 ⟨451540, by decide⟩ =
    .split (coordinate 11) (![⟨451460, by decide⟩,⟨451494, by decide⟩,⟨451539, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17684_451540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17684 ⟨451540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17684
    ⟨451540, by decide⟩ (by decide) (![⟨451460, by decide⟩,⟨451494, by decide⟩,⟨451539, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17684_451540 node_context_11_17684_451540
  intro a
  fin_cases a
  · exact context_12_70736_451460
  · exact context_12_70737_451494
  · exact context_12_70738_451539
  · exact context_12_70739_893

theorem selected_cut_17730 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 17685) = some ⟨11, 1, 0, 451541, 17685, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17685_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17685 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 17685 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 17685, 1, 262144⟩
    (by decide) selected_cut_17730

theorem selected_cut_17731 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 282976) = some ⟨13, 1, 0, 3444, 282976, 1, 16384⟩ := by
  decide +kernel

theorem context_13_282976_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282976 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 282976 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 282976, 1, 16384⟩
    (by decide) selected_cut_17731

theorem selected_cut_17732 : selected 8 ⟨451557, by decide⟩
    (prefixPartial 13 282977) = some ⟨13, 2, 0, 451557, 282977, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_282977_451557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282977 ⟨451557, by decide⟩ :=
  accepted_of_selected 13 282977 ⟨451557, by decide⟩ ⟨13, 2, 0, 451557, 282977, 1637, 16384⟩
    (by decide) selected_cut_17732

theorem selected_cut_17733 : selected 8 ⟨451573, by decide⟩
    (prefixPartial 13 282978) = some ⟨13, 2, 0, 451573, 282978, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_282978_451573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282978 ⟨451573, by decide⟩ :=
  accepted_of_selected 13 282978 ⟨451573, by decide⟩ ⟨13, 2, 0, 451573, 282978, 1665, 16384⟩
    (by decide) selected_cut_17733

theorem selected_cut_17734 : selected 8 ⟨451579, by decide⟩
    (prefixPartial 13 282979) = some ⟨13, 2, 0, 451579, 282979, 845, 16384⟩ := by
  decide +kernel

theorem context_13_282979_451579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282979 ⟨451579, by decide⟩ :=
  accepted_of_selected 13 282979 ⟨451579, by decide⟩ ⟨13, 2, 0, 451579, 282979, 845, 16384⟩
    (by decide) selected_cut_17734

theorem unmarked_context_12_70744_451580 : frontier 9 ⟨451580, by decide⟩
    (prefixCache 12 70744) (prefixPartial 12 70744) = false := by
  decide +kernel

theorem node_context_12_70744_451580 : EJMOriginalGlobalDAGData.nodes 9 ⟨451580, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨451557, by decide⟩,⟨451573, by decide⟩,⟨451579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70744_451580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70744 ⟨451580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70744
    ⟨451580, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨451557, by decide⟩,⟨451573, by decide⟩,⟨451579, by decide⟩]) unmarked_context_12_70744_451580 node_context_12_70744_451580
  intro a
  fin_cases a
  · exact context_13_282976_3444
  · exact context_13_282977_451557
  · exact context_13_282978_451573
  · exact context_13_282979_451579

theorem selected_cut_17735 : selected 9 ⟨451629, by decide⟩
    (prefixPartial 12 70745) = some ⟨12, 2, 0, 451629, 70745, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_70745_451629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70745 ⟨451629, by decide⟩ :=
  accepted_of_selected 12 70745 ⟨451629, by decide⟩ ⟨12, 2, 0, 451629, 70745, 4073, 65536⟩
    (by decide) selected_cut_17735

theorem selected_cut_17736 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 282984) = some ⟨13, 1, 0, 3444, 282984, 1, 16384⟩ := by
  decide +kernel

theorem context_13_282984_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282984 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 282984 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 282984, 1, 16384⟩
    (by decide) selected_cut_17736

theorem selected_cut_17737 : selected 8 ⟨451645, by decide⟩
    (prefixPartial 13 282985) = some ⟨13, 2, 0, 451645, 282985, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_282985_451645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282985 ⟨451645, by decide⟩ :=
  accepted_of_selected 13 282985 ⟨451645, by decide⟩ ⟨13, 2, 0, 451645, 282985, 1713, 16384⟩
    (by decide) selected_cut_17737

theorem selected_cut_17738 : selected 8 ⟨451666, by decide⟩
    (prefixPartial 13 282986) = some ⟨13, 2, 0, 451666, 282986, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_282986_451666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282986 ⟨451666, by decide⟩ :=
  accepted_of_selected 13 282986 ⟨451666, by decide⟩ ⟨13, 2, 0, 451666, 282986, 1701, 16384⟩
    (by decide) selected_cut_17738

theorem selected_cut_17739 : selected 8 ⟨451670, by decide⟩
    (prefixPartial 13 282987) = some ⟨13, 2, 0, 451670, 282987, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_282987_451670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282987 ⟨451670, by decide⟩ :=
  accepted_of_selected 13 282987 ⟨451670, by decide⟩ ⟨13, 2, 0, 451670, 282987, 1109, 16384⟩
    (by decide) selected_cut_17739

theorem unmarked_context_12_70746_451671 : frontier 9 ⟨451671, by decide⟩
    (prefixCache 12 70746) (prefixPartial 12 70746) = false := by
  decide +kernel

theorem node_context_12_70746_451671 : EJMOriginalGlobalDAGData.nodes 9 ⟨451671, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨451645, by decide⟩,⟨451666, by decide⟩,⟨451670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70746_451671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70746 ⟨451671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70746
    ⟨451671, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨451645, by decide⟩,⟨451666, by decide⟩,⟨451670, by decide⟩]) unmarked_context_12_70746_451671 node_context_12_70746_451671
  intro a
  fin_cases a
  · exact context_13_282984_3444
  · exact context_13_282985_451645
  · exact context_13_282986_451666
  · exact context_13_282987_451670

theorem selected_cut_17740 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 282988) = some ⟨13, 1, 0, 3444, 282988, 1, 16384⟩ := by
  decide +kernel

theorem context_13_282988_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282988 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 282988 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 282988, 1, 16384⟩
    (by decide) selected_cut_17740

theorem selected_cut_17741 : selected 8 ⟨451687, by decide⟩
    (prefixPartial 13 282989) = some ⟨13, 2, 0, 451687, 282989, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_282989_451687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282989 ⟨451687, by decide⟩ :=
  accepted_of_selected 13 282989 ⟨451687, by decide⟩ ⟨13, 2, 0, 451687, 282989, 1681, 16384⟩
    (by decide) selected_cut_17741

theorem selected_cut_17742 : selected 8 ⟨451706, by decide⟩
    (prefixPartial 13 282990) = some ⟨13, 2, 0, 451706, 282990, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_282990_451706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282990 ⟨451706, by decide⟩ :=
  accepted_of_selected 13 282990 ⟨451706, by decide⟩ ⟨13, 2, 0, 451706, 282990, 2093, 16384⟩
    (by decide) selected_cut_17742

theorem selected_cut_17743 : selected 8 ⟨451713, by decide⟩
    (prefixPartial 13 282991) = some ⟨13, 2, 0, 451713, 282991, 901, 16384⟩ := by
  decide +kernel

theorem context_13_282991_451713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282991 ⟨451713, by decide⟩ :=
  accepted_of_selected 13 282991 ⟨451713, by decide⟩ ⟨13, 2, 0, 451713, 282991, 901, 16384⟩
    (by decide) selected_cut_17743

theorem unmarked_context_12_70747_451714 : frontier 9 ⟨451714, by decide⟩
    (prefixCache 12 70747) (prefixPartial 12 70747) = false := by
  decide +kernel

theorem node_context_12_70747_451714 : EJMOriginalGlobalDAGData.nodes 9 ⟨451714, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨451687, by decide⟩,⟨451706, by decide⟩,⟨451713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70747_451714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70747 ⟨451714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70747
    ⟨451714, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨451687, by decide⟩,⟨451706, by decide⟩,⟨451713, by decide⟩]) unmarked_context_12_70747_451714 node_context_12_70747_451714
  intro a
  fin_cases a
  · exact context_13_282988_3444
  · exact context_13_282989_451687
  · exact context_13_282990_451706
  · exact context_13_282991_451713

theorem unmarked_context_11_17686_451715 : frontier 10 ⟨451715, by decide⟩
    (prefixCache 11 17686) (prefixPartial 11 17686) = false := by
  decide +kernel

theorem node_context_11_17686_451715 : EJMOriginalGlobalDAGData.nodes 10 ⟨451715, by decide⟩ =
    .split (coordinate 11) (![⟨451580, by decide⟩,⟨451629, by decide⟩,⟨451671, by decide⟩,⟨451714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17686_451715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17686 ⟨451715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17686
    ⟨451715, by decide⟩ (by decide) (![⟨451580, by decide⟩,⟨451629, by decide⟩,⟨451671, by decide⟩,⟨451714, by decide⟩]) unmarked_context_11_17686_451715 node_context_11_17686_451715
  intro a
  fin_cases a
  · exact context_12_70744_451580
  · exact context_12_70745_451629
  · exact context_12_70746_451671
  · exact context_12_70747_451714

theorem selected_cut_17744 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17687) = some ⟨11, 1, 0, 1736, 17687, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17687_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17687 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17687 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17687, 1, 262144⟩
    (by decide) selected_cut_17744

theorem unmarked_context_10_4421_451716 : frontier 11 ⟨451716, by decide⟩
    (prefixCache 10 4421) (prefixPartial 10 4421) = false := by
  decide +kernel

theorem node_context_10_4421_451716 : EJMOriginalGlobalDAGData.nodes 11 ⟨451716, by decide⟩ =
    .split (coordinate 10) (![⟨451540, by decide⟩,⟨451541, by decide⟩,⟨451715, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4421_451716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4421 ⟨451716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4421
    ⟨451716, by decide⟩ (by decide) (![⟨451540, by decide⟩,⟨451541, by decide⟩,⟨451715, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4421_451716 node_context_10_4421_451716
  intro a
  fin_cases a
  · exact context_11_17684_451540
  · exact context_11_17685_451541
  · exact context_11_17686_451715
  · exact context_11_17687_1736

theorem selected_cut_17745 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 283008) = some ⟨13, 1, 0, 3444, 283008, 1, 16384⟩ := by
  decide +kernel

theorem context_13_283008_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283008 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 283008 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 283008, 1, 16384⟩
    (by decide) selected_cut_17745

theorem selected_cut_17746 : selected 8 ⟨451769, by decide⟩
    (prefixPartial 13 283009) = some ⟨13, 2, 0, 451769, 283009, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_283009_451769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283009 ⟨451769, by decide⟩ :=
  accepted_of_selected 13 283009 ⟨451769, by decide⟩ ⟨13, 2, 0, 451769, 283009, 2309, 16384⟩
    (by decide) selected_cut_17746

theorem selected_cut_17747 : selected 8 ⟨451812, by decide⟩
    (prefixPartial 13 283010) = some ⟨13, 2, 0, 451812, 283010, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_283010_451812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283010 ⟨451812, by decide⟩ :=
  accepted_of_selected 13 283010 ⟨451812, by decide⟩ ⟨13, 2, 0, 451812, 283010, 2329, 16384⟩
    (by decide) selected_cut_17747

theorem selected_cut_17748 : selected 8 ⟨451824, by decide⟩
    (prefixPartial 13 283011) = some ⟨13, 2, 0, 451824, 283011, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_283011_451824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283011 ⟨451824, by decide⟩ :=
  accepted_of_selected 13 283011 ⟨451824, by decide⟩ ⟨13, 2, 0, 451824, 283011, 1065, 16384⟩
    (by decide) selected_cut_17748

theorem unmarked_context_12_70752_451825 : frontier 9 ⟨451825, by decide⟩
    (prefixCache 12 70752) (prefixPartial 12 70752) = false := by
  decide +kernel

theorem node_context_12_70752_451825 : EJMOriginalGlobalDAGData.nodes 9 ⟨451825, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨451769, by decide⟩,⟨451812, by decide⟩,⟨451824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70752_451825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70752 ⟨451825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70752
    ⟨451825, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨451769, by decide⟩,⟨451812, by decide⟩,⟨451824, by decide⟩]) unmarked_context_12_70752_451825 node_context_12_70752_451825
  intro a
  fin_cases a
  · exact context_13_283008_3444
  · exact context_13_283009_451769
  · exact context_13_283010_451812
  · exact context_13_283011_451824

theorem selected_cut_17749 : selected 9 ⟨451865, by decide⟩
    (prefixPartial 12 70753) = some ⟨12, 2, 0, 451865, 70753, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_70753_451865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70753 ⟨451865, by decide⟩ :=
  accepted_of_selected 12 70753 ⟨451865, by decide⟩ ⟨12, 2, 0, 451865, 70753, 3481, 65536⟩
    (by decide) selected_cut_17749

theorem selected_cut_17750 : selected 9 ⟨451920, by decide⟩
    (prefixPartial 12 70754) = some ⟨12, 2, 0, 451920, 70754, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_70754_451920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70754 ⟨451920, by decide⟩ :=
  accepted_of_selected 12 70754 ⟨451920, by decide⟩ ⟨12, 2, 0, 451920, 70754, 3817, 65536⟩
    (by decide) selected_cut_17750

theorem selected_cut_17751 : selected 9 ⟨451962, by decide⟩
    (prefixPartial 12 70755) = some ⟨12, 2, 0, 451962, 70755, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_70755_451962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70755 ⟨451962, by decide⟩ :=
  accepted_of_selected 12 70755 ⟨451962, by decide⟩ ⟨12, 2, 0, 451962, 70755, 3693, 65536⟩
    (by decide) selected_cut_17751

theorem unmarked_context_11_17688_451963 : frontier 10 ⟨451963, by decide⟩
    (prefixCache 11 17688) (prefixPartial 11 17688) = false := by
  decide +kernel

theorem node_context_11_17688_451963 : EJMOriginalGlobalDAGData.nodes 10 ⟨451963, by decide⟩ =
    .split (coordinate 11) (![⟨451825, by decide⟩,⟨451865, by decide⟩,⟨451920, by decide⟩,⟨451962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17688_451963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17688 ⟨451963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17688
    ⟨451963, by decide⟩ (by decide) (![⟨451825, by decide⟩,⟨451865, by decide⟩,⟨451920, by decide⟩,⟨451962, by decide⟩]) unmarked_context_11_17688_451963 node_context_11_17688_451963
  intro a
  fin_cases a
  · exact context_12_70752_451825
  · exact context_12_70753_451865
  · exact context_12_70754_451920
  · exact context_12_70755_451962

theorem selected_cut_17752 : selected 9 ⟨452009, by decide⟩
    (prefixPartial 12 70756) = some ⟨12, 2, 0, 452009, 70756, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_70756_452009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70756 ⟨452009, by decide⟩ :=
  accepted_of_selected 12 70756 ⟨452009, by decide⟩ ⟨12, 2, 0, 452009, 70756, 3385, 65536⟩
    (by decide) selected_cut_17752

theorem selected_cut_17753 : selected 9 ⟨452049, by decide⟩
    (prefixPartial 12 70757) = some ⟨12, 2, 0, 452049, 70757, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_70757_452049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70757 ⟨452049, by decide⟩ :=
  accepted_of_selected 12 70757 ⟨452049, by decide⟩ ⟨12, 2, 0, 452049, 70757, 3065, 65536⟩
    (by decide) selected_cut_17753

theorem selected_cut_17754 : selected 9 ⟨452105, by decide⟩
    (prefixPartial 12 70758) = some ⟨12, 2, 0, 452105, 70758, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_70758_452105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70758 ⟨452105, by decide⟩ :=
  accepted_of_selected 12 70758 ⟨452105, by decide⟩ ⟨12, 2, 0, 452105, 70758, 3625, 65536⟩
    (by decide) selected_cut_17754

theorem selected_cut_17755 : selected 9 ⟨452150, by decide⟩
    (prefixPartial 12 70759) = some ⟨12, 2, 0, 452150, 70759, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_70759_452150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70759 ⟨452150, by decide⟩ :=
  accepted_of_selected 12 70759 ⟨452150, by decide⟩ ⟨12, 2, 0, 452150, 70759, 3545, 65536⟩
    (by decide) selected_cut_17755

theorem unmarked_context_11_17689_452151 : frontier 10 ⟨452151, by decide⟩
    (prefixCache 11 17689) (prefixPartial 11 17689) = false := by
  decide +kernel

theorem node_context_11_17689_452151 : EJMOriginalGlobalDAGData.nodes 10 ⟨452151, by decide⟩ =
    .split (coordinate 11) (![⟨452009, by decide⟩,⟨452049, by decide⟩,⟨452105, by decide⟩,⟨452150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17689_452151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17689 ⟨452151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17689
    ⟨452151, by decide⟩ (by decide) (![⟨452009, by decide⟩,⟨452049, by decide⟩,⟨452105, by decide⟩,⟨452150, by decide⟩]) unmarked_context_11_17689_452151 node_context_11_17689_452151
  intro a
  fin_cases a
  · exact context_12_70756_452009
  · exact context_12_70757_452049
  · exact context_12_70758_452105
  · exact context_12_70759_452150

theorem selected_cut_17756 : selected 9 ⟨452188, by decide⟩
    (prefixPartial 12 70760) = some ⟨12, 2, 0, 452188, 70760, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_70760_452188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70760 ⟨452188, by decide⟩ :=
  accepted_of_selected 12 70760 ⟨452188, by decide⟩ ⟨12, 2, 0, 452188, 70760, 3169, 65536⟩
    (by decide) selected_cut_17756

theorem selected_cut_17757 : selected 9 ⟨452231, by decide⟩
    (prefixPartial 12 70761) = some ⟨12, 2, 0, 452231, 70761, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_70761_452231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70761 ⟨452231, by decide⟩ :=
  accepted_of_selected 12 70761 ⟨452231, by decide⟩ ⟨12, 2, 0, 452231, 70761, 3317, 65536⟩
    (by decide) selected_cut_17757

theorem selected_cut_17758 : selected 9 ⟨452274, by decide⟩
    (prefixPartial 12 70762) = some ⟨12, 2, 0, 452274, 70762, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_70762_452274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70762 ⟨452274, by decide⟩ :=
  accepted_of_selected 12 70762 ⟨452274, by decide⟩ ⟨12, 2, 0, 452274, 70762, 3265, 65536⟩
    (by decide) selected_cut_17758

theorem selected_cut_17759 : selected 9 ⟨452312, by decide⟩
    (prefixPartial 12 70763) = some ⟨12, 2, 0, 452312, 70763, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_70763_452312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70763 ⟨452312, by decide⟩ :=
  accepted_of_selected 12 70763 ⟨452312, by decide⟩ ⟨12, 2, 0, 452312, 70763, 3321, 65536⟩
    (by decide) selected_cut_17759

theorem unmarked_context_11_17690_452313 : frontier 10 ⟨452313, by decide⟩
    (prefixCache 11 17690) (prefixPartial 11 17690) = false := by
  decide +kernel

theorem node_context_11_17690_452313 : EJMOriginalGlobalDAGData.nodes 10 ⟨452313, by decide⟩ =
    .split (coordinate 11) (![⟨452188, by decide⟩,⟨452231, by decide⟩,⟨452274, by decide⟩,⟨452312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17690_452313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17690 ⟨452313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17690
    ⟨452313, by decide⟩ (by decide) (![⟨452188, by decide⟩,⟨452231, by decide⟩,⟨452274, by decide⟩,⟨452312, by decide⟩]) unmarked_context_11_17690_452313 node_context_11_17690_452313
  intro a
  fin_cases a
  · exact context_12_70760_452188
  · exact context_12_70761_452231
  · exact context_12_70762_452274
  · exact context_12_70763_452312

theorem selected_cut_17760 : selected 9 ⟨452349, by decide⟩
    (prefixPartial 12 70764) = some ⟨12, 2, 0, 452349, 70764, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_70764_452349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70764 ⟨452349, by decide⟩ :=
  accepted_of_selected 12 70764 ⟨452349, by decide⟩ ⟨12, 2, 0, 452349, 70764, 3005, 65536⟩
    (by decide) selected_cut_17760

theorem selected_cut_17761 : selected 9 ⟨452388, by decide⟩
    (prefixPartial 12 70765) = some ⟨12, 2, 0, 452388, 70765, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_70765_452388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70765 ⟨452388, by decide⟩ :=
  accepted_of_selected 12 70765 ⟨452388, by decide⟩ ⟨12, 2, 0, 452388, 70765, 3045, 65536⟩
    (by decide) selected_cut_17761

theorem selected_cut_17762 : selected 9 ⟨452429, by decide⟩
    (prefixPartial 12 70766) = some ⟨12, 2, 0, 452429, 70766, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_70766_452429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70766 ⟨452429, by decide⟩ :=
  accepted_of_selected 12 70766 ⟨452429, by decide⟩ ⟨12, 2, 0, 452429, 70766, 3165, 65536⟩
    (by decide) selected_cut_17762

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
