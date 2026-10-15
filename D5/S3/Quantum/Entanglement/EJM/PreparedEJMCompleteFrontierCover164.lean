/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover163
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15747 : selected 8 ⟨403269, by decide⟩
    (prefixPartial 13 111750) = some ⟨13, 2, 0, 403269, 111750, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_111750_403269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111750 ⟨403269, by decide⟩ :=
  accepted_of_selected 13 111750 ⟨403269, by decide⟩ ⟨13, 2, 0, 403269, 111750, 1809, 16384⟩
    (by decide) selected_cut_15747

theorem selected_cut_15748 : selected 8 ⟨403276, by decide⟩
    (prefixPartial 13 111751) = some ⟨13, 2, 0, 403276, 111751, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_111751_403276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111751 ⟨403276, by decide⟩ :=
  accepted_of_selected 13 111751 ⟨403276, by decide⟩ ⟨13, 2, 0, 403276, 111751, 1049, 16384⟩
    (by decide) selected_cut_15748

theorem unmarked_context_12_27937_403277 : frontier 9 ⟨403277, by decide⟩
    (prefixCache 12 27937) (prefixPartial 12 27937) = false := by
  decide +kernel

theorem node_context_12_27937_403277 : EJMOriginalGlobalDAGData.nodes 9 ⟨403277, by decide⟩ =
    .split (coordinate 12) (![⟨403224, by decide⟩,⟨403247, by decide⟩,⟨403269, by decide⟩,⟨403276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27937_403277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27937 ⟨403277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27937
    ⟨403277, by decide⟩ (by decide) (![⟨403224, by decide⟩,⟨403247, by decide⟩,⟨403269, by decide⟩,⟨403276, by decide⟩]) unmarked_context_12_27937_403277 node_context_12_27937_403277
  intro a
  fin_cases a
  · exact context_13_111748_403224
  · exact context_13_111749_403247
  · exact context_13_111750_403269
  · exact context_13_111751_403276

theorem selected_cut_15749 : selected 8 ⟨403307, by decide⟩
    (prefixPartial 13 111752) = some ⟨13, 2, 0, 403307, 111752, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_111752_403307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111752 ⟨403307, by decide⟩ :=
  accepted_of_selected 13 111752 ⟨403307, by decide⟩ ⟨13, 2, 0, 403307, 111752, 1689, 16384⟩
    (by decide) selected_cut_15749

theorem selected_cut_15750 : selected 8 ⟨403348, by decide⟩
    (prefixPartial 13 111753) = some ⟨13, 2, 0, 403348, 111753, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_111753_403348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111753 ⟨403348, by decide⟩ :=
  accepted_of_selected 13 111753 ⟨403348, by decide⟩ ⟨13, 2, 0, 403348, 111753, 2661, 16384⟩
    (by decide) selected_cut_15750

theorem selected_cut_15751 : selected 8 ⟨403377, by decide⟩
    (prefixPartial 13 111754) = some ⟨13, 2, 0, 403377, 111754, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_111754_403377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111754 ⟨403377, by decide⟩ :=
  accepted_of_selected 13 111754 ⟨403377, by decide⟩ ⟨13, 2, 0, 403377, 111754, 1769, 16384⟩
    (by decide) selected_cut_15751

theorem selected_cut_15752 : selected 8 ⟨403391, by decide⟩
    (prefixPartial 13 111755) = some ⟨13, 2, 0, 403391, 111755, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_111755_403391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111755 ⟨403391, by decide⟩ :=
  accepted_of_selected 13 111755 ⟨403391, by decide⟩ ⟨13, 2, 0, 403391, 111755, 1097, 16384⟩
    (by decide) selected_cut_15752

theorem unmarked_context_12_27938_403392 : frontier 9 ⟨403392, by decide⟩
    (prefixCache 12 27938) (prefixPartial 12 27938) = false := by
  decide +kernel

theorem node_context_12_27938_403392 : EJMOriginalGlobalDAGData.nodes 9 ⟨403392, by decide⟩ =
    .split (coordinate 12) (![⟨403307, by decide⟩,⟨403348, by decide⟩,⟨403377, by decide⟩,⟨403391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27938_403392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27938 ⟨403392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27938
    ⟨403392, by decide⟩ (by decide) (![⟨403307, by decide⟩,⟨403348, by decide⟩,⟨403377, by decide⟩,⟨403391, by decide⟩]) unmarked_context_12_27938_403392 node_context_12_27938_403392
  intro a
  fin_cases a
  · exact context_13_111752_403307
  · exact context_13_111753_403348
  · exact context_13_111754_403377
  · exact context_13_111755_403391

theorem selected_cut_15753 : selected 8 ⟨403412, by decide⟩
    (prefixPartial 13 111756) = some ⟨13, 2, 0, 403412, 111756, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_111756_403412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111756 ⟨403412, by decide⟩ :=
  accepted_of_selected 13 111756 ⟨403412, by decide⟩ ⟨13, 2, 0, 403412, 111756, 1605, 16384⟩
    (by decide) selected_cut_15753

theorem selected_cut_15754 : selected 8 ⟨403450, by decide⟩
    (prefixPartial 13 111757) = some ⟨13, 2, 0, 403450, 111757, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_111757_403450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111757 ⟨403450, by decide⟩ :=
  accepted_of_selected 13 111757 ⟨403450, by decide⟩ ⟨13, 2, 0, 403450, 111757, 2785, 16384⟩
    (by decide) selected_cut_15754

theorem selected_cut_15755 : selected 8 ⟨403480, by decide⟩
    (prefixPartial 13 111758) = some ⟨13, 2, 0, 403480, 111758, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_111758_403480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111758 ⟨403480, by decide⟩ :=
  accepted_of_selected 13 111758 ⟨403480, by decide⟩ ⟨13, 2, 0, 403480, 111758, 2133, 16384⟩
    (by decide) selected_cut_15755

theorem selected_cut_15756 : selected 8 ⟨403499, by decide⟩
    (prefixPartial 13 111759) = some ⟨13, 2, 0, 403499, 111759, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_111759_403499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111759 ⟨403499, by decide⟩ :=
  accepted_of_selected 13 111759 ⟨403499, by decide⟩ ⟨13, 2, 0, 403499, 111759, 1193, 16384⟩
    (by decide) selected_cut_15756

theorem unmarked_context_12_27939_403500 : frontier 9 ⟨403500, by decide⟩
    (prefixCache 12 27939) (prefixPartial 12 27939) = false := by
  decide +kernel

theorem node_context_12_27939_403500 : EJMOriginalGlobalDAGData.nodes 9 ⟨403500, by decide⟩ =
    .split (coordinate 12) (![⟨403412, by decide⟩,⟨403450, by decide⟩,⟨403480, by decide⟩,⟨403499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27939_403500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27939 ⟨403500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27939
    ⟨403500, by decide⟩ (by decide) (![⟨403412, by decide⟩,⟨403450, by decide⟩,⟨403480, by decide⟩,⟨403499, by decide⟩]) unmarked_context_12_27939_403500 node_context_12_27939_403500
  intro a
  fin_cases a
  · exact context_13_111756_403412
  · exact context_13_111757_403450
  · exact context_13_111758_403480
  · exact context_13_111759_403499

theorem unmarked_context_11_6984_403501 : frontier 10 ⟨403501, by decide⟩
    (prefixCache 11 6984) (prefixPartial 11 6984) = false := by
  decide +kernel

theorem node_context_11_6984_403501 : EJMOriginalGlobalDAGData.nodes 10 ⟨403501, by decide⟩ =
    .split (coordinate 11) (![⟨403212, by decide⟩,⟨403277, by decide⟩,⟨403392, by decide⟩,⟨403500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6984_403501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6984 ⟨403501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6984
    ⟨403501, by decide⟩ (by decide) (![⟨403212, by decide⟩,⟨403277, by decide⟩,⟨403392, by decide⟩,⟨403500, by decide⟩]) unmarked_context_11_6984_403501 node_context_11_6984_403501
  intro a
  fin_cases a
  · exact context_12_27936_403212
  · exact context_12_27937_403277
  · exact context_12_27938_403392
  · exact context_12_27939_403500

theorem selected_cut_15757 : selected 8 ⟨403513, by decide⟩
    (prefixPartial 13 111760) = some ⟨13, 2, 0, 403513, 111760, 945, 16384⟩ := by
  decide +kernel

theorem context_13_111760_403513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111760 ⟨403513, by decide⟩ :=
  accepted_of_selected 13 111760 ⟨403513, by decide⟩ ⟨13, 2, 0, 403513, 111760, 945, 16384⟩
    (by decide) selected_cut_15757

theorem selected_cut_15758 : selected 8 ⟨403539, by decide⟩
    (prefixPartial 13 111761) = some ⟨13, 2, 0, 403539, 111761, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_111761_403539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111761 ⟨403539, by decide⟩ :=
  accepted_of_selected 13 111761 ⟨403539, by decide⟩ ⟨13, 2, 0, 403539, 111761, 2037, 16384⟩
    (by decide) selected_cut_15758

theorem selected_cut_15759 : selected 8 ⟨403558, by decide⟩
    (prefixPartial 13 111762) = some ⟨13, 2, 0, 403558, 111762, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_111762_403558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111762 ⟨403558, by decide⟩ :=
  accepted_of_selected 13 111762 ⟨403558, by decide⟩ ⟨13, 2, 0, 403558, 111762, 1301, 16384⟩
    (by decide) selected_cut_15759

theorem selected_cut_15760 : selected 8 ⟨403568, by decide⟩
    (prefixPartial 13 111763) = some ⟨13, 2, 0, 403568, 111763, 789, 16384⟩ := by
  decide +kernel

theorem context_13_111763_403568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111763 ⟨403568, by decide⟩ :=
  accepted_of_selected 13 111763 ⟨403568, by decide⟩ ⟨13, 2, 0, 403568, 111763, 789, 16384⟩
    (by decide) selected_cut_15760

theorem unmarked_context_12_27940_403569 : frontier 9 ⟨403569, by decide⟩
    (prefixCache 12 27940) (prefixPartial 12 27940) = false := by
  decide +kernel

theorem node_context_12_27940_403569 : EJMOriginalGlobalDAGData.nodes 9 ⟨403569, by decide⟩ =
    .split (coordinate 12) (![⟨403513, by decide⟩,⟨403539, by decide⟩,⟨403558, by decide⟩,⟨403568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27940_403569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27940 ⟨403569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27940
    ⟨403569, by decide⟩ (by decide) (![⟨403513, by decide⟩,⟨403539, by decide⟩,⟨403558, by decide⟩,⟨403568, by decide⟩]) unmarked_context_12_27940_403569 node_context_12_27940_403569
  intro a
  fin_cases a
  · exact context_13_111760_403513
  · exact context_13_111761_403539
  · exact context_13_111762_403558
  · exact context_13_111763_403568

theorem selected_cut_15761 : selected 8 ⟨403593, by decide⟩
    (prefixPartial 13 111764) = some ⟨13, 2, 0, 403593, 111764, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_111764_403593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111764 ⟨403593, by decide⟩ :=
  accepted_of_selected 13 111764 ⟨403593, by decide⟩ ⟨13, 2, 0, 403593, 111764, 1709, 16384⟩
    (by decide) selected_cut_15761

theorem selected_cut_15762 : selected 8 ⟨403639, by decide⟩
    (prefixPartial 13 111765) = some ⟨13, 2, 0, 403639, 111765, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_111765_403639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111765 ⟨403639, by decide⟩ :=
  accepted_of_selected 13 111765 ⟨403639, by decide⟩ ⟨13, 2, 0, 403639, 111765, 3209, 16384⟩
    (by decide) selected_cut_15762

theorem selected_cut_15763 : selected 8 ⟨403673, by decide⟩
    (prefixPartial 13 111766) = some ⟨13, 2, 0, 403673, 111766, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_111766_403673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111766 ⟨403673, by decide⟩ :=
  accepted_of_selected 13 111766 ⟨403673, by decide⟩ ⟨13, 2, 0, 403673, 111766, 2361, 16384⟩
    (by decide) selected_cut_15763

theorem selected_cut_15764 : selected 8 ⟨403690, by decide⟩
    (prefixPartial 13 111767) = some ⟨13, 2, 0, 403690, 111767, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_111767_403690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111767 ⟨403690, by decide⟩ :=
  accepted_of_selected 13 111767 ⟨403690, by decide⟩ ⟨13, 2, 0, 403690, 111767, 1201, 16384⟩
    (by decide) selected_cut_15764

theorem unmarked_context_12_27941_403691 : frontier 9 ⟨403691, by decide⟩
    (prefixCache 12 27941) (prefixPartial 12 27941) = false := by
  decide +kernel

theorem node_context_12_27941_403691 : EJMOriginalGlobalDAGData.nodes 9 ⟨403691, by decide⟩ =
    .split (coordinate 12) (![⟨403593, by decide⟩,⟨403639, by decide⟩,⟨403673, by decide⟩,⟨403690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27941_403691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27941 ⟨403691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27941
    ⟨403691, by decide⟩ (by decide) (![⟨403593, by decide⟩,⟨403639, by decide⟩,⟨403673, by decide⟩,⟨403690, by decide⟩]) unmarked_context_12_27941_403691 node_context_12_27941_403691
  intro a
  fin_cases a
  · exact context_13_111764_403593
  · exact context_13_111765_403639
  · exact context_13_111766_403673
  · exact context_13_111767_403690

theorem selected_cut_15765 : selected 8 ⟨403710, by decide⟩
    (prefixPartial 13 111768) = some ⟨13, 2, 0, 403710, 111768, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_111768_403710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111768 ⟨403710, by decide⟩ :=
  accepted_of_selected 13 111768 ⟨403710, by decide⟩ ⟨13, 2, 0, 403710, 111768, 1237, 16384⟩
    (by decide) selected_cut_15765

theorem selected_cut_15766 : selected 8 ⟨403737, by decide⟩
    (prefixPartial 13 111769) = some ⟨13, 2, 0, 403737, 111769, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_111769_403737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111769 ⟨403737, by decide⟩ :=
  accepted_of_selected 13 111769 ⟨403737, by decide⟩ ⟨13, 2, 0, 403737, 111769, 2049, 16384⟩
    (by decide) selected_cut_15766

theorem selected_cut_15767 : selected 8 ⟨403757, by decide⟩
    (prefixPartial 13 111770) = some ⟨13, 2, 0, 403757, 111770, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_111770_403757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111770 ⟨403757, by decide⟩ :=
  accepted_of_selected 13 111770 ⟨403757, by decide⟩ ⟨13, 2, 0, 403757, 111770, 1373, 16384⟩
    (by decide) selected_cut_15767

theorem selected_cut_15768 : selected 8 ⟨403764, by decide⟩
    (prefixPartial 13 111771) = some ⟨13, 2, 0, 403764, 111771, 925, 16384⟩ := by
  decide +kernel

theorem context_13_111771_403764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111771 ⟨403764, by decide⟩ :=
  accepted_of_selected 13 111771 ⟨403764, by decide⟩ ⟨13, 2, 0, 403764, 111771, 925, 16384⟩
    (by decide) selected_cut_15768

theorem unmarked_context_12_27942_403765 : frontier 9 ⟨403765, by decide⟩
    (prefixCache 12 27942) (prefixPartial 12 27942) = false := by
  decide +kernel

theorem node_context_12_27942_403765 : EJMOriginalGlobalDAGData.nodes 9 ⟨403765, by decide⟩ =
    .split (coordinate 12) (![⟨403710, by decide⟩,⟨403737, by decide⟩,⟨403757, by decide⟩,⟨403764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27942_403765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27942 ⟨403765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27942
    ⟨403765, by decide⟩ (by decide) (![⟨403710, by decide⟩,⟨403737, by decide⟩,⟨403757, by decide⟩,⟨403764, by decide⟩]) unmarked_context_12_27942_403765 node_context_12_27942_403765
  intro a
  fin_cases a
  · exact context_13_111768_403710
  · exact context_13_111769_403737
  · exact context_13_111770_403757
  · exact context_13_111771_403764

theorem selected_cut_15769 : selected 8 ⟨403782, by decide⟩
    (prefixPartial 13 111772) = some ⟨13, 2, 0, 403782, 111772, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_111772_403782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111772 ⟨403782, by decide⟩ :=
  accepted_of_selected 13 111772 ⟨403782, by decide⟩ ⟨13, 2, 0, 403782, 111772, 1165, 16384⟩
    (by decide) selected_cut_15769

theorem selected_cut_15770 : selected 8 ⟨403808, by decide⟩
    (prefixPartial 13 111773) = some ⟨13, 2, 0, 403808, 111773, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_111773_403808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111773 ⟨403808, by decide⟩ :=
  accepted_of_selected 13 111773 ⟨403808, by decide⟩ ⟨13, 2, 0, 403808, 111773, 2349, 16384⟩
    (by decide) selected_cut_15770

theorem selected_cut_15771 : selected 8 ⟨403834, by decide⟩
    (prefixPartial 13 111774) = some ⟨13, 2, 0, 403834, 111774, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_111774_403834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111774 ⟨403834, by decide⟩ :=
  accepted_of_selected 13 111774 ⟨403834, by decide⟩ ⟨13, 2, 0, 403834, 111774, 1749, 16384⟩
    (by decide) selected_cut_15771

theorem selected_cut_15772 : selected 8 ⟨403845, by decide⟩
    (prefixPartial 13 111775) = some ⟨13, 2, 0, 403845, 111775, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_111775_403845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111775 ⟨403845, by decide⟩ :=
  accepted_of_selected 13 111775 ⟨403845, by decide⟩ ⟨13, 2, 0, 403845, 111775, 1037, 16384⟩
    (by decide) selected_cut_15772

theorem unmarked_context_12_27943_403846 : frontier 9 ⟨403846, by decide⟩
    (prefixCache 12 27943) (prefixPartial 12 27943) = false := by
  decide +kernel

theorem node_context_12_27943_403846 : EJMOriginalGlobalDAGData.nodes 9 ⟨403846, by decide⟩ =
    .split (coordinate 12) (![⟨403782, by decide⟩,⟨403808, by decide⟩,⟨403834, by decide⟩,⟨403845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27943_403846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27943 ⟨403846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27943
    ⟨403846, by decide⟩ (by decide) (![⟨403782, by decide⟩,⟨403808, by decide⟩,⟨403834, by decide⟩,⟨403845, by decide⟩]) unmarked_context_12_27943_403846 node_context_12_27943_403846
  intro a
  fin_cases a
  · exact context_13_111772_403782
  · exact context_13_111773_403808
  · exact context_13_111774_403834
  · exact context_13_111775_403845

theorem unmarked_context_11_6985_403847 : frontier 10 ⟨403847, by decide⟩
    (prefixCache 11 6985) (prefixPartial 11 6985) = false := by
  decide +kernel

theorem node_context_11_6985_403847 : EJMOriginalGlobalDAGData.nodes 10 ⟨403847, by decide⟩ =
    .split (coordinate 11) (![⟨403569, by decide⟩,⟨403691, by decide⟩,⟨403765, by decide⟩,⟨403846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6985_403847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6985 ⟨403847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6985
    ⟨403847, by decide⟩ (by decide) (![⟨403569, by decide⟩,⟨403691, by decide⟩,⟨403765, by decide⟩,⟨403846, by decide⟩]) unmarked_context_11_6985_403847 node_context_11_6985_403847
  intro a
  fin_cases a
  · exact context_12_27940_403569
  · exact context_12_27941_403691
  · exact context_12_27942_403765
  · exact context_12_27943_403846

theorem selected_cut_15773 : selected 8 ⟨403859, by decide⟩
    (prefixPartial 13 111776) = some ⟨13, 2, 0, 403859, 111776, 917, 16384⟩ := by
  decide +kernel

theorem context_13_111776_403859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111776 ⟨403859, by decide⟩ :=
  accepted_of_selected 13 111776 ⟨403859, by decide⟩ ⟨13, 2, 0, 403859, 111776, 917, 16384⟩
    (by decide) selected_cut_15773

theorem selected_cut_15774 : selected 8 ⟨403889, by decide⟩
    (prefixPartial 13 111777) = some ⟨13, 2, 0, 403889, 111777, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_111777_403889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111777 ⟨403889, by decide⟩ :=
  accepted_of_selected 13 111777 ⟨403889, by decide⟩ ⟨13, 2, 0, 403889, 111777, 2357, 16384⟩
    (by decide) selected_cut_15774

theorem selected_cut_15775 : selected 8 ⟨403908, by decide⟩
    (prefixPartial 13 111778) = some ⟨13, 2, 0, 403908, 111778, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_111778_403908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111778 ⟨403908, by decide⟩ :=
  accepted_of_selected 13 111778 ⟨403908, by decide⟩ ⟨13, 2, 0, 403908, 111778, 1545, 16384⟩
    (by decide) selected_cut_15775

theorem selected_cut_15776 : selected 8 ⟨403916, by decide⟩
    (prefixPartial 13 111779) = some ⟨13, 2, 0, 403916, 111779, 841, 16384⟩ := by
  decide +kernel

theorem context_13_111779_403916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111779 ⟨403916, by decide⟩ :=
  accepted_of_selected 13 111779 ⟨403916, by decide⟩ ⟨13, 2, 0, 403916, 111779, 841, 16384⟩
    (by decide) selected_cut_15776

theorem unmarked_context_12_27944_403917 : frontier 9 ⟨403917, by decide⟩
    (prefixCache 12 27944) (prefixPartial 12 27944) = false := by
  decide +kernel

theorem node_context_12_27944_403917 : EJMOriginalGlobalDAGData.nodes 9 ⟨403917, by decide⟩ =
    .split (coordinate 12) (![⟨403859, by decide⟩,⟨403889, by decide⟩,⟨403908, by decide⟩,⟨403916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27944_403917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27944 ⟨403917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27944
    ⟨403917, by decide⟩ (by decide) (![⟨403859, by decide⟩,⟨403889, by decide⟩,⟨403908, by decide⟩,⟨403916, by decide⟩]) unmarked_context_12_27944_403917 node_context_12_27944_403917
  intro a
  fin_cases a
  · exact context_13_111776_403859
  · exact context_13_111777_403889
  · exact context_13_111778_403908
  · exact context_13_111779_403916

theorem selected_cut_15777 : selected 8 ⟨403929, by decide⟩
    (prefixPartial 13 111780) = some ⟨13, 2, 0, 403929, 111780, 997, 16384⟩ := by
  decide +kernel

theorem context_13_111780_403929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111780 ⟨403929, by decide⟩ :=
  accepted_of_selected 13 111780 ⟨403929, by decide⟩ ⟨13, 2, 0, 403929, 111780, 997, 16384⟩
    (by decide) selected_cut_15777

theorem selected_cut_15778 : selected 8 ⟨403951, by decide⟩
    (prefixPartial 13 111781) = some ⟨13, 2, 0, 403951, 111781, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_111781_403951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111781 ⟨403951, by decide⟩ :=
  accepted_of_selected 13 111781 ⟨403951, by decide⟩ ⟨13, 2, 0, 403951, 111781, 2025, 16384⟩
    (by decide) selected_cut_15778

theorem selected_cut_15779 : selected 8 ⟨403971, by decide⟩
    (prefixPartial 13 111782) = some ⟨13, 2, 0, 403971, 111782, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_111782_403971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111782 ⟨403971, by decide⟩ :=
  accepted_of_selected 13 111782 ⟨403971, by decide⟩ ⟨13, 2, 0, 403971, 111782, 1485, 16384⟩
    (by decide) selected_cut_15779

theorem selected_cut_15780 : selected 8 ⟨403977, by decide⟩
    (prefixPartial 13 111783) = some ⟨13, 2, 0, 403977, 111783, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_111783_403977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111783 ⟨403977, by decide⟩ :=
  accepted_of_selected 13 111783 ⟨403977, by decide⟩ ⟨13, 2, 0, 403977, 111783, 1021, 16384⟩
    (by decide) selected_cut_15780

theorem unmarked_context_12_27945_403978 : frontier 9 ⟨403978, by decide⟩
    (prefixCache 12 27945) (prefixPartial 12 27945) = false := by
  decide +kernel

theorem node_context_12_27945_403978 : EJMOriginalGlobalDAGData.nodes 9 ⟨403978, by decide⟩ =
    .split (coordinate 12) (![⟨403929, by decide⟩,⟨403951, by decide⟩,⟨403971, by decide⟩,⟨403977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27945_403978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27945 ⟨403978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27945
    ⟨403978, by decide⟩ (by decide) (![⟨403929, by decide⟩,⟨403951, by decide⟩,⟨403971, by decide⟩,⟨403977, by decide⟩]) unmarked_context_12_27945_403978 node_context_12_27945_403978
  intro a
  fin_cases a
  · exact context_13_111780_403929
  · exact context_13_111781_403951
  · exact context_13_111782_403971
  · exact context_13_111783_403977

theorem selected_cut_15781 : selected 8 ⟨403994, by decide⟩
    (prefixPartial 13 111784) = some ⟨13, 2, 0, 403994, 111784, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_111784_403994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111784 ⟨403994, by decide⟩ :=
  accepted_of_selected 13 111784 ⟨403994, by decide⟩ ⟨13, 2, 0, 403994, 111784, 1133, 16384⟩
    (by decide) selected_cut_15781

theorem selected_cut_15782 : selected 8 ⟨404025, by decide⟩
    (prefixPartial 13 111785) = some ⟨13, 2, 0, 404025, 111785, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_111785_404025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111785 ⟨404025, by decide⟩ :=
  accepted_of_selected 13 111785 ⟨404025, by decide⟩ ⟨13, 2, 0, 404025, 111785, 2389, 16384⟩
    (by decide) selected_cut_15782

theorem selected_cut_15783 : selected 8 ⟨404046, by decide⟩
    (prefixPartial 13 111786) = some ⟨13, 2, 0, 404046, 111786, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_111786_404046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111786 ⟨404046, by decide⟩ :=
  accepted_of_selected 13 111786 ⟨404046, by decide⟩ ⟨13, 2, 0, 404046, 111786, 1401, 16384⟩
    (by decide) selected_cut_15783

theorem selected_cut_15784 : selected 8 ⟨404054, by decide⟩
    (prefixPartial 13 111787) = some ⟨13, 2, 0, 404054, 111787, 969, 16384⟩ := by
  decide +kernel

theorem context_13_111787_404054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111787 ⟨404054, by decide⟩ :=
  accepted_of_selected 13 111787 ⟨404054, by decide⟩ ⟨13, 2, 0, 404054, 111787, 969, 16384⟩
    (by decide) selected_cut_15784

theorem unmarked_context_12_27946_404055 : frontier 9 ⟨404055, by decide⟩
    (prefixCache 12 27946) (prefixPartial 12 27946) = false := by
  decide +kernel

theorem node_context_12_27946_404055 : EJMOriginalGlobalDAGData.nodes 9 ⟨404055, by decide⟩ =
    .split (coordinate 12) (![⟨403994, by decide⟩,⟨404025, by decide⟩,⟨404046, by decide⟩,⟨404054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27946_404055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27946 ⟨404055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27946
    ⟨404055, by decide⟩ (by decide) (![⟨403994, by decide⟩,⟨404025, by decide⟩,⟨404046, by decide⟩,⟨404054, by decide⟩]) unmarked_context_12_27946_404055 node_context_12_27946_404055
  intro a
  fin_cases a
  · exact context_13_111784_403994
  · exact context_13_111785_404025
  · exact context_13_111786_404046
  · exact context_13_111787_404054

theorem selected_cut_15785 : selected 8 ⟨404072, by decide⟩
    (prefixPartial 13 111788) = some ⟨13, 2, 0, 404072, 111788, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_111788_404072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111788 ⟨404072, by decide⟩ :=
  accepted_of_selected 13 111788 ⟨404072, by decide⟩ ⟨13, 2, 0, 404072, 111788, 1137, 16384⟩
    (by decide) selected_cut_15785

theorem selected_cut_15786 : selected 8 ⟨404103, by decide⟩
    (prefixPartial 13 111789) = some ⟨13, 2, 0, 404103, 111789, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_111789_404103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111789 ⟨404103, by decide⟩ :=
  accepted_of_selected 13 111789 ⟨404103, by decide⟩ ⟨13, 2, 0, 404103, 111789, 2801, 16384⟩
    (by decide) selected_cut_15786

theorem selected_cut_15787 : selected 8 ⟨404124, by decide⟩
    (prefixPartial 13 111790) = some ⟨13, 2, 0, 404124, 111790, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_111790_404124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111790 ⟨404124, by decide⟩ :=
  accepted_of_selected 13 111790 ⟨404124, by decide⟩ ⟨13, 2, 0, 404124, 111790, 1697, 16384⟩
    (by decide) selected_cut_15787

theorem selected_cut_15788 : selected 8 ⟨404134, by decide⟩
    (prefixPartial 13 111791) = some ⟨13, 2, 0, 404134, 111791, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_111791_404134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111791 ⟨404134, by decide⟩ :=
  accepted_of_selected 13 111791 ⟨404134, by decide⟩ ⟨13, 2, 0, 404134, 111791, 1049, 16384⟩
    (by decide) selected_cut_15788

theorem unmarked_context_12_27947_404135 : frontier 9 ⟨404135, by decide⟩
    (prefixCache 12 27947) (prefixPartial 12 27947) = false := by
  decide +kernel

theorem node_context_12_27947_404135 : EJMOriginalGlobalDAGData.nodes 9 ⟨404135, by decide⟩ =
    .split (coordinate 12) (![⟨404072, by decide⟩,⟨404103, by decide⟩,⟨404124, by decide⟩,⟨404134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27947_404135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27947 ⟨404135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27947
    ⟨404135, by decide⟩ (by decide) (![⟨404072, by decide⟩,⟨404103, by decide⟩,⟨404124, by decide⟩,⟨404134, by decide⟩]) unmarked_context_12_27947_404135 node_context_12_27947_404135
  intro a
  fin_cases a
  · exact context_13_111788_404072
  · exact context_13_111789_404103
  · exact context_13_111790_404124
  · exact context_13_111791_404134

theorem unmarked_context_11_6986_404136 : frontier 10 ⟨404136, by decide⟩
    (prefixCache 11 6986) (prefixPartial 11 6986) = false := by
  decide +kernel

theorem node_context_11_6986_404136 : EJMOriginalGlobalDAGData.nodes 10 ⟨404136, by decide⟩ =
    .split (coordinate 11) (![⟨403917, by decide⟩,⟨403978, by decide⟩,⟨404055, by decide⟩,⟨404135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6986_404136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6986 ⟨404136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6986
    ⟨404136, by decide⟩ (by decide) (![⟨403917, by decide⟩,⟨403978, by decide⟩,⟨404055, by decide⟩,⟨404135, by decide⟩]) unmarked_context_11_6986_404136 node_context_11_6986_404136
  intro a
  fin_cases a
  · exact context_12_27944_403917
  · exact context_12_27945_403978
  · exact context_12_27946_404055
  · exact context_12_27947_404135

theorem selected_cut_15789 : selected 8 ⟨404144, by decide⟩
    (prefixPartial 13 111792) = some ⟨13, 2, 0, 404144, 111792, 669, 16384⟩ := by
  decide +kernel

theorem context_13_111792_404144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111792 ⟨404144, by decide⟩ :=
  accepted_of_selected 13 111792 ⟨404144, by decide⟩ ⟨13, 2, 0, 404144, 111792, 669, 16384⟩
    (by decide) selected_cut_15789

theorem selected_cut_15790 : selected 8 ⟨404177, by decide⟩
    (prefixPartial 13 111793) = some ⟨13, 2, 0, 404177, 111793, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_111793_404177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111793 ⟨404177, by decide⟩ :=
  accepted_of_selected 13 111793 ⟨404177, by decide⟩ ⟨13, 2, 0, 404177, 111793, 2545, 16384⟩
    (by decide) selected_cut_15790

theorem selected_cut_15791 : selected 8 ⟨404196, by decide⟩
    (prefixPartial 13 111794) = some ⟨13, 2, 0, 404196, 111794, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_111794_404196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111794 ⟨404196, by decide⟩ :=
  accepted_of_selected 13 111794 ⟨404196, by decide⟩ ⟨13, 2, 0, 404196, 111794, 1481, 16384⟩
    (by decide) selected_cut_15791

theorem selected_cut_15792 : selected 8 ⟨404202, by decide⟩
    (prefixPartial 13 111795) = some ⟨13, 2, 0, 404202, 111795, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_111795_404202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111795 ⟨404202, by decide⟩ :=
  accepted_of_selected 13 111795 ⟨404202, by decide⟩ ⟨13, 2, 0, 404202, 111795, 1005, 16384⟩
    (by decide) selected_cut_15792

theorem unmarked_context_12_27948_404203 : frontier 9 ⟨404203, by decide⟩
    (prefixCache 12 27948) (prefixPartial 12 27948) = false := by
  decide +kernel

theorem node_context_12_27948_404203 : EJMOriginalGlobalDAGData.nodes 9 ⟨404203, by decide⟩ =
    .split (coordinate 12) (![⟨404144, by decide⟩,⟨404177, by decide⟩,⟨404196, by decide⟩,⟨404202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27948_404203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27948 ⟨404203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27948
    ⟨404203, by decide⟩ (by decide) (![⟨404144, by decide⟩,⟨404177, by decide⟩,⟨404196, by decide⟩,⟨404202, by decide⟩]) unmarked_context_12_27948_404203 node_context_12_27948_404203
  intro a
  fin_cases a
  · exact context_13_111792_404144
  · exact context_13_111793_404177
  · exact context_13_111794_404196
  · exact context_13_111795_404202

theorem selected_cut_15793 : selected 8 ⟨404213, by decide⟩
    (prefixPartial 13 111796) = some ⟨13, 2, 0, 404213, 111796, 757, 16384⟩ := by
  decide +kernel

theorem context_13_111796_404213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111796 ⟨404213, by decide⟩ :=
  accepted_of_selected 13 111796 ⟨404213, by decide⟩ ⟨13, 2, 0, 404213, 111796, 757, 16384⟩
    (by decide) selected_cut_15793

theorem selected_cut_15794 : selected 8 ⟨404236, by decide⟩
    (prefixPartial 13 111797) = some ⟨13, 2, 0, 404236, 111797, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_111797_404236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111797 ⟨404236, by decide⟩ :=
  accepted_of_selected 13 111797 ⟨404236, by decide⟩ ⟨13, 2, 0, 404236, 111797, 2397, 16384⟩
    (by decide) selected_cut_15794

theorem selected_cut_15795 : selected 8 ⟨404257, by decide⟩
    (prefixPartial 13 111798) = some ⟨13, 2, 0, 404257, 111798, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_111798_404257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111798 ⟨404257, by decide⟩ :=
  accepted_of_selected 13 111798 ⟨404257, by decide⟩ ⟨13, 2, 0, 404257, 111798, 1645, 16384⟩
    (by decide) selected_cut_15795

theorem selected_cut_15796 : selected 8 ⟨404264, by decide⟩
    (prefixPartial 13 111799) = some ⟨13, 2, 0, 404264, 111799, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_111799_404264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111799 ⟨404264, by decide⟩ :=
  accepted_of_selected 13 111799 ⟨404264, by decide⟩ ⟨13, 2, 0, 404264, 111799, 1053, 16384⟩
    (by decide) selected_cut_15796

theorem unmarked_context_12_27949_404265 : frontier 9 ⟨404265, by decide⟩
    (prefixCache 12 27949) (prefixPartial 12 27949) = false := by
  decide +kernel

theorem node_context_12_27949_404265 : EJMOriginalGlobalDAGData.nodes 9 ⟨404265, by decide⟩ =
    .split (coordinate 12) (![⟨404213, by decide⟩,⟨404236, by decide⟩,⟨404257, by decide⟩,⟨404264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27949_404265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27949 ⟨404265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27949
    ⟨404265, by decide⟩ (by decide) (![⟨404213, by decide⟩,⟨404236, by decide⟩,⟨404257, by decide⟩,⟨404264, by decide⟩]) unmarked_context_12_27949_404265 node_context_12_27949_404265
  intro a
  fin_cases a
  · exact context_13_111796_404213
  · exact context_13_111797_404236
  · exact context_13_111798_404257
  · exact context_13_111799_404264

theorem selected_cut_15797 : selected 8 ⟨404280, by decide⟩
    (prefixPartial 13 111800) = some ⟨13, 2, 0, 404280, 111800, 877, 16384⟩ := by
  decide +kernel

theorem context_13_111800_404280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111800 ⟨404280, by decide⟩ :=
  accepted_of_selected 13 111800 ⟨404280, by decide⟩ ⟨13, 2, 0, 404280, 111800, 877, 16384⟩
    (by decide) selected_cut_15797

theorem selected_cut_15798 : selected 8 ⟨404317, by decide⟩
    (prefixPartial 13 111801) = some ⟨13, 2, 0, 404317, 111801, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_111801_404317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111801 ⟨404317, by decide⟩ :=
  accepted_of_selected 13 111801 ⟨404317, by decide⟩ ⟨13, 2, 0, 404317, 111801, 2741, 16384⟩
    (by decide) selected_cut_15798

theorem selected_cut_15799 : selected 8 ⟨404343, by decide⟩
    (prefixPartial 13 111802) = some ⟨13, 2, 0, 404343, 111802, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_111802_404343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111802 ⟨404343, by decide⟩ :=
  accepted_of_selected 13 111802 ⟨404343, by decide⟩ ⟨13, 2, 0, 404343, 111802, 1481, 16384⟩
    (by decide) selected_cut_15799

theorem selected_cut_15800 : selected 8 ⟨404352, by decide⟩
    (prefixPartial 13 111803) = some ⟨13, 2, 0, 404352, 111803, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_111803_404352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111803 ⟨404352, by decide⟩ :=
  accepted_of_selected 13 111803 ⟨404352, by decide⟩ ⟨13, 2, 0, 404352, 111803, 1081, 16384⟩
    (by decide) selected_cut_15800

theorem unmarked_context_12_27950_404353 : frontier 9 ⟨404353, by decide⟩
    (prefixCache 12 27950) (prefixPartial 12 27950) = false := by
  decide +kernel

theorem node_context_12_27950_404353 : EJMOriginalGlobalDAGData.nodes 9 ⟨404353, by decide⟩ =
    .split (coordinate 12) (![⟨404280, by decide⟩,⟨404317, by decide⟩,⟨404343, by decide⟩,⟨404352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27950_404353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27950 ⟨404353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27950
    ⟨404353, by decide⟩ (by decide) (![⟨404280, by decide⟩,⟨404317, by decide⟩,⟨404343, by decide⟩,⟨404352, by decide⟩]) unmarked_context_12_27950_404353 node_context_12_27950_404353
  intro a
  fin_cases a
  · exact context_13_111800_404280
  · exact context_13_111801_404317
  · exact context_13_111802_404343
  · exact context_13_111803_404352

theorem selected_cut_15801 : selected 8 ⟨404366, by decide⟩
    (prefixPartial 13 111804) = some ⟨13, 2, 0, 404366, 111804, 789, 16384⟩ := by
  decide +kernel

theorem context_13_111804_404366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111804 ⟨404366, by decide⟩ :=
  accepted_of_selected 13 111804 ⟨404366, by decide⟩ ⟨13, 2, 0, 404366, 111804, 789, 16384⟩
    (by decide) selected_cut_15801

theorem selected_cut_15802 : selected 8 ⟨404392, by decide⟩
    (prefixPartial 13 111805) = some ⟨13, 2, 0, 404392, 111805, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_111805_404392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111805 ⟨404392, by decide⟩ :=
  accepted_of_selected 13 111805 ⟨404392, by decide⟩ ⟨13, 2, 0, 404392, 111805, 2765, 16384⟩
    (by decide) selected_cut_15802

theorem selected_cut_15803 : selected 8 ⟨404413, by decide⟩
    (prefixPartial 13 111806) = some ⟨13, 2, 0, 404413, 111806, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_111806_404413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111806 ⟨404413, by decide⟩ :=
  accepted_of_selected 13 111806 ⟨404413, by decide⟩ ⟨13, 2, 0, 404413, 111806, 1761, 16384⟩
    (by decide) selected_cut_15803

theorem selected_cut_15804 : selected 8 ⟨404421, by decide⟩
    (prefixPartial 13 111807) = some ⟨13, 2, 0, 404421, 111807, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_111807_404421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111807 ⟨404421, by decide⟩ :=
  accepted_of_selected 13 111807 ⟨404421, by decide⟩ ⟨13, 2, 0, 404421, 111807, 1169, 16384⟩
    (by decide) selected_cut_15804

theorem unmarked_context_12_27951_404422 : frontier 9 ⟨404422, by decide⟩
    (prefixCache 12 27951) (prefixPartial 12 27951) = false := by
  decide +kernel

theorem node_context_12_27951_404422 : EJMOriginalGlobalDAGData.nodes 9 ⟨404422, by decide⟩ =
    .split (coordinate 12) (![⟨404366, by decide⟩,⟨404392, by decide⟩,⟨404413, by decide⟩,⟨404421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27951_404422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27951 ⟨404422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27951
    ⟨404422, by decide⟩ (by decide) (![⟨404366, by decide⟩,⟨404392, by decide⟩,⟨404413, by decide⟩,⟨404421, by decide⟩]) unmarked_context_12_27951_404422 node_context_12_27951_404422
  intro a
  fin_cases a
  · exact context_13_111804_404366
  · exact context_13_111805_404392
  · exact context_13_111806_404413
  · exact context_13_111807_404421

theorem unmarked_context_11_6987_404423 : frontier 10 ⟨404423, by decide⟩
    (prefixCache 11 6987) (prefixPartial 11 6987) = false := by
  decide +kernel

theorem node_context_11_6987_404423 : EJMOriginalGlobalDAGData.nodes 10 ⟨404423, by decide⟩ =
    .split (coordinate 11) (![⟨404203, by decide⟩,⟨404265, by decide⟩,⟨404353, by decide⟩,⟨404422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6987_404423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6987 ⟨404423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6987
    ⟨404423, by decide⟩ (by decide) (![⟨404203, by decide⟩,⟨404265, by decide⟩,⟨404353, by decide⟩,⟨404422, by decide⟩]) unmarked_context_11_6987_404423 node_context_11_6987_404423
  intro a
  fin_cases a
  · exact context_12_27948_404203
  · exact context_12_27949_404265
  · exact context_12_27950_404353
  · exact context_12_27951_404422

theorem unmarked_context_10_1746_404424 : frontier 11 ⟨404424, by decide⟩
    (prefixCache 10 1746) (prefixPartial 10 1746) = false := by
  decide +kernel

theorem node_context_10_1746_404424 : EJMOriginalGlobalDAGData.nodes 11 ⟨404424, by decide⟩ =
    .split (coordinate 10) (![⟨403501, by decide⟩,⟨403847, by decide⟩,⟨404136, by decide⟩,⟨404423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1746_404424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1746 ⟨404424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1746
    ⟨404424, by decide⟩ (by decide) (![⟨403501, by decide⟩,⟨403847, by decide⟩,⟨404136, by decide⟩,⟨404423, by decide⟩]) unmarked_context_10_1746_404424 node_context_10_1746_404424
  intro a
  fin_cases a
  · exact context_11_6984_403501
  · exact context_11_6985_403847
  · exact context_11_6986_404136
  · exact context_11_6987_404423

theorem selected_cut_15805 : selected 8 ⟨404435, by decide⟩
    (prefixPartial 13 111808) = some ⟨13, 2, 0, 404435, 111808, 885, 16384⟩ := by
  decide +kernel

theorem context_13_111808_404435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111808 ⟨404435, by decide⟩ :=
  accepted_of_selected 13 111808 ⟨404435, by decide⟩ ⟨13, 2, 0, 404435, 111808, 885, 16384⟩
    (by decide) selected_cut_15805

theorem selected_cut_15806 : selected 8 ⟨404459, by decide⟩
    (prefixPartial 13 111809) = some ⟨13, 2, 0, 404459, 111809, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_111809_404459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111809 ⟨404459, by decide⟩ :=
  accepted_of_selected 13 111809 ⟨404459, by decide⟩ ⟨13, 2, 0, 404459, 111809, 2557, 16384⟩
    (by decide) selected_cut_15806

theorem selected_cut_15807 : selected 8 ⟨404481, by decide⟩
    (prefixPartial 13 111810) = some ⟨13, 2, 0, 404481, 111810, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_111810_404481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111810 ⟨404481, by decide⟩ :=
  accepted_of_selected 13 111810 ⟨404481, by decide⟩ ⟨13, 2, 0, 404481, 111810, 1629, 16384⟩
    (by decide) selected_cut_15807

theorem selected_cut_15808 : selected 8 ⟨404486, by decide⟩
    (prefixPartial 13 111811) = some ⟨13, 2, 0, 404486, 111811, 721, 16384⟩ := by
  decide +kernel

theorem context_13_111811_404486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111811 ⟨404486, by decide⟩ :=
  accepted_of_selected 13 111811 ⟨404486, by decide⟩ ⟨13, 2, 0, 404486, 111811, 721, 16384⟩
    (by decide) selected_cut_15808

theorem unmarked_context_12_27952_404487 : frontier 9 ⟨404487, by decide⟩
    (prefixCache 12 27952) (prefixPartial 12 27952) = false := by
  decide +kernel

theorem node_context_12_27952_404487 : EJMOriginalGlobalDAGData.nodes 9 ⟨404487, by decide⟩ =
    .split (coordinate 12) (![⟨404435, by decide⟩,⟨404459, by decide⟩,⟨404481, by decide⟩,⟨404486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27952_404487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27952 ⟨404487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27952
    ⟨404487, by decide⟩ (by decide) (![⟨404435, by decide⟩,⟨404459, by decide⟩,⟨404481, by decide⟩,⟨404486, by decide⟩]) unmarked_context_12_27952_404487 node_context_12_27952_404487
  intro a
  fin_cases a
  · exact context_13_111808_404435
  · exact context_13_111809_404459
  · exact context_13_111810_404481
  · exact context_13_111811_404486

theorem selected_cut_15809 : selected 8 ⟨404495, by decide⟩
    (prefixPartial 13 111812) = some ⟨13, 2, 0, 404495, 111812, 749, 16384⟩ := by
  decide +kernel

theorem context_13_111812_404495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111812 ⟨404495, by decide⟩ :=
  accepted_of_selected 13 111812 ⟨404495, by decide⟩ ⟨13, 2, 0, 404495, 111812, 749, 16384⟩
    (by decide) selected_cut_15809

theorem selected_cut_15810 : selected 8 ⟨404518, by decide⟩
    (prefixPartial 13 111813) = some ⟨13, 2, 0, 404518, 111813, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_111813_404518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111813 ⟨404518, by decide⟩ :=
  accepted_of_selected 13 111813 ⟨404518, by decide⟩ ⟨13, 2, 0, 404518, 111813, 2313, 16384⟩
    (by decide) selected_cut_15810

theorem selected_cut_15811 : selected 8 ⟨404542, by decide⟩
    (prefixPartial 13 111814) = some ⟨13, 2, 0, 404542, 111814, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_111814_404542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111814 ⟨404542, by decide⟩ :=
  accepted_of_selected 13 111814 ⟨404542, by decide⟩ ⟨13, 2, 0, 404542, 111814, 1929, 16384⟩
    (by decide) selected_cut_15811

theorem selected_cut_15812 : selected 8 ⟨404548, by decide⟩
    (prefixPartial 13 111815) = some ⟨13, 2, 0, 404548, 111815, 917, 16384⟩ := by
  decide +kernel

theorem context_13_111815_404548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111815 ⟨404548, by decide⟩ :=
  accepted_of_selected 13 111815 ⟨404548, by decide⟩ ⟨13, 2, 0, 404548, 111815, 917, 16384⟩
    (by decide) selected_cut_15812

theorem unmarked_context_12_27953_404549 : frontier 9 ⟨404549, by decide⟩
    (prefixCache 12 27953) (prefixPartial 12 27953) = false := by
  decide +kernel

theorem node_context_12_27953_404549 : EJMOriginalGlobalDAGData.nodes 9 ⟨404549, by decide⟩ =
    .split (coordinate 12) (![⟨404495, by decide⟩,⟨404518, by decide⟩,⟨404542, by decide⟩,⟨404548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27953_404549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27953 ⟨404549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27953
    ⟨404549, by decide⟩ (by decide) (![⟨404495, by decide⟩,⟨404518, by decide⟩,⟨404542, by decide⟩,⟨404548, by decide⟩]) unmarked_context_12_27953_404549 node_context_12_27953_404549
  intro a
  fin_cases a
  · exact context_13_111812_404495
  · exact context_13_111813_404518
  · exact context_13_111814_404542
  · exact context_13_111815_404548

theorem selected_cut_15813 : selected 8 ⟨404564, by decide⟩
    (prefixPartial 13 111816) = some ⟨13, 2, 0, 404564, 111816, 885, 16384⟩ := by
  decide +kernel

theorem context_13_111816_404564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111816 ⟨404564, by decide⟩ :=
  accepted_of_selected 13 111816 ⟨404564, by decide⟩ ⟨13, 2, 0, 404564, 111816, 885, 16384⟩
    (by decide) selected_cut_15813

theorem selected_cut_15814 : selected 8 ⟨404607, by decide⟩
    (prefixPartial 13 111817) = some ⟨13, 2, 0, 404607, 111817, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_111817_404607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111817 ⟨404607, by decide⟩ :=
  accepted_of_selected 13 111817 ⟨404607, by decide⟩ ⟨13, 2, 0, 404607, 111817, 2753, 16384⟩
    (by decide) selected_cut_15814

theorem selected_cut_15815 : selected 8 ⟨404641, by decide⟩
    (prefixPartial 13 111818) = some ⟨13, 2, 0, 404641, 111818, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_111818_404641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111818 ⟨404641, by decide⟩ :=
  accepted_of_selected 13 111818 ⟨404641, by decide⟩ ⟨13, 2, 0, 404641, 111818, 1965, 16384⟩
    (by decide) selected_cut_15815

theorem selected_cut_15816 : selected 8 ⟨404648, by decide⟩
    (prefixPartial 13 111819) = some ⟨13, 2, 0, 404648, 111819, 937, 16384⟩ := by
  decide +kernel

theorem context_13_111819_404648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111819 ⟨404648, by decide⟩ :=
  accepted_of_selected 13 111819 ⟨404648, by decide⟩ ⟨13, 2, 0, 404648, 111819, 937, 16384⟩
    (by decide) selected_cut_15816

theorem unmarked_context_12_27954_404649 : frontier 9 ⟨404649, by decide⟩
    (prefixCache 12 27954) (prefixPartial 12 27954) = false := by
  decide +kernel

theorem node_context_12_27954_404649 : EJMOriginalGlobalDAGData.nodes 9 ⟨404649, by decide⟩ =
    .split (coordinate 12) (![⟨404564, by decide⟩,⟨404607, by decide⟩,⟨404641, by decide⟩,⟨404648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27954_404649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27954 ⟨404649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27954
    ⟨404649, by decide⟩ (by decide) (![⟨404564, by decide⟩,⟨404607, by decide⟩,⟨404641, by decide⟩,⟨404648, by decide⟩]) unmarked_context_12_27954_404649 node_context_12_27954_404649
  intro a
  fin_cases a
  · exact context_13_111816_404564
  · exact context_13_111817_404607
  · exact context_13_111818_404641
  · exact context_13_111819_404648

theorem selected_cut_15817 : selected 8 ⟨404662, by decide⟩
    (prefixPartial 13 111820) = some ⟨13, 2, 0, 404662, 111820, 941, 16384⟩ := by
  decide +kernel

theorem context_13_111820_404662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111820 ⟨404662, by decide⟩ :=
  accepted_of_selected 13 111820 ⟨404662, by decide⟩ ⟨13, 2, 0, 404662, 111820, 941, 16384⟩
    (by decide) selected_cut_15817

theorem selected_cut_15818 : selected 8 ⟨404697, by decide⟩
    (prefixPartial 13 111821) = some ⟨13, 2, 0, 404697, 111821, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_111821_404697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111821 ⟨404697, by decide⟩ :=
  accepted_of_selected 13 111821 ⟨404697, by decide⟩ ⟨13, 2, 0, 404697, 111821, 2881, 16384⟩
    (by decide) selected_cut_15818

theorem selected_cut_15819 : selected 8 ⟨404729, by decide⟩
    (prefixPartial 13 111822) = some ⟨13, 2, 0, 404729, 111822, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_111822_404729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111822 ⟨404729, by decide⟩ :=
  accepted_of_selected 13 111822 ⟨404729, by decide⟩ ⟨13, 2, 0, 404729, 111822, 2325, 16384⟩
    (by decide) selected_cut_15819

theorem selected_cut_15820 : selected 8 ⟨404737, by decide⟩
    (prefixPartial 13 111823) = some ⟨13, 2, 0, 404737, 111823, 989, 16384⟩ := by
  decide +kernel

theorem context_13_111823_404737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111823 ⟨404737, by decide⟩ :=
  accepted_of_selected 13 111823 ⟨404737, by decide⟩ ⟨13, 2, 0, 404737, 111823, 989, 16384⟩
    (by decide) selected_cut_15820

theorem unmarked_context_12_27955_404738 : frontier 9 ⟨404738, by decide⟩
    (prefixCache 12 27955) (prefixPartial 12 27955) = false := by
  decide +kernel

theorem node_context_12_27955_404738 : EJMOriginalGlobalDAGData.nodes 9 ⟨404738, by decide⟩ =
    .split (coordinate 12) (![⟨404662, by decide⟩,⟨404697, by decide⟩,⟨404729, by decide⟩,⟨404737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27955_404738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27955 ⟨404738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27955
    ⟨404738, by decide⟩ (by decide) (![⟨404662, by decide⟩,⟨404697, by decide⟩,⟨404729, by decide⟩,⟨404737, by decide⟩]) unmarked_context_12_27955_404738 node_context_12_27955_404738
  intro a
  fin_cases a
  · exact context_13_111820_404662
  · exact context_13_111821_404697
  · exact context_13_111822_404729
  · exact context_13_111823_404737

theorem unmarked_context_11_6988_404739 : frontier 10 ⟨404739, by decide⟩
    (prefixCache 11 6988) (prefixPartial 11 6988) = false := by
  decide +kernel

theorem node_context_11_6988_404739 : EJMOriginalGlobalDAGData.nodes 10 ⟨404739, by decide⟩ =
    .split (coordinate 11) (![⟨404487, by decide⟩,⟨404549, by decide⟩,⟨404649, by decide⟩,⟨404738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6988_404739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6988 ⟨404739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6988
    ⟨404739, by decide⟩ (by decide) (![⟨404487, by decide⟩,⟨404549, by decide⟩,⟨404649, by decide⟩,⟨404738, by decide⟩]) unmarked_context_11_6988_404739 node_context_11_6988_404739
  intro a
  fin_cases a
  · exact context_12_27952_404487
  · exact context_12_27953_404549
  · exact context_12_27954_404649
  · exact context_12_27955_404738

theorem selected_cut_15821 : selected 8 ⟨404747, by decide⟩
    (prefixPartial 13 111824) = some ⟨13, 2, 0, 404747, 111824, 513, 16384⟩ := by
  decide +kernel

theorem context_13_111824_404747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111824 ⟨404747, by decide⟩ :=
  accepted_of_selected 13 111824 ⟨404747, by decide⟩ ⟨13, 2, 0, 404747, 111824, 513, 16384⟩
    (by decide) selected_cut_15821

theorem selected_cut_15822 : selected 8 ⟨404768, by decide⟩
    (prefixPartial 13 111825) = some ⟨13, 2, 0, 404768, 111825, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_111825_404768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111825 ⟨404768, by decide⟩ :=
  accepted_of_selected 13 111825 ⟨404768, by decide⟩ ⟨13, 2, 0, 404768, 111825, 2025, 16384⟩
    (by decide) selected_cut_15822

theorem selected_cut_15823 : selected 8 ⟨404789, by decide⟩
    (prefixPartial 13 111826) = some ⟨13, 2, 0, 404789, 111826, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_111826_404789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111826 ⟨404789, by decide⟩ :=
  accepted_of_selected 13 111826 ⟨404789, by decide⟩ ⟨13, 2, 0, 404789, 111826, 1465, 16384⟩
    (by decide) selected_cut_15823

theorem selected_cut_15824 : selected 8 ⟨404797, by decide⟩
    (prefixPartial 13 111827) = some ⟨13, 2, 0, 404797, 111827, 793, 16384⟩ := by
  decide +kernel

theorem context_13_111827_404797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111827 ⟨404797, by decide⟩ :=
  accepted_of_selected 13 111827 ⟨404797, by decide⟩ ⟨13, 2, 0, 404797, 111827, 793, 16384⟩
    (by decide) selected_cut_15824

theorem unmarked_context_12_27956_404798 : frontier 9 ⟨404798, by decide⟩
    (prefixCache 12 27956) (prefixPartial 12 27956) = false := by
  decide +kernel

theorem node_context_12_27956_404798 : EJMOriginalGlobalDAGData.nodes 9 ⟨404798, by decide⟩ =
    .split (coordinate 12) (![⟨404747, by decide⟩,⟨404768, by decide⟩,⟨404789, by decide⟩,⟨404797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27956_404798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27956 ⟨404798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27956
    ⟨404798, by decide⟩ (by decide) (![⟨404747, by decide⟩,⟨404768, by decide⟩,⟨404789, by decide⟩,⟨404797, by decide⟩]) unmarked_context_12_27956_404798 node_context_12_27956_404798
  intro a
  fin_cases a
  · exact context_13_111824_404747
  · exact context_13_111825_404768
  · exact context_13_111826_404789
  · exact context_13_111827_404797

theorem selected_cut_15825 : selected 8 ⟨404807, by decide⟩
    (prefixPartial 13 111828) = some ⟨13, 2, 0, 404807, 111828, 749, 16384⟩ := by
  decide +kernel

theorem context_13_111828_404807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111828 ⟨404807, by decide⟩ :=
  accepted_of_selected 13 111828 ⟨404807, by decide⟩ ⟨13, 2, 0, 404807, 111828, 749, 16384⟩
    (by decide) selected_cut_15825

theorem selected_cut_15826 : selected 8 ⟨404847, by decide⟩
    (prefixPartial 13 111829) = some ⟨13, 2, 0, 404847, 111829, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_111829_404847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111829 ⟨404847, by decide⟩ :=
  accepted_of_selected 13 111829 ⟨404847, by decide⟩ ⟨13, 2, 0, 404847, 111829, 3109, 16384⟩
    (by decide) selected_cut_15826

theorem selected_cut_15827 : selected 8 ⟨404885, by decide⟩
    (prefixPartial 13 111830) = some ⟨13, 2, 0, 404885, 111830, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_111830_404885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111830 ⟨404885, by decide⟩ :=
  accepted_of_selected 13 111830 ⟨404885, by decide⟩ ⟨13, 2, 0, 404885, 111830, 2433, 16384⟩
    (by decide) selected_cut_15827

theorem selected_cut_15828 : selected 8 ⟨404892, by decide⟩
    (prefixPartial 13 111831) = some ⟨13, 2, 0, 404892, 111831, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_111831_404892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111831 ⟨404892, by decide⟩ :=
  accepted_of_selected 13 111831 ⟨404892, by decide⟩ ⟨13, 2, 0, 404892, 111831, 1141, 16384⟩
    (by decide) selected_cut_15828

theorem unmarked_context_12_27957_404893 : frontier 9 ⟨404893, by decide⟩
    (prefixCache 12 27957) (prefixPartial 12 27957) = false := by
  decide +kernel

theorem node_context_12_27957_404893 : EJMOriginalGlobalDAGData.nodes 9 ⟨404893, by decide⟩ =
    .split (coordinate 12) (![⟨404807, by decide⟩,⟨404847, by decide⟩,⟨404885, by decide⟩,⟨404892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27957_404893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27957 ⟨404893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27957
    ⟨404893, by decide⟩ (by decide) (![⟨404807, by decide⟩,⟨404847, by decide⟩,⟨404885, by decide⟩,⟨404892, by decide⟩]) unmarked_context_12_27957_404893 node_context_12_27957_404893
  intro a
  fin_cases a
  · exact context_13_111828_404807
  · exact context_13_111829_404847
  · exact context_13_111830_404885
  · exact context_13_111831_404892

theorem selected_cut_15829 : selected 8 ⟨404899, by decide⟩
    (prefixPartial 13 111832) = some ⟨13, 2, 0, 404899, 111832, 565, 16384⟩ := by
  decide +kernel

theorem context_13_111832_404899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111832 ⟨404899, by decide⟩ :=
  accepted_of_selected 13 111832 ⟨404899, by decide⟩ ⟨13, 2, 0, 404899, 111832, 565, 16384⟩
    (by decide) selected_cut_15829

theorem selected_cut_15830 : selected 8 ⟨404927, by decide⟩
    (prefixPartial 13 111833) = some ⟨13, 2, 0, 404927, 111833, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_111833_404927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111833 ⟨404927, by decide⟩ :=
  accepted_of_selected 13 111833 ⟨404927, by decide⟩ ⟨13, 2, 0, 404927, 111833, 2069, 16384⟩
    (by decide) selected_cut_15830

theorem selected_cut_15831 : selected 8 ⟨404946, by decide⟩
    (prefixPartial 13 111834) = some ⟨13, 2, 0, 404946, 111834, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_111834_404946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111834 ⟨404946, by decide⟩ :=
  accepted_of_selected 13 111834 ⟨404946, by decide⟩ ⟨13, 2, 0, 404946, 111834, 1601, 16384⟩
    (by decide) selected_cut_15831

theorem selected_cut_15832 : selected 8 ⟨404953, by decide⟩
    (prefixPartial 13 111835) = some ⟨13, 2, 0, 404953, 111835, 917, 16384⟩ := by
  decide +kernel

theorem context_13_111835_404953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111835 ⟨404953, by decide⟩ :=
  accepted_of_selected 13 111835 ⟨404953, by decide⟩ ⟨13, 2, 0, 404953, 111835, 917, 16384⟩
    (by decide) selected_cut_15832

theorem unmarked_context_12_27958_404954 : frontier 9 ⟨404954, by decide⟩
    (prefixCache 12 27958) (prefixPartial 12 27958) = false := by
  decide +kernel

theorem node_context_12_27958_404954 : EJMOriginalGlobalDAGData.nodes 9 ⟨404954, by decide⟩ =
    .split (coordinate 12) (![⟨404899, by decide⟩,⟨404927, by decide⟩,⟨404946, by decide⟩,⟨404953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27958_404954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27958 ⟨404954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27958
    ⟨404954, by decide⟩ (by decide) (![⟨404899, by decide⟩,⟨404927, by decide⟩,⟨404946, by decide⟩,⟨404953, by decide⟩]) unmarked_context_12_27958_404954 node_context_12_27958_404954
  intro a
  fin_cases a
  · exact context_13_111832_404899
  · exact context_13_111833_404927
  · exact context_13_111834_404946
  · exact context_13_111835_404953

theorem selected_cut_15833 : selected 8 ⟨404962, by decide⟩
    (prefixPartial 13 111836) = some ⟨13, 2, 0, 404962, 111836, 513, 16384⟩ := by
  decide +kernel

theorem context_13_111836_404962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111836 ⟨404962, by decide⟩ :=
  accepted_of_selected 13 111836 ⟨404962, by decide⟩ ⟨13, 2, 0, 404962, 111836, 513, 16384⟩
    (by decide) selected_cut_15833

theorem selected_cut_15834 : selected 8 ⟨404988, by decide⟩
    (prefixPartial 13 111837) = some ⟨13, 2, 0, 404988, 111837, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_111837_404988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111837 ⟨404988, by decide⟩ :=
  accepted_of_selected 13 111837 ⟨404988, by decide⟩ ⟨13, 2, 0, 404988, 111837, 2365, 16384⟩
    (by decide) selected_cut_15834

theorem selected_cut_15835 : selected 8 ⟨405009, by decide⟩
    (prefixPartial 13 111838) = some ⟨13, 2, 0, 405009, 111838, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_111838_405009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111838 ⟨405009, by decide⟩ :=
  accepted_of_selected 13 111838 ⟨405009, by decide⟩ ⟨13, 2, 0, 405009, 111838, 1869, 16384⟩
    (by decide) selected_cut_15835

theorem selected_cut_15836 : selected 8 ⟨405015, by decide⟩
    (prefixPartial 13 111839) = some ⟨13, 2, 0, 405015, 111839, 957, 16384⟩ := by
  decide +kernel

theorem context_13_111839_405015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111839 ⟨405015, by decide⟩ :=
  accepted_of_selected 13 111839 ⟨405015, by decide⟩ ⟨13, 2, 0, 405015, 111839, 957, 16384⟩
    (by decide) selected_cut_15836

theorem unmarked_context_12_27959_405016 : frontier 9 ⟨405016, by decide⟩
    (prefixCache 12 27959) (prefixPartial 12 27959) = false := by
  decide +kernel

theorem node_context_12_27959_405016 : EJMOriginalGlobalDAGData.nodes 9 ⟨405016, by decide⟩ =
    .split (coordinate 12) (![⟨404962, by decide⟩,⟨404988, by decide⟩,⟨405009, by decide⟩,⟨405015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27959_405016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27959 ⟨405016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27959
    ⟨405016, by decide⟩ (by decide) (![⟨404962, by decide⟩,⟨404988, by decide⟩,⟨405009, by decide⟩,⟨405015, by decide⟩]) unmarked_context_12_27959_405016 node_context_12_27959_405016
  intro a
  fin_cases a
  · exact context_13_111836_404962
  · exact context_13_111837_404988
  · exact context_13_111838_405009
  · exact context_13_111839_405015

theorem unmarked_context_11_6989_405017 : frontier 10 ⟨405017, by decide⟩
    (prefixCache 11 6989) (prefixPartial 11 6989) = false := by
  decide +kernel

theorem node_context_11_6989_405017 : EJMOriginalGlobalDAGData.nodes 10 ⟨405017, by decide⟩ =
    .split (coordinate 11) (![⟨404798, by decide⟩,⟨404893, by decide⟩,⟨404954, by decide⟩,⟨405016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6989_405017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6989 ⟨405017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6989
    ⟨405017, by decide⟩ (by decide) (![⟨404798, by decide⟩,⟨404893, by decide⟩,⟨404954, by decide⟩,⟨405016, by decide⟩]) unmarked_context_11_6989_405017 node_context_11_6989_405017
  intro a
  fin_cases a
  · exact context_12_27956_404798
  · exact context_12_27957_404893
  · exact context_12_27958_404954
  · exact context_12_27959_405016

theorem selected_cut_15837 : selected 8 ⟨405025, by decide⟩
    (prefixPartial 13 111840) = some ⟨13, 2, 0, 405025, 111840, 445, 16384⟩ := by
  decide +kernel

theorem context_13_111840_405025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111840 ⟨405025, by decide⟩ :=
  accepted_of_selected 13 111840 ⟨405025, by decide⟩ ⟨13, 2, 0, 405025, 111840, 445, 16384⟩
    (by decide) selected_cut_15837

theorem selected_cut_15838 : selected 8 ⟨405055, by decide⟩
    (prefixPartial 13 111841) = some ⟨13, 2, 0, 405055, 111841, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_111841_405055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111841 ⟨405055, by decide⟩ :=
  accepted_of_selected 13 111841 ⟨405055, by decide⟩ ⟨13, 2, 0, 405055, 111841, 2645, 16384⟩
    (by decide) selected_cut_15838

theorem selected_cut_15839 : selected 8 ⟨405075, by decide⟩
    (prefixPartial 13 111842) = some ⟨13, 2, 0, 405075, 111842, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_111842_405075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111842 ⟨405075, by decide⟩ :=
  accepted_of_selected 13 111842 ⟨405075, by decide⟩ ⟨13, 2, 0, 405075, 111842, 1761, 16384⟩
    (by decide) selected_cut_15839

theorem selected_cut_15840 : selected 8 ⟨405080, by decide⟩
    (prefixPartial 13 111843) = some ⟨13, 2, 0, 405080, 111843, 809, 16384⟩ := by
  decide +kernel

theorem context_13_111843_405080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111843 ⟨405080, by decide⟩ :=
  accepted_of_selected 13 111843 ⟨405080, by decide⟩ ⟨13, 2, 0, 405080, 111843, 809, 16384⟩
    (by decide) selected_cut_15840

theorem unmarked_context_12_27960_405081 : frontier 9 ⟨405081, by decide⟩
    (prefixCache 12 27960) (prefixPartial 12 27960) = false := by
  decide +kernel

theorem node_context_12_27960_405081 : EJMOriginalGlobalDAGData.nodes 9 ⟨405081, by decide⟩ =
    .split (coordinate 12) (![⟨405025, by decide⟩,⟨405055, by decide⟩,⟨405075, by decide⟩,⟨405080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27960_405081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27960 ⟨405081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27960
    ⟨405081, by decide⟩ (by decide) (![⟨405025, by decide⟩,⟨405055, by decide⟩,⟨405075, by decide⟩,⟨405080, by decide⟩]) unmarked_context_12_27960_405081 node_context_12_27960_405081
  intro a
  fin_cases a
  · exact context_13_111840_405025
  · exact context_13_111841_405055
  · exact context_13_111842_405075
  · exact context_13_111843_405080

theorem selected_cut_15841 : selected 8 ⟨405087, by decide⟩
    (prefixPartial 13 111844) = some ⟨13, 2, 0, 405087, 111844, 377, 16384⟩ := by
  decide +kernel

theorem context_13_111844_405087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111844 ⟨405087, by decide⟩ :=
  accepted_of_selected 13 111844 ⟨405087, by decide⟩ ⟨13, 2, 0, 405087, 111844, 377, 16384⟩
    (by decide) selected_cut_15841

theorem selected_cut_15842 : selected 8 ⟨405110, by decide⟩
    (prefixPartial 13 111845) = some ⟨13, 2, 0, 405110, 111845, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_111845_405110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111845 ⟨405110, by decide⟩ :=
  accepted_of_selected 13 111845 ⟨405110, by decide⟩ ⟨13, 2, 0, 405110, 111845, 2225, 16384⟩
    (by decide) selected_cut_15842

theorem selected_cut_15843 : selected 8 ⟨405130, by decide⟩
    (prefixPartial 13 111846) = some ⟨13, 2, 0, 405130, 111846, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_111846_405130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111846 ⟨405130, by decide⟩ :=
  accepted_of_selected 13 111846 ⟨405130, by decide⟩ ⟨13, 2, 0, 405130, 111846, 1689, 16384⟩
    (by decide) selected_cut_15843

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
