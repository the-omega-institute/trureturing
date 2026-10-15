/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover413
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39747 : selected 9 ⟨1078414, by decide⟩
    (prefixPartial 12 307761) = some ⟨12, 2, 0, 1078414, 307761, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_307761_1078414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307761 ⟨1078414, by decide⟩ :=
  accepted_of_selected 12 307761 ⟨1078414, by decide⟩ ⟨12, 2, 0, 1078414, 307761, 2857, 65536⟩
    (by decide) selected_cut_39747

theorem selected_cut_39748 : selected 9 ⟨1078465, by decide⟩
    (prefixPartial 12 307762) = some ⟨12, 2, 0, 1078465, 307762, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_307762_1078465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307762 ⟨1078465, by decide⟩ :=
  accepted_of_selected 12 307762 ⟨1078465, by decide⟩ ⟨12, 2, 0, 1078465, 307762, 2605, 65536⟩
    (by decide) selected_cut_39748

theorem selected_cut_39749 : selected 9 ⟨1078516, by decide⟩
    (prefixPartial 12 307763) = some ⟨12, 2, 0, 1078516, 307763, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_307763_1078516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307763 ⟨1078516, by decide⟩ :=
  accepted_of_selected 12 307763 ⟨1078516, by decide⟩ ⟨12, 2, 0, 1078516, 307763, 2697, 65536⟩
    (by decide) selected_cut_39749

theorem unmarked_context_11_76940_1078517 : frontier 10 ⟨1078517, by decide⟩
    (prefixCache 11 76940) (prefixPartial 11 76940) = false := by
  decide +kernel

theorem node_context_11_76940_1078517 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078517, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1078414, by decide⟩,⟨1078465, by decide⟩,⟨1078516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76940_1078517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76940 ⟨1078517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76940
    ⟨1078517, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1078414, by decide⟩,⟨1078465, by decide⟩,⟨1078516, by decide⟩]) unmarked_context_11_76940_1078517 node_context_11_76940_1078517
  intro a
  fin_cases a
  · exact context_12_307760_994572
  · exact context_12_307761_1078414
  · exact context_12_307762_1078465
  · exact context_12_307763_1078516

theorem selected_cut_39750 : selected 9 ⟨1078584, by decide⟩
    (prefixPartial 12 307764) = some ⟨12, 2, 0, 1078584, 307764, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_307764_1078584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307764 ⟨1078584, by decide⟩ :=
  accepted_of_selected 12 307764 ⟨1078584, by decide⟩ ⟨12, 2, 0, 1078584, 307764, 3797, 65536⟩
    (by decide) selected_cut_39750

theorem selected_cut_39751 : selected 9 ⟨1078633, by decide⟩
    (prefixPartial 12 307765) = some ⟨12, 2, 0, 1078633, 307765, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_307765_1078633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307765 ⟨1078633, by decide⟩ :=
  accepted_of_selected 12 307765 ⟨1078633, by decide⟩ ⟨12, 2, 0, 1078633, 307765, 3449, 65536⟩
    (by decide) selected_cut_39751

theorem selected_cut_39752 : selected 9 ⟨1078678, by decide⟩
    (prefixPartial 12 307766) = some ⟨12, 2, 0, 1078678, 307766, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_307766_1078678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307766 ⟨1078678, by decide⟩ :=
  accepted_of_selected 12 307766 ⟨1078678, by decide⟩ ⟨12, 2, 0, 1078678, 307766, 3237, 65536⟩
    (by decide) selected_cut_39752

theorem selected_cut_39753 : selected 9 ⟨1078721, by decide⟩
    (prefixPartial 12 307767) = some ⟨12, 2, 0, 1078721, 307767, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_307767_1078721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307767 ⟨1078721, by decide⟩ :=
  accepted_of_selected 12 307767 ⟨1078721, by decide⟩ ⟨12, 2, 0, 1078721, 307767, 2901, 65536⟩
    (by decide) selected_cut_39753

theorem unmarked_context_11_76941_1078722 : frontier 10 ⟨1078722, by decide⟩
    (prefixCache 11 76941) (prefixPartial 11 76941) = false := by
  decide +kernel

theorem node_context_11_76941_1078722 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078722, by decide⟩ =
    .split (coordinate 11) (![⟨1078584, by decide⟩,⟨1078633, by decide⟩,⟨1078678, by decide⟩,⟨1078721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76941_1078722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76941 ⟨1078722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76941
    ⟨1078722, by decide⟩ (by decide) (![⟨1078584, by decide⟩,⟨1078633, by decide⟩,⟨1078678, by decide⟩,⟨1078721, by decide⟩]) unmarked_context_11_76941_1078722 node_context_11_76941_1078722
  intro a
  fin_cases a
  · exact context_12_307764_1078584
  · exact context_12_307765_1078633
  · exact context_12_307766_1078678
  · exact context_12_307767_1078721

theorem selected_cut_39754 : selected 9 ⟨1078769, by decide⟩
    (prefixPartial 12 307768) = some ⟨12, 2, 0, 1078769, 307768, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_307768_1078769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307768 ⟨1078769, by decide⟩ :=
  accepted_of_selected 12 307768 ⟨1078769, by decide⟩ ⟨12, 2, 0, 1078769, 307768, 2993, 65536⟩
    (by decide) selected_cut_39754

theorem selected_cut_39755 : selected 9 ⟨1078804, by decide⟩
    (prefixPartial 12 307769) = some ⟨12, 2, 0, 1078804, 307769, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_307769_1078804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307769 ⟨1078804, by decide⟩ :=
  accepted_of_selected 12 307769 ⟨1078804, by decide⟩ ⟨12, 2, 0, 1078804, 307769, 2865, 65536⟩
    (by decide) selected_cut_39755

theorem selected_cut_39756 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 307770) = some ⟨12, 1, 0, 893903, 307770, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307770_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307770 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 307770 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 307770, 1, 65536⟩
    (by decide) selected_cut_39756

theorem selected_cut_39757 : selected 9 ⟨1078842, by decide⟩
    (prefixPartial 12 307771) = some ⟨12, 2, 0, 1078842, 307771, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_307771_1078842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307771 ⟨1078842, by decide⟩ :=
  accepted_of_selected 12 307771 ⟨1078842, by decide⟩ ⟨12, 2, 0, 1078842, 307771, 2657, 65536⟩
    (by decide) selected_cut_39757

theorem unmarked_context_11_76942_1078843 : frontier 10 ⟨1078843, by decide⟩
    (prefixCache 11 76942) (prefixPartial 11 76942) = false := by
  decide +kernel

theorem node_context_11_76942_1078843 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078843, by decide⟩ =
    .split (coordinate 11) (![⟨1078769, by decide⟩,⟨1078804, by decide⟩,⟨893903, by decide⟩,⟨1078842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76942_1078843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76942 ⟨1078843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76942
    ⟨1078843, by decide⟩ (by decide) (![⟨1078769, by decide⟩,⟨1078804, by decide⟩,⟨893903, by decide⟩,⟨1078842, by decide⟩]) unmarked_context_11_76942_1078843 node_context_11_76942_1078843
  intro a
  fin_cases a
  · exact context_12_307768_1078769
  · exact context_12_307769_1078804
  · exact context_12_307770_893903
  · exact context_12_307771_1078842

theorem selected_cut_39758 : selected 9 ⟨1078907, by decide⟩
    (prefixPartial 12 307772) = some ⟨12, 2, 0, 1078907, 307772, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_307772_1078907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307772 ⟨1078907, by decide⟩ :=
  accepted_of_selected 12 307772 ⟨1078907, by decide⟩ ⟨12, 2, 0, 1078907, 307772, 3317, 65536⟩
    (by decide) selected_cut_39758

theorem selected_cut_39759 : selected 9 ⟨1078954, by decide⟩
    (prefixPartial 12 307773) = some ⟨12, 2, 0, 1078954, 307773, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_307773_1078954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307773 ⟨1078954, by decide⟩ :=
  accepted_of_selected 12 307773 ⟨1078954, by decide⟩ ⟨12, 2, 0, 1078954, 307773, 3001, 65536⟩
    (by decide) selected_cut_39759

theorem selected_cut_39760 : selected 9 ⟨1078990, by decide⟩
    (prefixPartial 12 307774) = some ⟨12, 2, 0, 1078990, 307774, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_307774_1078990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307774 ⟨1078990, by decide⟩ :=
  accepted_of_selected 12 307774 ⟨1078990, by decide⟩ ⟨12, 2, 0, 1078990, 307774, 2973, 65536⟩
    (by decide) selected_cut_39760

theorem selected_cut_39761 : selected 9 ⟨1078991, by decide⟩
    (prefixPartial 12 307775) = some ⟨12, 1, 0, 1078991, 307775, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307775_1078991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307775 ⟨1078991, by decide⟩ :=
  accepted_of_selected 12 307775 ⟨1078991, by decide⟩ ⟨12, 1, 0, 1078991, 307775, 1, 65536⟩
    (by decide) selected_cut_39761

theorem unmarked_context_11_76943_1078992 : frontier 10 ⟨1078992, by decide⟩
    (prefixCache 11 76943) (prefixPartial 11 76943) = false := by
  decide +kernel

theorem node_context_11_76943_1078992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078992, by decide⟩ =
    .split (coordinate 11) (![⟨1078907, by decide⟩,⟨1078954, by decide⟩,⟨1078990, by decide⟩,⟨1078991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76943_1078992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76943 ⟨1078992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76943
    ⟨1078992, by decide⟩ (by decide) (![⟨1078907, by decide⟩,⟨1078954, by decide⟩,⟨1078990, by decide⟩,⟨1078991, by decide⟩]) unmarked_context_11_76943_1078992 node_context_11_76943_1078992
  intro a
  fin_cases a
  · exact context_12_307772_1078907
  · exact context_12_307773_1078954
  · exact context_12_307774_1078990
  · exact context_12_307775_1078991

theorem unmarked_context_10_19235_1078993 : frontier 11 ⟨1078993, by decide⟩
    (prefixCache 10 19235) (prefixPartial 10 19235) = false := by
  decide +kernel

theorem node_context_10_19235_1078993 : EJMOriginalGlobalDAGData.nodes 11 ⟨1078993, by decide⟩ =
    .split (coordinate 10) (![⟨1078517, by decide⟩,⟨1078722, by decide⟩,⟨1078843, by decide⟩,⟨1078992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19235_1078993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19235 ⟨1078993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19235
    ⟨1078993, by decide⟩ (by decide) (![⟨1078517, by decide⟩,⟨1078722, by decide⟩,⟨1078843, by decide⟩,⟨1078992, by decide⟩]) unmarked_context_10_19235_1078993 node_context_10_19235_1078993
  intro a
  fin_cases a
  · exact context_11_76940_1078517
  · exact context_11_76941_1078722
  · exact context_11_76942_1078843
  · exact context_11_76943_1078992

theorem unmarked_context_9_4808_1078994 : frontier 12 ⟨1078994, by decide⟩
    (prefixCache 9 4808) (prefixPartial 9 4808) = false := by
  decide +kernel

theorem node_context_9_4808_1078994 : EJMOriginalGlobalDAGData.nodes 12 ⟨1078994, by decide⟩ =
    .split (coordinate 9) (![⟨1076918, by decide⟩,⟨1077721, by decide⟩,⟨1078371, by decide⟩,⟨1078993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4808_1078994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4808 ⟨1078994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4808
    ⟨1078994, by decide⟩ (by decide) (![⟨1076918, by decide⟩,⟨1077721, by decide⟩,⟨1078371, by decide⟩,⟨1078993, by decide⟩]) unmarked_context_9_4808_1078994 node_context_9_4808_1078994
  intro a
  fin_cases a
  · exact context_10_19232_1076918
  · exact context_10_19233_1077721
  · exact context_10_19234_1078371
  · exact context_10_19235_1078993

theorem selected_cut_39762 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76944) = some ⟨11, 1, 0, 907917, 76944, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76944_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76944 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76944 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76944, 1, 262144⟩
    (by decide) selected_cut_39762

theorem selected_cut_39763 : selected 9 ⟨1079038, by decide⟩
    (prefixPartial 12 307780) = some ⟨12, 2, 0, 1079038, 307780, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_307780_1079038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307780 ⟨1079038, by decide⟩ :=
  accepted_of_selected 12 307780 ⟨1079038, by decide⟩ ⟨12, 2, 0, 1079038, 307780, 3045, 65536⟩
    (by decide) selected_cut_39763

theorem selected_cut_39764 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 307781) = some ⟨12, 1, 0, 691709, 307781, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307781_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307781 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 307781 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 307781, 1, 65536⟩
    (by decide) selected_cut_39764

theorem selected_cut_39765 : selected 9 ⟨1079081, by decide⟩
    (prefixPartial 12 307782) = some ⟨12, 2, 0, 1079081, 307782, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_307782_1079081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307782 ⟨1079081, by decide⟩ :=
  accepted_of_selected 12 307782 ⟨1079081, by decide⟩ ⟨12, 2, 0, 1079081, 307782, 2717, 65536⟩
    (by decide) selected_cut_39765

theorem selected_cut_39766 : selected 9 ⟨1079124, by decide⟩
    (prefixPartial 12 307783) = some ⟨12, 2, 0, 1079124, 307783, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_307783_1079124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307783 ⟨1079124, by decide⟩ :=
  accepted_of_selected 12 307783 ⟨1079124, by decide⟩ ⟨12, 2, 0, 1079124, 307783, 2657, 65536⟩
    (by decide) selected_cut_39766

theorem unmarked_context_11_76945_1079125 : frontier 10 ⟨1079125, by decide⟩
    (prefixCache 11 76945) (prefixPartial 11 76945) = false := by
  decide +kernel

theorem node_context_11_76945_1079125 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079125, by decide⟩ =
    .split (coordinate 11) (![⟨1079038, by decide⟩,⟨691709, by decide⟩,⟨1079081, by decide⟩,⟨1079124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76945_1079125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76945 ⟨1079125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76945
    ⟨1079125, by decide⟩ (by decide) (![⟨1079038, by decide⟩,⟨691709, by decide⟩,⟨1079081, by decide⟩,⟨1079124, by decide⟩]) unmarked_context_11_76945_1079125 node_context_11_76945_1079125
  intro a
  fin_cases a
  · exact context_12_307780_1079038
  · exact context_12_307781_691709
  · exact context_12_307782_1079081
  · exact context_12_307783_1079124

theorem selected_cut_39767 : selected 9 ⟨1079166, by decide⟩
    (prefixPartial 12 307784) = some ⟨12, 2, 0, 1079166, 307784, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_307784_1079166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307784 ⟨1079166, by decide⟩ :=
  accepted_of_selected 12 307784 ⟨1079166, by decide⟩ ⟨12, 2, 0, 1079166, 307784, 2921, 65536⟩
    (by decide) selected_cut_39767

theorem selected_cut_39768 : selected 9 ⟨1079204, by decide⟩
    (prefixPartial 12 307785) = some ⟨12, 2, 0, 1079204, 307785, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_307785_1079204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307785 ⟨1079204, by decide⟩ :=
  accepted_of_selected 12 307785 ⟨1079204, by decide⟩ ⟨12, 2, 0, 1079204, 307785, 2601, 65536⟩
    (by decide) selected_cut_39768

theorem selected_cut_39769 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 307786) = some ⟨12, 1, 0, 893903, 307786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307786_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307786 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 307786 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 307786, 1, 65536⟩
    (by decide) selected_cut_39769

theorem selected_cut_39770 : selected 9 ⟨1079241, by decide⟩
    (prefixPartial 12 307787) = some ⟨12, 2, 0, 1079241, 307787, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_307787_1079241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307787 ⟨1079241, by decide⟩ :=
  accepted_of_selected 12 307787 ⟨1079241, by decide⟩ ⟨12, 2, 0, 1079241, 307787, 2561, 65536⟩
    (by decide) selected_cut_39770

theorem unmarked_context_11_76946_1079242 : frontier 10 ⟨1079242, by decide⟩
    (prefixCache 11 76946) (prefixPartial 11 76946) = false := by
  decide +kernel

theorem node_context_11_76946_1079242 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079242, by decide⟩ =
    .split (coordinate 11) (![⟨1079166, by decide⟩,⟨1079204, by decide⟩,⟨893903, by decide⟩,⟨1079241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76946_1079242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76946 ⟨1079242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76946
    ⟨1079242, by decide⟩ (by decide) (![⟨1079166, by decide⟩,⟨1079204, by decide⟩,⟨893903, by decide⟩,⟨1079241, by decide⟩]) unmarked_context_11_76946_1079242 node_context_11_76946_1079242
  intro a
  fin_cases a
  · exact context_12_307784_1079166
  · exact context_12_307785_1079204
  · exact context_12_307786_893903
  · exact context_12_307787_1079241

theorem selected_cut_39771 : selected 9 ⟨1079300, by decide⟩
    (prefixPartial 12 307788) = some ⟨12, 2, 0, 1079300, 307788, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_307788_1079300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307788 ⟨1079300, by decide⟩ :=
  accepted_of_selected 12 307788 ⟨1079300, by decide⟩ ⟨12, 2, 0, 1079300, 307788, 3217, 65536⟩
    (by decide) selected_cut_39771

theorem selected_cut_39772 : selected 9 ⟨1079338, by decide⟩
    (prefixPartial 12 307789) = some ⟨12, 2, 0, 1079338, 307789, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_307789_1079338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307789 ⟨1079338, by decide⟩ :=
  accepted_of_selected 12 307789 ⟨1079338, by decide⟩ ⟨12, 2, 0, 1079338, 307789, 2925, 65536⟩
    (by decide) selected_cut_39772

theorem selected_cut_39773 : selected 9 ⟨1079379, by decide⟩
    (prefixPartial 12 307790) = some ⟨12, 2, 0, 1079379, 307790, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_307790_1079379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307790 ⟨1079379, by decide⟩ :=
  accepted_of_selected 12 307790 ⟨1079379, by decide⟩ ⟨12, 2, 0, 1079379, 307790, 2953, 65536⟩
    (by decide) selected_cut_39773

theorem selected_cut_39774 : selected 9 ⟨1079422, by decide⟩
    (prefixPartial 12 307791) = some ⟨12, 2, 0, 1079422, 307791, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_307791_1079422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307791 ⟨1079422, by decide⟩ :=
  accepted_of_selected 12 307791 ⟨1079422, by decide⟩ ⟨12, 2, 0, 1079422, 307791, 2529, 65536⟩
    (by decide) selected_cut_39774

theorem unmarked_context_11_76947_1079423 : frontier 10 ⟨1079423, by decide⟩
    (prefixCache 11 76947) (prefixPartial 11 76947) = false := by
  decide +kernel

theorem node_context_11_76947_1079423 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079423, by decide⟩ =
    .split (coordinate 11) (![⟨1079300, by decide⟩,⟨1079338, by decide⟩,⟨1079379, by decide⟩,⟨1079422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76947_1079423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76947 ⟨1079423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76947
    ⟨1079423, by decide⟩ (by decide) (![⟨1079300, by decide⟩,⟨1079338, by decide⟩,⟨1079379, by decide⟩,⟨1079422, by decide⟩]) unmarked_context_11_76947_1079423 node_context_11_76947_1079423
  intro a
  fin_cases a
  · exact context_12_307788_1079300
  · exact context_12_307789_1079338
  · exact context_12_307790_1079379
  · exact context_12_307791_1079422

theorem unmarked_context_10_19236_1079424 : frontier 11 ⟨1079424, by decide⟩
    (prefixCache 10 19236) (prefixPartial 10 19236) = false := by
  decide +kernel

theorem node_context_10_19236_1079424 : EJMOriginalGlobalDAGData.nodes 11 ⟨1079424, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1079125, by decide⟩,⟨1079242, by decide⟩,⟨1079423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19236_1079424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19236 ⟨1079424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19236
    ⟨1079424, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1079125, by decide⟩,⟨1079242, by decide⟩,⟨1079423, by decide⟩]) unmarked_context_10_19236_1079424 node_context_10_19236_1079424
  intro a
  fin_cases a
  · exact context_11_76944_907917
  · exact context_11_76945_1079125
  · exact context_11_76946_1079242
  · exact context_11_76947_1079423

theorem selected_cut_39775 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19237) = some ⟨10, 1, 0, 893098, 19237, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19237_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19237 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19237 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19237, 1, 1048576⟩
    (by decide) selected_cut_39775

theorem selected_cut_39776 : selected 9 ⟨1079444, by decide⟩
    (prefixPartial 12 307808) = some ⟨12, 2, 0, 1079444, 307808, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_307808_1079444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307808 ⟨1079444, by decide⟩ :=
  accepted_of_selected 12 307808 ⟨1079444, by decide⟩ ⟨12, 2, 0, 1079444, 307808, 1913, 65536⟩
    (by decide) selected_cut_39776

theorem selected_cut_39777 : selected 9 ⟨1079474, by decide⟩
    (prefixPartial 12 307809) = some ⟨12, 2, 0, 1079474, 307809, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_307809_1079474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307809 ⟨1079474, by decide⟩ :=
  accepted_of_selected 12 307809 ⟨1079474, by decide⟩ ⟨12, 2, 0, 1079474, 307809, 2093, 65536⟩
    (by decide) selected_cut_39777

theorem selected_cut_39778 : selected 9 ⟨1079503, by decide⟩
    (prefixPartial 12 307810) = some ⟨12, 2, 0, 1079503, 307810, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_307810_1079503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307810 ⟨1079503, by decide⟩ :=
  accepted_of_selected 12 307810 ⟨1079503, by decide⟩ ⟨12, 2, 0, 1079503, 307810, 1853, 65536⟩
    (by decide) selected_cut_39778

theorem selected_cut_39779 : selected 9 ⟨1079531, by decide⟩
    (prefixPartial 12 307811) = some ⟨12, 2, 0, 1079531, 307811, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_307811_1079531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307811 ⟨1079531, by decide⟩ :=
  accepted_of_selected 12 307811 ⟨1079531, by decide⟩ ⟨12, 2, 0, 1079531, 307811, 1985, 65536⟩
    (by decide) selected_cut_39779

theorem unmarked_context_11_76952_1079532 : frontier 10 ⟨1079532, by decide⟩
    (prefixCache 11 76952) (prefixPartial 11 76952) = false := by
  decide +kernel

theorem node_context_11_76952_1079532 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079532, by decide⟩ =
    .split (coordinate 11) (![⟨1079444, by decide⟩,⟨1079474, by decide⟩,⟨1079503, by decide⟩,⟨1079531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76952_1079532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76952 ⟨1079532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76952
    ⟨1079532, by decide⟩ (by decide) (![⟨1079444, by decide⟩,⟨1079474, by decide⟩,⟨1079503, by decide⟩,⟨1079531, by decide⟩]) unmarked_context_11_76952_1079532 node_context_11_76952_1079532
  intro a
  fin_cases a
  · exact context_12_307808_1079444
  · exact context_12_307809_1079474
  · exact context_12_307810_1079503
  · exact context_12_307811_1079531

theorem selected_cut_39780 : selected 9 ⟨1079557, by decide⟩
    (prefixPartial 12 307812) = some ⟨12, 2, 0, 1079557, 307812, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_307812_1079557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307812 ⟨1079557, by decide⟩ :=
  accepted_of_selected 12 307812 ⟨1079557, by decide⟩ ⟨12, 2, 0, 1079557, 307812, 1957, 65536⟩
    (by decide) selected_cut_39780

theorem selected_cut_39781 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 307813) = some ⟨12, 1, 0, 691709, 307813, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307813_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307813 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 307813 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 307813, 1, 65536⟩
    (by decide) selected_cut_39781

theorem selected_cut_39782 : selected 9 ⟨1079581, by decide⟩
    (prefixPartial 12 307814) = some ⟨12, 2, 0, 1079581, 307814, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_307814_1079581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307814 ⟨1079581, by decide⟩ :=
  accepted_of_selected 12 307814 ⟨1079581, by decide⟩ ⟨12, 2, 0, 1079581, 307814, 1817, 65536⟩
    (by decide) selected_cut_39782

theorem selected_cut_39783 : selected 9 ⟨1079610, by decide⟩
    (prefixPartial 12 307815) = some ⟨12, 2, 0, 1079610, 307815, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_307815_1079610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307815 ⟨1079610, by decide⟩ :=
  accepted_of_selected 12 307815 ⟨1079610, by decide⟩ ⟨12, 2, 0, 1079610, 307815, 1901, 65536⟩
    (by decide) selected_cut_39783

theorem unmarked_context_11_76953_1079611 : frontier 10 ⟨1079611, by decide⟩
    (prefixCache 11 76953) (prefixPartial 11 76953) = false := by
  decide +kernel

theorem node_context_11_76953_1079611 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079611, by decide⟩ =
    .split (coordinate 11) (![⟨1079557, by decide⟩,⟨691709, by decide⟩,⟨1079581, by decide⟩,⟨1079610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76953_1079611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76953 ⟨1079611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76953
    ⟨1079611, by decide⟩ (by decide) (![⟨1079557, by decide⟩,⟨691709, by decide⟩,⟨1079581, by decide⟩,⟨1079610, by decide⟩]) unmarked_context_11_76953_1079611 node_context_11_76953_1079611
  intro a
  fin_cases a
  · exact context_12_307812_1079557
  · exact context_12_307813_691709
  · exact context_12_307814_1079581
  · exact context_12_307815_1079610

theorem selected_cut_39784 : selected 9 ⟨1079637, by decide⟩
    (prefixPartial 12 307816) = some ⟨12, 2, 0, 1079637, 307816, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_307816_1079637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307816 ⟨1079637, by decide⟩ :=
  accepted_of_selected 12 307816 ⟨1079637, by decide⟩ ⟨12, 2, 0, 1079637, 307816, 1989, 65536⟩
    (by decide) selected_cut_39784

theorem selected_cut_39785 : selected 9 ⟨1079667, by decide⟩
    (prefixPartial 12 307817) = some ⟨12, 2, 0, 1079667, 307817, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_307817_1079667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307817 ⟨1079667, by decide⟩ :=
  accepted_of_selected 12 307817 ⟨1079667, by decide⟩ ⟨12, 2, 0, 1079667, 307817, 2009, 65536⟩
    (by decide) selected_cut_39785

theorem selected_cut_39786 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 307818) = some ⟨12, 1, 0, 242157, 307818, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307818_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307818 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 307818 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 307818, 1, 65536⟩
    (by decide) selected_cut_39786

theorem selected_cut_39787 : selected 9 ⟨1079695, by decide⟩
    (prefixPartial 12 307819) = some ⟨12, 2, 0, 1079695, 307819, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_307819_1079695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307819 ⟨1079695, by decide⟩ :=
  accepted_of_selected 12 307819 ⟨1079695, by decide⟩ ⟨12, 2, 0, 1079695, 307819, 2009, 65536⟩
    (by decide) selected_cut_39787

theorem unmarked_context_11_76954_1079696 : frontier 10 ⟨1079696, by decide⟩
    (prefixCache 11 76954) (prefixPartial 11 76954) = false := by
  decide +kernel

theorem node_context_11_76954_1079696 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079696, by decide⟩ =
    .split (coordinate 11) (![⟨1079637, by decide⟩,⟨1079667, by decide⟩,⟨242157, by decide⟩,⟨1079695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76954_1079696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76954 ⟨1079696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76954
    ⟨1079696, by decide⟩ (by decide) (![⟨1079637, by decide⟩,⟨1079667, by decide⟩,⟨242157, by decide⟩,⟨1079695, by decide⟩]) unmarked_context_11_76954_1079696 node_context_11_76954_1079696
  intro a
  fin_cases a
  · exact context_12_307816_1079637
  · exact context_12_307817_1079667
  · exact context_12_307818_242157
  · exact context_12_307819_1079695

theorem selected_cut_39788 : selected 9 ⟨1079731, by decide⟩
    (prefixPartial 12 307820) = some ⟨12, 2, 0, 1079731, 307820, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_307820_1079731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307820 ⟨1079731, by decide⟩ :=
  accepted_of_selected 12 307820 ⟨1079731, by decide⟩ ⟨12, 2, 0, 1079731, 307820, 2113, 65536⟩
    (by decide) selected_cut_39788

theorem selected_cut_39789 : selected 9 ⟨1079764, by decide⟩
    (prefixPartial 12 307821) = some ⟨12, 2, 0, 1079764, 307821, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_307821_1079764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307821 ⟨1079764, by decide⟩ :=
  accepted_of_selected 12 307821 ⟨1079764, by decide⟩ ⟨12, 2, 0, 1079764, 307821, 2133, 65536⟩
    (by decide) selected_cut_39789

theorem selected_cut_39790 : selected 9 ⟨1079792, by decide⟩
    (prefixPartial 12 307822) = some ⟨12, 2, 0, 1079792, 307822, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_307822_1079792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307822 ⟨1079792, by decide⟩ :=
  accepted_of_selected 12 307822 ⟨1079792, by decide⟩ ⟨12, 2, 0, 1079792, 307822, 1849, 65536⟩
    (by decide) selected_cut_39790

theorem selected_cut_39791 : selected 9 ⟨1079823, by decide⟩
    (prefixPartial 12 307823) = some ⟨12, 2, 0, 1079823, 307823, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_307823_1079823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307823 ⟨1079823, by decide⟩ :=
  accepted_of_selected 12 307823 ⟨1079823, by decide⟩ ⟨12, 2, 0, 1079823, 307823, 1833, 65536⟩
    (by decide) selected_cut_39791

theorem unmarked_context_11_76955_1079824 : frontier 10 ⟨1079824, by decide⟩
    (prefixCache 11 76955) (prefixPartial 11 76955) = false := by
  decide +kernel

theorem node_context_11_76955_1079824 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079824, by decide⟩ =
    .split (coordinate 11) (![⟨1079731, by decide⟩,⟨1079764, by decide⟩,⟨1079792, by decide⟩,⟨1079823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76955_1079824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76955 ⟨1079824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76955
    ⟨1079824, by decide⟩ (by decide) (![⟨1079731, by decide⟩,⟨1079764, by decide⟩,⟨1079792, by decide⟩,⟨1079823, by decide⟩]) unmarked_context_11_76955_1079824 node_context_11_76955_1079824
  intro a
  fin_cases a
  · exact context_12_307820_1079731
  · exact context_12_307821_1079764
  · exact context_12_307822_1079792
  · exact context_12_307823_1079823

theorem unmarked_context_10_19238_1079825 : frontier 11 ⟨1079825, by decide⟩
    (prefixCache 10 19238) (prefixPartial 10 19238) = false := by
  decide +kernel

theorem node_context_10_19238_1079825 : EJMOriginalGlobalDAGData.nodes 11 ⟨1079825, by decide⟩ =
    .split (coordinate 10) (![⟨1079532, by decide⟩,⟨1079611, by decide⟩,⟨1079696, by decide⟩,⟨1079824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19238_1079825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19238 ⟨1079825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19238
    ⟨1079825, by decide⟩ (by decide) (![⟨1079532, by decide⟩,⟨1079611, by decide⟩,⟨1079696, by decide⟩,⟨1079824, by decide⟩]) unmarked_context_10_19238_1079825 node_context_10_19238_1079825
  intro a
  fin_cases a
  · exact context_11_76952_1079532
  · exact context_11_76953_1079611
  · exact context_11_76954_1079696
  · exact context_11_76955_1079824

theorem selected_cut_39792 : selected 9 ⟨1079840, by decide⟩
    (prefixPartial 12 307824) = some ⟨12, 2, 0, 1079840, 307824, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_307824_1079840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307824 ⟨1079840, by decide⟩ :=
  accepted_of_selected 12 307824 ⟨1079840, by decide⟩ ⟨12, 2, 0, 1079840, 307824, 1561, 65536⟩
    (by decide) selected_cut_39792

theorem selected_cut_39793 : selected 9 ⟨1079863, by decide⟩
    (prefixPartial 12 307825) = some ⟨12, 2, 0, 1079863, 307825, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_307825_1079863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307825 ⟨1079863, by decide⟩ :=
  accepted_of_selected 12 307825 ⟨1079863, by decide⟩ ⟨12, 2, 0, 1079863, 307825, 1673, 65536⟩
    (by decide) selected_cut_39793

theorem selected_cut_39794 : selected 9 ⟨1079885, by decide⟩
    (prefixPartial 12 307826) = some ⟨12, 2, 0, 1079885, 307826, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_307826_1079885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307826 ⟨1079885, by decide⟩ :=
  accepted_of_selected 12 307826 ⟨1079885, by decide⟩ ⟨12, 2, 0, 1079885, 307826, 1477, 65536⟩
    (by decide) selected_cut_39794

theorem selected_cut_39795 : selected 9 ⟨1079912, by decide⟩
    (prefixPartial 12 307827) = some ⟨12, 2, 0, 1079912, 307827, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_307827_1079912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307827 ⟨1079912, by decide⟩ :=
  accepted_of_selected 12 307827 ⟨1079912, by decide⟩ ⟨12, 2, 0, 1079912, 307827, 1569, 65536⟩
    (by decide) selected_cut_39795

theorem unmarked_context_11_76956_1079913 : frontier 10 ⟨1079913, by decide⟩
    (prefixCache 11 76956) (prefixPartial 11 76956) = false := by
  decide +kernel

theorem node_context_11_76956_1079913 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079913, by decide⟩ =
    .split (coordinate 11) (![⟨1079840, by decide⟩,⟨1079863, by decide⟩,⟨1079885, by decide⟩,⟨1079912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76956_1079913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76956 ⟨1079913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76956
    ⟨1079913, by decide⟩ (by decide) (![⟨1079840, by decide⟩,⟨1079863, by decide⟩,⟨1079885, by decide⟩,⟨1079912, by decide⟩]) unmarked_context_11_76956_1079913 node_context_11_76956_1079913
  intro a
  fin_cases a
  · exact context_12_307824_1079840
  · exact context_12_307825_1079863
  · exact context_12_307826_1079885
  · exact context_12_307827_1079912

theorem selected_cut_39796 : selected 9 ⟨1079936, by decide⟩
    (prefixPartial 12 307828) = some ⟨12, 2, 0, 1079936, 307828, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_307828_1079936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307828 ⟨1079936, by decide⟩ :=
  accepted_of_selected 12 307828 ⟨1079936, by decide⟩ ⟨12, 2, 0, 1079936, 307828, 1721, 65536⟩
    (by decide) selected_cut_39796

theorem selected_cut_39797 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 307829) = some ⟨12, 1, 0, 691709, 307829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307829_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307829 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 307829 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 307829, 1, 65536⟩
    (by decide) selected_cut_39797

theorem selected_cut_39798 : selected 9 ⟨1079958, by decide⟩
    (prefixPartial 12 307830) = some ⟨12, 2, 0, 1079958, 307830, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_307830_1079958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307830 ⟨1079958, by decide⟩ :=
  accepted_of_selected 12 307830 ⟨1079958, by decide⟩ ⟨12, 2, 0, 1079958, 307830, 1605, 65536⟩
    (by decide) selected_cut_39798

theorem selected_cut_39799 : selected 9 ⟨1079986, by decide⟩
    (prefixPartial 12 307831) = some ⟨12, 2, 0, 1079986, 307831, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_307831_1079986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307831 ⟨1079986, by decide⟩ :=
  accepted_of_selected 12 307831 ⟨1079986, by decide⟩ ⟨12, 2, 0, 1079986, 307831, 1689, 65536⟩
    (by decide) selected_cut_39799

theorem unmarked_context_11_76957_1079987 : frontier 10 ⟨1079987, by decide⟩
    (prefixCache 11 76957) (prefixPartial 11 76957) = false := by
  decide +kernel

theorem node_context_11_76957_1079987 : EJMOriginalGlobalDAGData.nodes 10 ⟨1079987, by decide⟩ =
    .split (coordinate 11) (![⟨1079936, by decide⟩,⟨691709, by decide⟩,⟨1079958, by decide⟩,⟨1079986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76957_1079987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76957 ⟨1079987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76957
    ⟨1079987, by decide⟩ (by decide) (![⟨1079936, by decide⟩,⟨691709, by decide⟩,⟨1079958, by decide⟩,⟨1079986, by decide⟩]) unmarked_context_11_76957_1079987 node_context_11_76957_1079987
  intro a
  fin_cases a
  · exact context_12_307828_1079936
  · exact context_12_307829_691709
  · exact context_12_307830_1079958
  · exact context_12_307831_1079986

theorem selected_cut_39800 : selected 9 ⟨1080008, by decide⟩
    (prefixPartial 12 307832) = some ⟨12, 2, 0, 1080008, 307832, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_307832_1080008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307832 ⟨1080008, by decide⟩ :=
  accepted_of_selected 12 307832 ⟨1080008, by decide⟩ ⟨12, 2, 0, 1080008, 307832, 1629, 65536⟩
    (by decide) selected_cut_39800

theorem selected_cut_39801 : selected 9 ⟨1080030, by decide⟩
    (prefixPartial 12 307833) = some ⟨12, 2, 0, 1080030, 307833, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_307833_1080030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307833 ⟨1080030, by decide⟩ :=
  accepted_of_selected 12 307833 ⟨1080030, by decide⟩ ⟨12, 2, 0, 1080030, 307833, 1581, 65536⟩
    (by decide) selected_cut_39801

theorem selected_cut_39802 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 307834) = some ⟨12, 1, 0, 893903, 307834, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307834_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307834 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 307834 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 307834, 1, 65536⟩
    (by decide) selected_cut_39802

theorem selected_cut_39803 : selected 9 ⟨1080055, by decide⟩
    (prefixPartial 12 307835) = some ⟨12, 2, 0, 1080055, 307835, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_307835_1080055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307835 ⟨1080055, by decide⟩ :=
  accepted_of_selected 12 307835 ⟨1080055, by decide⟩ ⟨12, 2, 0, 1080055, 307835, 1649, 65536⟩
    (by decide) selected_cut_39803

theorem unmarked_context_11_76958_1080056 : frontier 10 ⟨1080056, by decide⟩
    (prefixCache 11 76958) (prefixPartial 11 76958) = false := by
  decide +kernel

theorem node_context_11_76958_1080056 : EJMOriginalGlobalDAGData.nodes 10 ⟨1080056, by decide⟩ =
    .split (coordinate 11) (![⟨1080008, by decide⟩,⟨1080030, by decide⟩,⟨893903, by decide⟩,⟨1080055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76958_1080056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76958 ⟨1080056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76958
    ⟨1080056, by decide⟩ (by decide) (![⟨1080008, by decide⟩,⟨1080030, by decide⟩,⟨893903, by decide⟩,⟨1080055, by decide⟩]) unmarked_context_11_76958_1080056 node_context_11_76958_1080056
  intro a
  fin_cases a
  · exact context_12_307832_1080008
  · exact context_12_307833_1080030
  · exact context_12_307834_893903
  · exact context_12_307835_1080055

theorem selected_cut_39804 : selected 9 ⟨1080082, by decide⟩
    (prefixPartial 12 307836) = some ⟨12, 2, 0, 1080082, 307836, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_307836_1080082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307836 ⟨1080082, by decide⟩ :=
  accepted_of_selected 12 307836 ⟨1080082, by decide⟩ ⟨12, 2, 0, 1080082, 307836, 1685, 65536⟩
    (by decide) selected_cut_39804

theorem selected_cut_39805 : selected 9 ⟨1080114, by decide⟩
    (prefixPartial 12 307837) = some ⟨12, 2, 0, 1080114, 307837, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_307837_1080114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307837 ⟨1080114, by decide⟩ :=
  accepted_of_selected 12 307837 ⟨1080114, by decide⟩ ⟨12, 2, 0, 1080114, 307837, 1765, 65536⟩
    (by decide) selected_cut_39805

theorem selected_cut_39806 : selected 9 ⟨1080138, by decide⟩
    (prefixPartial 12 307838) = some ⟨12, 2, 0, 1080138, 307838, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_307838_1080138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307838 ⟨1080138, by decide⟩ :=
  accepted_of_selected 12 307838 ⟨1080138, by decide⟩ ⟨12, 2, 0, 1080138, 307838, 1493, 65536⟩
    (by decide) selected_cut_39806

theorem selected_cut_39807 : selected 9 ⟨1080158, by decide⟩
    (prefixPartial 12 307839) = some ⟨12, 2, 0, 1080158, 307839, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_307839_1080158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307839 ⟨1080158, by decide⟩ :=
  accepted_of_selected 12 307839 ⟨1080158, by decide⟩ ⟨12, 2, 0, 1080158, 307839, 1469, 65536⟩
    (by decide) selected_cut_39807

theorem unmarked_context_11_76959_1080159 : frontier 10 ⟨1080159, by decide⟩
    (prefixCache 11 76959) (prefixPartial 11 76959) = false := by
  decide +kernel

theorem node_context_11_76959_1080159 : EJMOriginalGlobalDAGData.nodes 10 ⟨1080159, by decide⟩ =
    .split (coordinate 11) (![⟨1080082, by decide⟩,⟨1080114, by decide⟩,⟨1080138, by decide⟩,⟨1080158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76959_1080159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76959 ⟨1080159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76959
    ⟨1080159, by decide⟩ (by decide) (![⟨1080082, by decide⟩,⟨1080114, by decide⟩,⟨1080138, by decide⟩,⟨1080158, by decide⟩]) unmarked_context_11_76959_1080159 node_context_11_76959_1080159
  intro a
  fin_cases a
  · exact context_12_307836_1080082
  · exact context_12_307837_1080114
  · exact context_12_307838_1080138
  · exact context_12_307839_1080158

theorem unmarked_context_10_19239_1080160 : frontier 11 ⟨1080160, by decide⟩
    (prefixCache 10 19239) (prefixPartial 10 19239) = false := by
  decide +kernel

theorem node_context_10_19239_1080160 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080160, by decide⟩ =
    .split (coordinate 10) (![⟨1079913, by decide⟩,⟨1079987, by decide⟩,⟨1080056, by decide⟩,⟨1080159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19239_1080160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19239 ⟨1080160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19239
    ⟨1080160, by decide⟩ (by decide) (![⟨1079913, by decide⟩,⟨1079987, by decide⟩,⟨1080056, by decide⟩,⟨1080159, by decide⟩]) unmarked_context_10_19239_1080160 node_context_10_19239_1080160
  intro a
  fin_cases a
  · exact context_11_76956_1079913
  · exact context_11_76957_1079987
  · exact context_11_76958_1080056
  · exact context_11_76959_1080159

theorem unmarked_context_9_4809_1080161 : frontier 12 ⟨1080161, by decide⟩
    (prefixCache 9 4809) (prefixPartial 9 4809) = false := by
  decide +kernel

theorem node_context_9_4809_1080161 : EJMOriginalGlobalDAGData.nodes 12 ⟨1080161, by decide⟩ =
    .split (coordinate 9) (![⟨1079424, by decide⟩,⟨893098, by decide⟩,⟨1079825, by decide⟩,⟨1080160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4809_1080161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4809 ⟨1080161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4809
    ⟨1080161, by decide⟩ (by decide) (![⟨1079424, by decide⟩,⟨893098, by decide⟩,⟨1079825, by decide⟩,⟨1080160, by decide⟩]) unmarked_context_9_4809_1080161 node_context_9_4809_1080161
  intro a
  fin_cases a
  · exact context_10_19236_1079424
  · exact context_10_19237_893098
  · exact context_10_19238_1079825
  · exact context_10_19239_1080160

theorem selected_cut_39808 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76960) = some ⟨11, 1, 0, 907917, 76960, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76960_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76960 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76960 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76960, 1, 262144⟩
    (by decide) selected_cut_39808

theorem selected_cut_39809 : selected 9 ⟨1080181, by decide⟩
    (prefixPartial 12 307844) = some ⟨12, 2, 0, 1080181, 307844, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_307844_1080181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307844 ⟨1080181, by decide⟩ :=
  accepted_of_selected 12 307844 ⟨1080181, by decide⟩ ⟨12, 2, 0, 1080181, 307844, 1469, 65536⟩
    (by decide) selected_cut_39809

theorem selected_cut_39810 : selected 9 ⟨1080204, by decide⟩
    (prefixPartial 12 307845) = some ⟨12, 2, 0, 1080204, 307845, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_307845_1080204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307845 ⟨1080204, by decide⟩ :=
  accepted_of_selected 12 307845 ⟨1080204, by decide⟩ ⟨12, 2, 0, 1080204, 307845, 1421, 65536⟩
    (by decide) selected_cut_39810

theorem selected_cut_39811 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 307846) = some ⟨12, 1, 0, 984676, 307846, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307846_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307846 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 307846 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 307846, 1, 65536⟩
    (by decide) selected_cut_39811

theorem selected_cut_39812 : selected 9 ⟨1080222, by decide⟩
    (prefixPartial 12 307847) = some ⟨12, 2, 0, 1080222, 307847, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_307847_1080222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307847 ⟨1080222, by decide⟩ :=
  accepted_of_selected 12 307847 ⟨1080222, by decide⟩ ⟨12, 2, 0, 1080222, 307847, 1373, 65536⟩
    (by decide) selected_cut_39812

theorem unmarked_context_11_76961_1080223 : frontier 10 ⟨1080223, by decide⟩
    (prefixCache 11 76961) (prefixPartial 11 76961) = false := by
  decide +kernel

theorem node_context_11_76961_1080223 : EJMOriginalGlobalDAGData.nodes 10 ⟨1080223, by decide⟩ =
    .split (coordinate 11) (![⟨1080181, by decide⟩,⟨1080204, by decide⟩,⟨984676, by decide⟩,⟨1080222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76961_1080223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76961 ⟨1080223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76961
    ⟨1080223, by decide⟩ (by decide) (![⟨1080181, by decide⟩,⟨1080204, by decide⟩,⟨984676, by decide⟩,⟨1080222, by decide⟩]) unmarked_context_11_76961_1080223 node_context_11_76961_1080223
  intro a
  fin_cases a
  · exact context_12_307844_1080181
  · exact context_12_307845_1080204
  · exact context_12_307846_984676
  · exact context_12_307847_1080222

theorem selected_cut_39813 : selected 10 ⟨1080283, by decide⟩
    (prefixPartial 11 76962) = some ⟨11, 2, 0, 1080283, 76962, 3817, 262144⟩ := by
  decide +kernel

theorem context_11_76962_1080283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76962 ⟨1080283, by decide⟩ :=
  accepted_of_selected 11 76962 ⟨1080283, by decide⟩ ⟨11, 2, 0, 1080283, 76962, 3817, 262144⟩
    (by decide) selected_cut_39813

theorem selected_cut_39814 : selected 9 ⟨1080308, by decide⟩
    (prefixPartial 12 307852) = some ⟨12, 2, 0, 1080308, 307852, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_307852_1080308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307852 ⟨1080308, by decide⟩ :=
  accepted_of_selected 12 307852 ⟨1080308, by decide⟩ ⟨12, 2, 0, 1080308, 307852, 1577, 65536⟩
    (by decide) selected_cut_39814

theorem selected_cut_39815 : selected 9 ⟨1080333, by decide⟩
    (prefixPartial 12 307853) = some ⟨12, 2, 0, 1080333, 307853, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_307853_1080333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307853 ⟨1080333, by decide⟩ :=
  accepted_of_selected 12 307853 ⟨1080333, by decide⟩ ⟨12, 2, 0, 1080333, 307853, 1505, 65536⟩
    (by decide) selected_cut_39815

theorem selected_cut_39816 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 307854) = some ⟨12, 1, 0, 984676, 307854, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307854_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307854 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 307854 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 307854, 1, 65536⟩
    (by decide) selected_cut_39816

theorem selected_cut_39817 : selected 9 ⟨1080355, by decide⟩
    (prefixPartial 12 307855) = some ⟨12, 2, 0, 1080355, 307855, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_307855_1080355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307855 ⟨1080355, by decide⟩ :=
  accepted_of_selected 12 307855 ⟨1080355, by decide⟩ ⟨12, 2, 0, 1080355, 307855, 1253, 65536⟩
    (by decide) selected_cut_39817

theorem unmarked_context_11_76963_1080356 : frontier 10 ⟨1080356, by decide⟩
    (prefixCache 11 76963) (prefixPartial 11 76963) = false := by
  decide +kernel

theorem node_context_11_76963_1080356 : EJMOriginalGlobalDAGData.nodes 10 ⟨1080356, by decide⟩ =
    .split (coordinate 11) (![⟨1080308, by decide⟩,⟨1080333, by decide⟩,⟨984676, by decide⟩,⟨1080355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76963_1080356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76963 ⟨1080356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76963
    ⟨1080356, by decide⟩ (by decide) (![⟨1080308, by decide⟩,⟨1080333, by decide⟩,⟨984676, by decide⟩,⟨1080355, by decide⟩]) unmarked_context_11_76963_1080356 node_context_11_76963_1080356
  intro a
  fin_cases a
  · exact context_12_307852_1080308
  · exact context_12_307853_1080333
  · exact context_12_307854_984676
  · exact context_12_307855_1080355

theorem unmarked_context_10_19240_1080357 : frontier 11 ⟨1080357, by decide⟩
    (prefixCache 10 19240) (prefixPartial 10 19240) = false := by
  decide +kernel

theorem node_context_10_19240_1080357 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080357, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1080223, by decide⟩,⟨1080283, by decide⟩,⟨1080356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19240_1080357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19240 ⟨1080357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19240
    ⟨1080357, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1080223, by decide⟩,⟨1080283, by decide⟩,⟨1080356, by decide⟩]) unmarked_context_10_19240_1080357 node_context_10_19240_1080357
  intro a
  fin_cases a
  · exact context_11_76960_907917
  · exact context_11_76961_1080223
  · exact context_11_76962_1080283
  · exact context_11_76963_1080356

theorem selected_cut_39818 : selected 10 ⟨1080419, by decide⟩
    (prefixPartial 11 76964) = some ⟨11, 2, 0, 1080419, 76964, 3669, 262144⟩ := by
  decide +kernel

theorem context_11_76964_1080419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76964 ⟨1080419, by decide⟩ :=
  accepted_of_selected 11 76964 ⟨1080419, by decide⟩ ⟨11, 2, 0, 1080419, 76964, 3669, 262144⟩
    (by decide) selected_cut_39818

theorem selected_cut_39819 : selected 10 ⟨1080453, by decide⟩
    (prefixPartial 11 76965) = some ⟨11, 2, 0, 1080453, 76965, 2373, 262144⟩ := by
  decide +kernel

theorem context_11_76965_1080453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76965 ⟨1080453, by decide⟩ :=
  accepted_of_selected 11 76965 ⟨1080453, by decide⟩ ⟨11, 2, 0, 1080453, 76965, 2373, 262144⟩
    (by decide) selected_cut_39819

theorem selected_cut_39820 : selected 10 ⟨1080497, by decide⟩
    (prefixPartial 11 76966) = some ⟨11, 2, 0, 1080497, 76966, 2941, 262144⟩ := by
  decide +kernel

theorem context_11_76966_1080497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76966 ⟨1080497, by decide⟩ :=
  accepted_of_selected 11 76966 ⟨1080497, by decide⟩ ⟨11, 2, 0, 1080497, 76966, 2941, 262144⟩
    (by decide) selected_cut_39820

theorem selected_cut_39821 : selected 10 ⟨1080552, by decide⟩
    (prefixPartial 11 76967) = some ⟨11, 2, 0, 1080552, 76967, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_76967_1080552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76967 ⟨1080552, by decide⟩ :=
  accepted_of_selected 11 76967 ⟨1080552, by decide⟩ ⟨11, 2, 0, 1080552, 76967, 3313, 262144⟩
    (by decide) selected_cut_39821

theorem unmarked_context_10_19241_1080553 : frontier 11 ⟨1080553, by decide⟩
    (prefixCache 10 19241) (prefixPartial 10 19241) = false := by
  decide +kernel

theorem node_context_10_19241_1080553 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080553, by decide⟩ =
    .split (coordinate 10) (![⟨1080419, by decide⟩,⟨1080453, by decide⟩,⟨1080497, by decide⟩,⟨1080552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19241_1080553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19241 ⟨1080553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19241
    ⟨1080553, by decide⟩ (by decide) (![⟨1080419, by decide⟩,⟨1080453, by decide⟩,⟨1080497, by decide⟩,⟨1080552, by decide⟩]) unmarked_context_10_19241_1080553 node_context_10_19241_1080553
  intro a
  fin_cases a
  · exact context_11_76964_1080419
  · exact context_11_76965_1080453
  · exact context_11_76966_1080497
  · exact context_11_76967_1080552

theorem selected_cut_39822 : selected 10 ⟨1080582, by decide⟩
    (prefixPartial 11 76968) = some ⟨11, 2, 0, 1080582, 76968, 2537, 262144⟩ := by
  decide +kernel

theorem context_11_76968_1080582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76968 ⟨1080582, by decide⟩ :=
  accepted_of_selected 11 76968 ⟨1080582, by decide⟩ ⟨11, 2, 0, 1080582, 76968, 2537, 262144⟩
    (by decide) selected_cut_39822

theorem selected_cut_39823 : selected 10 ⟨1080617, by decide⟩
    (prefixPartial 11 76969) = some ⟨11, 2, 0, 1080617, 76969, 2561, 262144⟩ := by
  decide +kernel

theorem context_11_76969_1080617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76969 ⟨1080617, by decide⟩ :=
  accepted_of_selected 11 76969 ⟨1080617, by decide⟩ ⟨11, 2, 0, 1080617, 76969, 2561, 262144⟩
    (by decide) selected_cut_39823

theorem selected_cut_39824 : selected 10 ⟨1080618, by decide⟩
    (prefixPartial 11 76970) = some ⟨11, 2, 0, 1080618, 76970, 5, 262144⟩ := by
  decide +kernel

theorem context_11_76970_1080618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76970 ⟨1080618, by decide⟩ :=
  accepted_of_selected 11 76970 ⟨1080618, by decide⟩ ⟨11, 2, 0, 1080618, 76970, 5, 262144⟩
    (by decide) selected_cut_39824

theorem selected_cut_39825 : selected 10 ⟨1080644, by decide⟩
    (prefixPartial 11 76971) = some ⟨11, 2, 0, 1080644, 76971, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_76971_1080644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76971 ⟨1080644, by decide⟩ :=
  accepted_of_selected 11 76971 ⟨1080644, by decide⟩ ⟨11, 2, 0, 1080644, 76971, 2405, 262144⟩
    (by decide) selected_cut_39825

theorem unmarked_context_10_19242_1080645 : frontier 11 ⟨1080645, by decide⟩
    (prefixCache 10 19242) (prefixPartial 10 19242) = false := by
  decide +kernel

theorem node_context_10_19242_1080645 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080645, by decide⟩ =
    .split (coordinate 10) (![⟨1080582, by decide⟩,⟨1080617, by decide⟩,⟨1080618, by decide⟩,⟨1080644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19242_1080645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19242 ⟨1080645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19242
    ⟨1080645, by decide⟩ (by decide) (![⟨1080582, by decide⟩,⟨1080617, by decide⟩,⟨1080618, by decide⟩,⟨1080644, by decide⟩]) unmarked_context_10_19242_1080645 node_context_10_19242_1080645
  intro a
  fin_cases a
  · exact context_11_76968_1080582
  · exact context_11_76969_1080617
  · exact context_11_76970_1080618
  · exact context_11_76971_1080644

theorem selected_cut_39826 : selected 10 ⟨1080675, by decide⟩
    (prefixPartial 11 76972) = some ⟨11, 2, 0, 1080675, 76972, 2065, 262144⟩ := by
  decide +kernel

theorem context_11_76972_1080675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76972 ⟨1080675, by decide⟩ :=
  accepted_of_selected 11 76972 ⟨1080675, by decide⟩ ⟨11, 2, 0, 1080675, 76972, 2065, 262144⟩
    (by decide) selected_cut_39826

theorem selected_cut_39827 : selected 10 ⟨1080707, by decide⟩
    (prefixPartial 11 76973) = some ⟨11, 2, 0, 1080707, 76973, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_76973_1080707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76973 ⟨1080707, by decide⟩ :=
  accepted_of_selected 11 76973 ⟨1080707, by decide⟩ ⟨11, 2, 0, 1080707, 76973, 2189, 262144⟩
    (by decide) selected_cut_39827

theorem selected_cut_39828 : selected 10 ⟨1080734, by decide⟩
    (prefixPartial 11 76974) = some ⟨11, 2, 0, 1080734, 76974, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_76974_1080734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76974 ⟨1080734, by decide⟩ :=
  accepted_of_selected 11 76974 ⟨1080734, by decide⟩ ⟨11, 2, 0, 1080734, 76974, 1821, 262144⟩
    (by decide) selected_cut_39828

theorem selected_cut_39829 : selected 10 ⟨1080753, by decide⟩
    (prefixPartial 11 76975) = some ⟨11, 2, 0, 1080753, 76975, 1185, 262144⟩ := by
  decide +kernel

theorem context_11_76975_1080753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76975 ⟨1080753, by decide⟩ :=
  accepted_of_selected 11 76975 ⟨1080753, by decide⟩ ⟨11, 2, 0, 1080753, 76975, 1185, 262144⟩
    (by decide) selected_cut_39829

theorem unmarked_context_10_19243_1080754 : frontier 11 ⟨1080754, by decide⟩
    (prefixCache 10 19243) (prefixPartial 10 19243) = false := by
  decide +kernel

theorem node_context_10_19243_1080754 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080754, by decide⟩ =
    .split (coordinate 10) (![⟨1080675, by decide⟩,⟨1080707, by decide⟩,⟨1080734, by decide⟩,⟨1080753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19243_1080754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19243 ⟨1080754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19243
    ⟨1080754, by decide⟩ (by decide) (![⟨1080675, by decide⟩,⟨1080707, by decide⟩,⟨1080734, by decide⟩,⟨1080753, by decide⟩]) unmarked_context_10_19243_1080754 node_context_10_19243_1080754
  intro a
  fin_cases a
  · exact context_11_76972_1080675
  · exact context_11_76973_1080707
  · exact context_11_76974_1080734
  · exact context_11_76975_1080753

theorem unmarked_context_9_4810_1080755 : frontier 12 ⟨1080755, by decide⟩
    (prefixCache 9 4810) (prefixPartial 9 4810) = false := by
  decide +kernel

theorem node_context_9_4810_1080755 : EJMOriginalGlobalDAGData.nodes 12 ⟨1080755, by decide⟩ =
    .split (coordinate 9) (![⟨1080357, by decide⟩,⟨1080553, by decide⟩,⟨1080645, by decide⟩,⟨1080754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4810_1080755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4810 ⟨1080755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4810
    ⟨1080755, by decide⟩ (by decide) (![⟨1080357, by decide⟩,⟨1080553, by decide⟩,⟨1080645, by decide⟩,⟨1080754, by decide⟩]) unmarked_context_9_4810_1080755 node_context_9_4810_1080755
  intro a
  fin_cases a
  · exact context_10_19240_1080357
  · exact context_10_19241_1080553
  · exact context_10_19242_1080645
  · exact context_10_19243_1080754

theorem selected_cut_39830 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76976) = some ⟨11, 1, 0, 907917, 76976, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76976_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76976 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76976 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76976, 1, 262144⟩
    (by decide) selected_cut_39830

theorem selected_cut_39831 : selected 10 ⟨1080787, by decide⟩
    (prefixPartial 11 76977) = some ⟨11, 2, 0, 1080787, 76977, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_76977_1080787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76977 ⟨1080787, by decide⟩ :=
  accepted_of_selected 11 76977 ⟨1080787, by decide⟩ ⟨11, 2, 0, 1080787, 76977, 2357, 262144⟩
    (by decide) selected_cut_39831

theorem selected_cut_39832 : selected 10 ⟨1080805, by decide⟩
    (prefixPartial 11 76978) = some ⟨11, 2, 0, 1080805, 76978, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_76978_1080805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76978 ⟨1080805, by decide⟩ :=
  accepted_of_selected 11 76978 ⟨1080805, by decide⟩ ⟨11, 2, 0, 1080805, 76978, 1429, 262144⟩
    (by decide) selected_cut_39832

theorem selected_cut_39833 : selected 10 ⟨1080838, by decide⟩
    (prefixPartial 11 76979) = some ⟨11, 2, 0, 1080838, 76979, 1625, 262144⟩ := by
  decide +kernel

theorem context_11_76979_1080838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76979 ⟨1080838, by decide⟩ :=
  accepted_of_selected 11 76979 ⟨1080838, by decide⟩ ⟨11, 2, 0, 1080838, 76979, 1625, 262144⟩
    (by decide) selected_cut_39833

theorem unmarked_context_10_19244_1080839 : frontier 11 ⟨1080839, by decide⟩
    (prefixCache 10 19244) (prefixPartial 10 19244) = false := by
  decide +kernel

theorem node_context_10_19244_1080839 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080839, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1080787, by decide⟩,⟨1080805, by decide⟩,⟨1080838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19244_1080839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19244 ⟨1080839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19244
    ⟨1080839, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1080787, by decide⟩,⟨1080805, by decide⟩,⟨1080838, by decide⟩]) unmarked_context_10_19244_1080839 node_context_10_19244_1080839
  intro a
  fin_cases a
  · exact context_11_76976_907917
  · exact context_11_76977_1080787
  · exact context_11_76978_1080805
  · exact context_11_76979_1080838

theorem selected_cut_39834 : selected 10 ⟨1080856, by decide⟩
    (prefixPartial 11 76980) = some ⟨11, 2, 0, 1080856, 76980, 1545, 262144⟩ := by
  decide +kernel

theorem context_11_76980_1080856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76980 ⟨1080856, by decide⟩ :=
  accepted_of_selected 11 76980 ⟨1080856, by decide⟩ ⟨11, 2, 0, 1080856, 76980, 1545, 262144⟩
    (by decide) selected_cut_39834

theorem selected_cut_39835 : selected 10 ⟨1080875, by decide⟩
    (prefixPartial 11 76981) = some ⟨11, 2, 0, 1080875, 76981, 1097, 262144⟩ := by
  decide +kernel

theorem context_11_76981_1080875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76981 ⟨1080875, by decide⟩ :=
  accepted_of_selected 11 76981 ⟨1080875, by decide⟩ ⟨11, 2, 0, 1080875, 76981, 1097, 262144⟩
    (by decide) selected_cut_39835

theorem selected_cut_39836 : selected 10 ⟨1080886, by decide⟩
    (prefixPartial 11 76982) = some ⟨11, 2, 0, 1080886, 76982, 873, 262144⟩ := by
  decide +kernel

theorem context_11_76982_1080886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76982 ⟨1080886, by decide⟩ :=
  accepted_of_selected 11 76982 ⟨1080886, by decide⟩ ⟨11, 2, 0, 1080886, 76982, 873, 262144⟩
    (by decide) selected_cut_39836

theorem selected_cut_39837 : selected 10 ⟨1080897, by decide⟩
    (prefixPartial 11 76983) = some ⟨11, 2, 0, 1080897, 76983, 885, 262144⟩ := by
  decide +kernel

theorem context_11_76983_1080897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76983 ⟨1080897, by decide⟩ :=
  accepted_of_selected 11 76983 ⟨1080897, by decide⟩ ⟨11, 2, 0, 1080897, 76983, 885, 262144⟩
    (by decide) selected_cut_39837

theorem unmarked_context_10_19245_1080898 : frontier 11 ⟨1080898, by decide⟩
    (prefixCache 10 19245) (prefixPartial 10 19245) = false := by
  decide +kernel

theorem node_context_10_19245_1080898 : EJMOriginalGlobalDAGData.nodes 11 ⟨1080898, by decide⟩ =
    .split (coordinate 10) (![⟨1080856, by decide⟩,⟨1080875, by decide⟩,⟨1080886, by decide⟩,⟨1080897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19245_1080898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19245 ⟨1080898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19245
    ⟨1080898, by decide⟩ (by decide) (![⟨1080856, by decide⟩,⟨1080875, by decide⟩,⟨1080886, by decide⟩,⟨1080897, by decide⟩]) unmarked_context_10_19245_1080898 node_context_10_19245_1080898
  intro a
  fin_cases a
  · exact context_11_76980_1080856
  · exact context_11_76981_1080875
  · exact context_11_76982_1080886
  · exact context_11_76983_1080897

theorem selected_cut_39838 : selected 11 ⟨1080940, by decide⟩
    (prefixPartial 10 19246) = some ⟨10, 2, 0, 1080940, 19246, 2617, 1048576⟩ := by
  decide +kernel

theorem context_10_19246_1080940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19246 ⟨1080940, by decide⟩ :=
  accepted_of_selected 10 19246 ⟨1080940, by decide⟩ ⟨10, 2, 0, 1080940, 19246, 2617, 1048576⟩
    (by decide) selected_cut_39838

theorem selected_cut_39839 : selected 11 ⟨1080972, by decide⟩
    (prefixPartial 10 19247) = some ⟨10, 2, 0, 1080972, 19247, 689, 1048576⟩ := by
  decide +kernel

theorem context_10_19247_1080972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19247 ⟨1080972, by decide⟩ :=
  accepted_of_selected 10 19247 ⟨1080972, by decide⟩ ⟨10, 2, 0, 1080972, 19247, 689, 1048576⟩
    (by decide) selected_cut_39839

theorem unmarked_context_9_4811_1080973 : frontier 12 ⟨1080973, by decide⟩
    (prefixCache 9 4811) (prefixPartial 9 4811) = false := by
  decide +kernel

theorem node_context_9_4811_1080973 : EJMOriginalGlobalDAGData.nodes 12 ⟨1080973, by decide⟩ =
    .split (coordinate 9) (![⟨1080839, by decide⟩,⟨1080898, by decide⟩,⟨1080940, by decide⟩,⟨1080972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4811_1080973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4811 ⟨1080973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4811
    ⟨1080973, by decide⟩ (by decide) (![⟨1080839, by decide⟩,⟨1080898, by decide⟩,⟨1080940, by decide⟩,⟨1080972, by decide⟩]) unmarked_context_9_4811_1080973 node_context_9_4811_1080973
  intro a
  fin_cases a
  · exact context_10_19244_1080839
  · exact context_10_19245_1080898
  · exact context_10_19246_1080940
  · exact context_10_19247_1080972

theorem unmarked_context_8_1202_1080974 : frontier 13 ⟨1080974, by decide⟩
    (prefixCache 8 1202) (prefixPartial 8 1202) = false := by
  decide +kernel

theorem node_context_8_1202_1080974 : EJMOriginalGlobalDAGData.nodes 13 ⟨1080974, by decide⟩ =
    .split (coordinate 8) (![⟨1078994, by decide⟩,⟨1080161, by decide⟩,⟨1080755, by decide⟩,⟨1080973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1202_1080974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1202 ⟨1080974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1202
    ⟨1080974, by decide⟩ (by decide) (![⟨1078994, by decide⟩,⟨1080161, by decide⟩,⟨1080755, by decide⟩,⟨1080973, by decide⟩]) unmarked_context_8_1202_1080974 node_context_8_1202_1080974
  intro a
  fin_cases a
  · exact context_9_4808_1078994
  · exact context_9_4809_1080161
  · exact context_9_4810_1080755
  · exact context_9_4811_1080973

theorem selected_cut_39840 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 76992) = some ⟨11, 1, 0, 167448, 76992, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76992_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76992 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 76992 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 76992, 1, 262144⟩
    (by decide) selected_cut_39840

theorem selected_cut_39841 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307972) = some ⟨12, 1, 0, 34034, 307972, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307972_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307972 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307972 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307972, 1, 65536⟩
    (by decide) selected_cut_39841

theorem selected_cut_39842 : selected 8 ⟨1081014, by decide⟩
    (prefixPartial 13 1231892) = some ⟨13, 2, 0, 1081014, 1231892, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_1231892_1081014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231892 ⟨1081014, by decide⟩ :=
  accepted_of_selected 13 1231892 ⟨1081014, by decide⟩ ⟨13, 2, 0, 1081014, 1231892, 2037, 16384⟩
    (by decide) selected_cut_39842

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
