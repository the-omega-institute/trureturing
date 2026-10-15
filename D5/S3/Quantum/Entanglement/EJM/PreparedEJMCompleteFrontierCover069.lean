/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover068
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06626 : selected 8 ⟨197493, by decide⟩
    (prefixPartial 13 87173) = some ⟨13, 2, 0, 197493, 87173, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_87173_197493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87173 ⟨197493, by decide⟩ :=
  accepted_of_selected 13 87173 ⟨197493, by decide⟩ ⟨13, 2, 0, 197493, 87173, 1329, 16384⟩
    (by decide) selected_cut_06626

theorem selected_cut_06627 : selected 8 ⟨197512, by decide⟩
    (prefixPartial 13 87174) = some ⟨13, 2, 0, 197512, 87174, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_87174_197512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87174 ⟨197512, by decide⟩ :=
  accepted_of_selected 13 87174 ⟨197512, by decide⟩ ⟨13, 2, 0, 197512, 87174, 1245, 16384⟩
    (by decide) selected_cut_06627

theorem selected_cut_06628 : selected 8 ⟨197519, by decide⟩
    (prefixPartial 13 87175) = some ⟨13, 2, 0, 197519, 87175, 873, 16384⟩ := by
  decide +kernel

theorem context_13_87175_197519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87175 ⟨197519, by decide⟩ :=
  accepted_of_selected 13 87175 ⟨197519, by decide⟩ ⟨13, 2, 0, 197519, 87175, 873, 16384⟩
    (by decide) selected_cut_06628

theorem unmarked_context_12_21793_197520 : frontier 9 ⟨197520, by decide⟩
    (prefixCache 12 21793) (prefixPartial 12 21793) = false := by
  decide +kernel

theorem node_context_12_21793_197520 : EJMOriginalGlobalDAGData.nodes 9 ⟨197520, by decide⟩ =
    .split (coordinate 12) (![⟨197474, by decide⟩,⟨197493, by decide⟩,⟨197512, by decide⟩,⟨197519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21793_197520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21793 ⟨197520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21793
    ⟨197520, by decide⟩ (by decide) (![⟨197474, by decide⟩,⟨197493, by decide⟩,⟨197512, by decide⟩,⟨197519, by decide⟩]) unmarked_context_12_21793_197520 node_context_12_21793_197520
  intro a
  fin_cases a
  · exact context_13_87172_197474
  · exact context_13_87173_197493
  · exact context_13_87174_197512
  · exact context_13_87175_197519

theorem selected_cut_06629 : selected 8 ⟨197550, by decide⟩
    (prefixPartial 13 87176) = some ⟨13, 2, 0, 197550, 87176, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_87176_197550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87176 ⟨197550, by decide⟩ :=
  accepted_of_selected 13 87176 ⟨197550, by decide⟩ ⟨13, 2, 0, 197550, 87176, 1805, 16384⟩
    (by decide) selected_cut_06629

theorem selected_cut_06630 : selected 8 ⟨197588, by decide⟩
    (prefixPartial 13 87177) = some ⟨13, 2, 0, 197588, 87177, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_87177_197588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87177 ⟨197588, by decide⟩ :=
  accepted_of_selected 13 87177 ⟨197588, by decide⟩ ⟨13, 2, 0, 197588, 87177, 2413, 16384⟩
    (by decide) selected_cut_06630

theorem selected_cut_06631 : selected 8 ⟨197607, by decide⟩
    (prefixPartial 13 87178) = some ⟨13, 2, 0, 197607, 87178, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_87178_197607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87178 ⟨197607, by decide⟩ :=
  accepted_of_selected 13 87178 ⟨197607, by decide⟩ ⟨13, 2, 0, 197607, 87178, 1545, 16384⟩
    (by decide) selected_cut_06631

theorem selected_cut_06632 : selected 8 ⟨197616, by decide⟩
    (prefixPartial 13 87179) = some ⟨13, 2, 0, 197616, 87179, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_87179_197616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87179 ⟨197616, by decide⟩ :=
  accepted_of_selected 13 87179 ⟨197616, by decide⟩ ⟨13, 2, 0, 197616, 87179, 1057, 16384⟩
    (by decide) selected_cut_06632

theorem unmarked_context_12_21794_197617 : frontier 9 ⟨197617, by decide⟩
    (prefixCache 12 21794) (prefixPartial 12 21794) = false := by
  decide +kernel

theorem node_context_12_21794_197617 : EJMOriginalGlobalDAGData.nodes 9 ⟨197617, by decide⟩ =
    .split (coordinate 12) (![⟨197550, by decide⟩,⟨197588, by decide⟩,⟨197607, by decide⟩,⟨197616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21794_197617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21794 ⟨197617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21794
    ⟨197617, by decide⟩ (by decide) (![⟨197550, by decide⟩,⟨197588, by decide⟩,⟨197607, by decide⟩,⟨197616, by decide⟩]) unmarked_context_12_21794_197617 node_context_12_21794_197617
  intro a
  fin_cases a
  · exact context_13_87176_197550
  · exact context_13_87177_197588
  · exact context_13_87178_197607
  · exact context_13_87179_197616

theorem selected_cut_06633 : selected 8 ⟨197638, by decide⟩
    (prefixPartial 13 87180) = some ⟨13, 2, 0, 197638, 87180, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_87180_197638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87180 ⟨197638, by decide⟩ :=
  accepted_of_selected 13 87180 ⟨197638, by decide⟩ ⟨13, 2, 0, 197638, 87180, 1565, 16384⟩
    (by decide) selected_cut_06633

theorem selected_cut_06634 : selected 8 ⟨197671, by decide⟩
    (prefixPartial 13 87181) = some ⟨13, 2, 0, 197671, 87181, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_87181_197671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87181 ⟨197671, by decide⟩ :=
  accepted_of_selected 13 87181 ⟨197671, by decide⟩ ⟨13, 2, 0, 197671, 87181, 2269, 16384⟩
    (by decide) selected_cut_06634

theorem selected_cut_06635 : selected 8 ⟨197692, by decide⟩
    (prefixPartial 13 87182) = some ⟨13, 2, 0, 197692, 87182, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_87182_197692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87182 ⟨197692, by decide⟩ :=
  accepted_of_selected 13 87182 ⟨197692, by decide⟩ ⟨13, 2, 0, 197692, 87182, 1553, 16384⟩
    (by decide) selected_cut_06635

theorem selected_cut_06636 : selected 8 ⟨197700, by decide⟩
    (prefixPartial 13 87183) = some ⟨13, 2, 0, 197700, 87183, 925, 16384⟩ := by
  decide +kernel

theorem context_13_87183_197700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87183 ⟨197700, by decide⟩ :=
  accepted_of_selected 13 87183 ⟨197700, by decide⟩ ⟨13, 2, 0, 197700, 87183, 925, 16384⟩
    (by decide) selected_cut_06636

theorem unmarked_context_12_21795_197701 : frontier 9 ⟨197701, by decide⟩
    (prefixCache 12 21795) (prefixPartial 12 21795) = false := by
  decide +kernel

theorem node_context_12_21795_197701 : EJMOriginalGlobalDAGData.nodes 9 ⟨197701, by decide⟩ =
    .split (coordinate 12) (![⟨197638, by decide⟩,⟨197671, by decide⟩,⟨197692, by decide⟩,⟨197700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21795_197701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21795 ⟨197701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21795
    ⟨197701, by decide⟩ (by decide) (![⟨197638, by decide⟩,⟨197671, by decide⟩,⟨197692, by decide⟩,⟨197700, by decide⟩]) unmarked_context_12_21795_197701 node_context_12_21795_197701
  intro a
  fin_cases a
  · exact context_13_87180_197638
  · exact context_13_87181_197671
  · exact context_13_87182_197692
  · exact context_13_87183_197700

theorem unmarked_context_11_5448_197702 : frontier 10 ⟨197702, by decide⟩
    (prefixCache 11 5448) (prefixPartial 11 5448) = false := by
  decide +kernel

theorem node_context_11_5448_197702 : EJMOriginalGlobalDAGData.nodes 10 ⟨197702, by decide⟩ =
    .split (coordinate 11) (![⟨197457, by decide⟩,⟨197520, by decide⟩,⟨197617, by decide⟩,⟨197701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5448_197702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5448 ⟨197702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5448
    ⟨197702, by decide⟩ (by decide) (![⟨197457, by decide⟩,⟨197520, by decide⟩,⟨197617, by decide⟩,⟨197701, by decide⟩]) unmarked_context_11_5448_197702 node_context_11_5448_197702
  intro a
  fin_cases a
  · exact context_12_21792_197457
  · exact context_12_21793_197520
  · exact context_12_21794_197617
  · exact context_12_21795_197701

theorem selected_cut_06637 : selected 8 ⟨197715, by decide⟩
    (prefixPartial 13 87184) = some ⟨13, 2, 0, 197715, 87184, 713, 16384⟩ := by
  decide +kernel

theorem context_13_87184_197715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87184 ⟨197715, by decide⟩ :=
  accepted_of_selected 13 87184 ⟨197715, by decide⟩ ⟨13, 2, 0, 197715, 87184, 713, 16384⟩
    (by decide) selected_cut_06637

theorem selected_cut_06638 : selected 8 ⟨197740, by decide⟩
    (prefixPartial 13 87185) = some ⟨13, 2, 0, 197740, 87185, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_87185_197740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87185 ⟨197740, by decide⟩ :=
  accepted_of_selected 13 87185 ⟨197740, by decide⟩ ⟨13, 2, 0, 197740, 87185, 1681, 16384⟩
    (by decide) selected_cut_06638

theorem selected_cut_06639 : selected 8 ⟨197760, by decide⟩
    (prefixPartial 13 87186) = some ⟨13, 2, 0, 197760, 87186, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_87186_197760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87186 ⟨197760, by decide⟩ :=
  accepted_of_selected 13 87186 ⟨197760, by decide⟩ ⟨13, 2, 0, 197760, 87186, 1269, 16384⟩
    (by decide) selected_cut_06639

theorem selected_cut_06640 : selected 8 ⟨197767, by decide⟩
    (prefixPartial 13 87187) = some ⟨13, 2, 0, 197767, 87187, 785, 16384⟩ := by
  decide +kernel

theorem context_13_87187_197767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87187 ⟨197767, by decide⟩ :=
  accepted_of_selected 13 87187 ⟨197767, by decide⟩ ⟨13, 2, 0, 197767, 87187, 785, 16384⟩
    (by decide) selected_cut_06640

theorem unmarked_context_12_21796_197768 : frontier 9 ⟨197768, by decide⟩
    (prefixCache 12 21796) (prefixPartial 12 21796) = false := by
  decide +kernel

theorem node_context_12_21796_197768 : EJMOriginalGlobalDAGData.nodes 9 ⟨197768, by decide⟩ =
    .split (coordinate 12) (![⟨197715, by decide⟩,⟨197740, by decide⟩,⟨197760, by decide⟩,⟨197767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21796_197768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21796 ⟨197768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21796
    ⟨197768, by decide⟩ (by decide) (![⟨197715, by decide⟩,⟨197740, by decide⟩,⟨197760, by decide⟩,⟨197767, by decide⟩]) unmarked_context_12_21796_197768 node_context_12_21796_197768
  intro a
  fin_cases a
  · exact context_13_87184_197715
  · exact context_13_87185_197740
  · exact context_13_87186_197760
  · exact context_13_87187_197767

theorem selected_cut_06641 : selected 8 ⟨197785, by decide⟩
    (prefixPartial 13 87188) = some ⟨13, 2, 0, 197785, 87188, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_87188_197785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87188 ⟨197785, by decide⟩ :=
  accepted_of_selected 13 87188 ⟨197785, by decide⟩ ⟨13, 2, 0, 197785, 87188, 1273, 16384⟩
    (by decide) selected_cut_06641

theorem selected_cut_06642 : selected 8 ⟨197809, by decide⟩
    (prefixPartial 13 87189) = some ⟨13, 2, 0, 197809, 87189, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_87189_197809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87189 ⟨197809, by decide⟩ :=
  accepted_of_selected 13 87189 ⟨197809, by decide⟩ ⟨13, 2, 0, 197809, 87189, 2825, 16384⟩
    (by decide) selected_cut_06642

theorem selected_cut_06643 : selected 8 ⟨197829, by decide⟩
    (prefixPartial 13 87190) = some ⟨13, 2, 0, 197829, 87190, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_87190_197829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87190 ⟨197829, by decide⟩ :=
  accepted_of_selected 13 87190 ⟨197829, by decide⟩ ⟨13, 2, 0, 197829, 87190, 2069, 16384⟩
    (by decide) selected_cut_06643

theorem selected_cut_06644 : selected 8 ⟨197836, by decide⟩
    (prefixPartial 13 87191) = some ⟨13, 2, 0, 197836, 87191, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_87191_197836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87191 ⟨197836, by decide⟩ :=
  accepted_of_selected 13 87191 ⟨197836, by decide⟩ ⟨13, 2, 0, 197836, 87191, 1109, 16384⟩
    (by decide) selected_cut_06644

theorem unmarked_context_12_21797_197837 : frontier 9 ⟨197837, by decide⟩
    (prefixCache 12 21797) (prefixPartial 12 21797) = false := by
  decide +kernel

theorem node_context_12_21797_197837 : EJMOriginalGlobalDAGData.nodes 9 ⟨197837, by decide⟩ =
    .split (coordinate 12) (![⟨197785, by decide⟩,⟨197809, by decide⟩,⟨197829, by decide⟩,⟨197836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21797_197837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21797 ⟨197837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21797
    ⟨197837, by decide⟩ (by decide) (![⟨197785, by decide⟩,⟨197809, by decide⟩,⟨197829, by decide⟩,⟨197836, by decide⟩]) unmarked_context_12_21797_197837 node_context_12_21797_197837
  intro a
  fin_cases a
  · exact context_13_87188_197785
  · exact context_13_87189_197809
  · exact context_13_87190_197829
  · exact context_13_87191_197836

theorem selected_cut_06645 : selected 8 ⟨197857, by decide⟩
    (prefixPartial 13 87192) = some ⟨13, 2, 0, 197857, 87192, 929, 16384⟩ := by
  decide +kernel

theorem context_13_87192_197857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87192 ⟨197857, by decide⟩ :=
  accepted_of_selected 13 87192 ⟨197857, by decide⟩ ⟨13, 2, 0, 197857, 87192, 929, 16384⟩
    (by decide) selected_cut_06645

theorem selected_cut_06646 : selected 8 ⟨197881, by decide⟩
    (prefixPartial 13 87193) = some ⟨13, 2, 0, 197881, 87193, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_87193_197881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87193 ⟨197881, by decide⟩ :=
  accepted_of_selected 13 87193 ⟨197881, by decide⟩ ⟨13, 2, 0, 197881, 87193, 2169, 16384⟩
    (by decide) selected_cut_06646

theorem selected_cut_06647 : selected 8 ⟨197900, by decide⟩
    (prefixPartial 13 87194) = some ⟨13, 2, 0, 197900, 87194, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_87194_197900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87194 ⟨197900, by decide⟩ :=
  accepted_of_selected 13 87194 ⟨197900, by decide⟩ ⟨13, 2, 0, 197900, 87194, 1233, 16384⟩
    (by decide) selected_cut_06647

theorem selected_cut_06648 : selected 8 ⟨197912, by decide⟩
    (prefixPartial 13 87195) = some ⟨13, 2, 0, 197912, 87195, 909, 16384⟩ := by
  decide +kernel

theorem context_13_87195_197912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87195 ⟨197912, by decide⟩ :=
  accepted_of_selected 13 87195 ⟨197912, by decide⟩ ⟨13, 2, 0, 197912, 87195, 909, 16384⟩
    (by decide) selected_cut_06648

theorem unmarked_context_12_21798_197913 : frontier 9 ⟨197913, by decide⟩
    (prefixCache 12 21798) (prefixPartial 12 21798) = false := by
  decide +kernel

theorem node_context_12_21798_197913 : EJMOriginalGlobalDAGData.nodes 9 ⟨197913, by decide⟩ =
    .split (coordinate 12) (![⟨197857, by decide⟩,⟨197881, by decide⟩,⟨197900, by decide⟩,⟨197912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21798_197913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21798 ⟨197913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21798
    ⟨197913, by decide⟩ (by decide) (![⟨197857, by decide⟩,⟨197881, by decide⟩,⟨197900, by decide⟩,⟨197912, by decide⟩]) unmarked_context_12_21798_197913 node_context_12_21798_197913
  intro a
  fin_cases a
  · exact context_13_87192_197857
  · exact context_13_87193_197881
  · exact context_13_87194_197900
  · exact context_13_87195_197912

theorem selected_cut_06649 : selected 8 ⟨197930, by decide⟩
    (prefixPartial 13 87196) = some ⟨13, 2, 0, 197930, 87196, 769, 16384⟩ := by
  decide +kernel

theorem context_13_87196_197930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87196 ⟨197930, by decide⟩ :=
  accepted_of_selected 13 87196 ⟨197930, by decide⟩ ⟨13, 2, 0, 197930, 87196, 769, 16384⟩
    (by decide) selected_cut_06649

theorem selected_cut_06650 : selected 8 ⟨197958, by decide⟩
    (prefixPartial 13 87197) = some ⟨13, 2, 0, 197958, 87197, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_87197_197958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87197 ⟨197958, by decide⟩ :=
  accepted_of_selected 13 87197 ⟨197958, by decide⟩ ⟨13, 2, 0, 197958, 87197, 2065, 16384⟩
    (by decide) selected_cut_06650

theorem selected_cut_06651 : selected 8 ⟨197977, by decide⟩
    (prefixPartial 13 87198) = some ⟨13, 2, 0, 197977, 87198, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_87198_197977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87198 ⟨197977, by decide⟩ :=
  accepted_of_selected 13 87198 ⟨197977, by decide⟩ ⟨13, 2, 0, 197977, 87198, 1369, 16384⟩
    (by decide) selected_cut_06651

theorem selected_cut_06652 : selected 8 ⟨197986, by decide⟩
    (prefixPartial 13 87199) = some ⟨13, 2, 0, 197986, 87199, 729, 16384⟩ := by
  decide +kernel

theorem context_13_87199_197986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87199 ⟨197986, by decide⟩ :=
  accepted_of_selected 13 87199 ⟨197986, by decide⟩ ⟨13, 2, 0, 197986, 87199, 729, 16384⟩
    (by decide) selected_cut_06652

theorem unmarked_context_12_21799_197987 : frontier 9 ⟨197987, by decide⟩
    (prefixCache 12 21799) (prefixPartial 12 21799) = false := by
  decide +kernel

theorem node_context_12_21799_197987 : EJMOriginalGlobalDAGData.nodes 9 ⟨197987, by decide⟩ =
    .split (coordinate 12) (![⟨197930, by decide⟩,⟨197958, by decide⟩,⟨197977, by decide⟩,⟨197986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21799_197987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21799 ⟨197987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21799
    ⟨197987, by decide⟩ (by decide) (![⟨197930, by decide⟩,⟨197958, by decide⟩,⟨197977, by decide⟩,⟨197986, by decide⟩]) unmarked_context_12_21799_197987 node_context_12_21799_197987
  intro a
  fin_cases a
  · exact context_13_87196_197930
  · exact context_13_87197_197958
  · exact context_13_87198_197977
  · exact context_13_87199_197986

theorem unmarked_context_11_5449_197988 : frontier 10 ⟨197988, by decide⟩
    (prefixCache 11 5449) (prefixPartial 11 5449) = false := by
  decide +kernel

theorem node_context_11_5449_197988 : EJMOriginalGlobalDAGData.nodes 10 ⟨197988, by decide⟩ =
    .split (coordinate 11) (![⟨197768, by decide⟩,⟨197837, by decide⟩,⟨197913, by decide⟩,⟨197987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5449_197988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5449 ⟨197988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5449
    ⟨197988, by decide⟩ (by decide) (![⟨197768, by decide⟩,⟨197837, by decide⟩,⟨197913, by decide⟩,⟨197987, by decide⟩]) unmarked_context_11_5449_197988 node_context_11_5449_197988
  intro a
  fin_cases a
  · exact context_12_21796_197768
  · exact context_12_21797_197837
  · exact context_12_21798_197913
  · exact context_12_21799_197987

theorem selected_cut_06653 : selected 8 ⟨197996, by decide⟩
    (prefixPartial 13 87200) = some ⟨13, 2, 0, 197996, 87200, 545, 16384⟩ := by
  decide +kernel

theorem context_13_87200_197996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87200 ⟨197996, by decide⟩ :=
  accepted_of_selected 13 87200 ⟨197996, by decide⟩ ⟨13, 2, 0, 197996, 87200, 545, 16384⟩
    (by decide) selected_cut_06653

theorem selected_cut_06654 : selected 8 ⟨198024, by decide⟩
    (prefixPartial 13 87201) = some ⟨13, 2, 0, 198024, 87201, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_87201_198024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87201 ⟨198024, by decide⟩ :=
  accepted_of_selected 13 87201 ⟨198024, by decide⟩ ⟨13, 2, 0, 198024, 87201, 1985, 16384⟩
    (by decide) selected_cut_06654

theorem selected_cut_06655 : selected 8 ⟨198043, by decide⟩
    (prefixPartial 13 87202) = some ⟨13, 2, 0, 198043, 87202, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_87202_198043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87202 ⟨198043, by decide⟩ :=
  accepted_of_selected 13 87202 ⟨198043, by decide⟩ ⟨13, 2, 0, 198043, 87202, 1633, 16384⟩
    (by decide) selected_cut_06655

theorem selected_cut_06656 : selected 8 ⟨198053, by decide⟩
    (prefixPartial 13 87203) = some ⟨13, 2, 0, 198053, 87203, 929, 16384⟩ := by
  decide +kernel

theorem context_13_87203_198053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87203 ⟨198053, by decide⟩ :=
  accepted_of_selected 13 87203 ⟨198053, by decide⟩ ⟨13, 2, 0, 198053, 87203, 929, 16384⟩
    (by decide) selected_cut_06656

theorem unmarked_context_12_21800_198054 : frontier 9 ⟨198054, by decide⟩
    (prefixCache 12 21800) (prefixPartial 12 21800) = false := by
  decide +kernel

theorem node_context_12_21800_198054 : EJMOriginalGlobalDAGData.nodes 9 ⟨198054, by decide⟩ =
    .split (coordinate 12) (![⟨197996, by decide⟩,⟨198024, by decide⟩,⟨198043, by decide⟩,⟨198053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21800_198054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21800 ⟨198054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21800
    ⟨198054, by decide⟩ (by decide) (![⟨197996, by decide⟩,⟨198024, by decide⟩,⟨198043, by decide⟩,⟨198053, by decide⟩]) unmarked_context_12_21800_198054 node_context_12_21800_198054
  intro a
  fin_cases a
  · exact context_13_87200_197996
  · exact context_13_87201_198024
  · exact context_13_87202_198043
  · exact context_13_87203_198053

theorem selected_cut_06657 : selected 8 ⟨198064, by decide⟩
    (prefixPartial 13 87204) = some ⟨13, 2, 0, 198064, 87204, 569, 16384⟩ := by
  decide +kernel

theorem context_13_87204_198064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87204 ⟨198064, by decide⟩ :=
  accepted_of_selected 13 87204 ⟨198064, by decide⟩ ⟨13, 2, 0, 198064, 87204, 569, 16384⟩
    (by decide) selected_cut_06657

theorem selected_cut_06658 : selected 8 ⟨198089, by decide⟩
    (prefixPartial 13 87205) = some ⟨13, 2, 0, 198089, 87205, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_87205_198089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87205 ⟨198089, by decide⟩ :=
  accepted_of_selected 13 87205 ⟨198089, by decide⟩ ⟨13, 2, 0, 198089, 87205, 1545, 16384⟩
    (by decide) selected_cut_06658

theorem selected_cut_06659 : selected 8 ⟨198108, by decide⟩
    (prefixPartial 13 87206) = some ⟨13, 2, 0, 198108, 87206, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_87206_198108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87206 ⟨198108, by decide⟩ :=
  accepted_of_selected 13 87206 ⟨198108, by decide⟩ ⟨13, 2, 0, 198108, 87206, 1329, 16384⟩
    (by decide) selected_cut_06659

theorem selected_cut_06660 : selected 8 ⟨198119, by decide⟩
    (prefixPartial 13 87207) = some ⟨13, 2, 0, 198119, 87207, 893, 16384⟩ := by
  decide +kernel

theorem context_13_87207_198119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87207 ⟨198119, by decide⟩ :=
  accepted_of_selected 13 87207 ⟨198119, by decide⟩ ⟨13, 2, 0, 198119, 87207, 893, 16384⟩
    (by decide) selected_cut_06660

theorem unmarked_context_12_21801_198120 : frontier 9 ⟨198120, by decide⟩
    (prefixCache 12 21801) (prefixPartial 12 21801) = false := by
  decide +kernel

theorem node_context_12_21801_198120 : EJMOriginalGlobalDAGData.nodes 9 ⟨198120, by decide⟩ =
    .split (coordinate 12) (![⟨198064, by decide⟩,⟨198089, by decide⟩,⟨198108, by decide⟩,⟨198119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21801_198120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21801 ⟨198120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21801
    ⟨198120, by decide⟩ (by decide) (![⟨198064, by decide⟩,⟨198089, by decide⟩,⟨198108, by decide⟩,⟨198119, by decide⟩]) unmarked_context_12_21801_198120 node_context_12_21801_198120
  intro a
  fin_cases a
  · exact context_13_87204_198064
  · exact context_13_87205_198089
  · exact context_13_87206_198108
  · exact context_13_87207_198119

theorem selected_cut_06661 : selected 8 ⟨198138, by decide⟩
    (prefixPartial 13 87208) = some ⟨13, 2, 0, 198138, 87208, 701, 16384⟩ := by
  decide +kernel

theorem context_13_87208_198138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87208 ⟨198138, by decide⟩ :=
  accepted_of_selected 13 87208 ⟨198138, by decide⟩ ⟨13, 2, 0, 198138, 87208, 701, 16384⟩
    (by decide) selected_cut_06661

theorem selected_cut_06662 : selected 8 ⟨198175, by decide⟩
    (prefixPartial 13 87209) = some ⟨13, 2, 0, 198175, 87209, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_87209_198175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87209 ⟨198175, by decide⟩ :=
  accepted_of_selected 13 87209 ⟨198175, by decide⟩ ⟨13, 2, 0, 198175, 87209, 2469, 16384⟩
    (by decide) selected_cut_06662

theorem selected_cut_06663 : selected 8 ⟨198196, by decide⟩
    (prefixPartial 13 87210) = some ⟨13, 2, 0, 198196, 87210, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_87210_198196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87210 ⟨198196, by decide⟩ :=
  accepted_of_selected 13 87210 ⟨198196, by decide⟩ ⟨13, 2, 0, 198196, 87210, 1481, 16384⟩
    (by decide) selected_cut_06663

theorem selected_cut_06664 : selected 8 ⟨198205, by decide⟩
    (prefixPartial 13 87211) = some ⟨13, 2, 0, 198205, 87211, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_87211_198205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87211 ⟨198205, by decide⟩ :=
  accepted_of_selected 13 87211 ⟨198205, by decide⟩ ⟨13, 2, 0, 198205, 87211, 1041, 16384⟩
    (by decide) selected_cut_06664

theorem unmarked_context_12_21802_198206 : frontier 9 ⟨198206, by decide⟩
    (prefixCache 12 21802) (prefixPartial 12 21802) = false := by
  decide +kernel

theorem node_context_12_21802_198206 : EJMOriginalGlobalDAGData.nodes 9 ⟨198206, by decide⟩ =
    .split (coordinate 12) (![⟨198138, by decide⟩,⟨198175, by decide⟩,⟨198196, by decide⟩,⟨198205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21802_198206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21802 ⟨198206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21802
    ⟨198206, by decide⟩ (by decide) (![⟨198138, by decide⟩,⟨198175, by decide⟩,⟨198196, by decide⟩,⟨198205, by decide⟩]) unmarked_context_12_21802_198206 node_context_12_21802_198206
  intro a
  fin_cases a
  · exact context_13_87208_198138
  · exact context_13_87209_198175
  · exact context_13_87210_198196
  · exact context_13_87211_198205

theorem selected_cut_06665 : selected 8 ⟨198218, by decide⟩
    (prefixPartial 13 87212) = some ⟨13, 2, 0, 198218, 87212, 573, 16384⟩ := by
  decide +kernel

theorem context_13_87212_198218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87212 ⟨198218, by decide⟩ :=
  accepted_of_selected 13 87212 ⟨198218, by decide⟩ ⟨13, 2, 0, 198218, 87212, 573, 16384⟩
    (by decide) selected_cut_06665

theorem selected_cut_06666 : selected 8 ⟨198248, by decide⟩
    (prefixPartial 13 87213) = some ⟨13, 2, 0, 198248, 87213, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_87213_198248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87213 ⟨198248, by decide⟩ :=
  accepted_of_selected 13 87213 ⟨198248, by decide⟩ ⟨13, 2, 0, 198248, 87213, 2353, 16384⟩
    (by decide) selected_cut_06666

theorem selected_cut_06667 : selected 8 ⟨198269, by decide⟩
    (prefixPartial 13 87214) = some ⟨13, 2, 0, 198269, 87214, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_87214_198269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87214 ⟨198269, by decide⟩ :=
  accepted_of_selected 13 87214 ⟨198269, by decide⟩ ⟨13, 2, 0, 198269, 87214, 1557, 16384⟩
    (by decide) selected_cut_06667

theorem selected_cut_06668 : selected 8 ⟨198283, by decide⟩
    (prefixPartial 13 87215) = some ⟨13, 2, 0, 198283, 87215, 949, 16384⟩ := by
  decide +kernel

theorem context_13_87215_198283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87215 ⟨198283, by decide⟩ :=
  accepted_of_selected 13 87215 ⟨198283, by decide⟩ ⟨13, 2, 0, 198283, 87215, 949, 16384⟩
    (by decide) selected_cut_06668

theorem unmarked_context_12_21803_198284 : frontier 9 ⟨198284, by decide⟩
    (prefixCache 12 21803) (prefixPartial 12 21803) = false := by
  decide +kernel

theorem node_context_12_21803_198284 : EJMOriginalGlobalDAGData.nodes 9 ⟨198284, by decide⟩ =
    .split (coordinate 12) (![⟨198218, by decide⟩,⟨198248, by decide⟩,⟨198269, by decide⟩,⟨198283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21803_198284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21803 ⟨198284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21803
    ⟨198284, by decide⟩ (by decide) (![⟨198218, by decide⟩,⟨198248, by decide⟩,⟨198269, by decide⟩,⟨198283, by decide⟩]) unmarked_context_12_21803_198284 node_context_12_21803_198284
  intro a
  fin_cases a
  · exact context_13_87212_198218
  · exact context_13_87213_198248
  · exact context_13_87214_198269
  · exact context_13_87215_198283

theorem unmarked_context_11_5450_198285 : frontier 10 ⟨198285, by decide⟩
    (prefixCache 11 5450) (prefixPartial 11 5450) = false := by
  decide +kernel

theorem node_context_11_5450_198285 : EJMOriginalGlobalDAGData.nodes 10 ⟨198285, by decide⟩ =
    .split (coordinate 11) (![⟨198054, by decide⟩,⟨198120, by decide⟩,⟨198206, by decide⟩,⟨198284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5450_198285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5450 ⟨198285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5450
    ⟨198285, by decide⟩ (by decide) (![⟨198054, by decide⟩,⟨198120, by decide⟩,⟨198206, by decide⟩,⟨198284, by decide⟩]) unmarked_context_11_5450_198285 node_context_11_5450_198285
  intro a
  fin_cases a
  · exact context_12_21800_198054
  · exact context_12_21801_198120
  · exact context_12_21802_198206
  · exact context_12_21803_198284

theorem selected_cut_06669 : selected 8 ⟨198292, by decide⟩
    (prefixPartial 13 87216) = some ⟨13, 2, 0, 198292, 87216, 289, 16384⟩ := by
  decide +kernel

theorem context_13_87216_198292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87216 ⟨198292, by decide⟩ :=
  accepted_of_selected 13 87216 ⟨198292, by decide⟩ ⟨13, 2, 0, 198292, 87216, 289, 16384⟩
    (by decide) selected_cut_06669

theorem selected_cut_06670 : selected 8 ⟨198316, by decide⟩
    (prefixPartial 13 87217) = some ⟨13, 2, 0, 198316, 87217, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_87217_198316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87217 ⟨198316, by decide⟩ :=
  accepted_of_selected 13 87217 ⟨198316, by decide⟩ ⟨13, 2, 0, 198316, 87217, 2017, 16384⟩
    (by decide) selected_cut_06670

theorem selected_cut_06671 : selected 8 ⟨198335, by decide⟩
    (prefixPartial 13 87218) = some ⟨13, 2, 0, 198335, 87218, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_87218_198335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87218 ⟨198335, by decide⟩ :=
  accepted_of_selected 13 87218 ⟨198335, by decide⟩ ⟨13, 2, 0, 198335, 87218, 1517, 16384⟩
    (by decide) selected_cut_06671

theorem selected_cut_06672 : selected 8 ⟨198344, by decide⟩
    (prefixPartial 13 87219) = some ⟨13, 2, 0, 198344, 87219, 941, 16384⟩ := by
  decide +kernel

theorem context_13_87219_198344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87219 ⟨198344, by decide⟩ :=
  accepted_of_selected 13 87219 ⟨198344, by decide⟩ ⟨13, 2, 0, 198344, 87219, 941, 16384⟩
    (by decide) selected_cut_06672

theorem unmarked_context_12_21804_198345 : frontier 9 ⟨198345, by decide⟩
    (prefixCache 12 21804) (prefixPartial 12 21804) = false := by
  decide +kernel

theorem node_context_12_21804_198345 : EJMOriginalGlobalDAGData.nodes 9 ⟨198345, by decide⟩ =
    .split (coordinate 12) (![⟨198292, by decide⟩,⟨198316, by decide⟩,⟨198335, by decide⟩,⟨198344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21804_198345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21804 ⟨198345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21804
    ⟨198345, by decide⟩ (by decide) (![⟨198292, by decide⟩,⟨198316, by decide⟩,⟨198335, by decide⟩,⟨198344, by decide⟩]) unmarked_context_12_21804_198345 node_context_12_21804_198345
  intro a
  fin_cases a
  · exact context_13_87216_198292
  · exact context_13_87217_198316
  · exact context_13_87218_198335
  · exact context_13_87219_198344

theorem selected_cut_06673 : selected 9 ⟨198406, by decide⟩
    (prefixPartial 12 21805) = some ⟨12, 2, 0, 198406, 21805, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_21805_198406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21805 ⟨198406, by decide⟩ :=
  accepted_of_selected 12 21805 ⟨198406, by decide⟩ ⟨12, 2, 0, 198406, 21805, 3873, 65536⟩
    (by decide) selected_cut_06673

theorem selected_cut_06674 : selected 8 ⟨198417, by decide⟩
    (prefixPartial 13 87224) = some ⟨13, 2, 0, 198417, 87224, 305, 16384⟩ := by
  decide +kernel

theorem context_13_87224_198417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87224 ⟨198417, by decide⟩ :=
  accepted_of_selected 13 87224 ⟨198417, by decide⟩ ⟨13, 2, 0, 198417, 87224, 305, 16384⟩
    (by decide) selected_cut_06674

theorem selected_cut_06675 : selected 8 ⟨198458, by decide⟩
    (prefixPartial 13 87225) = some ⟨13, 2, 0, 198458, 87225, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_87225_198458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87225 ⟨198458, by decide⟩ :=
  accepted_of_selected 13 87225 ⟨198458, by decide⟩ ⟨13, 2, 0, 198458, 87225, 2525, 16384⟩
    (by decide) selected_cut_06675

theorem selected_cut_06676 : selected 8 ⟨198481, by decide⟩
    (prefixPartial 13 87226) = some ⟨13, 2, 0, 198481, 87226, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_87226_198481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87226 ⟨198481, by decide⟩ :=
  accepted_of_selected 13 87226 ⟨198481, by decide⟩ ⟨13, 2, 0, 198481, 87226, 1561, 16384⟩
    (by decide) selected_cut_06676

theorem selected_cut_06677 : selected 8 ⟨198491, by decide⟩
    (prefixPartial 13 87227) = some ⟨13, 2, 0, 198491, 87227, 965, 16384⟩ := by
  decide +kernel

theorem context_13_87227_198491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87227 ⟨198491, by decide⟩ :=
  accepted_of_selected 13 87227 ⟨198491, by decide⟩ ⟨13, 2, 0, 198491, 87227, 965, 16384⟩
    (by decide) selected_cut_06677

theorem unmarked_context_12_21806_198492 : frontier 9 ⟨198492, by decide⟩
    (prefixCache 12 21806) (prefixPartial 12 21806) = false := by
  decide +kernel

theorem node_context_12_21806_198492 : EJMOriginalGlobalDAGData.nodes 9 ⟨198492, by decide⟩ =
    .split (coordinate 12) (![⟨198417, by decide⟩,⟨198458, by decide⟩,⟨198481, by decide⟩,⟨198491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21806_198492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21806 ⟨198492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21806
    ⟨198492, by decide⟩ (by decide) (![⟨198417, by decide⟩,⟨198458, by decide⟩,⟨198481, by decide⟩,⟨198491, by decide⟩]) unmarked_context_12_21806_198492 node_context_12_21806_198492
  intro a
  fin_cases a
  · exact context_13_87224_198417
  · exact context_13_87225_198458
  · exact context_13_87226_198481
  · exact context_13_87227_198491

theorem selected_cut_06678 : selected 8 ⟨198499, by decide⟩
    (prefixPartial 13 87228) = some ⟨13, 2, 0, 198499, 87228, 133, 16384⟩ := by
  decide +kernel

theorem context_13_87228_198499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87228 ⟨198499, by decide⟩ :=
  accepted_of_selected 13 87228 ⟨198499, by decide⟩ ⟨13, 2, 0, 198499, 87228, 133, 16384⟩
    (by decide) selected_cut_06678

theorem selected_cut_06679 : selected 8 ⟨198532, by decide⟩
    (prefixPartial 13 87229) = some ⟨13, 2, 0, 198532, 87229, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_87229_198532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87229 ⟨198532, by decide⟩ :=
  accepted_of_selected 13 87229 ⟨198532, by decide⟩ ⟨13, 2, 0, 198532, 87229, 2345, 16384⟩
    (by decide) selected_cut_06679

theorem selected_cut_06680 : selected 8 ⟨198551, by decide⟩
    (prefixPartial 13 87230) = some ⟨13, 2, 0, 198551, 87230, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_87230_198551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87230 ⟨198551, by decide⟩ :=
  accepted_of_selected 13 87230 ⟨198551, by decide⟩ ⟨13, 2, 0, 198551, 87230, 1473, 16384⟩
    (by decide) selected_cut_06680

theorem selected_cut_06681 : selected 8 ⟨198561, by decide⟩
    (prefixPartial 13 87231) = some ⟨13, 2, 0, 198561, 87231, 825, 16384⟩ := by
  decide +kernel

theorem context_13_87231_198561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87231 ⟨198561, by decide⟩ :=
  accepted_of_selected 13 87231 ⟨198561, by decide⟩ ⟨13, 2, 0, 198561, 87231, 825, 16384⟩
    (by decide) selected_cut_06681

theorem unmarked_context_12_21807_198562 : frontier 9 ⟨198562, by decide⟩
    (prefixCache 12 21807) (prefixPartial 12 21807) = false := by
  decide +kernel

theorem node_context_12_21807_198562 : EJMOriginalGlobalDAGData.nodes 9 ⟨198562, by decide⟩ =
    .split (coordinate 12) (![⟨198499, by decide⟩,⟨198532, by decide⟩,⟨198551, by decide⟩,⟨198561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21807_198562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21807 ⟨198562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21807
    ⟨198562, by decide⟩ (by decide) (![⟨198499, by decide⟩,⟨198532, by decide⟩,⟨198551, by decide⟩,⟨198561, by decide⟩]) unmarked_context_12_21807_198562 node_context_12_21807_198562
  intro a
  fin_cases a
  · exact context_13_87228_198499
  · exact context_13_87229_198532
  · exact context_13_87230_198551
  · exact context_13_87231_198561

theorem unmarked_context_11_5451_198563 : frontier 10 ⟨198563, by decide⟩
    (prefixCache 11 5451) (prefixPartial 11 5451) = false := by
  decide +kernel

theorem node_context_11_5451_198563 : EJMOriginalGlobalDAGData.nodes 10 ⟨198563, by decide⟩ =
    .split (coordinate 11) (![⟨198345, by decide⟩,⟨198406, by decide⟩,⟨198492, by decide⟩,⟨198562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5451_198563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5451 ⟨198563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5451
    ⟨198563, by decide⟩ (by decide) (![⟨198345, by decide⟩,⟨198406, by decide⟩,⟨198492, by decide⟩,⟨198562, by decide⟩]) unmarked_context_11_5451_198563 node_context_11_5451_198563
  intro a
  fin_cases a
  · exact context_12_21804_198345
  · exact context_12_21805_198406
  · exact context_12_21806_198492
  · exact context_12_21807_198562

theorem unmarked_context_10_1362_198564 : frontier 11 ⟨198564, by decide⟩
    (prefixCache 10 1362) (prefixPartial 10 1362) = false := by
  decide +kernel

theorem node_context_10_1362_198564 : EJMOriginalGlobalDAGData.nodes 11 ⟨198564, by decide⟩ =
    .split (coordinate 10) (![⟨197702, by decide⟩,⟨197988, by decide⟩,⟨198285, by decide⟩,⟨198563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1362_198564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1362 ⟨198564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1362
    ⟨198564, by decide⟩ (by decide) (![⟨197702, by decide⟩,⟨197988, by decide⟩,⟨198285, by decide⟩,⟨198563, by decide⟩]) unmarked_context_10_1362_198564 node_context_10_1362_198564
  intro a
  fin_cases a
  · exact context_11_5448_197702
  · exact context_11_5449_197988
  · exact context_11_5450_198285
  · exact context_11_5451_198563

theorem selected_cut_06682 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1363) = some ⟨10, 1, 0, 3440, 1363, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1363_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1363 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1363 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1363, 1, 1048576⟩
    (by decide) selected_cut_06682

theorem unmarked_context_9_340_198565 : frontier 12 ⟨198565, by decide⟩
    (prefixCache 9 340) (prefixPartial 9 340) = false := by
  decide +kernel

theorem node_context_9_340_198565 : EJMOriginalGlobalDAGData.nodes 12 ⟨198565, by decide⟩ =
    .split (coordinate 9) (![⟨196776, by decide⟩,⟨197393, by decide⟩,⟨198564, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_340_198565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 340 ⟨198565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 340
    ⟨198565, by decide⟩ (by decide) (![⟨196776, by decide⟩,⟨197393, by decide⟩,⟨198564, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_340_198565 node_context_9_340_198565
  intro a
  fin_cases a
  · exact context_10_1360_196776
  · exact context_10_1361_197393
  · exact context_10_1362_198564
  · exact context_10_1363_3440

theorem selected_cut_06683 : selected 9 ⟨198600, by decide⟩
    (prefixPartial 12 21824) = some ⟨12, 2, 0, 198600, 21824, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_21824_198600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21824 ⟨198600, by decide⟩ :=
  accepted_of_selected 12 21824 ⟨198600, by decide⟩ ⟨12, 2, 0, 198600, 21824, 2497, 65536⟩
    (by decide) selected_cut_06683

theorem selected_cut_06684 : selected 9 ⟨198644, by decide⟩
    (prefixPartial 12 21825) = some ⟨12, 2, 0, 198644, 21825, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_21825_198644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21825 ⟨198644, by decide⟩ :=
  accepted_of_selected 12 21825 ⟨198644, by decide⟩ ⟨12, 2, 0, 198644, 21825, 3117, 65536⟩
    (by decide) selected_cut_06684

theorem selected_cut_06685 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87304) = some ⟨13, 1, 0, 3444, 87304, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87304_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87304 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87304 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87304, 1, 16384⟩
    (by decide) selected_cut_06685

theorem selected_cut_06686 : selected 8 ⟨198671, by decide⟩
    (prefixPartial 13 87305) = some ⟨13, 2, 0, 198671, 87305, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_87305_198671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87305 ⟨198671, by decide⟩ :=
  accepted_of_selected 13 87305 ⟨198671, by decide⟩ ⟨13, 2, 0, 198671, 87305, 2217, 16384⟩
    (by decide) selected_cut_06686

theorem selected_cut_06687 : selected 8 ⟨198690, by decide⟩
    (prefixPartial 13 87306) = some ⟨13, 2, 0, 198690, 87306, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_87306_198690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87306 ⟨198690, by decide⟩ :=
  accepted_of_selected 13 87306 ⟨198690, by decide⟩ ⟨13, 2, 0, 198690, 87306, 1949, 16384⟩
    (by decide) selected_cut_06687

theorem selected_cut_06688 : selected 8 ⟨198702, by decide⟩
    (prefixPartial 13 87307) = some ⟨13, 2, 0, 198702, 87307, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_87307_198702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87307 ⟨198702, by decide⟩ :=
  accepted_of_selected 13 87307 ⟨198702, by decide⟩ ⟨13, 2, 0, 198702, 87307, 1045, 16384⟩
    (by decide) selected_cut_06688

theorem unmarked_context_12_21826_198703 : frontier 9 ⟨198703, by decide⟩
    (prefixCache 12 21826) (prefixPartial 12 21826) = false := by
  decide +kernel

theorem node_context_12_21826_198703 : EJMOriginalGlobalDAGData.nodes 9 ⟨198703, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨198671, by decide⟩,⟨198690, by decide⟩,⟨198702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21826_198703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21826 ⟨198703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21826
    ⟨198703, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨198671, by decide⟩,⟨198690, by decide⟩,⟨198702, by decide⟩]) unmarked_context_12_21826_198703 node_context_12_21826_198703
  intro a
  fin_cases a
  · exact context_13_87304_3444
  · exact context_13_87305_198671
  · exact context_13_87306_198690
  · exact context_13_87307_198702

theorem selected_cut_06689 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21827) = some ⟨12, 1, 0, 893, 21827, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21827_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21827 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21827 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21827, 1, 65536⟩
    (by decide) selected_cut_06689

theorem unmarked_context_11_5456_198704 : frontier 10 ⟨198704, by decide⟩
    (prefixCache 11 5456) (prefixPartial 11 5456) = false := by
  decide +kernel

theorem node_context_11_5456_198704 : EJMOriginalGlobalDAGData.nodes 10 ⟨198704, by decide⟩ =
    .split (coordinate 11) (![⟨198600, by decide⟩,⟨198644, by decide⟩,⟨198703, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5456_198704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5456 ⟨198704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5456
    ⟨198704, by decide⟩ (by decide) (![⟨198600, by decide⟩,⟨198644, by decide⟩,⟨198703, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5456_198704 node_context_11_5456_198704
  intro a
  fin_cases a
  · exact context_12_21824_198600
  · exact context_12_21825_198644
  · exact context_12_21826_198703
  · exact context_12_21827_893

theorem selected_cut_06690 : selected 9 ⟨198745, by decide⟩
    (prefixPartial 12 21828) = some ⟨12, 2, 0, 198745, 21828, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_21828_198745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21828 ⟨198745, by decide⟩ :=
  accepted_of_selected 12 21828 ⟨198745, by decide⟩ ⟨12, 2, 0, 198745, 21828, 2065, 65536⟩
    (by decide) selected_cut_06690

theorem selected_cut_06691 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 21829) = some ⟨12, 1, 0, 126884, 21829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21829_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21829 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 21829 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 21829, 1, 65536⟩
    (by decide) selected_cut_06691

theorem selected_cut_06692 : selected 9 ⟨198804, by decide⟩
    (prefixPartial 12 21830) = some ⟨12, 2, 0, 198804, 21830, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_21830_198804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21830 ⟨198804, by decide⟩ :=
  accepted_of_selected 12 21830 ⟨198804, by decide⟩ ⟨12, 2, 0, 198804, 21830, 3777, 65536⟩
    (by decide) selected_cut_06692

theorem selected_cut_06693 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21831) = some ⟨12, 1, 0, 893, 21831, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21831_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21831 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21831 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21831, 1, 65536⟩
    (by decide) selected_cut_06693

theorem unmarked_context_11_5457_198805 : frontier 10 ⟨198805, by decide⟩
    (prefixCache 11 5457) (prefixPartial 11 5457) = false := by
  decide +kernel

theorem node_context_11_5457_198805 : EJMOriginalGlobalDAGData.nodes 10 ⟨198805, by decide⟩ =
    .split (coordinate 11) (![⟨198745, by decide⟩,⟨126884, by decide⟩,⟨198804, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5457_198805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5457 ⟨198805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5457
    ⟨198805, by decide⟩ (by decide) (![⟨198745, by decide⟩,⟨126884, by decide⟩,⟨198804, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5457_198805 node_context_11_5457_198805
  intro a
  fin_cases a
  · exact context_12_21828_198745
  · exact context_12_21829_126884
  · exact context_12_21830_198804
  · exact context_12_21831_893

theorem selected_cut_06694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87328) = some ⟨13, 1, 0, 3444, 87328, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87328_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87328 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87328 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87328, 1, 16384⟩
    (by decide) selected_cut_06694

theorem selected_cut_06695 : selected 8 ⟨198829, by decide⟩
    (prefixPartial 13 87329) = some ⟨13, 2, 0, 198829, 87329, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_87329_198829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87329 ⟨198829, by decide⟩ :=
  accepted_of_selected 13 87329 ⟨198829, by decide⟩ ⟨13, 2, 0, 198829, 87329, 1973, 16384⟩
    (by decide) selected_cut_06695

theorem selected_cut_06696 : selected 8 ⟨198851, by decide⟩
    (prefixPartial 13 87330) = some ⟨13, 2, 0, 198851, 87330, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_87330_198851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87330 ⟨198851, by decide⟩ :=
  accepted_of_selected 13 87330 ⟨198851, by decide⟩ ⟨13, 2, 0, 198851, 87330, 1761, 16384⟩
    (by decide) selected_cut_06696

theorem selected_cut_06697 : selected 8 ⟨198863, by decide⟩
    (prefixPartial 13 87331) = some ⟨13, 2, 0, 198863, 87331, 825, 16384⟩ := by
  decide +kernel

theorem context_13_87331_198863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87331 ⟨198863, by decide⟩ :=
  accepted_of_selected 13 87331 ⟨198863, by decide⟩ ⟨13, 2, 0, 198863, 87331, 825, 16384⟩
    (by decide) selected_cut_06697

theorem unmarked_context_12_21832_198864 : frontier 9 ⟨198864, by decide⟩
    (prefixCache 12 21832) (prefixPartial 12 21832) = false := by
  decide +kernel

theorem node_context_12_21832_198864 : EJMOriginalGlobalDAGData.nodes 9 ⟨198864, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨198829, by decide⟩,⟨198851, by decide⟩,⟨198863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21832_198864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21832 ⟨198864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21832
    ⟨198864, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨198829, by decide⟩,⟨198851, by decide⟩,⟨198863, by decide⟩]) unmarked_context_12_21832_198864 node_context_12_21832_198864
  intro a
  fin_cases a
  · exact context_13_87328_3444
  · exact context_13_87329_198829
  · exact context_13_87330_198851
  · exact context_13_87331_198863

theorem selected_cut_06698 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87332) = some ⟨13, 1, 0, 3444, 87332, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87332_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87332 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87332 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87332, 1, 16384⟩
    (by decide) selected_cut_06698

theorem selected_cut_06699 : selected 8 ⟨198906, by decide⟩
    (prefixPartial 13 87333) = some ⟨13, 2, 0, 198906, 87333, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_87333_198906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87333 ⟨198906, by decide⟩ :=
  accepted_of_selected 13 87333 ⟨198906, by decide⟩ ⟨13, 2, 0, 198906, 87333, 2133, 16384⟩
    (by decide) selected_cut_06699

theorem selected_cut_06700 : selected 8 ⟨198944, by decide⟩
    (prefixPartial 13 87334) = some ⟨13, 2, 0, 198944, 87334, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_87334_198944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87334 ⟨198944, by decide⟩ :=
  accepted_of_selected 13 87334 ⟨198944, by decide⟩ ⟨13, 2, 0, 198944, 87334, 2177, 16384⟩
    (by decide) selected_cut_06700

theorem selected_cut_06701 : selected 8 ⟨198955, by decide⟩
    (prefixPartial 13 87335) = some ⟨13, 2, 0, 198955, 87335, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_87335_198955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87335 ⟨198955, by decide⟩ :=
  accepted_of_selected 13 87335 ⟨198955, by decide⟩ ⟨13, 2, 0, 198955, 87335, 1113, 16384⟩
    (by decide) selected_cut_06701

theorem unmarked_context_12_21833_198956 : frontier 9 ⟨198956, by decide⟩
    (prefixCache 12 21833) (prefixPartial 12 21833) = false := by
  decide +kernel

theorem node_context_12_21833_198956 : EJMOriginalGlobalDAGData.nodes 9 ⟨198956, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨198906, by decide⟩,⟨198944, by decide⟩,⟨198955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21833_198956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21833 ⟨198956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21833
    ⟨198956, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨198906, by decide⟩,⟨198944, by decide⟩,⟨198955, by decide⟩]) unmarked_context_12_21833_198956 node_context_12_21833_198956
  intro a
  fin_cases a
  · exact context_13_87332_3444
  · exact context_13_87333_198906
  · exact context_13_87334_198944
  · exact context_13_87335_198955

theorem selected_cut_06702 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87336) = some ⟨13, 1, 0, 3444, 87336, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87336_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87336 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87336 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87336, 1, 16384⟩
    (by decide) selected_cut_06702

theorem selected_cut_06703 : selected 8 ⟨198989, by decide⟩
    (prefixPartial 13 87337) = some ⟨13, 2, 0, 198989, 87337, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_87337_198989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87337 ⟨198989, by decide⟩ :=
  accepted_of_selected 13 87337 ⟨198989, by decide⟩ ⟨13, 2, 0, 198989, 87337, 1705, 16384⟩
    (by decide) selected_cut_06703

theorem selected_cut_06704 : selected 8 ⟨199013, by decide⟩
    (prefixPartial 13 87338) = some ⟨13, 2, 0, 199013, 87338, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_87338_199013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87338 ⟨199013, by decide⟩ :=
  accepted_of_selected 13 87338 ⟨199013, by decide⟩ ⟨13, 2, 0, 199013, 87338, 1717, 16384⟩
    (by decide) selected_cut_06704

theorem selected_cut_06705 : selected 8 ⟨199023, by decide⟩
    (prefixPartial 13 87339) = some ⟨13, 2, 0, 199023, 87339, 873, 16384⟩ := by
  decide +kernel

theorem context_13_87339_199023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87339 ⟨199023, by decide⟩ :=
  accepted_of_selected 13 87339 ⟨199023, by decide⟩ ⟨13, 2, 0, 199023, 87339, 873, 16384⟩
    (by decide) selected_cut_06705

theorem unmarked_context_12_21834_199024 : frontier 9 ⟨199024, by decide⟩
    (prefixCache 12 21834) (prefixPartial 12 21834) = false := by
  decide +kernel

theorem node_context_12_21834_199024 : EJMOriginalGlobalDAGData.nodes 9 ⟨199024, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨198989, by decide⟩,⟨199013, by decide⟩,⟨199023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21834_199024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21834 ⟨199024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21834
    ⟨199024, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨198989, by decide⟩,⟨199013, by decide⟩,⟨199023, by decide⟩]) unmarked_context_12_21834_199024 node_context_12_21834_199024
  intro a
  fin_cases a
  · exact context_13_87336_3444
  · exact context_13_87337_198989
  · exact context_13_87338_199013
  · exact context_13_87339_199023

theorem selected_cut_06706 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87340) = some ⟨13, 1, 0, 3444, 87340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87340, 1, 16384⟩
    (by decide) selected_cut_06706

theorem selected_cut_06707 : selected 8 ⟨199048, by decide⟩
    (prefixPartial 13 87341) = some ⟨13, 2, 0, 199048, 87341, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_87341_199048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87341 ⟨199048, by decide⟩ :=
  accepted_of_selected 13 87341 ⟨199048, by decide⟩ ⟨13, 2, 0, 199048, 87341, 1761, 16384⟩
    (by decide) selected_cut_06707

theorem selected_cut_06708 : selected 8 ⟨199070, by decide⟩
    (prefixPartial 13 87342) = some ⟨13, 2, 0, 199070, 87342, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_87342_199070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87342 ⟨199070, by decide⟩ :=
  accepted_of_selected 13 87342 ⟨199070, by decide⟩ ⟨13, 2, 0, 199070, 87342, 1749, 16384⟩
    (by decide) selected_cut_06708

theorem selected_cut_06709 : selected 8 ⟨199078, by decide⟩
    (prefixPartial 13 87343) = some ⟨13, 2, 0, 199078, 87343, 981, 16384⟩ := by
  decide +kernel

theorem context_13_87343_199078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87343 ⟨199078, by decide⟩ :=
  accepted_of_selected 13 87343 ⟨199078, by decide⟩ ⟨13, 2, 0, 199078, 87343, 981, 16384⟩
    (by decide) selected_cut_06709

theorem unmarked_context_12_21835_199079 : frontier 9 ⟨199079, by decide⟩
    (prefixCache 12 21835) (prefixPartial 12 21835) = false := by
  decide +kernel

theorem node_context_12_21835_199079 : EJMOriginalGlobalDAGData.nodes 9 ⟨199079, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199048, by decide⟩,⟨199070, by decide⟩,⟨199078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21835_199079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21835 ⟨199079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21835
    ⟨199079, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199048, by decide⟩,⟨199070, by decide⟩,⟨199078, by decide⟩]) unmarked_context_12_21835_199079 node_context_12_21835_199079
  intro a
  fin_cases a
  · exact context_13_87340_3444
  · exact context_13_87341_199048
  · exact context_13_87342_199070
  · exact context_13_87343_199078

theorem unmarked_context_11_5458_199080 : frontier 10 ⟨199080, by decide⟩
    (prefixCache 11 5458) (prefixPartial 11 5458) = false := by
  decide +kernel

theorem node_context_11_5458_199080 : EJMOriginalGlobalDAGData.nodes 10 ⟨199080, by decide⟩ =
    .split (coordinate 11) (![⟨198864, by decide⟩,⟨198956, by decide⟩,⟨199024, by decide⟩,⟨199079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5458_199080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5458 ⟨199080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5458
    ⟨199080, by decide⟩ (by decide) (![⟨198864, by decide⟩,⟨198956, by decide⟩,⟨199024, by decide⟩,⟨199079, by decide⟩]) unmarked_context_11_5458_199080 node_context_11_5458_199080
  intro a
  fin_cases a
  · exact context_12_21832_198864
  · exact context_12_21833_198956
  · exact context_12_21834_199024
  · exact context_12_21835_199079

theorem selected_cut_06710 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5459) = some ⟨11, 1, 0, 1736, 5459, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5459_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5459 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5459 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5459, 1, 262144⟩
    (by decide) selected_cut_06710

theorem unmarked_context_10_1364_199081 : frontier 11 ⟨199081, by decide⟩
    (prefixCache 10 1364) (prefixPartial 10 1364) = false := by
  decide +kernel

theorem node_context_10_1364_199081 : EJMOriginalGlobalDAGData.nodes 11 ⟨199081, by decide⟩ =
    .split (coordinate 10) (![⟨198704, by decide⟩,⟨198805, by decide⟩,⟨199080, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1364_199081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1364 ⟨199081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1364
    ⟨199081, by decide⟩ (by decide) (![⟨198704, by decide⟩,⟨198805, by decide⟩,⟨199080, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1364_199081 node_context_10_1364_199081
  intro a
  fin_cases a
  · exact context_11_5456_198704
  · exact context_11_5457_198805
  · exact context_11_5458_199080
  · exact context_11_5459_1736

theorem selected_cut_06711 : selected 9 ⟨199119, by decide⟩
    (prefixPartial 12 21840) = some ⟨12, 2, 0, 199119, 21840, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_21840_199119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21840 ⟨199119, by decide⟩ :=
  accepted_of_selected 12 21840 ⟨199119, by decide⟩ ⟨12, 2, 0, 199119, 21840, 1993, 65536⟩
    (by decide) selected_cut_06711

theorem selected_cut_06712 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 21841) = some ⟨12, 1, 0, 126371, 21841, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21841_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21841 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 21841 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 21841, 1, 65536⟩
    (by decide) selected_cut_06712

theorem selected_cut_06713 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87368) = some ⟨13, 1, 0, 3444, 87368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87368, 1, 16384⟩
    (by decide) selected_cut_06713

theorem selected_cut_06714 : selected 8 ⟨199142, by decide⟩
    (prefixPartial 13 87369) = some ⟨13, 2, 0, 199142, 87369, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_87369_199142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87369 ⟨199142, by decide⟩ :=
  accepted_of_selected 13 87369 ⟨199142, by decide⟩ ⟨13, 2, 0, 199142, 87369, 1597, 16384⟩
    (by decide) selected_cut_06714

theorem selected_cut_06715 : selected 8 ⟨199165, by decide⟩
    (prefixPartial 13 87370) = some ⟨13, 2, 0, 199165, 87370, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_87370_199165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87370 ⟨199165, by decide⟩ :=
  accepted_of_selected 13 87370 ⟨199165, by decide⟩ ⟨13, 2, 0, 199165, 87370, 1997, 16384⟩
    (by decide) selected_cut_06715

theorem selected_cut_06716 : selected 8 ⟨199177, by decide⟩
    (prefixPartial 13 87371) = some ⟨13, 2, 0, 199177, 87371, 917, 16384⟩ := by
  decide +kernel

theorem context_13_87371_199177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87371 ⟨199177, by decide⟩ :=
  accepted_of_selected 13 87371 ⟨199177, by decide⟩ ⟨13, 2, 0, 199177, 87371, 917, 16384⟩
    (by decide) selected_cut_06716

theorem unmarked_context_12_21842_199178 : frontier 9 ⟨199178, by decide⟩
    (prefixCache 12 21842) (prefixPartial 12 21842) = false := by
  decide +kernel

theorem node_context_12_21842_199178 : EJMOriginalGlobalDAGData.nodes 9 ⟨199178, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199142, by decide⟩,⟨199165, by decide⟩,⟨199177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21842_199178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21842 ⟨199178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21842
    ⟨199178, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199142, by decide⟩,⟨199165, by decide⟩,⟨199177, by decide⟩]) unmarked_context_12_21842_199178 node_context_12_21842_199178
  intro a
  fin_cases a
  · exact context_13_87368_3444
  · exact context_13_87369_199142
  · exact context_13_87370_199165
  · exact context_13_87371_199177

theorem selected_cut_06717 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21843) = some ⟨12, 1, 0, 893, 21843, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21843_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21843 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21843 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21843, 1, 65536⟩
    (by decide) selected_cut_06717

theorem unmarked_context_11_5460_199179 : frontier 10 ⟨199179, by decide⟩
    (prefixCache 11 5460) (prefixPartial 11 5460) = false := by
  decide +kernel

theorem node_context_11_5460_199179 : EJMOriginalGlobalDAGData.nodes 10 ⟨199179, by decide⟩ =
    .split (coordinate 11) (![⟨199119, by decide⟩,⟨126371, by decide⟩,⟨199178, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5460_199179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5460 ⟨199179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5460
    ⟨199179, by decide⟩ (by decide) (![⟨199119, by decide⟩,⟨126371, by decide⟩,⟨199178, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5460_199179 node_context_11_5460_199179
  intro a
  fin_cases a
  · exact context_12_21840_199119
  · exact context_12_21841_126371
  · exact context_12_21842_199178
  · exact context_12_21843_893

theorem selected_cut_06718 : selected 9 ⟨199180, by decide⟩
    (prefixPartial 12 21844) = some ⟨12, 1, 0, 199180, 21844, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21844_199180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21844 ⟨199180, by decide⟩ :=
  accepted_of_selected 12 21844 ⟨199180, by decide⟩ ⟨12, 1, 0, 199180, 21844, 1, 65536⟩
    (by decide) selected_cut_06718

theorem selected_cut_06719 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 21845) = some ⟨12, 1, 0, 170504, 21845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21845_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21845 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 21845 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 21845, 1, 65536⟩
    (by decide) selected_cut_06719

theorem selected_cut_06720 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87384) = some ⟨13, 1, 0, 3444, 87384, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87384_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87384 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87384 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87384, 1, 16384⟩
    (by decide) selected_cut_06720

theorem selected_cut_06721 : selected 8 ⟨199205, by decide⟩
    (prefixPartial 13 87385) = some ⟨13, 2, 0, 199205, 87385, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_87385_199205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87385 ⟨199205, by decide⟩ :=
  accepted_of_selected 13 87385 ⟨199205, by decide⟩ ⟨13, 2, 0, 199205, 87385, 1905, 16384⟩
    (by decide) selected_cut_06721

theorem selected_cut_06722 : selected 8 ⟨199225, by decide⟩
    (prefixPartial 13 87386) = some ⟨13, 2, 0, 199225, 87386, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_87386_199225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87386 ⟨199225, by decide⟩ :=
  accepted_of_selected 13 87386 ⟨199225, by decide⟩ ⟨13, 2, 0, 199225, 87386, 1869, 16384⟩
    (by decide) selected_cut_06722

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
