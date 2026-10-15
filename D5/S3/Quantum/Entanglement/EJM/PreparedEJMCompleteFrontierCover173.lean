/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover172
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_13_113688_422466 : frontier 8 ⟨422466, by decide⟩
    (prefixCache 13 113688) (prefixPartial 13 113688) = false := by
  decide +kernel

theorem node_context_13_113688_422466 : EJMOriginalGlobalDAGData.nodes 8 ⟨422466, by decide⟩ =
    .split (coordinate 13) (![⟨422383, by decide⟩,⟨422417, by decide⟩,⟨422445, by decide⟩,⟨422465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113688_422466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113688 ⟨422466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113688
    ⟨422466, by decide⟩ (by decide) (![⟨422383, by decide⟩,⟨422417, by decide⟩,⟨422445, by decide⟩,⟨422465, by decide⟩]) unmarked_context_13_113688_422466 node_context_13_113688_422466
  intro a
  fin_cases a
  · exact context_14_454752_422383
  · exact context_14_454753_422417
  · exact context_14_454754_422445
  · exact context_14_454755_422465

theorem selected_cut_16612 : selected 7 ⟨422493, by decide⟩
    (prefixPartial 14 454756) = some ⟨14, 2, 0, 422493, 454756, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_454756_422493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454756 ⟨422493, by decide⟩ :=
  accepted_of_selected 14 454756 ⟨422493, by decide⟩ ⟨14, 2, 0, 422493, 454756, 1145, 4096⟩
    (by decide) selected_cut_16612

theorem selected_cut_16613 : selected 7 ⟨422526, by decide⟩
    (prefixPartial 14 454757) = some ⟨14, 2, 0, 422526, 454757, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_454757_422526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454757 ⟨422526, by decide⟩ :=
  accepted_of_selected 14 454757 ⟨422526, by decide⟩ ⟨14, 2, 0, 422526, 454757, 1117, 4096⟩
    (by decide) selected_cut_16613

theorem selected_cut_16614 : selected 7 ⟨422556, by decide⟩
    (prefixPartial 14 454758) = some ⟨14, 2, 0, 422556, 454758, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_454758_422556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454758 ⟨422556, by decide⟩ :=
  accepted_of_selected 14 454758 ⟨422556, by decide⟩ ⟨14, 2, 0, 422556, 454758, 1105, 4096⟩
    (by decide) selected_cut_16614

theorem selected_cut_16615 : selected 7 ⟨422577, by decide⟩
    (prefixPartial 14 454759) = some ⟨14, 2, 0, 422577, 454759, 893, 4096⟩ := by
  decide +kernel

theorem context_14_454759_422577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454759 ⟨422577, by decide⟩ :=
  accepted_of_selected 14 454759 ⟨422577, by decide⟩ ⟨14, 2, 0, 422577, 454759, 893, 4096⟩
    (by decide) selected_cut_16615

theorem unmarked_context_13_113689_422578 : frontier 8 ⟨422578, by decide⟩
    (prefixCache 13 113689) (prefixPartial 13 113689) = false := by
  decide +kernel

theorem node_context_13_113689_422578 : EJMOriginalGlobalDAGData.nodes 8 ⟨422578, by decide⟩ =
    .split (coordinate 13) (![⟨422493, by decide⟩,⟨422526, by decide⟩,⟨422556, by decide⟩,⟨422577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113689_422578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113689 ⟨422578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113689
    ⟨422578, by decide⟩ (by decide) (![⟨422493, by decide⟩,⟨422526, by decide⟩,⟨422556, by decide⟩,⟨422577, by decide⟩]) unmarked_context_13_113689_422578 node_context_13_113689_422578
  intro a
  fin_cases a
  · exact context_14_454756_422493
  · exact context_14_454757_422526
  · exact context_14_454758_422556
  · exact context_14_454759_422577

theorem selected_cut_16616 : selected 8 ⟨422641, by decide⟩
    (prefixPartial 13 113690) = some ⟨13, 2, 0, 422641, 113690, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_113690_422641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113690 ⟨422641, by decide⟩ :=
  accepted_of_selected 13 113690 ⟨422641, by decide⟩ ⟨13, 2, 0, 422641, 113690, 2945, 16384⟩
    (by decide) selected_cut_16616

theorem selected_cut_16617 : selected 8 ⟨422676, by decide⟩
    (prefixPartial 13 113691) = some ⟨13, 2, 0, 422676, 113691, 969, 16384⟩ := by
  decide +kernel

theorem context_13_113691_422676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113691 ⟨422676, by decide⟩ :=
  accepted_of_selected 13 113691 ⟨422676, by decide⟩ ⟨13, 2, 0, 422676, 113691, 969, 16384⟩
    (by decide) selected_cut_16617

theorem unmarked_context_12_28422_422677 : frontier 9 ⟨422677, by decide⟩
    (prefixCache 12 28422) (prefixPartial 12 28422) = false := by
  decide +kernel

theorem node_context_12_28422_422677 : EJMOriginalGlobalDAGData.nodes 9 ⟨422677, by decide⟩ =
    .split (coordinate 12) (![⟨422466, by decide⟩,⟨422578, by decide⟩,⟨422641, by decide⟩,⟨422676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28422_422677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28422 ⟨422677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28422
    ⟨422677, by decide⟩ (by decide) (![⟨422466, by decide⟩,⟨422578, by decide⟩,⟨422641, by decide⟩,⟨422676, by decide⟩]) unmarked_context_12_28422_422677 node_context_12_28422_422677
  intro a
  fin_cases a
  · exact context_13_113688_422466
  · exact context_13_113689_422578
  · exact context_13_113690_422641
  · exact context_13_113691_422676

theorem selected_cut_16618 : selected 7 ⟨422702, by decide⟩
    (prefixPartial 14 454768) = some ⟨14, 2, 0, 422702, 454768, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_454768_422702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454768 ⟨422702, by decide⟩ :=
  accepted_of_selected 14 454768 ⟨422702, by decide⟩ ⟨14, 2, 0, 422702, 454768, 1017, 4096⟩
    (by decide) selected_cut_16618

theorem selected_cut_16619 : selected 7 ⟨422721, by decide⟩
    (prefixPartial 14 454769) = some ⟨14, 2, 0, 422721, 454769, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_454769_422721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454769 ⟨422721, by decide⟩ :=
  accepted_of_selected 14 454769 ⟨422721, by decide⟩ ⟨14, 2, 0, 422721, 454769, 1281, 4096⟩
    (by decide) selected_cut_16619

theorem selected_cut_16620 : selected 7 ⟨422742, by decide⟩
    (prefixPartial 14 454770) = some ⟨14, 2, 0, 422742, 454770, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_454770_422742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454770 ⟨422742, by decide⟩ :=
  accepted_of_selected 14 454770 ⟨422742, by decide⟩ ⟨14, 2, 0, 422742, 454770, 1161, 4096⟩
    (by decide) selected_cut_16620

theorem selected_cut_16621 : selected 7 ⟨422755, by decide⟩
    (prefixPartial 14 454771) = some ⟨14, 2, 0, 422755, 454771, 985, 4096⟩ := by
  decide +kernel

theorem context_14_454771_422755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454771 ⟨422755, by decide⟩ :=
  accepted_of_selected 14 454771 ⟨422755, by decide⟩ ⟨14, 2, 0, 422755, 454771, 985, 4096⟩
    (by decide) selected_cut_16621

theorem unmarked_context_13_113692_422756 : frontier 8 ⟨422756, by decide⟩
    (prefixCache 13 113692) (prefixPartial 13 113692) = false := by
  decide +kernel

theorem node_context_13_113692_422756 : EJMOriginalGlobalDAGData.nodes 8 ⟨422756, by decide⟩ =
    .split (coordinate 13) (![⟨422702, by decide⟩,⟨422721, by decide⟩,⟨422742, by decide⟩,⟨422755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113692_422756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113692 ⟨422756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113692
    ⟨422756, by decide⟩ (by decide) (![⟨422702, by decide⟩,⟨422721, by decide⟩,⟨422742, by decide⟩,⟨422755, by decide⟩]) unmarked_context_13_113692_422756 node_context_13_113692_422756
  intro a
  fin_cases a
  · exact context_14_454768_422702
  · exact context_14_454769_422721
  · exact context_14_454770_422742
  · exact context_14_454771_422755

theorem selected_cut_16622 : selected 7 ⟨422785, by decide⟩
    (prefixPartial 14 454772) = some ⟨14, 2, 0, 422785, 454772, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_454772_422785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454772 ⟨422785, by decide⟩ :=
  accepted_of_selected 14 454772 ⟨422785, by decide⟩ ⟨14, 2, 0, 422785, 454772, 1285, 4096⟩
    (by decide) selected_cut_16622

theorem selected_cut_16623 : selected 7 ⟨422815, by decide⟩
    (prefixPartial 14 454773) = some ⟨14, 2, 0, 422815, 454773, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_454773_422815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454773 ⟨422815, by decide⟩ :=
  accepted_of_selected 14 454773 ⟨422815, by decide⟩ ⟨14, 2, 0, 422815, 454773, 1061, 4096⟩
    (by decide) selected_cut_16623

theorem selected_cut_16624 : selected 7 ⟨422845, by decide⟩
    (prefixPartial 14 454774) = some ⟨14, 2, 0, 422845, 454774, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_454774_422845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454774 ⟨422845, by decide⟩ :=
  accepted_of_selected 14 454774 ⟨422845, by decide⟩ ⟨14, 2, 0, 422845, 454774, 1133, 4096⟩
    (by decide) selected_cut_16624

theorem selected_cut_16625 : selected 7 ⟨422861, by decide⟩
    (prefixPartial 14 454775) = some ⟨14, 2, 0, 422861, 454775, 865, 4096⟩ := by
  decide +kernel

theorem context_14_454775_422861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454775 ⟨422861, by decide⟩ :=
  accepted_of_selected 14 454775 ⟨422861, by decide⟩ ⟨14, 2, 0, 422861, 454775, 865, 4096⟩
    (by decide) selected_cut_16625

theorem unmarked_context_13_113693_422862 : frontier 8 ⟨422862, by decide⟩
    (prefixCache 13 113693) (prefixPartial 13 113693) = false := by
  decide +kernel

theorem node_context_13_113693_422862 : EJMOriginalGlobalDAGData.nodes 8 ⟨422862, by decide⟩ =
    .split (coordinate 13) (![⟨422785, by decide⟩,⟨422815, by decide⟩,⟨422845, by decide⟩,⟨422861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113693_422862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113693 ⟨422862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113693
    ⟨422862, by decide⟩ (by decide) (![⟨422785, by decide⟩,⟨422815, by decide⟩,⟨422845, by decide⟩,⟨422861, by decide⟩]) unmarked_context_13_113693_422862 node_context_13_113693_422862
  intro a
  fin_cases a
  · exact context_14_454772_422785
  · exact context_14_454773_422815
  · exact context_14_454774_422845
  · exact context_14_454775_422861

theorem selected_cut_16626 : selected 8 ⟨422931, by decide⟩
    (prefixPartial 13 113694) = some ⟨13, 2, 0, 422931, 113694, 3037, 16384⟩ := by
  decide +kernel

theorem context_13_113694_422931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113694 ⟨422931, by decide⟩ :=
  accepted_of_selected 13 113694 ⟨422931, by decide⟩ ⟨13, 2, 0, 422931, 113694, 3037, 16384⟩
    (by decide) selected_cut_16626

theorem selected_cut_16627 : selected 8 ⟨422963, by decide⟩
    (prefixPartial 13 113695) = some ⟨13, 2, 0, 422963, 113695, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_113695_422963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113695 ⟨422963, by decide⟩ :=
  accepted_of_selected 13 113695 ⟨422963, by decide⟩ ⟨13, 2, 0, 422963, 113695, 1085, 16384⟩
    (by decide) selected_cut_16627

theorem unmarked_context_12_28423_422964 : frontier 9 ⟨422964, by decide⟩
    (prefixCache 12 28423) (prefixPartial 12 28423) = false := by
  decide +kernel

theorem node_context_12_28423_422964 : EJMOriginalGlobalDAGData.nodes 9 ⟨422964, by decide⟩ =
    .split (coordinate 12) (![⟨422756, by decide⟩,⟨422862, by decide⟩,⟨422931, by decide⟩,⟨422963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28423_422964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28423 ⟨422964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28423
    ⟨422964, by decide⟩ (by decide) (![⟨422756, by decide⟩,⟨422862, by decide⟩,⟨422931, by decide⟩,⟨422963, by decide⟩]) unmarked_context_12_28423_422964 node_context_12_28423_422964
  intro a
  fin_cases a
  · exact context_13_113692_422756
  · exact context_13_113693_422862
  · exact context_13_113694_422931
  · exact context_13_113695_422963

theorem unmarked_context_11_7105_422965 : frontier 10 ⟨422965, by decide⟩
    (prefixCache 11 7105) (prefixPartial 11 7105) = false := by
  decide +kernel

theorem node_context_11_7105_422965 : EJMOriginalGlobalDAGData.nodes 10 ⟨422965, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨422349, by decide⟩,⟨422677, by decide⟩,⟨422964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7105_422965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7105 ⟨422965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7105
    ⟨422965, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨422349, by decide⟩,⟨422677, by decide⟩,⟨422964, by decide⟩]) unmarked_context_11_7105_422965 node_context_11_7105_422965
  intro a
  fin_cases a
  · exact context_12_28420_34034
  · exact context_12_28421_422349
  · exact context_12_28422_422677
  · exact context_12_28423_422964

theorem selected_cut_16628 : selected 8 ⟨423045, by decide⟩
    (prefixPartial 13 113696) = some ⟨13, 2, 0, 423045, 113696, 3617, 16384⟩ := by
  decide +kernel

theorem context_13_113696_423045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113696 ⟨423045, by decide⟩ :=
  accepted_of_selected 13 113696 ⟨423045, by decide⟩ ⟨13, 2, 0, 423045, 113696, 3617, 16384⟩
    (by decide) selected_cut_16628

theorem selected_cut_16629 : selected 7 ⟨423080, by decide⟩
    (prefixPartial 14 454788) = some ⟨14, 2, 0, 423080, 454788, 1493, 4096⟩ := by
  decide +kernel

theorem context_14_454788_423080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454788 ⟨423080, by decide⟩ :=
  accepted_of_selected 14 454788 ⟨423080, by decide⟩ ⟨14, 2, 0, 423080, 454788, 1493, 4096⟩
    (by decide) selected_cut_16629

theorem selected_cut_16630 : selected 7 ⟨423111, by decide⟩
    (prefixPartial 14 454789) = some ⟨14, 2, 0, 423111, 454789, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_454789_423111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454789 ⟨423111, by decide⟩ :=
  accepted_of_selected 14 454789 ⟨423111, by decide⟩ ⟨14, 2, 0, 423111, 454789, 1093, 4096⟩
    (by decide) selected_cut_16630

theorem selected_cut_16631 : selected 7 ⟨423147, by decide⟩
    (prefixPartial 14 454790) = some ⟨14, 2, 0, 423147, 454790, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_454790_423147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454790 ⟨423147, by decide⟩ :=
  accepted_of_selected 14 454790 ⟨423147, by decide⟩ ⟨14, 2, 0, 423147, 454790, 1429, 4096⟩
    (by decide) selected_cut_16631

theorem selected_cut_16632 : selected 7 ⟨423165, by decide⟩
    (prefixPartial 14 454791) = some ⟨14, 2, 0, 423165, 454791, 873, 4096⟩ := by
  decide +kernel

theorem context_14_454791_423165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454791 ⟨423165, by decide⟩ :=
  accepted_of_selected 14 454791 ⟨423165, by decide⟩ ⟨14, 2, 0, 423165, 454791, 873, 4096⟩
    (by decide) selected_cut_16632

theorem unmarked_context_13_113697_423166 : frontier 8 ⟨423166, by decide⟩
    (prefixCache 13 113697) (prefixPartial 13 113697) = false := by
  decide +kernel

theorem node_context_13_113697_423166 : EJMOriginalGlobalDAGData.nodes 8 ⟨423166, by decide⟩ =
    .split (coordinate 13) (![⟨423080, by decide⟩,⟨423111, by decide⟩,⟨423147, by decide⟩,⟨423165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113697_423166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113697 ⟨423166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113697
    ⟨423166, by decide⟩ (by decide) (![⟨423080, by decide⟩,⟨423111, by decide⟩,⟨423147, by decide⟩,⟨423165, by decide⟩]) unmarked_context_13_113697_423166 node_context_13_113697_423166
  intro a
  fin_cases a
  · exact context_14_454788_423080
  · exact context_14_454789_423111
  · exact context_14_454790_423147
  · exact context_14_454791_423165

theorem selected_cut_16633 : selected 8 ⟨423237, by decide⟩
    (prefixPartial 13 113698) = some ⟨13, 2, 0, 423237, 113698, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_113698_423237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113698 ⟨423237, by decide⟩ :=
  accepted_of_selected 13 113698 ⟨423237, by decide⟩ ⟨13, 2, 0, 423237, 113698, 3029, 16384⟩
    (by decide) selected_cut_16633

theorem selected_cut_16634 : selected 8 ⟨423279, by decide⟩
    (prefixPartial 13 113699) = some ⟨13, 2, 0, 423279, 113699, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_113699_423279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113699 ⟨423279, by decide⟩ :=
  accepted_of_selected 13 113699 ⟨423279, by decide⟩ ⟨13, 2, 0, 423279, 113699, 1125, 16384⟩
    (by decide) selected_cut_16634

theorem unmarked_context_12_28424_423280 : frontier 9 ⟨423280, by decide⟩
    (prefixCache 12 28424) (prefixPartial 12 28424) = false := by
  decide +kernel

theorem node_context_12_28424_423280 : EJMOriginalGlobalDAGData.nodes 9 ⟨423280, by decide⟩ =
    .split (coordinate 12) (![⟨423045, by decide⟩,⟨423166, by decide⟩,⟨423237, by decide⟩,⟨423279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28424_423280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28424 ⟨423280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28424
    ⟨423280, by decide⟩ (by decide) (![⟨423045, by decide⟩,⟨423166, by decide⟩,⟨423237, by decide⟩,⟨423279, by decide⟩]) unmarked_context_12_28424_423280 node_context_12_28424_423280
  intro a
  fin_cases a
  · exact context_13_113696_423045
  · exact context_13_113697_423166
  · exact context_13_113698_423237
  · exact context_13_113699_423279

theorem selected_cut_16635 : selected 7 ⟨423302, by decide⟩
    (prefixPartial 14 454800) = some ⟨14, 2, 0, 423302, 454800, 949, 4096⟩ := by
  decide +kernel

theorem context_14_454800_423302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454800 ⟨423302, by decide⟩ :=
  accepted_of_selected 14 454800 ⟨423302, by decide⟩ ⟨14, 2, 0, 423302, 454800, 949, 4096⟩
    (by decide) selected_cut_16635

theorem selected_cut_16636 : selected 7 ⟨423326, by decide⟩
    (prefixPartial 14 454801) = some ⟨14, 2, 0, 423326, 454801, 1461, 4096⟩ := by
  decide +kernel

theorem context_14_454801_423326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454801 ⟨423326, by decide⟩ :=
  accepted_of_selected 14 454801 ⟨423326, by decide⟩ ⟨14, 2, 0, 423326, 454801, 1461, 4096⟩
    (by decide) selected_cut_16636

theorem selected_cut_16637 : selected 7 ⟨423346, by decide⟩
    (prefixPartial 14 454802) = some ⟨14, 2, 0, 423346, 454802, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_454802_423346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454802 ⟨423346, by decide⟩ :=
  accepted_of_selected 14 454802 ⟨423346, by decide⟩ ⟨14, 2, 0, 423346, 454802, 1097, 4096⟩
    (by decide) selected_cut_16637

theorem selected_cut_16638 : selected 7 ⟨423369, by decide⟩
    (prefixPartial 14 454803) = some ⟨14, 2, 0, 423369, 454803, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_454803_423369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454803 ⟨423369, by decide⟩ :=
  accepted_of_selected 14 454803 ⟨423369, by decide⟩ ⟨14, 2, 0, 423369, 454803, 1073, 4096⟩
    (by decide) selected_cut_16638

theorem unmarked_context_13_113700_423370 : frontier 8 ⟨423370, by decide⟩
    (prefixCache 13 113700) (prefixPartial 13 113700) = false := by
  decide +kernel

theorem node_context_13_113700_423370 : EJMOriginalGlobalDAGData.nodes 8 ⟨423370, by decide⟩ =
    .split (coordinate 13) (![⟨423302, by decide⟩,⟨423326, by decide⟩,⟨423346, by decide⟩,⟨423369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113700_423370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113700 ⟨423370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113700
    ⟨423370, by decide⟩ (by decide) (![⟨423302, by decide⟩,⟨423326, by decide⟩,⟨423346, by decide⟩,⟨423369, by decide⟩]) unmarked_context_13_113700_423370 node_context_13_113700_423370
  intro a
  fin_cases a
  · exact context_14_454800_423302
  · exact context_14_454801_423326
  · exact context_14_454802_423346
  · exact context_14_454803_423369

theorem selected_cut_16639 : selected 7 ⟨423394, by decide⟩
    (prefixPartial 14 454804) = some ⟨14, 2, 0, 423394, 454804, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_454804_423394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454804 ⟨423394, by decide⟩ :=
  accepted_of_selected 14 454804 ⟨423394, by decide⟩ ⟨14, 2, 0, 423394, 454804, 1265, 4096⟩
    (by decide) selected_cut_16639

theorem selected_cut_16640 : selected 7 ⟨423416, by decide⟩
    (prefixPartial 14 454805) = some ⟨14, 2, 0, 423416, 454805, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_454805_423416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454805 ⟨423416, by decide⟩ :=
  accepted_of_selected 14 454805 ⟨423416, by decide⟩ ⟨14, 2, 0, 423416, 454805, 1105, 4096⟩
    (by decide) selected_cut_16640

theorem selected_cut_16641 : selected 7 ⟨423439, by decide⟩
    (prefixPartial 14 454806) = some ⟨14, 2, 0, 423439, 454806, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_454806_423439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454806 ⟨423439, by decide⟩ :=
  accepted_of_selected 14 454806 ⟨423439, by decide⟩ ⟨14, 2, 0, 423439, 454806, 1193, 4096⟩
    (by decide) selected_cut_16641

theorem selected_cut_16642 : selected 7 ⟨423456, by decide⟩
    (prefixPartial 14 454807) = some ⟨14, 2, 0, 423456, 454807, 949, 4096⟩ := by
  decide +kernel

theorem context_14_454807_423456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454807 ⟨423456, by decide⟩ :=
  accepted_of_selected 14 454807 ⟨423456, by decide⟩ ⟨14, 2, 0, 423456, 454807, 949, 4096⟩
    (by decide) selected_cut_16642

theorem unmarked_context_13_113701_423457 : frontier 8 ⟨423457, by decide⟩
    (prefixCache 13 113701) (prefixPartial 13 113701) = false := by
  decide +kernel

theorem node_context_13_113701_423457 : EJMOriginalGlobalDAGData.nodes 8 ⟨423457, by decide⟩ =
    .split (coordinate 13) (![⟨423394, by decide⟩,⟨423416, by decide⟩,⟨423439, by decide⟩,⟨423456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113701_423457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113701 ⟨423457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113701
    ⟨423457, by decide⟩ (by decide) (![⟨423394, by decide⟩,⟨423416, by decide⟩,⟨423439, by decide⟩,⟨423456, by decide⟩]) unmarked_context_13_113701_423457 node_context_13_113701_423457
  intro a
  fin_cases a
  · exact context_14_454804_423394
  · exact context_14_454805_423416
  · exact context_14_454806_423439
  · exact context_14_454807_423456

theorem selected_cut_16643 : selected 8 ⟨423507, by decide⟩
    (prefixPartial 13 113702) = some ⟨13, 2, 0, 423507, 113702, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_113702_423507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113702 ⟨423507, by decide⟩ :=
  accepted_of_selected 13 113702 ⟨423507, by decide⟩ ⟨13, 2, 0, 423507, 113702, 2813, 16384⟩
    (by decide) selected_cut_16643

theorem selected_cut_16644 : selected 8 ⟨423521, by decide⟩
    (prefixPartial 13 113703) = some ⟨13, 2, 0, 423521, 113703, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_113703_423521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113703 ⟨423521, by decide⟩ :=
  accepted_of_selected 13 113703 ⟨423521, by decide⟩ ⟨13, 2, 0, 423521, 113703, 1065, 16384⟩
    (by decide) selected_cut_16644

theorem unmarked_context_12_28425_423522 : frontier 9 ⟨423522, by decide⟩
    (prefixCache 12 28425) (prefixPartial 12 28425) = false := by
  decide +kernel

theorem node_context_12_28425_423522 : EJMOriginalGlobalDAGData.nodes 9 ⟨423522, by decide⟩ =
    .split (coordinate 12) (![⟨423370, by decide⟩,⟨423457, by decide⟩,⟨423507, by decide⟩,⟨423521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28425_423522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28425 ⟨423522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28425
    ⟨423522, by decide⟩ (by decide) (![⟨423370, by decide⟩,⟨423457, by decide⟩,⟨423507, by decide⟩,⟨423521, by decide⟩]) unmarked_context_12_28425_423522 node_context_12_28425_423522
  intro a
  fin_cases a
  · exact context_13_113700_423370
  · exact context_13_113701_423457
  · exact context_13_113702_423507
  · exact context_13_113703_423521

theorem selected_cut_16645 : selected 7 ⟨423536, by decide⟩
    (prefixPartial 14 454816) = some ⟨14, 2, 0, 423536, 454816, 661, 4096⟩ := by
  decide +kernel

theorem context_14_454816_423536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454816 ⟨423536, by decide⟩ :=
  accepted_of_selected 14 454816 ⟨423536, by decide⟩ ⟨14, 2, 0, 423536, 454816, 661, 4096⟩
    (by decide) selected_cut_16645

theorem selected_cut_16646 : selected 7 ⟨423562, by decide⟩
    (prefixPartial 14 454817) = some ⟨14, 2, 0, 423562, 454817, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_454817_423562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454817 ⟨423562, by decide⟩ :=
  accepted_of_selected 14 454817 ⟨423562, by decide⟩ ⟨14, 2, 0, 423562, 454817, 1417, 4096⟩
    (by decide) selected_cut_16646

theorem selected_cut_16647 : selected 7 ⟨423582, by decide⟩
    (prefixPartial 14 454818) = some ⟨14, 2, 0, 423582, 454818, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_454818_423582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454818 ⟨423582, by decide⟩ :=
  accepted_of_selected 14 454818 ⟨423582, by decide⟩ ⟨14, 2, 0, 423582, 454818, 1169, 4096⟩
    (by decide) selected_cut_16647

theorem selected_cut_16648 : selected 7 ⟨423604, by decide⟩
    (prefixPartial 14 454819) = some ⟨14, 2, 0, 423604, 454819, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_454819_423604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454819 ⟨423604, by decide⟩ :=
  accepted_of_selected 14 454819 ⟨423604, by decide⟩ ⟨14, 2, 0, 423604, 454819, 1101, 4096⟩
    (by decide) selected_cut_16648

theorem unmarked_context_13_113704_423605 : frontier 8 ⟨423605, by decide⟩
    (prefixCache 13 113704) (prefixPartial 13 113704) = false := by
  decide +kernel

theorem node_context_13_113704_423605 : EJMOriginalGlobalDAGData.nodes 8 ⟨423605, by decide⟩ =
    .split (coordinate 13) (![⟨423536, by decide⟩,⟨423562, by decide⟩,⟨423582, by decide⟩,⟨423604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113704_423605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113704 ⟨423605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113704
    ⟨423605, by decide⟩ (by decide) (![⟨423536, by decide⟩,⟨423562, by decide⟩,⟨423582, by decide⟩,⟨423604, by decide⟩]) unmarked_context_13_113704_423605 node_context_13_113704_423605
  intro a
  fin_cases a
  · exact context_14_454816_423536
  · exact context_14_454817_423562
  · exact context_14_454818_423582
  · exact context_14_454819_423604

theorem selected_cut_16649 : selected 7 ⟨423629, by decide⟩
    (prefixPartial 14 454820) = some ⟨14, 2, 0, 423629, 454820, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_454820_423629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454820 ⟨423629, by decide⟩ :=
  accepted_of_selected 14 454820 ⟨423629, by decide⟩ ⟨14, 2, 0, 423629, 454820, 1301, 4096⟩
    (by decide) selected_cut_16649

theorem selected_cut_16650 : selected 7 ⟨423651, by decide⟩
    (prefixPartial 14 454821) = some ⟨14, 2, 0, 423651, 454821, 993, 4096⟩ := by
  decide +kernel

theorem context_14_454821_423651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454821 ⟨423651, by decide⟩ :=
  accepted_of_selected 14 454821 ⟨423651, by decide⟩ ⟨14, 2, 0, 423651, 454821, 993, 4096⟩
    (by decide) selected_cut_16650

theorem selected_cut_16651 : selected 7 ⟨423672, by decide⟩
    (prefixPartial 14 454822) = some ⟨14, 2, 0, 423672, 454822, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_454822_423672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454822 ⟨423672, by decide⟩ :=
  accepted_of_selected 14 454822 ⟨423672, by decide⟩ ⟨14, 2, 0, 423672, 454822, 1181, 4096⟩
    (by decide) selected_cut_16651

theorem selected_cut_16652 : selected 7 ⟨423686, by decide⟩
    (prefixPartial 14 454823) = some ⟨14, 2, 0, 423686, 454823, 873, 4096⟩ := by
  decide +kernel

theorem context_14_454823_423686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454823 ⟨423686, by decide⟩ :=
  accepted_of_selected 14 454823 ⟨423686, by decide⟩ ⟨14, 2, 0, 423686, 454823, 873, 4096⟩
    (by decide) selected_cut_16652

theorem unmarked_context_13_113705_423687 : frontier 8 ⟨423687, by decide⟩
    (prefixCache 13 113705) (prefixPartial 13 113705) = false := by
  decide +kernel

theorem node_context_13_113705_423687 : EJMOriginalGlobalDAGData.nodes 8 ⟨423687, by decide⟩ =
    .split (coordinate 13) (![⟨423629, by decide⟩,⟨423651, by decide⟩,⟨423672, by decide⟩,⟨423686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113705_423687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113705 ⟨423687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113705
    ⟨423687, by decide⟩ (by decide) (![⟨423629, by decide⟩,⟨423651, by decide⟩,⟨423672, by decide⟩,⟨423686, by decide⟩]) unmarked_context_13_113705_423687 node_context_13_113705_423687
  intro a
  fin_cases a
  · exact context_14_454820_423629
  · exact context_14_454821_423651
  · exact context_14_454822_423672
  · exact context_14_454823_423686

theorem selected_cut_16653 : selected 8 ⟨423736, by decide⟩
    (prefixPartial 13 113706) = some ⟨13, 2, 0, 423736, 113706, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_113706_423736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113706 ⟨423736, by decide⟩ :=
  accepted_of_selected 13 113706 ⟨423736, by decide⟩ ⟨13, 2, 0, 423736, 113706, 2945, 16384⟩
    (by decide) selected_cut_16653

theorem selected_cut_16654 : selected 8 ⟨423754, by decide⟩
    (prefixPartial 13 113707) = some ⟨13, 2, 0, 423754, 113707, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_113707_423754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113707 ⟨423754, by decide⟩ :=
  accepted_of_selected 13 113707 ⟨423754, by decide⟩ ⟨13, 2, 0, 423754, 113707, 1021, 16384⟩
    (by decide) selected_cut_16654

theorem unmarked_context_12_28426_423755 : frontier 9 ⟨423755, by decide⟩
    (prefixCache 12 28426) (prefixPartial 12 28426) = false := by
  decide +kernel

theorem node_context_12_28426_423755 : EJMOriginalGlobalDAGData.nodes 9 ⟨423755, by decide⟩ =
    .split (coordinate 12) (![⟨423605, by decide⟩,⟨423687, by decide⟩,⟨423736, by decide⟩,⟨423754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28426_423755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28426 ⟨423755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28426
    ⟨423755, by decide⟩ (by decide) (![⟨423605, by decide⟩,⟨423687, by decide⟩,⟨423736, by decide⟩,⟨423754, by decide⟩]) unmarked_context_12_28426_423755 node_context_12_28426_423755
  intro a
  fin_cases a
  · exact context_13_113704_423605
  · exact context_13_113705_423687
  · exact context_13_113706_423736
  · exact context_13_113707_423754

theorem selected_cut_16655 : selected 8 ⟨423834, by decide⟩
    (prefixPartial 13 113708) = some ⟨13, 2, 0, 423834, 113708, 3933, 16384⟩ := by
  decide +kernel

theorem context_13_113708_423834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113708 ⟨423834, by decide⟩ :=
  accepted_of_selected 13 113708 ⟨423834, by decide⟩ ⟨13, 2, 0, 423834, 113708, 3933, 16384⟩
    (by decide) selected_cut_16655

theorem selected_cut_16656 : selected 7 ⟨423865, by decide⟩
    (prefixPartial 14 454836) = some ⟨14, 2, 0, 423865, 454836, 1497, 4096⟩ := by
  decide +kernel

theorem context_14_454836_423865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454836 ⟨423865, by decide⟩ :=
  accepted_of_selected 14 454836 ⟨423865, by decide⟩ ⟨14, 2, 0, 423865, 454836, 1497, 4096⟩
    (by decide) selected_cut_16656

theorem selected_cut_16657 : selected 7 ⟨423895, by decide⟩
    (prefixPartial 14 454837) = some ⟨14, 2, 0, 423895, 454837, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_454837_423895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454837 ⟨423895, by decide⟩ :=
  accepted_of_selected 14 454837 ⟨423895, by decide⟩ ⟨14, 2, 0, 423895, 454837, 1121, 4096⟩
    (by decide) selected_cut_16657

theorem selected_cut_16658 : selected 7 ⟨423918, by decide⟩
    (prefixPartial 14 454838) = some ⟨14, 2, 0, 423918, 454838, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_454838_423918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454838 ⟨423918, by decide⟩ :=
  accepted_of_selected 14 454838 ⟨423918, by decide⟩ ⟨14, 2, 0, 423918, 454838, 1185, 4096⟩
    (by decide) selected_cut_16658

theorem selected_cut_16659 : selected 7 ⟨423932, by decide⟩
    (prefixPartial 14 454839) = some ⟨14, 2, 0, 423932, 454839, 977, 4096⟩ := by
  decide +kernel

theorem context_14_454839_423932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454839 ⟨423932, by decide⟩ :=
  accepted_of_selected 14 454839 ⟨423932, by decide⟩ ⟨14, 2, 0, 423932, 454839, 977, 4096⟩
    (by decide) selected_cut_16659

theorem unmarked_context_13_113709_423933 : frontier 8 ⟨423933, by decide⟩
    (prefixCache 13 113709) (prefixPartial 13 113709) = false := by
  decide +kernel

theorem node_context_13_113709_423933 : EJMOriginalGlobalDAGData.nodes 8 ⟨423933, by decide⟩ =
    .split (coordinate 13) (![⟨423865, by decide⟩,⟨423895, by decide⟩,⟨423918, by decide⟩,⟨423932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113709_423933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113709 ⟨423933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113709
    ⟨423933, by decide⟩ (by decide) (![⟨423865, by decide⟩,⟨423895, by decide⟩,⟨423918, by decide⟩,⟨423932, by decide⟩]) unmarked_context_13_113709_423933 node_context_13_113709_423933
  intro a
  fin_cases a
  · exact context_14_454836_423865
  · exact context_14_454837_423895
  · exact context_14_454838_423918
  · exact context_14_454839_423932

theorem selected_cut_16660 : selected 8 ⟨423967, by decide⟩
    (prefixPartial 13 113710) = some ⟨13, 2, 0, 423967, 113710, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_113710_423967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113710 ⟨423967, by decide⟩ :=
  accepted_of_selected 13 113710 ⟨423967, by decide⟩ ⟨13, 2, 0, 423967, 113710, 2693, 16384⟩
    (by decide) selected_cut_16660

theorem selected_cut_16661 : selected 8 ⟨423991, by decide⟩
    (prefixPartial 13 113711) = some ⟨13, 2, 0, 423991, 113711, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_113711_423991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113711 ⟨423991, by decide⟩ :=
  accepted_of_selected 13 113711 ⟨423991, by decide⟩ ⟨13, 2, 0, 423991, 113711, 1153, 16384⟩
    (by decide) selected_cut_16661

theorem unmarked_context_12_28427_423992 : frontier 9 ⟨423992, by decide⟩
    (prefixCache 12 28427) (prefixPartial 12 28427) = false := by
  decide +kernel

theorem node_context_12_28427_423992 : EJMOriginalGlobalDAGData.nodes 9 ⟨423992, by decide⟩ =
    .split (coordinate 12) (![⟨423834, by decide⟩,⟨423933, by decide⟩,⟨423967, by decide⟩,⟨423991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28427_423992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28427 ⟨423992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28427
    ⟨423992, by decide⟩ (by decide) (![⟨423834, by decide⟩,⟨423933, by decide⟩,⟨423967, by decide⟩,⟨423991, by decide⟩]) unmarked_context_12_28427_423992 node_context_12_28427_423992
  intro a
  fin_cases a
  · exact context_13_113708_423834
  · exact context_13_113709_423933
  · exact context_13_113710_423967
  · exact context_13_113711_423991

theorem unmarked_context_11_7106_423993 : frontier 10 ⟨423993, by decide⟩
    (prefixCache 11 7106) (prefixPartial 11 7106) = false := by
  decide +kernel

theorem node_context_11_7106_423993 : EJMOriginalGlobalDAGData.nodes 10 ⟨423993, by decide⟩ =
    .split (coordinate 11) (![⟨423280, by decide⟩,⟨423522, by decide⟩,⟨423755, by decide⟩,⟨423992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7106_423993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7106 ⟨423993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7106
    ⟨423993, by decide⟩ (by decide) (![⟨423280, by decide⟩,⟨423522, by decide⟩,⟨423755, by decide⟩,⟨423992, by decide⟩]) unmarked_context_11_7106_423993 node_context_11_7106_423993
  intro a
  fin_cases a
  · exact context_12_28424_423280
  · exact context_12_28425_423522
  · exact context_12_28426_423755
  · exact context_12_28427_423992

theorem selected_cut_16662 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 28428) = some ⟨12, 1, 0, 390434, 28428, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28428_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28428 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 28428 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 28428, 1, 65536⟩
    (by decide) selected_cut_16662

theorem selected_cut_16663 : selected 8 ⟨424060, by decide⟩
    (prefixPartial 13 113716) = some ⟨13, 2, 0, 424060, 113716, 3833, 16384⟩ := by
  decide +kernel

theorem context_13_113716_424060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113716 ⟨424060, by decide⟩ :=
  accepted_of_selected 13 113716 ⟨424060, by decide⟩ ⟨13, 2, 0, 424060, 113716, 3833, 16384⟩
    (by decide) selected_cut_16663

theorem selected_cut_16664 : selected 8 ⟨424143, by decide⟩
    (prefixPartial 13 113717) = some ⟨13, 2, 0, 424143, 113717, 3857, 16384⟩ := by
  decide +kernel

theorem context_13_113717_424143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113717 ⟨424143, by decide⟩ :=
  accepted_of_selected 13 113717 ⟨424143, by decide⟩ ⟨13, 2, 0, 424143, 113717, 3857, 16384⟩
    (by decide) selected_cut_16664

theorem selected_cut_16665 : selected 8 ⟨424198, by decide⟩
    (prefixPartial 13 113718) = some ⟨13, 2, 0, 424198, 113718, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_113718_424198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113718 ⟨424198, by decide⟩ :=
  accepted_of_selected 13 113718 ⟨424198, by decide⟩ ⟨13, 2, 0, 424198, 113718, 2617, 16384⟩
    (by decide) selected_cut_16665

theorem selected_cut_16666 : selected 8 ⟨424209, by decide⟩
    (prefixPartial 13 113719) = some ⟨13, 2, 0, 424209, 113719, 913, 16384⟩ := by
  decide +kernel

theorem context_13_113719_424209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113719 ⟨424209, by decide⟩ :=
  accepted_of_selected 13 113719 ⟨424209, by decide⟩ ⟨13, 2, 0, 424209, 113719, 913, 16384⟩
    (by decide) selected_cut_16666

theorem unmarked_context_12_28429_424210 : frontier 9 ⟨424210, by decide⟩
    (prefixCache 12 28429) (prefixPartial 12 28429) = false := by
  decide +kernel

theorem node_context_12_28429_424210 : EJMOriginalGlobalDAGData.nodes 9 ⟨424210, by decide⟩ =
    .split (coordinate 12) (![⟨424060, by decide⟩,⟨424143, by decide⟩,⟨424198, by decide⟩,⟨424209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28429_424210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28429 ⟨424210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28429
    ⟨424210, by decide⟩ (by decide) (![⟨424060, by decide⟩,⟨424143, by decide⟩,⟨424198, by decide⟩,⟨424209, by decide⟩]) unmarked_context_12_28429_424210 node_context_12_28429_424210
  intro a
  fin_cases a
  · exact context_13_113716_424060
  · exact context_13_113717_424143
  · exact context_13_113718_424198
  · exact context_13_113719_424209

theorem selected_cut_16667 : selected 8 ⟨424289, by decide⟩
    (prefixPartial 13 113720) = some ⟨13, 2, 0, 424289, 113720, 4069, 16384⟩ := by
  decide +kernel

theorem context_13_113720_424289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113720 ⟨424289, by decide⟩ :=
  accepted_of_selected 13 113720 ⟨424289, by decide⟩ ⟨13, 2, 0, 424289, 113720, 4069, 16384⟩
    (by decide) selected_cut_16667

theorem selected_cut_16668 : selected 8 ⟨424372, by decide⟩
    (prefixPartial 13 113721) = some ⟨13, 2, 0, 424372, 113721, 4065, 16384⟩ := by
  decide +kernel

theorem context_13_113721_424372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113721 ⟨424372, by decide⟩ :=
  accepted_of_selected 13 113721 ⟨424372, by decide⟩ ⟨13, 2, 0, 424372, 113721, 4065, 16384⟩
    (by decide) selected_cut_16668

theorem selected_cut_16669 : selected 8 ⟨424407, by decide⟩
    (prefixPartial 13 113722) = some ⟨13, 2, 0, 424407, 113722, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_113722_424407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113722 ⟨424407, by decide⟩ :=
  accepted_of_selected 13 113722 ⟨424407, by decide⟩ ⟨13, 2, 0, 424407, 113722, 2469, 16384⟩
    (by decide) selected_cut_16669

theorem selected_cut_16670 : selected 8 ⟨424413, by decide⟩
    (prefixPartial 13 113723) = some ⟨13, 2, 0, 424413, 113723, 893, 16384⟩ := by
  decide +kernel

theorem context_13_113723_424413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113723 ⟨424413, by decide⟩ :=
  accepted_of_selected 13 113723 ⟨424413, by decide⟩ ⟨13, 2, 0, 424413, 113723, 893, 16384⟩
    (by decide) selected_cut_16670

theorem unmarked_context_12_28430_424414 : frontier 9 ⟨424414, by decide⟩
    (prefixCache 12 28430) (prefixPartial 12 28430) = false := by
  decide +kernel

theorem node_context_12_28430_424414 : EJMOriginalGlobalDAGData.nodes 9 ⟨424414, by decide⟩ =
    .split (coordinate 12) (![⟨424289, by decide⟩,⟨424372, by decide⟩,⟨424407, by decide⟩,⟨424413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28430_424414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28430 ⟨424414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28430
    ⟨424414, by decide⟩ (by decide) (![⟨424289, by decide⟩,⟨424372, by decide⟩,⟨424407, by decide⟩,⟨424413, by decide⟩]) unmarked_context_12_28430_424414 node_context_12_28430_424414
  intro a
  fin_cases a
  · exact context_13_113720_424289
  · exact context_13_113721_424372
  · exact context_13_113722_424407
  · exact context_13_113723_424413

theorem selected_cut_16671 : selected 7 ⟨424419, by decide⟩
    (prefixPartial 14 454896) = some ⟨14, 2, 0, 424419, 454896, 297, 4096⟩ := by
  decide +kernel

theorem context_14_454896_424419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454896 ⟨424419, by decide⟩ :=
  accepted_of_selected 14 454896 ⟨424419, by decide⟩ ⟨14, 2, 0, 424419, 454896, 297, 4096⟩
    (by decide) selected_cut_16671

theorem selected_cut_16672 : selected 7 ⟨424460, by decide⟩
    (prefixPartial 14 454897) = some ⟨14, 2, 0, 424460, 454897, 2121, 4096⟩ := by
  decide +kernel

theorem context_14_454897_424460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454897 ⟨424460, by decide⟩ :=
  accepted_of_selected 14 454897 ⟨424460, by decide⟩ ⟨14, 2, 0, 424460, 454897, 2121, 4096⟩
    (by decide) selected_cut_16672

theorem selected_cut_16673 : selected 7 ⟨424490, by decide⟩
    (prefixPartial 14 454898) = some ⟨14, 2, 0, 424490, 454898, 1613, 4096⟩ := by
  decide +kernel

theorem context_14_454898_424490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454898 ⟨424490, by decide⟩ :=
  accepted_of_selected 14 454898 ⟨424490, by decide⟩ ⟨14, 2, 0, 424490, 454898, 1613, 4096⟩
    (by decide) selected_cut_16673

theorem selected_cut_16674 : selected 7 ⟨424521, by decide⟩
    (prefixPartial 14 454899) = some ⟨14, 2, 0, 424521, 454899, 1545, 4096⟩ := by
  decide +kernel

theorem context_14_454899_424521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454899 ⟨424521, by decide⟩ :=
  accepted_of_selected 14 454899 ⟨424521, by decide⟩ ⟨14, 2, 0, 424521, 454899, 1545, 4096⟩
    (by decide) selected_cut_16674

theorem unmarked_context_13_113724_424522 : frontier 8 ⟨424522, by decide⟩
    (prefixCache 13 113724) (prefixPartial 13 113724) = false := by
  decide +kernel

theorem node_context_13_113724_424522 : EJMOriginalGlobalDAGData.nodes 8 ⟨424522, by decide⟩ =
    .split (coordinate 13) (![⟨424419, by decide⟩,⟨424460, by decide⟩,⟨424490, by decide⟩,⟨424521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113724_424522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113724 ⟨424522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113724
    ⟨424522, by decide⟩ (by decide) (![⟨424419, by decide⟩,⟨424460, by decide⟩,⟨424490, by decide⟩,⟨424521, by decide⟩]) unmarked_context_13_113724_424522 node_context_13_113724_424522
  intro a
  fin_cases a
  · exact context_14_454896_424419
  · exact context_14_454897_424460
  · exact context_14_454898_424490
  · exact context_14_454899_424521

theorem selected_cut_16675 : selected 7 ⟨424564, by decide⟩
    (prefixPartial 14 454900) = some ⟨14, 2, 0, 424564, 454900, 2061, 4096⟩ := by
  decide +kernel

theorem context_14_454900_424564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454900 ⟨424564, by decide⟩ :=
  accepted_of_selected 14 454900 ⟨424564, by decide⟩ ⟨14, 2, 0, 424564, 454900, 2061, 4096⟩
    (by decide) selected_cut_16675

theorem selected_cut_16676 : selected 7 ⟨424609, by decide⟩
    (prefixPartial 14 454901) = some ⟨14, 2, 0, 424609, 454901, 1741, 4096⟩ := by
  decide +kernel

theorem context_14_454901_424609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454901 ⟨424609, by decide⟩ :=
  accepted_of_selected 14 454901 ⟨424609, by decide⟩ ⟨14, 2, 0, 424609, 454901, 1741, 4096⟩
    (by decide) selected_cut_16676

theorem selected_cut_16677 : selected 7 ⟨424650, by decide⟩
    (prefixPartial 14 454902) = some ⟨14, 2, 0, 424650, 454902, 1649, 4096⟩ := by
  decide +kernel

theorem context_14_454902_424650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454902 ⟨424650, by decide⟩ :=
  accepted_of_selected 14 454902 ⟨424650, by decide⟩ ⟨14, 2, 0, 424650, 454902, 1649, 4096⟩
    (by decide) selected_cut_16677

theorem selected_cut_16678 : selected 7 ⟨424682, by decide⟩
    (prefixPartial 14 454903) = some ⟨14, 2, 0, 424682, 454903, 1369, 4096⟩ := by
  decide +kernel

theorem context_14_454903_424682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454903 ⟨424682, by decide⟩ :=
  accepted_of_selected 14 454903 ⟨424682, by decide⟩ ⟨14, 2, 0, 424682, 454903, 1369, 4096⟩
    (by decide) selected_cut_16678

theorem unmarked_context_13_113725_424683 : frontier 8 ⟨424683, by decide⟩
    (prefixCache 13 113725) (prefixPartial 13 113725) = false := by
  decide +kernel

theorem node_context_13_113725_424683 : EJMOriginalGlobalDAGData.nodes 8 ⟨424683, by decide⟩ =
    .split (coordinate 13) (![⟨424564, by decide⟩,⟨424609, by decide⟩,⟨424650, by decide⟩,⟨424682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113725_424683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113725 ⟨424683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113725
    ⟨424683, by decide⟩ (by decide) (![⟨424564, by decide⟩,⟨424609, by decide⟩,⟨424650, by decide⟩,⟨424682, by decide⟩]) unmarked_context_13_113725_424683 node_context_13_113725_424683
  intro a
  fin_cases a
  · exact context_14_454900_424564
  · exact context_14_454901_424609
  · exact context_14_454902_424650
  · exact context_14_454903_424682

theorem selected_cut_16679 : selected 7 ⟨424713, by decide⟩
    (prefixPartial 14 454904) = some ⟨14, 2, 0, 424713, 454904, 1141, 4096⟩ := by
  decide +kernel

theorem context_14_454904_424713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454904 ⟨424713, by decide⟩ :=
  accepted_of_selected 14 454904 ⟨424713, by decide⟩ ⟨14, 2, 0, 424713, 454904, 1141, 4096⟩
    (by decide) selected_cut_16679

theorem selected_cut_16680 : selected 7 ⟨424759, by decide⟩
    (prefixPartial 14 454905) = some ⟨14, 2, 0, 424759, 454905, 1561, 4096⟩ := by
  decide +kernel

theorem context_14_454905_424759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454905 ⟨424759, by decide⟩ :=
  accepted_of_selected 14 454905 ⟨424759, by decide⟩ ⟨14, 2, 0, 424759, 454905, 1561, 4096⟩
    (by decide) selected_cut_16680

theorem selected_cut_16681 : selected 7 ⟨424793, by decide⟩
    (prefixPartial 14 454906) = some ⟨14, 2, 0, 424793, 454906, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_454906_424793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454906 ⟨424793, by decide⟩ :=
  accepted_of_selected 14 454906 ⟨424793, by decide⟩ ⟨14, 2, 0, 424793, 454906, 1073, 4096⟩
    (by decide) selected_cut_16681

theorem selected_cut_16682 : selected 7 ⟨424826, by decide⟩
    (prefixPartial 14 454907) = some ⟨14, 2, 0, 424826, 454907, 913, 4096⟩ := by
  decide +kernel

theorem context_14_454907_424826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454907 ⟨424826, by decide⟩ :=
  accepted_of_selected 14 454907 ⟨424826, by decide⟩ ⟨14, 2, 0, 424826, 454907, 913, 4096⟩
    (by decide) selected_cut_16682

theorem unmarked_context_13_113726_424827 : frontier 8 ⟨424827, by decide⟩
    (prefixCache 13 113726) (prefixPartial 13 113726) = false := by
  decide +kernel

theorem node_context_13_113726_424827 : EJMOriginalGlobalDAGData.nodes 8 ⟨424827, by decide⟩ =
    .split (coordinate 13) (![⟨424713, by decide⟩,⟨424759, by decide⟩,⟨424793, by decide⟩,⟨424826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113726_424827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113726 ⟨424827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113726
    ⟨424827, by decide⟩ (by decide) (![⟨424713, by decide⟩,⟨424759, by decide⟩,⟨424793, by decide⟩,⟨424826, by decide⟩]) unmarked_context_13_113726_424827 node_context_13_113726_424827
  intro a
  fin_cases a
  · exact context_14_454904_424713
  · exact context_14_454905_424759
  · exact context_14_454906_424793
  · exact context_14_454907_424826

theorem selected_cut_16683 : selected 8 ⟨424898, by decide⟩
    (prefixPartial 13 113727) = some ⟨13, 2, 0, 424898, 113727, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_113727_424898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113727 ⟨424898, by decide⟩ :=
  accepted_of_selected 13 113727 ⟨424898, by decide⟩ ⟨13, 2, 0, 424898, 113727, 1745, 16384⟩
    (by decide) selected_cut_16683

theorem unmarked_context_12_28431_424899 : frontier 9 ⟨424899, by decide⟩
    (prefixCache 12 28431) (prefixPartial 12 28431) = false := by
  decide +kernel

theorem node_context_12_28431_424899 : EJMOriginalGlobalDAGData.nodes 9 ⟨424899, by decide⟩ =
    .split (coordinate 12) (![⟨424522, by decide⟩,⟨424683, by decide⟩,⟨424827, by decide⟩,⟨424898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28431_424899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28431 ⟨424899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28431
    ⟨424899, by decide⟩ (by decide) (![⟨424522, by decide⟩,⟨424683, by decide⟩,⟨424827, by decide⟩,⟨424898, by decide⟩]) unmarked_context_12_28431_424899 node_context_12_28431_424899
  intro a
  fin_cases a
  · exact context_13_113724_424522
  · exact context_13_113725_424683
  · exact context_13_113726_424827
  · exact context_13_113727_424898

theorem unmarked_context_11_7107_424900 : frontier 10 ⟨424900, by decide⟩
    (prefixCache 11 7107) (prefixPartial 11 7107) = false := by
  decide +kernel

theorem node_context_11_7107_424900 : EJMOriginalGlobalDAGData.nodes 10 ⟨424900, by decide⟩ =
    .split (coordinate 11) (![⟨390434, by decide⟩,⟨424210, by decide⟩,⟨424414, by decide⟩,⟨424899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7107_424900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7107 ⟨424900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7107
    ⟨424900, by decide⟩ (by decide) (![⟨390434, by decide⟩,⟨424210, by decide⟩,⟨424414, by decide⟩,⟨424899, by decide⟩]) unmarked_context_11_7107_424900 node_context_11_7107_424900
  intro a
  fin_cases a
  · exact context_12_28428_390434
  · exact context_12_28429_424210
  · exact context_12_28430_424414
  · exact context_12_28431_424899

theorem unmarked_context_10_1776_424901 : frontier 11 ⟨424901, by decide⟩
    (prefixCache 10 1776) (prefixPartial 10 1776) = false := by
  decide +kernel

theorem node_context_10_1776_424901 : EJMOriginalGlobalDAGData.nodes 11 ⟨424901, by decide⟩ =
    .split (coordinate 10) (![⟨422001, by decide⟩,⟨422965, by decide⟩,⟨423993, by decide⟩,⟨424900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1776_424901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1776 ⟨424901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1776
    ⟨424901, by decide⟩ (by decide) (![⟨422001, by decide⟩,⟨422965, by decide⟩,⟨423993, by decide⟩,⟨424900, by decide⟩]) unmarked_context_10_1776_424901 node_context_10_1776_424901
  intro a
  fin_cases a
  · exact context_11_7104_422001
  · exact context_11_7105_422965
  · exact context_11_7106_423993
  · exact context_11_7107_424900

theorem selected_cut_16684 : selected 8 ⟨424930, by decide⟩
    (prefixPartial 13 113728) = some ⟨13, 2, 0, 424930, 113728, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_113728_424930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113728 ⟨424930, by decide⟩ :=
  accepted_of_selected 13 113728 ⟨424930, by decide⟩ ⟨13, 2, 0, 424930, 113728, 2293, 16384⟩
    (by decide) selected_cut_16684

theorem selected_cut_16685 : selected 8 ⟨424962, by decide⟩
    (prefixPartial 13 113729) = some ⟨13, 2, 0, 424962, 113729, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_113729_424962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113729 ⟨424962, by decide⟩ :=
  accepted_of_selected 13 113729 ⟨424962, by decide⟩ ⟨13, 2, 0, 424962, 113729, 2241, 16384⟩
    (by decide) selected_cut_16685

theorem selected_cut_16686 : selected 8 ⟨424981, by decide⟩
    (prefixPartial 13 113730) = some ⟨13, 2, 0, 424981, 113730, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_113730_424981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113730 ⟨424981, by decide⟩ :=
  accepted_of_selected 13 113730 ⟨424981, by decide⟩ ⟨13, 2, 0, 424981, 113730, 1461, 16384⟩
    (by decide) selected_cut_16686

theorem selected_cut_16687 : selected 8 ⟨424988, by decide⟩
    (prefixPartial 13 113731) = some ⟨13, 2, 0, 424988, 113731, 649, 16384⟩ := by
  decide +kernel

theorem context_13_113731_424988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113731 ⟨424988, by decide⟩ :=
  accepted_of_selected 13 113731 ⟨424988, by decide⟩ ⟨13, 2, 0, 424988, 113731, 649, 16384⟩
    (by decide) selected_cut_16687

theorem unmarked_context_12_28432_424989 : frontier 9 ⟨424989, by decide⟩
    (prefixCache 12 28432) (prefixPartial 12 28432) = false := by
  decide +kernel

theorem node_context_12_28432_424989 : EJMOriginalGlobalDAGData.nodes 9 ⟨424989, by decide⟩ =
    .split (coordinate 12) (![⟨424930, by decide⟩,⟨424962, by decide⟩,⟨424981, by decide⟩,⟨424988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28432_424989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28432 ⟨424989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28432
    ⟨424989, by decide⟩ (by decide) (![⟨424930, by decide⟩,⟨424962, by decide⟩,⟨424981, by decide⟩,⟨424988, by decide⟩]) unmarked_context_12_28432_424989 node_context_12_28432_424989
  intro a
  fin_cases a
  · exact context_13_113728_424930
  · exact context_13_113729_424962
  · exact context_13_113730_424981
  · exact context_13_113731_424988

theorem selected_cut_16688 : selected 8 ⟨425035, by decide⟩
    (prefixPartial 13 113732) = some ⟨13, 2, 0, 425035, 113732, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_113732_425035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113732 ⟨425035, by decide⟩ :=
  accepted_of_selected 13 113732 ⟨425035, by decide⟩ ⟨13, 2, 0, 425035, 113732, 2877, 16384⟩
    (by decide) selected_cut_16688

theorem selected_cut_16689 : selected 8 ⟨425081, by decide⟩
    (prefixPartial 13 113733) = some ⟨13, 2, 0, 425081, 113733, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_113733_425081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113733 ⟨425081, by decide⟩ :=
  accepted_of_selected 13 113733 ⟨425081, by decide⟩ ⟨13, 2, 0, 425081, 113733, 2413, 16384⟩
    (by decide) selected_cut_16689

theorem selected_cut_16690 : selected 8 ⟨425115, by decide⟩
    (prefixPartial 13 113734) = some ⟨13, 2, 0, 425115, 113734, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_113734_425115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113734 ⟨425115, by decide⟩ :=
  accepted_of_selected 13 113734 ⟨425115, by decide⟩ ⟨13, 2, 0, 425115, 113734, 1805, 16384⟩
    (by decide) selected_cut_16690

theorem selected_cut_16691 : selected 8 ⟨425123, by decide⟩
    (prefixPartial 13 113735) = some ⟨13, 2, 0, 425123, 113735, 669, 16384⟩ := by
  decide +kernel

theorem context_13_113735_425123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113735 ⟨425123, by decide⟩ :=
  accepted_of_selected 13 113735 ⟨425123, by decide⟩ ⟨13, 2, 0, 425123, 113735, 669, 16384⟩
    (by decide) selected_cut_16691

theorem unmarked_context_12_28433_425124 : frontier 9 ⟨425124, by decide⟩
    (prefixCache 12 28433) (prefixPartial 12 28433) = false := by
  decide +kernel

theorem node_context_12_28433_425124 : EJMOriginalGlobalDAGData.nodes 9 ⟨425124, by decide⟩ =
    .split (coordinate 12) (![⟨425035, by decide⟩,⟨425081, by decide⟩,⟨425115, by decide⟩,⟨425123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28433_425124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28433 ⟨425124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28433
    ⟨425124, by decide⟩ (by decide) (![⟨425035, by decide⟩,⟨425081, by decide⟩,⟨425115, by decide⟩,⟨425123, by decide⟩]) unmarked_context_12_28433_425124 node_context_12_28433_425124
  intro a
  fin_cases a
  · exact context_13_113732_425035
  · exact context_13_113733_425081
  · exact context_13_113734_425115
  · exact context_13_113735_425123

theorem selected_cut_16692 : selected 8 ⟨425173, by decide⟩
    (prefixPartial 13 113736) = some ⟨13, 2, 0, 425173, 113736, 2989, 16384⟩ := by
  decide +kernel

theorem context_13_113736_425173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113736 ⟨425173, by decide⟩ :=
  accepted_of_selected 13 113736 ⟨425173, by decide⟩ ⟨13, 2, 0, 425173, 113736, 2989, 16384⟩
    (by decide) selected_cut_16692

theorem selected_cut_16693 : selected 8 ⟨425210, by decide⟩
    (prefixPartial 13 113737) = some ⟨13, 2, 0, 425210, 113737, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_113737_425210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113737 ⟨425210, by decide⟩ :=
  accepted_of_selected 13 113737 ⟨425210, by decide⟩ ⟨13, 2, 0, 425210, 113737, 2649, 16384⟩
    (by decide) selected_cut_16693

theorem selected_cut_16694 : selected 8 ⟨425242, by decide⟩
    (prefixPartial 13 113738) = some ⟨13, 2, 0, 425242, 113738, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_113738_425242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113738 ⟨425242, by decide⟩ :=
  accepted_of_selected 13 113738 ⟨425242, by decide⟩ ⟨13, 2, 0, 425242, 113738, 1909, 16384⟩
    (by decide) selected_cut_16694

theorem selected_cut_16695 : selected 8 ⟨425247, by decide⟩
    (prefixPartial 13 113739) = some ⟨13, 2, 0, 425247, 113739, 709, 16384⟩ := by
  decide +kernel

theorem context_13_113739_425247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113739 ⟨425247, by decide⟩ :=
  accepted_of_selected 13 113739 ⟨425247, by decide⟩ ⟨13, 2, 0, 425247, 113739, 709, 16384⟩
    (by decide) selected_cut_16695

theorem unmarked_context_12_28434_425248 : frontier 9 ⟨425248, by decide⟩
    (prefixCache 12 28434) (prefixPartial 12 28434) = false := by
  decide +kernel

theorem node_context_12_28434_425248 : EJMOriginalGlobalDAGData.nodes 9 ⟨425248, by decide⟩ =
    .split (coordinate 12) (![⟨425173, by decide⟩,⟨425210, by decide⟩,⟨425242, by decide⟩,⟨425247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28434_425248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28434 ⟨425248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28434
    ⟨425248, by decide⟩ (by decide) (![⟨425173, by decide⟩,⟨425210, by decide⟩,⟨425242, by decide⟩,⟨425247, by decide⟩]) unmarked_context_12_28434_425248 node_context_12_28434_425248
  intro a
  fin_cases a
  · exact context_13_113736_425173
  · exact context_13_113737_425210
  · exact context_13_113738_425242
  · exact context_13_113739_425247

theorem selected_cut_16696 : selected 8 ⟨425279, by decide⟩
    (prefixPartial 13 113740) = some ⟨13, 2, 0, 425279, 113740, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_113740_425279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113740 ⟨425279, by decide⟩ :=
  accepted_of_selected 13 113740 ⟨425279, by decide⟩ ⟨13, 2, 0, 425279, 113740, 2665, 16384⟩
    (by decide) selected_cut_16696

theorem selected_cut_16697 : selected 8 ⟨425319, by decide⟩
    (prefixPartial 13 113741) = some ⟨13, 2, 0, 425319, 113741, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_113741_425319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113741 ⟨425319, by decide⟩ :=
  accepted_of_selected 13 113741 ⟨425319, by decide⟩ ⟨13, 2, 0, 425319, 113741, 2645, 16384⟩
    (by decide) selected_cut_16697

theorem selected_cut_16698 : selected 8 ⟨425340, by decide⟩
    (prefixPartial 13 113742) = some ⟨13, 2, 0, 425340, 113742, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_113742_425340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113742 ⟨425340, by decide⟩ :=
  accepted_of_selected 13 113742 ⟨425340, by decide⟩ ⟨13, 2, 0, 425340, 113742, 1949, 16384⟩
    (by decide) selected_cut_16698

theorem selected_cut_16699 : selected 8 ⟨425346, by decide⟩
    (prefixPartial 13 113743) = some ⟨13, 2, 0, 425346, 113743, 813, 16384⟩ := by
  decide +kernel

theorem context_13_113743_425346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113743 ⟨425346, by decide⟩ :=
  accepted_of_selected 13 113743 ⟨425346, by decide⟩ ⟨13, 2, 0, 425346, 113743, 813, 16384⟩
    (by decide) selected_cut_16699

theorem unmarked_context_12_28435_425347 : frontier 9 ⟨425347, by decide⟩
    (prefixCache 12 28435) (prefixPartial 12 28435) = false := by
  decide +kernel

theorem node_context_12_28435_425347 : EJMOriginalGlobalDAGData.nodes 9 ⟨425347, by decide⟩ =
    .split (coordinate 12) (![⟨425279, by decide⟩,⟨425319, by decide⟩,⟨425340, by decide⟩,⟨425346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28435_425347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28435 ⟨425347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28435
    ⟨425347, by decide⟩ (by decide) (![⟨425279, by decide⟩,⟨425319, by decide⟩,⟨425340, by decide⟩,⟨425346, by decide⟩]) unmarked_context_12_28435_425347 node_context_12_28435_425347
  intro a
  fin_cases a
  · exact context_13_113740_425279
  · exact context_13_113741_425319
  · exact context_13_113742_425340
  · exact context_13_113743_425346

theorem unmarked_context_11_7108_425348 : frontier 10 ⟨425348, by decide⟩
    (prefixCache 11 7108) (prefixPartial 11 7108) = false := by
  decide +kernel

theorem node_context_11_7108_425348 : EJMOriginalGlobalDAGData.nodes 10 ⟨425348, by decide⟩ =
    .split (coordinate 11) (![⟨424989, by decide⟩,⟨425124, by decide⟩,⟨425248, by decide⟩,⟨425347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7108_425348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7108 ⟨425348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7108
    ⟨425348, by decide⟩ (by decide) (![⟨424989, by decide⟩,⟨425124, by decide⟩,⟨425248, by decide⟩,⟨425347, by decide⟩]) unmarked_context_11_7108_425348 node_context_11_7108_425348
  intro a
  fin_cases a
  · exact context_12_28432_424989
  · exact context_12_28433_425124
  · exact context_12_28434_425248
  · exact context_12_28435_425347

theorem selected_cut_16700 : selected 8 ⟨425381, by decide⟩
    (prefixPartial 13 113744) = some ⟨13, 2, 0, 425381, 113744, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_113744_425381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113744 ⟨425381, by decide⟩ :=
  accepted_of_selected 13 113744 ⟨425381, by decide⟩ ⟨13, 2, 0, 425381, 113744, 2117, 16384⟩
    (by decide) selected_cut_16700

theorem selected_cut_16701 : selected 8 ⟨425420, by decide⟩
    (prefixPartial 13 113745) = some ⟨13, 2, 0, 425420, 113745, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_113745_425420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113745 ⟨425420, by decide⟩ :=
  accepted_of_selected 13 113745 ⟨425420, by decide⟩ ⟨13, 2, 0, 425420, 113745, 2641, 16384⟩
    (by decide) selected_cut_16701

theorem selected_cut_16702 : selected 8 ⟨425448, by decide⟩
    (prefixPartial 13 113746) = some ⟨13, 2, 0, 425448, 113746, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_113746_425448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113746 ⟨425448, by decide⟩ :=
  accepted_of_selected 13 113746 ⟨425448, by decide⟩ ⟨13, 2, 0, 425448, 113746, 1697, 16384⟩
    (by decide) selected_cut_16702

theorem selected_cut_16703 : selected 8 ⟨425453, by decide⟩
    (prefixPartial 13 113747) = some ⟨13, 2, 0, 425453, 113747, 633, 16384⟩ := by
  decide +kernel

theorem context_13_113747_425453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113747 ⟨425453, by decide⟩ :=
  accepted_of_selected 13 113747 ⟨425453, by decide⟩ ⟨13, 2, 0, 425453, 113747, 633, 16384⟩
    (by decide) selected_cut_16703

theorem unmarked_context_12_28436_425454 : frontier 9 ⟨425454, by decide⟩
    (prefixCache 12 28436) (prefixPartial 12 28436) = false := by
  decide +kernel

theorem node_context_12_28436_425454 : EJMOriginalGlobalDAGData.nodes 9 ⟨425454, by decide⟩ =
    .split (coordinate 12) (![⟨425381, by decide⟩,⟨425420, by decide⟩,⟨425448, by decide⟩,⟨425453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28436_425454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28436 ⟨425454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28436
    ⟨425454, by decide⟩ (by decide) (![⟨425381, by decide⟩,⟨425420, by decide⟩,⟨425448, by decide⟩,⟨425453, by decide⟩]) unmarked_context_12_28436_425454 node_context_12_28436_425454
  intro a
  fin_cases a
  · exact context_13_113744_425381
  · exact context_13_113745_425420
  · exact context_13_113746_425448
  · exact context_13_113747_425453

theorem selected_cut_16704 : selected 8 ⟨425493, by decide⟩
    (prefixPartial 13 113748) = some ⟨13, 2, 0, 425493, 113748, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_113748_425493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113748 ⟨425493, by decide⟩ :=
  accepted_of_selected 13 113748 ⟨425493, by decide⟩ ⟨13, 2, 0, 425493, 113748, 2617, 16384⟩
    (by decide) selected_cut_16704

theorem selected_cut_16705 : selected 8 ⟨425532, by decide⟩
    (prefixPartial 13 113749) = some ⟨13, 2, 0, 425532, 113749, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_113749_425532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113749 ⟨425532, by decide⟩ :=
  accepted_of_selected 13 113749 ⟨425532, by decide⟩ ⟨13, 2, 0, 425532, 113749, 2517, 16384⟩
    (by decide) selected_cut_16705

theorem selected_cut_16706 : selected 8 ⟨425556, by decide⟩
    (prefixPartial 13 113750) = some ⟨13, 2, 0, 425556, 113750, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_113750_425556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113750 ⟨425556, by decide⟩ :=
  accepted_of_selected 13 113750 ⟨425556, by decide⟩ ⟨13, 2, 0, 425556, 113750, 1833, 16384⟩
    (by decide) selected_cut_16706

theorem selected_cut_16707 : selected 8 ⟨425564, by decide⟩
    (prefixPartial 13 113751) = some ⟨13, 2, 0, 425564, 113751, 713, 16384⟩ := by
  decide +kernel

theorem context_13_113751_425564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113751 ⟨425564, by decide⟩ :=
  accepted_of_selected 13 113751 ⟨425564, by decide⟩ ⟨13, 2, 0, 425564, 113751, 713, 16384⟩
    (by decide) selected_cut_16707

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
