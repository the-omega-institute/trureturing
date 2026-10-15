/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover173
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_28437_425565 : frontier 9 ⟨425565, by decide⟩
    (prefixCache 12 28437) (prefixPartial 12 28437) = false := by
  decide +kernel

theorem node_context_12_28437_425565 : EJMOriginalGlobalDAGData.nodes 9 ⟨425565, by decide⟩ =
    .split (coordinate 12) (![⟨425493, by decide⟩,⟨425532, by decide⟩,⟨425556, by decide⟩,⟨425564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28437_425565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28437 ⟨425565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28437
    ⟨425565, by decide⟩ (by decide) (![⟨425493, by decide⟩,⟨425532, by decide⟩,⟨425556, by decide⟩,⟨425564, by decide⟩]) unmarked_context_12_28437_425565 node_context_12_28437_425565
  intro a
  fin_cases a
  · exact context_13_113748_425493
  · exact context_13_113749_425532
  · exact context_13_113750_425556
  · exact context_13_113751_425564

theorem selected_cut_16708 : selected 8 ⟨425607, by decide⟩
    (prefixPartial 13 113752) = some ⟨13, 2, 0, 425607, 113752, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_113752_425607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113752 ⟨425607, by decide⟩ :=
  accepted_of_selected 13 113752 ⟨425607, by decide⟩ ⟨13, 2, 0, 425607, 113752, 2781, 16384⟩
    (by decide) selected_cut_16708

theorem selected_cut_16709 : selected 8 ⟨425648, by decide⟩
    (prefixPartial 13 113753) = some ⟨13, 2, 0, 425648, 113753, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_113753_425648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113753 ⟨425648, by decide⟩ :=
  accepted_of_selected 13 113753 ⟨425648, by decide⟩ ⟨13, 2, 0, 425648, 113753, 2729, 16384⟩
    (by decide) selected_cut_16709

theorem selected_cut_16710 : selected 8 ⟨425673, by decide⟩
    (prefixPartial 13 113754) = some ⟨13, 2, 0, 425673, 113754, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_113754_425673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113754 ⟨425673, by decide⟩ :=
  accepted_of_selected 13 113754 ⟨425673, by decide⟩ ⟨13, 2, 0, 425673, 113754, 1901, 16384⟩
    (by decide) selected_cut_16710

theorem selected_cut_16711 : selected 8 ⟨425681, by decide⟩
    (prefixPartial 13 113755) = some ⟨13, 2, 0, 425681, 113755, 785, 16384⟩ := by
  decide +kernel

theorem context_13_113755_425681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113755 ⟨425681, by decide⟩ :=
  accepted_of_selected 13 113755 ⟨425681, by decide⟩ ⟨13, 2, 0, 425681, 113755, 785, 16384⟩
    (by decide) selected_cut_16711

theorem unmarked_context_12_28438_425682 : frontier 9 ⟨425682, by decide⟩
    (prefixCache 12 28438) (prefixPartial 12 28438) = false := by
  decide +kernel

theorem node_context_12_28438_425682 : EJMOriginalGlobalDAGData.nodes 9 ⟨425682, by decide⟩ =
    .split (coordinate 12) (![⟨425607, by decide⟩,⟨425648, by decide⟩,⟨425673, by decide⟩,⟨425681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28438_425682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28438 ⟨425682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28438
    ⟨425682, by decide⟩ (by decide) (![⟨425607, by decide⟩,⟨425648, by decide⟩,⟨425673, by decide⟩,⟨425681, by decide⟩]) unmarked_context_12_28438_425682 node_context_12_28438_425682
  intro a
  fin_cases a
  · exact context_13_113752_425607
  · exact context_13_113753_425648
  · exact context_13_113754_425673
  · exact context_13_113755_425681

theorem selected_cut_16712 : selected 8 ⟨425714, by decide⟩
    (prefixPartial 13 113756) = some ⟨13, 2, 0, 425714, 113756, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_113756_425714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113756 ⟨425714, by decide⟩ :=
  accepted_of_selected 13 113756 ⟨425714, by decide⟩ ⟨13, 2, 0, 425714, 113756, 2437, 16384⟩
    (by decide) selected_cut_16712

theorem selected_cut_16713 : selected 8 ⟨425755, by decide⟩
    (prefixPartial 13 113757) = some ⟨13, 2, 0, 425755, 113757, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_113757_425755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113757 ⟨425755, by decide⟩ :=
  accepted_of_selected 13 113757 ⟨425755, by decide⟩ ⟨13, 2, 0, 425755, 113757, 2753, 16384⟩
    (by decide) selected_cut_16713

theorem selected_cut_16714 : selected 8 ⟨425781, by decide⟩
    (prefixPartial 13 113758) = some ⟨13, 2, 0, 425781, 113758, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_113758_425781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113758 ⟨425781, by decide⟩ :=
  accepted_of_selected 13 113758 ⟨425781, by decide⟩ ⟨13, 2, 0, 425781, 113758, 2049, 16384⟩
    (by decide) selected_cut_16714

theorem selected_cut_16715 : selected 8 ⟨425786, by decide⟩
    (prefixPartial 13 113759) = some ⟨13, 2, 0, 425786, 113759, 857, 16384⟩ := by
  decide +kernel

theorem context_13_113759_425786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113759 ⟨425786, by decide⟩ :=
  accepted_of_selected 13 113759 ⟨425786, by decide⟩ ⟨13, 2, 0, 425786, 113759, 857, 16384⟩
    (by decide) selected_cut_16715

theorem unmarked_context_12_28439_425787 : frontier 9 ⟨425787, by decide⟩
    (prefixCache 12 28439) (prefixPartial 12 28439) = false := by
  decide +kernel

theorem node_context_12_28439_425787 : EJMOriginalGlobalDAGData.nodes 9 ⟨425787, by decide⟩ =
    .split (coordinate 12) (![⟨425714, by decide⟩,⟨425755, by decide⟩,⟨425781, by decide⟩,⟨425786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28439_425787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28439 ⟨425787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28439
    ⟨425787, by decide⟩ (by decide) (![⟨425714, by decide⟩,⟨425755, by decide⟩,⟨425781, by decide⟩,⟨425786, by decide⟩]) unmarked_context_12_28439_425787 node_context_12_28439_425787
  intro a
  fin_cases a
  · exact context_13_113756_425714
  · exact context_13_113757_425755
  · exact context_13_113758_425781
  · exact context_13_113759_425786

theorem unmarked_context_11_7109_425788 : frontier 10 ⟨425788, by decide⟩
    (prefixCache 11 7109) (prefixPartial 11 7109) = false := by
  decide +kernel

theorem node_context_11_7109_425788 : EJMOriginalGlobalDAGData.nodes 10 ⟨425788, by decide⟩ =
    .split (coordinate 11) (![⟨425454, by decide⟩,⟨425565, by decide⟩,⟨425682, by decide⟩,⟨425787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7109_425788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7109 ⟨425788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7109
    ⟨425788, by decide⟩ (by decide) (![⟨425454, by decide⟩,⟨425565, by decide⟩,⟨425682, by decide⟩,⟨425787, by decide⟩]) unmarked_context_11_7109_425788 node_context_11_7109_425788
  intro a
  fin_cases a
  · exact context_12_28436_425454
  · exact context_12_28437_425565
  · exact context_12_28438_425682
  · exact context_12_28439_425787

theorem selected_cut_16716 : selected 8 ⟨425817, by decide⟩
    (prefixPartial 13 113760) = some ⟨13, 2, 0, 425817, 113760, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_113760_425817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113760 ⟨425817, by decide⟩ :=
  accepted_of_selected 13 113760 ⟨425817, by decide⟩ ⟨13, 2, 0, 425817, 113760, 1953, 16384⟩
    (by decide) selected_cut_16716

theorem selected_cut_16717 : selected 8 ⟨425865, by decide⟩
    (prefixPartial 13 113761) = some ⟨13, 2, 0, 425865, 113761, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_113761_425865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113761 ⟨425865, by decide⟩ :=
  accepted_of_selected 13 113761 ⟨425865, by decide⟩ ⟨13, 2, 0, 425865, 113761, 2617, 16384⟩
    (by decide) selected_cut_16717

theorem selected_cut_16718 : selected 8 ⟨425888, by decide⟩
    (prefixPartial 13 113762) = some ⟨13, 2, 0, 425888, 113762, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_113762_425888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113762 ⟨425888, by decide⟩ :=
  accepted_of_selected 13 113762 ⟨425888, by decide⟩ ⟨13, 2, 0, 425888, 113762, 1601, 16384⟩
    (by decide) selected_cut_16718

theorem selected_cut_16719 : selected 8 ⟨425892, by decide⟩
    (prefixPartial 13 113763) = some ⟨13, 2, 0, 425892, 113763, 601, 16384⟩ := by
  decide +kernel

theorem context_13_113763_425892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113763 ⟨425892, by decide⟩ :=
  accepted_of_selected 13 113763 ⟨425892, by decide⟩ ⟨13, 2, 0, 425892, 113763, 601, 16384⟩
    (by decide) selected_cut_16719

theorem unmarked_context_12_28440_425893 : frontier 9 ⟨425893, by decide⟩
    (prefixCache 12 28440) (prefixPartial 12 28440) = false := by
  decide +kernel

theorem node_context_12_28440_425893 : EJMOriginalGlobalDAGData.nodes 9 ⟨425893, by decide⟩ =
    .split (coordinate 12) (![⟨425817, by decide⟩,⟨425865, by decide⟩,⟨425888, by decide⟩,⟨425892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28440_425893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28440 ⟨425893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28440
    ⟨425893, by decide⟩ (by decide) (![⟨425817, by decide⟩,⟨425865, by decide⟩,⟨425888, by decide⟩,⟨425892, by decide⟩]) unmarked_context_12_28440_425893 node_context_12_28440_425893
  intro a
  fin_cases a
  · exact context_13_113760_425817
  · exact context_13_113761_425865
  · exact context_13_113762_425888
  · exact context_13_113763_425892

theorem selected_cut_16720 : selected 8 ⟨425929, by decide⟩
    (prefixPartial 13 113764) = some ⟨13, 2, 0, 425929, 113764, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_113764_425929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113764 ⟨425929, by decide⟩ :=
  accepted_of_selected 13 113764 ⟨425929, by decide⟩ ⟨13, 2, 0, 425929, 113764, 2269, 16384⟩
    (by decide) selected_cut_16720

theorem selected_cut_16721 : selected 8 ⟨425974, by decide⟩
    (prefixPartial 13 113765) = some ⟨13, 2, 0, 425974, 113765, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_113765_425974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113765 ⟨425974, by decide⟩ :=
  accepted_of_selected 13 113765 ⟨425974, by decide⟩ ⟨13, 2, 0, 425974, 113765, 2581, 16384⟩
    (by decide) selected_cut_16721

theorem selected_cut_16722 : selected 8 ⟨425994, by decide⟩
    (prefixPartial 13 113766) = some ⟨13, 2, 0, 425994, 113766, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_113766_425994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113766 ⟨425994, by decide⟩ :=
  accepted_of_selected 13 113766 ⟨425994, by decide⟩ ⟨13, 2, 0, 425994, 113766, 1581, 16384⟩
    (by decide) selected_cut_16722

theorem selected_cut_16723 : selected 8 ⟨426004, by decide⟩
    (prefixPartial 13 113767) = some ⟨13, 2, 0, 426004, 113767, 717, 16384⟩ := by
  decide +kernel

theorem context_13_113767_426004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113767 ⟨426004, by decide⟩ :=
  accepted_of_selected 13 113767 ⟨426004, by decide⟩ ⟨13, 2, 0, 426004, 113767, 717, 16384⟩
    (by decide) selected_cut_16723

theorem unmarked_context_12_28441_426005 : frontier 9 ⟨426005, by decide⟩
    (prefixCache 12 28441) (prefixPartial 12 28441) = false := by
  decide +kernel

theorem node_context_12_28441_426005 : EJMOriginalGlobalDAGData.nodes 9 ⟨426005, by decide⟩ =
    .split (coordinate 12) (![⟨425929, by decide⟩,⟨425974, by decide⟩,⟨425994, by decide⟩,⟨426004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28441_426005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28441 ⟨426005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28441
    ⟨426005, by decide⟩ (by decide) (![⟨425929, by decide⟩,⟨425974, by decide⟩,⟨425994, by decide⟩,⟨426004, by decide⟩]) unmarked_context_12_28441_426005 node_context_12_28441_426005
  intro a
  fin_cases a
  · exact context_13_113764_425929
  · exact context_13_113765_425974
  · exact context_13_113766_425994
  · exact context_13_113767_426004

theorem selected_cut_16724 : selected 8 ⟨426043, by decide⟩
    (prefixPartial 13 113768) = some ⟨13, 2, 0, 426043, 113768, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_113768_426043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113768 ⟨426043, by decide⟩ :=
  accepted_of_selected 13 113768 ⟨426043, by decide⟩ ⟨13, 2, 0, 426043, 113768, 2249, 16384⟩
    (by decide) selected_cut_16724

theorem selected_cut_16725 : selected 8 ⟨426088, by decide⟩
    (prefixPartial 13 113769) = some ⟨13, 2, 0, 426088, 113769, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_113769_426088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113769 ⟨426088, by decide⟩ :=
  accepted_of_selected 13 113769 ⟨426088, by decide⟩ ⟨13, 2, 0, 426088, 113769, 2677, 16384⟩
    (by decide) selected_cut_16725

theorem selected_cut_16726 : selected 8 ⟨426109, by decide⟩
    (prefixPartial 13 113770) = some ⟨13, 2, 0, 426109, 113770, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_113770_426109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113770 ⟨426109, by decide⟩ :=
  accepted_of_selected 13 113770 ⟨426109, by decide⟩ ⟨13, 2, 0, 426109, 113770, 1657, 16384⟩
    (by decide) selected_cut_16726

theorem selected_cut_16727 : selected 8 ⟨426116, by decide⟩
    (prefixPartial 13 113771) = some ⟨13, 2, 0, 426116, 113771, 689, 16384⟩ := by
  decide +kernel

theorem context_13_113771_426116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113771 ⟨426116, by decide⟩ :=
  accepted_of_selected 13 113771 ⟨426116, by decide⟩ ⟨13, 2, 0, 426116, 113771, 689, 16384⟩
    (by decide) selected_cut_16727

theorem unmarked_context_12_28442_426117 : frontier 9 ⟨426117, by decide⟩
    (prefixCache 12 28442) (prefixPartial 12 28442) = false := by
  decide +kernel

theorem node_context_12_28442_426117 : EJMOriginalGlobalDAGData.nodes 9 ⟨426117, by decide⟩ =
    .split (coordinate 12) (![⟨426043, by decide⟩,⟨426088, by decide⟩,⟨426109, by decide⟩,⟨426116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28442_426117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28442 ⟨426117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28442
    ⟨426117, by decide⟩ (by decide) (![⟨426043, by decide⟩,⟨426088, by decide⟩,⟨426109, by decide⟩,⟨426116, by decide⟩]) unmarked_context_12_28442_426117 node_context_12_28442_426117
  intro a
  fin_cases a
  · exact context_13_113768_426043
  · exact context_13_113769_426088
  · exact context_13_113770_426109
  · exact context_13_113771_426116

theorem selected_cut_16728 : selected 8 ⟨426148, by decide⟩
    (prefixPartial 13 113772) = some ⟨13, 2, 0, 426148, 113772, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_113772_426148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113772 ⟨426148, by decide⟩ :=
  accepted_of_selected 13 113772 ⟨426148, by decide⟩ ⟨13, 2, 0, 426148, 113772, 2001, 16384⟩
    (by decide) selected_cut_16728

theorem selected_cut_16729 : selected 8 ⟨426206, by decide⟩
    (prefixPartial 13 113773) = some ⟨13, 2, 0, 426206, 113773, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_113773_426206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113773 ⟨426206, by decide⟩ :=
  accepted_of_selected 13 113773 ⟨426206, by decide⟩ ⟨13, 2, 0, 426206, 113773, 2881, 16384⟩
    (by decide) selected_cut_16729

theorem selected_cut_16730 : selected 8 ⟨426226, by decide⟩
    (prefixPartial 13 113774) = some ⟨13, 2, 0, 426226, 113774, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_113774_426226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113774 ⟨426226, by decide⟩ :=
  accepted_of_selected 13 113774 ⟨426226, by decide⟩ ⟨13, 2, 0, 426226, 113774, 1681, 16384⟩
    (by decide) selected_cut_16730

theorem selected_cut_16731 : selected 8 ⟨426232, by decide⟩
    (prefixPartial 13 113775) = some ⟨13, 2, 0, 426232, 113775, 745, 16384⟩ := by
  decide +kernel

theorem context_13_113775_426232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113775 ⟨426232, by decide⟩ :=
  accepted_of_selected 13 113775 ⟨426232, by decide⟩ ⟨13, 2, 0, 426232, 113775, 745, 16384⟩
    (by decide) selected_cut_16731

theorem unmarked_context_12_28443_426233 : frontier 9 ⟨426233, by decide⟩
    (prefixCache 12 28443) (prefixPartial 12 28443) = false := by
  decide +kernel

theorem node_context_12_28443_426233 : EJMOriginalGlobalDAGData.nodes 9 ⟨426233, by decide⟩ =
    .split (coordinate 12) (![⟨426148, by decide⟩,⟨426206, by decide⟩,⟨426226, by decide⟩,⟨426232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28443_426233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28443 ⟨426233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28443
    ⟨426233, by decide⟩ (by decide) (![⟨426148, by decide⟩,⟨426206, by decide⟩,⟨426226, by decide⟩,⟨426232, by decide⟩]) unmarked_context_12_28443_426233 node_context_12_28443_426233
  intro a
  fin_cases a
  · exact context_13_113772_426148
  · exact context_13_113773_426206
  · exact context_13_113774_426226
  · exact context_13_113775_426232

theorem unmarked_context_11_7110_426234 : frontier 10 ⟨426234, by decide⟩
    (prefixCache 11 7110) (prefixPartial 11 7110) = false := by
  decide +kernel

theorem node_context_11_7110_426234 : EJMOriginalGlobalDAGData.nodes 10 ⟨426234, by decide⟩ =
    .split (coordinate 11) (![⟨425893, by decide⟩,⟨426005, by decide⟩,⟨426117, by decide⟩,⟨426233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7110_426234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7110 ⟨426234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7110
    ⟨426234, by decide⟩ (by decide) (![⟨425893, by decide⟩,⟨426005, by decide⟩,⟨426117, by decide⟩,⟨426233, by decide⟩]) unmarked_context_11_7110_426234 node_context_11_7110_426234
  intro a
  fin_cases a
  · exact context_12_28440_425893
  · exact context_12_28441_426005
  · exact context_12_28442_426117
  · exact context_12_28443_426233

theorem selected_cut_16732 : selected 8 ⟨426251, by decide⟩
    (prefixPartial 13 113776) = some ⟨13, 2, 0, 426251, 113776, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_113776_426251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113776 ⟨426251, by decide⟩ :=
  accepted_of_selected 13 113776 ⟨426251, by decide⟩ ⟨13, 2, 0, 426251, 113776, 1453, 16384⟩
    (by decide) selected_cut_16732

theorem selected_cut_16733 : selected 8 ⟨426281, by decide⟩
    (prefixPartial 13 113777) = some ⟨13, 2, 0, 426281, 113777, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_113777_426281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113777 ⟨426281, by decide⟩ :=
  accepted_of_selected 13 113777 ⟨426281, by decide⟩ ⟨13, 2, 0, 426281, 113777, 2105, 16384⟩
    (by decide) selected_cut_16733

theorem selected_cut_16734 : selected 8 ⟨426299, by decide⟩
    (prefixPartial 13 113778) = some ⟨13, 2, 0, 426299, 113778, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_113778_426299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113778 ⟨426299, by decide⟩ :=
  accepted_of_selected 13 113778 ⟨426299, by decide⟩ ⟨13, 2, 0, 426299, 113778, 1293, 16384⟩
    (by decide) selected_cut_16734

theorem selected_cut_16735 : selected 8 ⟨426305, by decide⟩
    (prefixPartial 13 113779) = some ⟨13, 2, 0, 426305, 113779, 601, 16384⟩ := by
  decide +kernel

theorem context_13_113779_426305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113779 ⟨426305, by decide⟩ :=
  accepted_of_selected 13 113779 ⟨426305, by decide⟩ ⟨13, 2, 0, 426305, 113779, 601, 16384⟩
    (by decide) selected_cut_16735

theorem unmarked_context_12_28444_426306 : frontier 9 ⟨426306, by decide⟩
    (prefixCache 12 28444) (prefixPartial 12 28444) = false := by
  decide +kernel

theorem node_context_12_28444_426306 : EJMOriginalGlobalDAGData.nodes 9 ⟨426306, by decide⟩ =
    .split (coordinate 12) (![⟨426251, by decide⟩,⟨426281, by decide⟩,⟨426299, by decide⟩,⟨426305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28444_426306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28444 ⟨426306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28444
    ⟨426306, by decide⟩ (by decide) (![⟨426251, by decide⟩,⟨426281, by decide⟩,⟨426299, by decide⟩,⟨426305, by decide⟩]) unmarked_context_12_28444_426306 node_context_12_28444_426306
  intro a
  fin_cases a
  · exact context_13_113776_426251
  · exact context_13_113777_426281
  · exact context_13_113778_426299
  · exact context_13_113779_426305

theorem selected_cut_16736 : selected 8 ⟨426339, by decide⟩
    (prefixPartial 13 113780) = some ⟨13, 2, 0, 426339, 113780, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_113780_426339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113780 ⟨426339, by decide⟩ :=
  accepted_of_selected 13 113780 ⟨426339, by decide⟩ ⟨13, 2, 0, 426339, 113780, 1885, 16384⟩
    (by decide) selected_cut_16736

theorem selected_cut_16737 : selected 8 ⟨426380, by decide⟩
    (prefixPartial 13 113781) = some ⟨13, 2, 0, 426380, 113781, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_113781_426380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113781 ⟨426380, by decide⟩ :=
  accepted_of_selected 13 113781 ⟨426380, by decide⟩ ⟨13, 2, 0, 426380, 113781, 2201, 16384⟩
    (by decide) selected_cut_16737

theorem selected_cut_16738 : selected 8 ⟨426406, by decide⟩
    (prefixPartial 13 113782) = some ⟨13, 2, 0, 426406, 113782, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_113782_426406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113782 ⟨426406, by decide⟩ :=
  accepted_of_selected 13 113782 ⟨426406, by decide⟩ ⟨13, 2, 0, 426406, 113782, 1621, 16384⟩
    (by decide) selected_cut_16738

theorem selected_cut_16739 : selected 8 ⟨426412, by decide⟩
    (prefixPartial 13 113783) = some ⟨13, 2, 0, 426412, 113783, 681, 16384⟩ := by
  decide +kernel

theorem context_13_113783_426412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113783 ⟨426412, by decide⟩ :=
  accepted_of_selected 13 113783 ⟨426412, by decide⟩ ⟨13, 2, 0, 426412, 113783, 681, 16384⟩
    (by decide) selected_cut_16739

theorem unmarked_context_12_28445_426413 : frontier 9 ⟨426413, by decide⟩
    (prefixCache 12 28445) (prefixPartial 12 28445) = false := by
  decide +kernel

theorem node_context_12_28445_426413 : EJMOriginalGlobalDAGData.nodes 9 ⟨426413, by decide⟩ =
    .split (coordinate 12) (![⟨426339, by decide⟩,⟨426380, by decide⟩,⟨426406, by decide⟩,⟨426412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28445_426413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28445 ⟨426413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28445
    ⟨426413, by decide⟩ (by decide) (![⟨426339, by decide⟩,⟨426380, by decide⟩,⟨426406, by decide⟩,⟨426412, by decide⟩]) unmarked_context_12_28445_426413 node_context_12_28445_426413
  intro a
  fin_cases a
  · exact context_13_113780_426339
  · exact context_13_113781_426380
  · exact context_13_113782_426406
  · exact context_13_113783_426412

theorem selected_cut_16740 : selected 8 ⟨426453, by decide⟩
    (prefixPartial 13 113784) = some ⟨13, 2, 0, 426453, 113784, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_113784_426453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113784 ⟨426453, by decide⟩ :=
  accepted_of_selected 13 113784 ⟨426453, by decide⟩ ⟨13, 2, 0, 426453, 113784, 2005, 16384⟩
    (by decide) selected_cut_16740

theorem selected_cut_16741 : selected 8 ⟨426492, by decide⟩
    (prefixPartial 13 113785) = some ⟨13, 2, 0, 426492, 113785, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_113785_426492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113785 ⟨426492, by decide⟩ :=
  accepted_of_selected 13 113785 ⟨426492, by decide⟩ ⟨13, 2, 0, 426492, 113785, 2473, 16384⟩
    (by decide) selected_cut_16741

theorem selected_cut_16742 : selected 8 ⟨426511, by decide⟩
    (prefixPartial 13 113786) = some ⟨13, 2, 0, 426511, 113786, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_113786_426511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113786 ⟨426511, by decide⟩ :=
  accepted_of_selected 13 113786 ⟨426511, by decide⟩ ⟨13, 2, 0, 426511, 113786, 1489, 16384⟩
    (by decide) selected_cut_16742

theorem selected_cut_16743 : selected 8 ⟨426515, by decide⟩
    (prefixPartial 13 113787) = some ⟨13, 2, 0, 426515, 113787, 673, 16384⟩ := by
  decide +kernel

theorem context_13_113787_426515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113787 ⟨426515, by decide⟩ :=
  accepted_of_selected 13 113787 ⟨426515, by decide⟩ ⟨13, 2, 0, 426515, 113787, 673, 16384⟩
    (by decide) selected_cut_16743

theorem unmarked_context_12_28446_426516 : frontier 9 ⟨426516, by decide⟩
    (prefixCache 12 28446) (prefixPartial 12 28446) = false := by
  decide +kernel

theorem node_context_12_28446_426516 : EJMOriginalGlobalDAGData.nodes 9 ⟨426516, by decide⟩ =
    .split (coordinate 12) (![⟨426453, by decide⟩,⟨426492, by decide⟩,⟨426511, by decide⟩,⟨426515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28446_426516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28446 ⟨426516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28446
    ⟨426516, by decide⟩ (by decide) (![⟨426453, by decide⟩,⟨426492, by decide⟩,⟨426511, by decide⟩,⟨426515, by decide⟩]) unmarked_context_12_28446_426516 node_context_12_28446_426516
  intro a
  fin_cases a
  · exact context_13_113784_426453
  · exact context_13_113785_426492
  · exact context_13_113786_426511
  · exact context_13_113787_426515

theorem selected_cut_16744 : selected 8 ⟨426568, by decide⟩
    (prefixPartial 13 113788) = some ⟨13, 2, 0, 426568, 113788, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_113788_426568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113788 ⟨426568, by decide⟩ :=
  accepted_of_selected 13 113788 ⟨426568, by decide⟩ ⟨13, 2, 0, 426568, 113788, 2781, 16384⟩
    (by decide) selected_cut_16744

theorem selected_cut_16745 : selected 7 ⟨426596, by decide⟩
    (prefixPartial 14 455156) = some ⟨14, 2, 0, 426596, 455156, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_455156_426596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455156 ⟨426596, by decide⟩ :=
  accepted_of_selected 14 455156 ⟨426596, by decide⟩ ⟨14, 2, 0, 426596, 455156, 1273, 4096⟩
    (by decide) selected_cut_16745

theorem selected_cut_16746 : selected 7 ⟨426620, by decide⟩
    (prefixPartial 14 455157) = some ⟨14, 2, 0, 426620, 455157, 885, 4096⟩ := by
  decide +kernel

theorem context_14_455157_426620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455157 ⟨426620, by decide⟩ :=
  accepted_of_selected 14 455157 ⟨426620, by decide⟩ ⟨14, 2, 0, 426620, 455157, 885, 4096⟩
    (by decide) selected_cut_16746

theorem selected_cut_16747 : selected 7 ⟨426643, by decide⟩
    (prefixPartial 14 455158) = some ⟨14, 2, 0, 426643, 455158, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_455158_426643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455158 ⟨426643, by decide⟩ :=
  accepted_of_selected 14 455158 ⟨426643, by decide⟩ ⟨14, 2, 0, 426643, 455158, 1065, 4096⟩
    (by decide) selected_cut_16747

theorem selected_cut_16748 : selected 7 ⟨426658, by decide⟩
    (prefixPartial 14 455159) = some ⟨14, 2, 0, 426658, 455159, 937, 4096⟩ := by
  decide +kernel

theorem context_14_455159_426658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455159 ⟨426658, by decide⟩ :=
  accepted_of_selected 14 455159 ⟨426658, by decide⟩ ⟨14, 2, 0, 426658, 455159, 937, 4096⟩
    (by decide) selected_cut_16748

theorem unmarked_context_13_113789_426659 : frontier 8 ⟨426659, by decide⟩
    (prefixCache 13 113789) (prefixPartial 13 113789) = false := by
  decide +kernel

theorem node_context_13_113789_426659 : EJMOriginalGlobalDAGData.nodes 8 ⟨426659, by decide⟩ =
    .split (coordinate 13) (![⟨426596, by decide⟩,⟨426620, by decide⟩,⟨426643, by decide⟩,⟨426658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113789_426659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113789 ⟨426659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113789
    ⟨426659, by decide⟩ (by decide) (![⟨426596, by decide⟩,⟨426620, by decide⟩,⟨426643, by decide⟩,⟨426658, by decide⟩]) unmarked_context_13_113789_426659 node_context_13_113789_426659
  intro a
  fin_cases a
  · exact context_14_455156_426596
  · exact context_14_455157_426620
  · exact context_14_455158_426643
  · exact context_14_455159_426658

theorem selected_cut_16749 : selected 8 ⟨426696, by decide⟩
    (prefixPartial 13 113790) = some ⟨13, 2, 0, 426696, 113790, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_113790_426696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113790 ⟨426696, by decide⟩ :=
  accepted_of_selected 13 113790 ⟨426696, by decide⟩ ⟨13, 2, 0, 426696, 113790, 2605, 16384⟩
    (by decide) selected_cut_16749

theorem selected_cut_16750 : selected 8 ⟨426718, by decide⟩
    (prefixPartial 13 113791) = some ⟨13, 2, 0, 426718, 113791, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_113791_426718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113791 ⟨426718, by decide⟩ :=
  accepted_of_selected 13 113791 ⟨426718, by decide⟩ ⟨13, 2, 0, 426718, 113791, 1181, 16384⟩
    (by decide) selected_cut_16750

theorem unmarked_context_12_28447_426719 : frontier 9 ⟨426719, by decide⟩
    (prefixCache 12 28447) (prefixPartial 12 28447) = false := by
  decide +kernel

theorem node_context_12_28447_426719 : EJMOriginalGlobalDAGData.nodes 9 ⟨426719, by decide⟩ =
    .split (coordinate 12) (![⟨426568, by decide⟩,⟨426659, by decide⟩,⟨426696, by decide⟩,⟨426718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28447_426719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28447 ⟨426719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28447
    ⟨426719, by decide⟩ (by decide) (![⟨426568, by decide⟩,⟨426659, by decide⟩,⟨426696, by decide⟩,⟨426718, by decide⟩]) unmarked_context_12_28447_426719 node_context_12_28447_426719
  intro a
  fin_cases a
  · exact context_13_113788_426568
  · exact context_13_113789_426659
  · exact context_13_113790_426696
  · exact context_13_113791_426718

theorem unmarked_context_11_7111_426720 : frontier 10 ⟨426720, by decide⟩
    (prefixCache 11 7111) (prefixPartial 11 7111) = false := by
  decide +kernel

theorem node_context_11_7111_426720 : EJMOriginalGlobalDAGData.nodes 10 ⟨426720, by decide⟩ =
    .split (coordinate 11) (![⟨426306, by decide⟩,⟨426413, by decide⟩,⟨426516, by decide⟩,⟨426719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7111_426720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7111 ⟨426720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7111
    ⟨426720, by decide⟩ (by decide) (![⟨426306, by decide⟩,⟨426413, by decide⟩,⟨426516, by decide⟩,⟨426719, by decide⟩]) unmarked_context_11_7111_426720 node_context_11_7111_426720
  intro a
  fin_cases a
  · exact context_12_28444_426306
  · exact context_12_28445_426413
  · exact context_12_28446_426516
  · exact context_12_28447_426719

theorem unmarked_context_10_1777_426721 : frontier 11 ⟨426721, by decide⟩
    (prefixCache 10 1777) (prefixPartial 10 1777) = false := by
  decide +kernel

theorem node_context_10_1777_426721 : EJMOriginalGlobalDAGData.nodes 11 ⟨426721, by decide⟩ =
    .split (coordinate 10) (![⟨425348, by decide⟩,⟨425788, by decide⟩,⟨426234, by decide⟩,⟨426720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1777_426721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1777 ⟨426721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1777
    ⟨426721, by decide⟩ (by decide) (![⟨425348, by decide⟩,⟨425788, by decide⟩,⟨426234, by decide⟩,⟨426720, by decide⟩]) unmarked_context_10_1777_426721 node_context_10_1777_426721
  intro a
  fin_cases a
  · exact context_11_7108_425348
  · exact context_11_7109_425788
  · exact context_11_7110_426234
  · exact context_11_7111_426720

theorem selected_cut_16751 : selected 8 ⟨426736, by decide⟩
    (prefixPartial 13 113792) = some ⟨13, 2, 0, 426736, 113792, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_113792_426736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113792 ⟨426736, by decide⟩ :=
  accepted_of_selected 13 113792 ⟨426736, by decide⟩ ⟨13, 2, 0, 426736, 113792, 1245, 16384⟩
    (by decide) selected_cut_16751

theorem selected_cut_16752 : selected 8 ⟨426765, by decide⟩
    (prefixPartial 13 113793) = some ⟨13, 2, 0, 426765, 113793, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_113793_426765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113793 ⟨426765, by decide⟩ :=
  accepted_of_selected 13 113793 ⟨426765, by decide⟩ ⟨13, 2, 0, 426765, 113793, 2261, 16384⟩
    (by decide) selected_cut_16752

theorem selected_cut_16753 : selected 8 ⟨426784, by decide⟩
    (prefixPartial 13 113794) = some ⟨13, 2, 0, 426784, 113794, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_113794_426784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113794 ⟨426784, by decide⟩ :=
  accepted_of_selected 13 113794 ⟨426784, by decide⟩ ⟨13, 2, 0, 426784, 113794, 1237, 16384⟩
    (by decide) selected_cut_16753

theorem selected_cut_16754 : selected 8 ⟨426789, by decide⟩
    (prefixPartial 13 113795) = some ⟨13, 2, 0, 426789, 113795, 669, 16384⟩ := by
  decide +kernel

theorem context_13_113795_426789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113795 ⟨426789, by decide⟩ :=
  accepted_of_selected 13 113795 ⟨426789, by decide⟩ ⟨13, 2, 0, 426789, 113795, 669, 16384⟩
    (by decide) selected_cut_16754

theorem unmarked_context_12_28448_426790 : frontier 9 ⟨426790, by decide⟩
    (prefixCache 12 28448) (prefixPartial 12 28448) = false := by
  decide +kernel

theorem node_context_12_28448_426790 : EJMOriginalGlobalDAGData.nodes 9 ⟨426790, by decide⟩ =
    .split (coordinate 12) (![⟨426736, by decide⟩,⟨426765, by decide⟩,⟨426784, by decide⟩,⟨426789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28448_426790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28448 ⟨426790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28448
    ⟨426790, by decide⟩ (by decide) (![⟨426736, by decide⟩,⟨426765, by decide⟩,⟨426784, by decide⟩,⟨426789, by decide⟩]) unmarked_context_12_28448_426790 node_context_12_28448_426790
  intro a
  fin_cases a
  · exact context_13_113792_426736
  · exact context_13_113793_426765
  · exact context_13_113794_426784
  · exact context_13_113795_426789

theorem selected_cut_16755 : selected 8 ⟨426807, by decide⟩
    (prefixPartial 13 113796) = some ⟨13, 2, 0, 426807, 113796, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_113796_426807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113796 ⟨426807, by decide⟩ :=
  accepted_of_selected 13 113796 ⟨426807, by decide⟩ ⟨13, 2, 0, 426807, 113796, 1593, 16384⟩
    (by decide) selected_cut_16755

theorem selected_cut_16756 : selected 8 ⟨426850, by decide⟩
    (prefixPartial 13 113797) = some ⟨13, 2, 0, 426850, 113797, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_113797_426850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113797 ⟨426850, by decide⟩ :=
  accepted_of_selected 13 113797 ⟨426850, by decide⟩ ⟨13, 2, 0, 426850, 113797, 2437, 16384⟩
    (by decide) selected_cut_16756

theorem selected_cut_16757 : selected 8 ⟨426874, by decide⟩
    (prefixPartial 13 113798) = some ⟨13, 2, 0, 426874, 113798, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_113798_426874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113798 ⟨426874, by decide⟩ :=
  accepted_of_selected 13 113798 ⟨426874, by decide⟩ ⟨13, 2, 0, 426874, 113798, 1645, 16384⟩
    (by decide) selected_cut_16757

theorem selected_cut_16758 : selected 8 ⟨426880, by decide⟩
    (prefixPartial 13 113799) = some ⟨13, 2, 0, 426880, 113799, 641, 16384⟩ := by
  decide +kernel

theorem context_13_113799_426880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113799 ⟨426880, by decide⟩ :=
  accepted_of_selected 13 113799 ⟨426880, by decide⟩ ⟨13, 2, 0, 426880, 113799, 641, 16384⟩
    (by decide) selected_cut_16758

theorem unmarked_context_12_28449_426881 : frontier 9 ⟨426881, by decide⟩
    (prefixCache 12 28449) (prefixPartial 12 28449) = false := by
  decide +kernel

theorem node_context_12_28449_426881 : EJMOriginalGlobalDAGData.nodes 9 ⟨426881, by decide⟩ =
    .split (coordinate 12) (![⟨426807, by decide⟩,⟨426850, by decide⟩,⟨426874, by decide⟩,⟨426880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28449_426881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28449 ⟨426881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28449
    ⟨426881, by decide⟩ (by decide) (![⟨426807, by decide⟩,⟨426850, by decide⟩,⟨426874, by decide⟩,⟨426880, by decide⟩]) unmarked_context_12_28449_426881 node_context_12_28449_426881
  intro a
  fin_cases a
  · exact context_13_113796_426807
  · exact context_13_113797_426850
  · exact context_13_113798_426874
  · exact context_13_113799_426880

theorem selected_cut_16759 : selected 8 ⟨426902, by decide⟩
    (prefixPartial 13 113800) = some ⟨13, 2, 0, 426902, 113800, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_113800_426902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113800 ⟨426902, by decide⟩ :=
  accepted_of_selected 13 113800 ⟨426902, by decide⟩ ⟨13, 2, 0, 426902, 113800, 1637, 16384⟩
    (by decide) selected_cut_16759

theorem selected_cut_16760 : selected 8 ⟨426946, by decide⟩
    (prefixPartial 13 113801) = some ⟨13, 2, 0, 426946, 113801, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_113801_426946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113801 ⟨426946, by decide⟩ :=
  accepted_of_selected 13 113801 ⟨426946, by decide⟩ ⟨13, 2, 0, 426946, 113801, 2465, 16384⟩
    (by decide) selected_cut_16760

theorem selected_cut_16761 : selected 8 ⟨426971, by decide⟩
    (prefixPartial 13 113802) = some ⟨13, 2, 0, 426971, 113802, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_113802_426971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113802 ⟨426971, by decide⟩ :=
  accepted_of_selected 13 113802 ⟨426971, by decide⟩ ⟨13, 2, 0, 426971, 113802, 1621, 16384⟩
    (by decide) selected_cut_16761

theorem selected_cut_16762 : selected 8 ⟨426976, by decide⟩
    (prefixPartial 13 113803) = some ⟨13, 2, 0, 426976, 113803, 677, 16384⟩ := by
  decide +kernel

theorem context_13_113803_426976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113803 ⟨426976, by decide⟩ :=
  accepted_of_selected 13 113803 ⟨426976, by decide⟩ ⟨13, 2, 0, 426976, 113803, 677, 16384⟩
    (by decide) selected_cut_16762

theorem unmarked_context_12_28450_426977 : frontier 9 ⟨426977, by decide⟩
    (prefixCache 12 28450) (prefixPartial 12 28450) = false := by
  decide +kernel

theorem node_context_12_28450_426977 : EJMOriginalGlobalDAGData.nodes 9 ⟨426977, by decide⟩ =
    .split (coordinate 12) (![⟨426902, by decide⟩,⟨426946, by decide⟩,⟨426971, by decide⟩,⟨426976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28450_426977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28450 ⟨426977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28450
    ⟨426977, by decide⟩ (by decide) (![⟨426902, by decide⟩,⟨426946, by decide⟩,⟨426971, by decide⟩,⟨426976, by decide⟩]) unmarked_context_12_28450_426977 node_context_12_28450_426977
  intro a
  fin_cases a
  · exact context_13_113800_426902
  · exact context_13_113801_426946
  · exact context_13_113802_426971
  · exact context_13_113803_426976

theorem selected_cut_16763 : selected 8 ⟨426995, by decide⟩
    (prefixPartial 13 113804) = some ⟨13, 2, 0, 426995, 113804, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_113804_426995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113804 ⟨426995, by decide⟩ :=
  accepted_of_selected 13 113804 ⟨426995, by decide⟩ ⟨13, 2, 0, 426995, 113804, 1437, 16384⟩
    (by decide) selected_cut_16763

theorem selected_cut_16764 : selected 8 ⟨427038, by decide⟩
    (prefixPartial 13 113805) = some ⟨13, 2, 0, 427038, 113805, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_113805_427038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113805 ⟨427038, by decide⟩ :=
  accepted_of_selected 13 113805 ⟨427038, by decide⟩ ⟨13, 2, 0, 427038, 113805, 2569, 16384⟩
    (by decide) selected_cut_16764

theorem selected_cut_16765 : selected 8 ⟨427057, by decide⟩
    (prefixPartial 13 113806) = some ⟨13, 2, 0, 427057, 113806, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_113806_427057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113806 ⟨427057, by decide⟩ :=
  accepted_of_selected 13 113806 ⟨427057, by decide⟩ ⟨13, 2, 0, 427057, 113806, 1677, 16384⟩
    (by decide) selected_cut_16765

theorem selected_cut_16766 : selected 8 ⟨427063, by decide⟩
    (prefixPartial 13 113807) = some ⟨13, 2, 0, 427063, 113807, 785, 16384⟩ := by
  decide +kernel

theorem context_13_113807_427063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113807 ⟨427063, by decide⟩ :=
  accepted_of_selected 13 113807 ⟨427063, by decide⟩ ⟨13, 2, 0, 427063, 113807, 785, 16384⟩
    (by decide) selected_cut_16766

theorem unmarked_context_12_28451_427064 : frontier 9 ⟨427064, by decide⟩
    (prefixCache 12 28451) (prefixPartial 12 28451) = false := by
  decide +kernel

theorem node_context_12_28451_427064 : EJMOriginalGlobalDAGData.nodes 9 ⟨427064, by decide⟩ =
    .split (coordinate 12) (![⟨426995, by decide⟩,⟨427038, by decide⟩,⟨427057, by decide⟩,⟨427063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28451_427064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28451 ⟨427064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28451
    ⟨427064, by decide⟩ (by decide) (![⟨426995, by decide⟩,⟨427038, by decide⟩,⟨427057, by decide⟩,⟨427063, by decide⟩]) unmarked_context_12_28451_427064 node_context_12_28451_427064
  intro a
  fin_cases a
  · exact context_13_113804_426995
  · exact context_13_113805_427038
  · exact context_13_113806_427057
  · exact context_13_113807_427063

theorem unmarked_context_11_7112_427065 : frontier 10 ⟨427065, by decide⟩
    (prefixCache 11 7112) (prefixPartial 11 7112) = false := by
  decide +kernel

theorem node_context_11_7112_427065 : EJMOriginalGlobalDAGData.nodes 10 ⟨427065, by decide⟩ =
    .split (coordinate 11) (![⟨426790, by decide⟩,⟨426881, by decide⟩,⟨426977, by decide⟩,⟨427064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7112_427065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7112 ⟨427065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7112
    ⟨427065, by decide⟩ (by decide) (![⟨426790, by decide⟩,⟨426881, by decide⟩,⟨426977, by decide⟩,⟨427064, by decide⟩]) unmarked_context_11_7112_427065 node_context_11_7112_427065
  intro a
  fin_cases a
  · exact context_12_28448_426790
  · exact context_12_28449_426881
  · exact context_12_28450_426977
  · exact context_12_28451_427064

theorem selected_cut_16767 : selected 8 ⟨427081, by decide⟩
    (prefixPartial 13 113808) = some ⟨13, 2, 0, 427081, 113808, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_113808_427081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113808 ⟨427081, by decide⟩ :=
  accepted_of_selected 13 113808 ⟨427081, by decide⟩ ⟨13, 2, 0, 427081, 113808, 1117, 16384⟩
    (by decide) selected_cut_16767

theorem selected_cut_16768 : selected 8 ⟨427120, by decide⟩
    (prefixPartial 13 113809) = some ⟨13, 2, 0, 427120, 113809, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_113809_427120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113809 ⟨427120, by decide⟩ :=
  accepted_of_selected 13 113809 ⟨427120, by decide⟩ ⟨13, 2, 0, 427120, 113809, 2493, 16384⟩
    (by decide) selected_cut_16768

theorem selected_cut_16769 : selected 8 ⟨427137, by decide⟩
    (prefixPartial 13 113810) = some ⟨13, 2, 0, 427137, 113810, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_113810_427137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113810 ⟨427137, by decide⟩ :=
  accepted_of_selected 13 113810 ⟨427137, by decide⟩ ⟨13, 2, 0, 427137, 113810, 1429, 16384⟩
    (by decide) selected_cut_16769

theorem selected_cut_16770 : selected 8 ⟨427144, by decide⟩
    (prefixPartial 13 113811) = some ⟨13, 2, 0, 427144, 113811, 657, 16384⟩ := by
  decide +kernel

theorem context_13_113811_427144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113811 ⟨427144, by decide⟩ :=
  accepted_of_selected 13 113811 ⟨427144, by decide⟩ ⟨13, 2, 0, 427144, 113811, 657, 16384⟩
    (by decide) selected_cut_16770

theorem unmarked_context_12_28452_427145 : frontier 9 ⟨427145, by decide⟩
    (prefixCache 12 28452) (prefixPartial 12 28452) = false := by
  decide +kernel

theorem node_context_12_28452_427145 : EJMOriginalGlobalDAGData.nodes 9 ⟨427145, by decide⟩ =
    .split (coordinate 12) (![⟨427081, by decide⟩,⟨427120, by decide⟩,⟨427137, by decide⟩,⟨427144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28452_427145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28452 ⟨427145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28452
    ⟨427145, by decide⟩ (by decide) (![⟨427081, by decide⟩,⟨427120, by decide⟩,⟨427137, by decide⟩,⟨427144, by decide⟩]) unmarked_context_12_28452_427145 node_context_12_28452_427145
  intro a
  fin_cases a
  · exact context_13_113808_427081
  · exact context_13_113809_427120
  · exact context_13_113810_427137
  · exact context_13_113811_427144

theorem selected_cut_16771 : selected 8 ⟨427164, by decide⟩
    (prefixPartial 13 113812) = some ⟨13, 2, 0, 427164, 113812, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_113812_427164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113812 ⟨427164, by decide⟩ :=
  accepted_of_selected 13 113812 ⟨427164, by decide⟩ ⟨13, 2, 0, 427164, 113812, 1229, 16384⟩
    (by decide) selected_cut_16771

theorem selected_cut_16772 : selected 8 ⟨427195, by decide⟩
    (prefixPartial 13 113813) = some ⟨13, 2, 0, 427195, 113813, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_113813_427195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113813 ⟨427195, by decide⟩ :=
  accepted_of_selected 13 113813 ⟨427195, by decide⟩ ⟨13, 2, 0, 427195, 113813, 2273, 16384⟩
    (by decide) selected_cut_16772

theorem selected_cut_16773 : selected 8 ⟨427218, by decide⟩
    (prefixPartial 13 113814) = some ⟨13, 2, 0, 427218, 113814, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_113814_427218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113814 ⟨427218, by decide⟩ :=
  accepted_of_selected 13 113814 ⟨427218, by decide⟩ ⟨13, 2, 0, 427218, 113814, 1609, 16384⟩
    (by decide) selected_cut_16773

theorem selected_cut_16774 : selected 8 ⟨427227, by decide⟩
    (prefixPartial 13 113815) = some ⟨13, 2, 0, 427227, 113815, 717, 16384⟩ := by
  decide +kernel

theorem context_13_113815_427227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113815 ⟨427227, by decide⟩ :=
  accepted_of_selected 13 113815 ⟨427227, by decide⟩ ⟨13, 2, 0, 427227, 113815, 717, 16384⟩
    (by decide) selected_cut_16774

theorem unmarked_context_12_28453_427228 : frontier 9 ⟨427228, by decide⟩
    (prefixCache 12 28453) (prefixPartial 12 28453) = false := by
  decide +kernel

theorem node_context_12_28453_427228 : EJMOriginalGlobalDAGData.nodes 9 ⟨427228, by decide⟩ =
    .split (coordinate 12) (![⟨427164, by decide⟩,⟨427195, by decide⟩,⟨427218, by decide⟩,⟨427227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28453_427228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28453 ⟨427228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28453
    ⟨427228, by decide⟩ (by decide) (![⟨427164, by decide⟩,⟨427195, by decide⟩,⟨427218, by decide⟩,⟨427227, by decide⟩]) unmarked_context_12_28453_427228 node_context_12_28453_427228
  intro a
  fin_cases a
  · exact context_13_113812_427164
  · exact context_13_113813_427195
  · exact context_13_113814_427218
  · exact context_13_113815_427227

theorem selected_cut_16775 : selected 8 ⟨427249, by decide⟩
    (prefixPartial 13 113816) = some ⟨13, 2, 0, 427249, 113816, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_113816_427249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113816 ⟨427249, by decide⟩ :=
  accepted_of_selected 13 113816 ⟨427249, by decide⟩ ⟨13, 2, 0, 427249, 113816, 1269, 16384⟩
    (by decide) selected_cut_16775

theorem selected_cut_16776 : selected 8 ⟨427286, by decide⟩
    (prefixPartial 13 113817) = some ⟨13, 2, 0, 427286, 113817, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_113817_427286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113817 ⟨427286, by decide⟩ :=
  accepted_of_selected 13 113817 ⟨427286, by decide⟩ ⟨13, 2, 0, 427286, 113817, 2297, 16384⟩
    (by decide) selected_cut_16776

theorem selected_cut_16777 : selected 8 ⟨427310, by decide⟩
    (prefixPartial 13 113818) = some ⟨13, 2, 0, 427310, 113818, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_113818_427310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113818 ⟨427310, by decide⟩ :=
  accepted_of_selected 13 113818 ⟨427310, by decide⟩ ⟨13, 2, 0, 427310, 113818, 1529, 16384⟩
    (by decide) selected_cut_16777

theorem selected_cut_16778 : selected 8 ⟨427318, by decide⟩
    (prefixPartial 13 113819) = some ⟨13, 2, 0, 427318, 113819, 789, 16384⟩ := by
  decide +kernel

theorem context_13_113819_427318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113819 ⟨427318, by decide⟩ :=
  accepted_of_selected 13 113819 ⟨427318, by decide⟩ ⟨13, 2, 0, 427318, 113819, 789, 16384⟩
    (by decide) selected_cut_16778

theorem unmarked_context_12_28454_427319 : frontier 9 ⟨427319, by decide⟩
    (prefixCache 12 28454) (prefixPartial 12 28454) = false := by
  decide +kernel

theorem node_context_12_28454_427319 : EJMOriginalGlobalDAGData.nodes 9 ⟨427319, by decide⟩ =
    .split (coordinate 12) (![⟨427249, by decide⟩,⟨427286, by decide⟩,⟨427310, by decide⟩,⟨427318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28454_427319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28454 ⟨427319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28454
    ⟨427319, by decide⟩ (by decide) (![⟨427249, by decide⟩,⟨427286, by decide⟩,⟨427310, by decide⟩,⟨427318, by decide⟩]) unmarked_context_12_28454_427319 node_context_12_28454_427319
  intro a
  fin_cases a
  · exact context_13_113816_427249
  · exact context_13_113817_427286
  · exact context_13_113818_427310
  · exact context_13_113819_427318

theorem selected_cut_16779 : selected 8 ⟨427331, by decide⟩
    (prefixPartial 13 113820) = some ⟨13, 2, 0, 427331, 113820, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_113820_427331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113820 ⟨427331, by decide⟩ :=
  accepted_of_selected 13 113820 ⟨427331, by decide⟩ ⟨13, 2, 0, 427331, 113820, 1049, 16384⟩
    (by decide) selected_cut_16779

theorem selected_cut_16780 : selected 8 ⟨427367, by decide⟩
    (prefixPartial 13 113821) = some ⟨13, 2, 0, 427367, 113821, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_113821_427367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113821 ⟨427367, by decide⟩ :=
  accepted_of_selected 13 113821 ⟨427367, by decide⟩ ⟨13, 2, 0, 427367, 113821, 2309, 16384⟩
    (by decide) selected_cut_16780

theorem selected_cut_16781 : selected 8 ⟨427389, by decide⟩
    (prefixPartial 13 113822) = some ⟨13, 2, 0, 427389, 113822, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_113822_427389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113822 ⟨427389, by decide⟩ :=
  accepted_of_selected 13 113822 ⟨427389, by decide⟩ ⟨13, 2, 0, 427389, 113822, 1673, 16384⟩
    (by decide) selected_cut_16781

theorem selected_cut_16782 : selected 8 ⟨427399, by decide⟩
    (prefixPartial 13 113823) = some ⟨13, 2, 0, 427399, 113823, 841, 16384⟩ := by
  decide +kernel

theorem context_13_113823_427399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113823 ⟨427399, by decide⟩ :=
  accepted_of_selected 13 113823 ⟨427399, by decide⟩ ⟨13, 2, 0, 427399, 113823, 841, 16384⟩
    (by decide) selected_cut_16782

theorem unmarked_context_12_28455_427400 : frontier 9 ⟨427400, by decide⟩
    (prefixCache 12 28455) (prefixPartial 12 28455) = false := by
  decide +kernel

theorem node_context_12_28455_427400 : EJMOriginalGlobalDAGData.nodes 9 ⟨427400, by decide⟩ =
    .split (coordinate 12) (![⟨427331, by decide⟩,⟨427367, by decide⟩,⟨427389, by decide⟩,⟨427399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28455_427400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28455 ⟨427400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28455
    ⟨427400, by decide⟩ (by decide) (![⟨427331, by decide⟩,⟨427367, by decide⟩,⟨427389, by decide⟩,⟨427399, by decide⟩]) unmarked_context_12_28455_427400 node_context_12_28455_427400
  intro a
  fin_cases a
  · exact context_13_113820_427331
  · exact context_13_113821_427367
  · exact context_13_113822_427389
  · exact context_13_113823_427399

theorem unmarked_context_11_7113_427401 : frontier 10 ⟨427401, by decide⟩
    (prefixCache 11 7113) (prefixPartial 11 7113) = false := by
  decide +kernel

theorem node_context_11_7113_427401 : EJMOriginalGlobalDAGData.nodes 10 ⟨427401, by decide⟩ =
    .split (coordinate 11) (![⟨427145, by decide⟩,⟨427228, by decide⟩,⟨427319, by decide⟩,⟨427400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7113_427401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7113 ⟨427401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7113
    ⟨427401, by decide⟩ (by decide) (![⟨427145, by decide⟩,⟨427228, by decide⟩,⟨427319, by decide⟩,⟨427400, by decide⟩]) unmarked_context_11_7113_427401 node_context_11_7113_427401
  intro a
  fin_cases a
  · exact context_12_28452_427145
  · exact context_12_28453_427228
  · exact context_12_28454_427319
  · exact context_12_28455_427400

theorem selected_cut_16783 : selected 8 ⟨427413, by decide⟩
    (prefixPartial 13 113824) = some ⟨13, 2, 0, 427413, 113824, 945, 16384⟩ := by
  decide +kernel

theorem context_13_113824_427413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113824 ⟨427413, by decide⟩ :=
  accepted_of_selected 13 113824 ⟨427413, by decide⟩ ⟨13, 2, 0, 427413, 113824, 945, 16384⟩
    (by decide) selected_cut_16783

theorem selected_cut_16784 : selected 8 ⟨427448, by decide⟩
    (prefixPartial 13 113825) = some ⟨13, 2, 0, 427448, 113825, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_113825_427448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113825 ⟨427448, by decide⟩ :=
  accepted_of_selected 13 113825 ⟨427448, by decide⟩ ⟨13, 2, 0, 427448, 113825, 2333, 16384⟩
    (by decide) selected_cut_16784

theorem selected_cut_16785 : selected 8 ⟨427464, by decide⟩
    (prefixPartial 13 113826) = some ⟨13, 2, 0, 427464, 113826, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_113826_427464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113826 ⟨427464, by decide⟩ :=
  accepted_of_selected 13 113826 ⟨427464, by decide⟩ ⟨13, 2, 0, 427464, 113826, 1397, 16384⟩
    (by decide) selected_cut_16785

theorem selected_cut_16786 : selected 8 ⟨427471, by decide⟩
    (prefixPartial 13 113827) = some ⟨13, 2, 0, 427471, 113827, 641, 16384⟩ := by
  decide +kernel

theorem context_13_113827_427471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113827 ⟨427471, by decide⟩ :=
  accepted_of_selected 13 113827 ⟨427471, by decide⟩ ⟨13, 2, 0, 427471, 113827, 641, 16384⟩
    (by decide) selected_cut_16786

theorem unmarked_context_12_28456_427472 : frontier 9 ⟨427472, by decide⟩
    (prefixCache 12 28456) (prefixPartial 12 28456) = false := by
  decide +kernel

theorem node_context_12_28456_427472 : EJMOriginalGlobalDAGData.nodes 9 ⟨427472, by decide⟩ =
    .split (coordinate 12) (![⟨427413, by decide⟩,⟨427448, by decide⟩,⟨427464, by decide⟩,⟨427471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28456_427472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28456 ⟨427472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28456
    ⟨427472, by decide⟩ (by decide) (![⟨427413, by decide⟩,⟨427448, by decide⟩,⟨427464, by decide⟩,⟨427471, by decide⟩]) unmarked_context_12_28456_427472 node_context_12_28456_427472
  intro a
  fin_cases a
  · exact context_13_113824_427413
  · exact context_13_113825_427448
  · exact context_13_113826_427464
  · exact context_13_113827_427471

theorem selected_cut_16787 : selected 8 ⟨427492, by decide⟩
    (prefixPartial 13 113828) = some ⟨13, 2, 0, 427492, 113828, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_113828_427492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113828 ⟨427492, by decide⟩ :=
  accepted_of_selected 13 113828 ⟨427492, by decide⟩ ⟨13, 2, 0, 427492, 113828, 1125, 16384⟩
    (by decide) selected_cut_16787

theorem selected_cut_16788 : selected 8 ⟨427529, by decide⟩
    (prefixPartial 13 113829) = some ⟨13, 2, 0, 427529, 113829, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_113829_427529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113829 ⟨427529, by decide⟩ :=
  accepted_of_selected 13 113829 ⟨427529, by decide⟩ ⟨13, 2, 0, 427529, 113829, 2397, 16384⟩
    (by decide) selected_cut_16788

theorem selected_cut_16789 : selected 8 ⟨427549, by decide⟩
    (prefixPartial 13 113830) = some ⟨13, 2, 0, 427549, 113830, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_113830_427549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113830 ⟨427549, by decide⟩ :=
  accepted_of_selected 13 113830 ⟨427549, by decide⟩ ⟨13, 2, 0, 427549, 113830, 1469, 16384⟩
    (by decide) selected_cut_16789

theorem selected_cut_16790 : selected 8 ⟨427562, by decide⟩
    (prefixPartial 13 113831) = some ⟨13, 2, 0, 427562, 113831, 753, 16384⟩ := by
  decide +kernel

theorem context_13_113831_427562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113831 ⟨427562, by decide⟩ :=
  accepted_of_selected 13 113831 ⟨427562, by decide⟩ ⟨13, 2, 0, 427562, 113831, 753, 16384⟩
    (by decide) selected_cut_16790

theorem unmarked_context_12_28457_427563 : frontier 9 ⟨427563, by decide⟩
    (prefixCache 12 28457) (prefixPartial 12 28457) = false := by
  decide +kernel

theorem node_context_12_28457_427563 : EJMOriginalGlobalDAGData.nodes 9 ⟨427563, by decide⟩ =
    .split (coordinate 12) (![⟨427492, by decide⟩,⟨427529, by decide⟩,⟨427549, by decide⟩,⟨427562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28457_427563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28457 ⟨427563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28457
    ⟨427563, by decide⟩ (by decide) (![⟨427492, by decide⟩,⟨427529, by decide⟩,⟨427549, by decide⟩,⟨427562, by decide⟩]) unmarked_context_12_28457_427563 node_context_12_28457_427563
  intro a
  fin_cases a
  · exact context_13_113828_427492
  · exact context_13_113829_427529
  · exact context_13_113830_427549
  · exact context_13_113831_427562

theorem selected_cut_16791 : selected 8 ⟨427575, by decide⟩
    (prefixPartial 13 113832) = some ⟨13, 2, 0, 427575, 113832, 989, 16384⟩ := by
  decide +kernel

theorem context_13_113832_427575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113832 ⟨427575, by decide⟩ :=
  accepted_of_selected 13 113832 ⟨427575, by decide⟩ ⟨13, 2, 0, 427575, 113832, 989, 16384⟩
    (by decide) selected_cut_16791

theorem selected_cut_16792 : selected 8 ⟨427606, by decide⟩
    (prefixPartial 13 113833) = some ⟨13, 2, 0, 427606, 113833, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_113833_427606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113833 ⟨427606, by decide⟩ :=
  accepted_of_selected 13 113833 ⟨427606, by decide⟩ ⟨13, 2, 0, 427606, 113833, 2305, 16384⟩
    (by decide) selected_cut_16792

theorem selected_cut_16793 : selected 8 ⟨427622, by decide⟩
    (prefixPartial 13 113834) = some ⟨13, 2, 0, 427622, 113834, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_113834_427622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113834 ⟨427622, by decide⟩ :=
  accepted_of_selected 13 113834 ⟨427622, by decide⟩ ⟨13, 2, 0, 427622, 113834, 1449, 16384⟩
    (by decide) selected_cut_16793

theorem selected_cut_16794 : selected 8 ⟨427628, by decide⟩
    (prefixPartial 13 113835) = some ⟨13, 2, 0, 427628, 113835, 693, 16384⟩ := by
  decide +kernel

theorem context_13_113835_427628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113835 ⟨427628, by decide⟩ :=
  accepted_of_selected 13 113835 ⟨427628, by decide⟩ ⟨13, 2, 0, 427628, 113835, 693, 16384⟩
    (by decide) selected_cut_16794

theorem unmarked_context_12_28458_427629 : frontier 9 ⟨427629, by decide⟩
    (prefixCache 12 28458) (prefixPartial 12 28458) = false := by
  decide +kernel

theorem node_context_12_28458_427629 : EJMOriginalGlobalDAGData.nodes 9 ⟨427629, by decide⟩ =
    .split (coordinate 12) (![⟨427575, by decide⟩,⟨427606, by decide⟩,⟨427622, by decide⟩,⟨427628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28458_427629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28458 ⟨427629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28458
    ⟨427629, by decide⟩ (by decide) (![⟨427575, by decide⟩,⟨427606, by decide⟩,⟨427622, by decide⟩,⟨427628, by decide⟩]) unmarked_context_12_28458_427629 node_context_12_28458_427629
  intro a
  fin_cases a
  · exact context_13_113832_427575
  · exact context_13_113833_427606
  · exact context_13_113834_427622
  · exact context_13_113835_427628

theorem selected_cut_16795 : selected 8 ⟨427640, by decide⟩
    (prefixPartial 13 113836) = some ⟨13, 2, 0, 427640, 113836, 905, 16384⟩ := by
  decide +kernel

theorem context_13_113836_427640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113836 ⟨427640, by decide⟩ :=
  accepted_of_selected 13 113836 ⟨427640, by decide⟩ ⟨13, 2, 0, 427640, 113836, 905, 16384⟩
    (by decide) selected_cut_16795

theorem selected_cut_16796 : selected 8 ⟨427683, by decide⟩
    (prefixPartial 13 113837) = some ⟨13, 2, 0, 427683, 113837, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_113837_427683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113837 ⟨427683, by decide⟩ :=
  accepted_of_selected 13 113837 ⟨427683, by decide⟩ ⟨13, 2, 0, 427683, 113837, 2509, 16384⟩
    (by decide) selected_cut_16796

theorem selected_cut_16797 : selected 8 ⟨427701, by decide⟩
    (prefixPartial 13 113838) = some ⟨13, 2, 0, 427701, 113838, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_113838_427701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113838 ⟨427701, by decide⟩ :=
  accepted_of_selected 13 113838 ⟨427701, by decide⟩ ⟨13, 2, 0, 427701, 113838, 1421, 16384⟩
    (by decide) selected_cut_16797

theorem selected_cut_16798 : selected 8 ⟨427707, by decide⟩
    (prefixPartial 13 113839) = some ⟨13, 2, 0, 427707, 113839, 729, 16384⟩ := by
  decide +kernel

theorem context_13_113839_427707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113839 ⟨427707, by decide⟩ :=
  accepted_of_selected 13 113839 ⟨427707, by decide⟩ ⟨13, 2, 0, 427707, 113839, 729, 16384⟩
    (by decide) selected_cut_16798

theorem unmarked_context_12_28459_427708 : frontier 9 ⟨427708, by decide⟩
    (prefixCache 12 28459) (prefixPartial 12 28459) = false := by
  decide +kernel

theorem node_context_12_28459_427708 : EJMOriginalGlobalDAGData.nodes 9 ⟨427708, by decide⟩ =
    .split (coordinate 12) (![⟨427640, by decide⟩,⟨427683, by decide⟩,⟨427701, by decide⟩,⟨427707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28459_427708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28459 ⟨427708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28459
    ⟨427708, by decide⟩ (by decide) (![⟨427640, by decide⟩,⟨427683, by decide⟩,⟨427701, by decide⟩,⟨427707, by decide⟩]) unmarked_context_12_28459_427708 node_context_12_28459_427708
  intro a
  fin_cases a
  · exact context_13_113836_427640
  · exact context_13_113837_427683
  · exact context_13_113838_427701
  · exact context_13_113839_427707

theorem unmarked_context_11_7114_427709 : frontier 10 ⟨427709, by decide⟩
    (prefixCache 11 7114) (prefixPartial 11 7114) = false := by
  decide +kernel

theorem node_context_11_7114_427709 : EJMOriginalGlobalDAGData.nodes 10 ⟨427709, by decide⟩ =
    .split (coordinate 11) (![⟨427472, by decide⟩,⟨427563, by decide⟩,⟨427629, by decide⟩,⟨427708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7114_427709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7114 ⟨427709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7114
    ⟨427709, by decide⟩ (by decide) (![⟨427472, by decide⟩,⟨427563, by decide⟩,⟨427629, by decide⟩,⟨427708, by decide⟩]) unmarked_context_11_7114_427709 node_context_11_7114_427709
  intro a
  fin_cases a
  · exact context_12_28456_427472
  · exact context_12_28457_427563
  · exact context_12_28458_427629
  · exact context_12_28459_427708

theorem selected_cut_16799 : selected 8 ⟨427717, by decide⟩
    (prefixPartial 13 113840) = some ⟨13, 2, 0, 427717, 113840, 713, 16384⟩ := by
  decide +kernel

theorem context_13_113840_427717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113840 ⟨427717, by decide⟩ :=
  accepted_of_selected 13 113840 ⟨427717, by decide⟩ ⟨13, 2, 0, 427717, 113840, 713, 16384⟩
    (by decide) selected_cut_16799

theorem selected_cut_16800 : selected 8 ⟨427747, by decide⟩
    (prefixPartial 13 113841) = some ⟨13, 2, 0, 427747, 113841, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_113841_427747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113841 ⟨427747, by decide⟩ :=
  accepted_of_selected 13 113841 ⟨427747, by decide⟩ ⟨13, 2, 0, 427747, 113841, 2145, 16384⟩
    (by decide) selected_cut_16800

theorem selected_cut_16801 : selected 8 ⟨427762, by decide⟩
    (prefixPartial 13 113842) = some ⟨13, 2, 0, 427762, 113842, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_113842_427762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113842 ⟨427762, by decide⟩ :=
  accepted_of_selected 13 113842 ⟨427762, by decide⟩ ⟨13, 2, 0, 427762, 113842, 1185, 16384⟩
    (by decide) selected_cut_16801

theorem selected_cut_16802 : selected 8 ⟨427767, by decide⟩
    (prefixPartial 13 113843) = some ⟨13, 2, 0, 427767, 113843, 657, 16384⟩ := by
  decide +kernel

theorem context_13_113843_427767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113843 ⟨427767, by decide⟩ :=
  accepted_of_selected 13 113843 ⟨427767, by decide⟩ ⟨13, 2, 0, 427767, 113843, 657, 16384⟩
    (by decide) selected_cut_16802

theorem unmarked_context_12_28460_427768 : frontier 9 ⟨427768, by decide⟩
    (prefixCache 12 28460) (prefixPartial 12 28460) = false := by
  decide +kernel

theorem node_context_12_28460_427768 : EJMOriginalGlobalDAGData.nodes 9 ⟨427768, by decide⟩ =
    .split (coordinate 12) (![⟨427717, by decide⟩,⟨427747, by decide⟩,⟨427762, by decide⟩,⟨427767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28460_427768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28460 ⟨427768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28460
    ⟨427768, by decide⟩ (by decide) (![⟨427717, by decide⟩,⟨427747, by decide⟩,⟨427762, by decide⟩,⟨427767, by decide⟩]) unmarked_context_12_28460_427768 node_context_12_28460_427768
  intro a
  fin_cases a
  · exact context_13_113840_427717
  · exact context_13_113841_427747
  · exact context_13_113842_427762
  · exact context_13_113843_427767

theorem selected_cut_16803 : selected 8 ⟨427787, by decide⟩
    (prefixPartial 13 113844) = some ⟨13, 2, 0, 427787, 113844, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_113844_427787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113844 ⟨427787, by decide⟩ :=
  accepted_of_selected 13 113844 ⟨427787, by decide⟩ ⟨13, 2, 0, 427787, 113844, 1013, 16384⟩
    (by decide) selected_cut_16803

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
