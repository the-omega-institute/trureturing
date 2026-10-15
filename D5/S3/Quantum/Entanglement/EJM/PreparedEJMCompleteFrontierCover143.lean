/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover142
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13730 : selected 8 ⟨359722, by decide⟩
    (prefixPartial 13 107600) = some ⟨13, 2, 0, 359722, 107600, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_107600_359722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107600 ⟨359722, by decide⟩ :=
  accepted_of_selected 13 107600 ⟨359722, by decide⟩ ⟨13, 2, 0, 359722, 107600, 1417, 16384⟩
    (by decide) selected_cut_13730

theorem selected_cut_13731 : selected 8 ⟨359745, by decide⟩
    (prefixPartial 13 107601) = some ⟨13, 2, 0, 359745, 107601, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_107601_359745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107601 ⟨359745, by decide⟩ :=
  accepted_of_selected 13 107601 ⟨359745, by decide⟩ ⟨13, 2, 0, 359745, 107601, 1725, 16384⟩
    (by decide) selected_cut_13731

theorem selected_cut_13732 : selected 8 ⟨359761, by decide⟩
    (prefixPartial 13 107602) = some ⟨13, 2, 0, 359761, 107602, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_107602_359761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107602 ⟨359761, by decide⟩ :=
  accepted_of_selected 13 107602 ⟨359761, by decide⟩ ⟨13, 2, 0, 359761, 107602, 1177, 16384⟩
    (by decide) selected_cut_13732

theorem selected_cut_13733 : selected 8 ⟨359768, by decide⟩
    (prefixPartial 13 107603) = some ⟨13, 2, 0, 359768, 107603, 841, 16384⟩ := by
  decide +kernel

theorem context_13_107603_359768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107603 ⟨359768, by decide⟩ :=
  accepted_of_selected 13 107603 ⟨359768, by decide⟩ ⟨13, 2, 0, 359768, 107603, 841, 16384⟩
    (by decide) selected_cut_13733

theorem unmarked_context_12_26900_359769 : frontier 9 ⟨359769, by decide⟩
    (prefixCache 12 26900) (prefixPartial 12 26900) = false := by
  decide +kernel

theorem node_context_12_26900_359769 : EJMOriginalGlobalDAGData.nodes 9 ⟨359769, by decide⟩ =
    .split (coordinate 12) (![⟨359722, by decide⟩,⟨359745, by decide⟩,⟨359761, by decide⟩,⟨359768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26900_359769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26900 ⟨359769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26900
    ⟨359769, by decide⟩ (by decide) (![⟨359722, by decide⟩,⟨359745, by decide⟩,⟨359761, by decide⟩,⟨359768, by decide⟩]) unmarked_context_12_26900_359769 node_context_12_26900_359769
  intro a
  fin_cases a
  · exact context_13_107600_359722
  · exact context_13_107601_359745
  · exact context_13_107602_359761
  · exact context_13_107603_359768

theorem selected_cut_13734 : selected 9 ⟨234650, by decide⟩
    (prefixPartial 12 26901) = some ⟨12, 1, 0, 234650, 26901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26901_234650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26901 ⟨234650, by decide⟩ :=
  accepted_of_selected 12 26901 ⟨234650, by decide⟩ ⟨12, 1, 0, 234650, 26901, 1, 65536⟩
    (by decide) selected_cut_13734

theorem selected_cut_13735 : selected 8 ⟨359792, by decide⟩
    (prefixPartial 13 107608) = some ⟨13, 2, 0, 359792, 107608, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_107608_359792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107608 ⟨359792, by decide⟩ :=
  accepted_of_selected 13 107608 ⟨359792, by decide⟩ ⟨13, 2, 0, 359792, 107608, 1857, 16384⟩
    (by decide) selected_cut_13735

theorem selected_cut_13736 : selected 8 ⟨359815, by decide⟩
    (prefixPartial 13 107609) = some ⟨13, 2, 0, 359815, 107609, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_107609_359815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107609 ⟨359815, by decide⟩ :=
  accepted_of_selected 13 107609 ⟨359815, by decide⟩ ⟨13, 2, 0, 359815, 107609, 1949, 16384⟩
    (by decide) selected_cut_13736

theorem selected_cut_13737 : selected 8 ⟨359834, by decide⟩
    (prefixPartial 13 107610) = some ⟨13, 2, 0, 359834, 107610, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_107610_359834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107610 ⟨359834, by decide⟩ :=
  accepted_of_selected 13 107610 ⟨359834, by decide⟩ ⟨13, 2, 0, 359834, 107610, 1501, 16384⟩
    (by decide) selected_cut_13737

theorem selected_cut_13738 : selected 8 ⟨359841, by decide⟩
    (prefixPartial 13 107611) = some ⟨13, 2, 0, 359841, 107611, 945, 16384⟩ := by
  decide +kernel

theorem context_13_107611_359841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107611 ⟨359841, by decide⟩ :=
  accepted_of_selected 13 107611 ⟨359841, by decide⟩ ⟨13, 2, 0, 359841, 107611, 945, 16384⟩
    (by decide) selected_cut_13738

theorem unmarked_context_12_26902_359842 : frontier 9 ⟨359842, by decide⟩
    (prefixCache 12 26902) (prefixPartial 12 26902) = false := by
  decide +kernel

theorem node_context_12_26902_359842 : EJMOriginalGlobalDAGData.nodes 9 ⟨359842, by decide⟩ =
    .split (coordinate 12) (![⟨359792, by decide⟩,⟨359815, by decide⟩,⟨359834, by decide⟩,⟨359841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26902_359842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26902 ⟨359842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26902
    ⟨359842, by decide⟩ (by decide) (![⟨359792, by decide⟩,⟨359815, by decide⟩,⟨359834, by decide⟩,⟨359841, by decide⟩]) unmarked_context_12_26902_359842 node_context_12_26902_359842
  intro a
  fin_cases a
  · exact context_13_107608_359792
  · exact context_13_107609_359815
  · exact context_13_107610_359834
  · exact context_13_107611_359841

theorem selected_cut_13739 : selected 8 ⟨359862, by decide⟩
    (prefixPartial 13 107612) = some ⟨13, 2, 0, 359862, 107612, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_107612_359862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107612 ⟨359862, by decide⟩ :=
  accepted_of_selected 13 107612 ⟨359862, by decide⟩ ⟨13, 2, 0, 359862, 107612, 1773, 16384⟩
    (by decide) selected_cut_13739

theorem selected_cut_13740 : selected 8 ⟨359885, by decide⟩
    (prefixPartial 13 107613) = some ⟨13, 2, 0, 359885, 107613, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_107613_359885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107613 ⟨359885, by decide⟩ :=
  accepted_of_selected 13 107613 ⟨359885, by decide⟩ ⟨13, 2, 0, 359885, 107613, 2081, 16384⟩
    (by decide) selected_cut_13740

theorem selected_cut_13741 : selected 8 ⟨359901, by decide⟩
    (prefixPartial 13 107614) = some ⟨13, 2, 0, 359901, 107614, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_107614_359901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107614 ⟨359901, by decide⟩ :=
  accepted_of_selected 13 107614 ⟨359901, by decide⟩ ⟨13, 2, 0, 359901, 107614, 1409, 16384⟩
    (by decide) selected_cut_13741

theorem selected_cut_13742 : selected 8 ⟨359909, by decide⟩
    (prefixPartial 13 107615) = some ⟨13, 2, 0, 359909, 107615, 941, 16384⟩ := by
  decide +kernel

theorem context_13_107615_359909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107615 ⟨359909, by decide⟩ :=
  accepted_of_selected 13 107615 ⟨359909, by decide⟩ ⟨13, 2, 0, 359909, 107615, 941, 16384⟩
    (by decide) selected_cut_13742

theorem unmarked_context_12_26903_359910 : frontier 9 ⟨359910, by decide⟩
    (prefixCache 12 26903) (prefixPartial 12 26903) = false := by
  decide +kernel

theorem node_context_12_26903_359910 : EJMOriginalGlobalDAGData.nodes 9 ⟨359910, by decide⟩ =
    .split (coordinate 12) (![⟨359862, by decide⟩,⟨359885, by decide⟩,⟨359901, by decide⟩,⟨359909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26903_359910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26903 ⟨359910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26903
    ⟨359910, by decide⟩ (by decide) (![⟨359862, by decide⟩,⟨359885, by decide⟩,⟨359901, by decide⟩,⟨359909, by decide⟩]) unmarked_context_12_26903_359910 node_context_12_26903_359910
  intro a
  fin_cases a
  · exact context_13_107612_359862
  · exact context_13_107613_359885
  · exact context_13_107614_359901
  · exact context_13_107615_359909

theorem unmarked_context_11_6725_359911 : frontier 10 ⟨359911, by decide⟩
    (prefixCache 11 6725) (prefixPartial 11 6725) = false := by
  decide +kernel

theorem node_context_11_6725_359911 : EJMOriginalGlobalDAGData.nodes 10 ⟨359911, by decide⟩ =
    .split (coordinate 11) (![⟨359769, by decide⟩,⟨234650, by decide⟩,⟨359842, by decide⟩,⟨359910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6725_359911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6725 ⟨359911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6725
    ⟨359911, by decide⟩ (by decide) (![⟨359769, by decide⟩,⟨234650, by decide⟩,⟨359842, by decide⟩,⟨359910, by decide⟩]) unmarked_context_11_6725_359911 node_context_11_6725_359911
  intro a
  fin_cases a
  · exact context_12_26900_359769
  · exact context_12_26901_234650
  · exact context_12_26902_359842
  · exact context_12_26903_359910

theorem selected_cut_13743 : selected 8 ⟨359928, by decide⟩
    (prefixPartial 13 107616) = some ⟨13, 2, 0, 359928, 107616, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_107616_359928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107616 ⟨359928, by decide⟩ :=
  accepted_of_selected 13 107616 ⟨359928, by decide⟩ ⟨13, 2, 0, 359928, 107616, 1405, 16384⟩
    (by decide) selected_cut_13743

theorem selected_cut_13744 : selected 8 ⟨359955, by decide⟩
    (prefixPartial 13 107617) = some ⟨13, 2, 0, 359955, 107617, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_107617_359955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107617 ⟨359955, by decide⟩ :=
  accepted_of_selected 13 107617 ⟨359955, by decide⟩ ⟨13, 2, 0, 359955, 107617, 2113, 16384⟩
    (by decide) selected_cut_13744

theorem selected_cut_13745 : selected 8 ⟨359974, by decide⟩
    (prefixPartial 13 107618) = some ⟨13, 2, 0, 359974, 107618, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_107618_359974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107618 ⟨359974, by decide⟩ :=
  accepted_of_selected 13 107618 ⟨359974, by decide⟩ ⟨13, 2, 0, 359974, 107618, 1473, 16384⟩
    (by decide) selected_cut_13745

theorem selected_cut_13746 : selected 8 ⟨359982, by decide⟩
    (prefixPartial 13 107619) = some ⟨13, 2, 0, 359982, 107619, 829, 16384⟩ := by
  decide +kernel

theorem context_13_107619_359982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107619 ⟨359982, by decide⟩ :=
  accepted_of_selected 13 107619 ⟨359982, by decide⟩ ⟨13, 2, 0, 359982, 107619, 829, 16384⟩
    (by decide) selected_cut_13746

theorem unmarked_context_12_26904_359983 : frontier 9 ⟨359983, by decide⟩
    (prefixCache 12 26904) (prefixPartial 12 26904) = false := by
  decide +kernel

theorem node_context_12_26904_359983 : EJMOriginalGlobalDAGData.nodes 9 ⟨359983, by decide⟩ =
    .split (coordinate 12) (![⟨359928, by decide⟩,⟨359955, by decide⟩,⟨359974, by decide⟩,⟨359982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26904_359983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26904 ⟨359983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26904
    ⟨359983, by decide⟩ (by decide) (![⟨359928, by decide⟩,⟨359955, by decide⟩,⟨359974, by decide⟩,⟨359982, by decide⟩]) unmarked_context_12_26904_359983 node_context_12_26904_359983
  intro a
  fin_cases a
  · exact context_13_107616_359928
  · exact context_13_107617_359955
  · exact context_13_107618_359974
  · exact context_13_107619_359982

theorem selected_cut_13747 : selected 8 ⟨360005, by decide⟩
    (prefixPartial 13 107620) = some ⟨13, 2, 0, 360005, 107620, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_107620_360005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107620 ⟨360005, by decide⟩ :=
  accepted_of_selected 13 107620 ⟨360005, by decide⟩ ⟨13, 2, 0, 360005, 107620, 1197, 16384⟩
    (by decide) selected_cut_13747

theorem selected_cut_13748 : selected 8 ⟨360022, by decide⟩
    (prefixPartial 13 107621) = some ⟨13, 2, 0, 360022, 107621, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_107621_360022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107621 ⟨360022, by decide⟩ :=
  accepted_of_selected 13 107621 ⟨360022, by decide⟩ ⟨13, 2, 0, 360022, 107621, 1373, 16384⟩
    (by decide) selected_cut_13748

theorem selected_cut_13749 : selected 8 ⟨360038, by decide⟩
    (prefixPartial 13 107622) = some ⟨13, 2, 0, 360038, 107622, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_107622_360038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107622 ⟨360038, by decide⟩ :=
  accepted_of_selected 13 107622 ⟨360038, by decide⟩ ⟨13, 2, 0, 360038, 107622, 1297, 16384⟩
    (by decide) selected_cut_13749

theorem selected_cut_13750 : selected 8 ⟨360044, by decide⟩
    (prefixPartial 13 107623) = some ⟨13, 2, 0, 360044, 107623, 737, 16384⟩ := by
  decide +kernel

theorem context_13_107623_360044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107623 ⟨360044, by decide⟩ :=
  accepted_of_selected 13 107623 ⟨360044, by decide⟩ ⟨13, 2, 0, 360044, 107623, 737, 16384⟩
    (by decide) selected_cut_13750

theorem unmarked_context_12_26905_360045 : frontier 9 ⟨360045, by decide⟩
    (prefixCache 12 26905) (prefixPartial 12 26905) = false := by
  decide +kernel

theorem node_context_12_26905_360045 : EJMOriginalGlobalDAGData.nodes 9 ⟨360045, by decide⟩ =
    .split (coordinate 12) (![⟨360005, by decide⟩,⟨360022, by decide⟩,⟨360038, by decide⟩,⟨360044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26905_360045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26905 ⟨360045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26905
    ⟨360045, by decide⟩ (by decide) (![⟨360005, by decide⟩,⟨360022, by decide⟩,⟨360038, by decide⟩,⟨360044, by decide⟩]) unmarked_context_12_26905_360045 node_context_12_26905_360045
  intro a
  fin_cases a
  · exact context_13_107620_360005
  · exact context_13_107621_360022
  · exact context_13_107622_360038
  · exact context_13_107623_360044

theorem selected_cut_13751 : selected 8 ⟨360066, by decide⟩
    (prefixPartial 13 107624) = some ⟨13, 2, 0, 360066, 107624, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_107624_360066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107624 ⟨360066, by decide⟩ :=
  accepted_of_selected 13 107624 ⟨360066, by decide⟩ ⟨13, 2, 0, 360066, 107624, 1561, 16384⟩
    (by decide) selected_cut_13751

theorem selected_cut_13752 : selected 8 ⟨360088, by decide⟩
    (prefixPartial 13 107625) = some ⟨13, 2, 0, 360088, 107625, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_107625_360088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107625 ⟨360088, by decide⟩ :=
  accepted_of_selected 13 107625 ⟨360088, by decide⟩ ⟨13, 2, 0, 360088, 107625, 2205, 16384⟩
    (by decide) selected_cut_13752

theorem selected_cut_13753 : selected 8 ⟨360109, by decide⟩
    (prefixPartial 13 107626) = some ⟨13, 2, 0, 360109, 107626, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_107626_360109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107626 ⟨360109, by decide⟩ :=
  accepted_of_selected 13 107626 ⟨360109, by decide⟩ ⟨13, 2, 0, 360109, 107626, 1637, 16384⟩
    (by decide) selected_cut_13753

theorem selected_cut_13754 : selected 8 ⟨360116, by decide⟩
    (prefixPartial 13 107627) = some ⟨13, 2, 0, 360116, 107627, 885, 16384⟩ := by
  decide +kernel

theorem context_13_107627_360116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107627 ⟨360116, by decide⟩ :=
  accepted_of_selected 13 107627 ⟨360116, by decide⟩ ⟨13, 2, 0, 360116, 107627, 885, 16384⟩
    (by decide) selected_cut_13754

theorem unmarked_context_12_26906_360117 : frontier 9 ⟨360117, by decide⟩
    (prefixCache 12 26906) (prefixPartial 12 26906) = false := by
  decide +kernel

theorem node_context_12_26906_360117 : EJMOriginalGlobalDAGData.nodes 9 ⟨360117, by decide⟩ =
    .split (coordinate 12) (![⟨360066, by decide⟩,⟨360088, by decide⟩,⟨360109, by decide⟩,⟨360116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26906_360117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26906 ⟨360117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26906
    ⟨360117, by decide⟩ (by decide) (![⟨360066, by decide⟩,⟨360088, by decide⟩,⟨360109, by decide⟩,⟨360116, by decide⟩]) unmarked_context_12_26906_360117 node_context_12_26906_360117
  intro a
  fin_cases a
  · exact context_13_107624_360066
  · exact context_13_107625_360088
  · exact context_13_107626_360109
  · exact context_13_107627_360116

theorem selected_cut_13755 : selected 8 ⟨360144, by decide⟩
    (prefixPartial 13 107628) = some ⟨13, 2, 0, 360144, 107628, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_107628_360144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107628 ⟨360144, by decide⟩ :=
  accepted_of_selected 13 107628 ⟨360144, by decide⟩ ⟨13, 2, 0, 360144, 107628, 1685, 16384⟩
    (by decide) selected_cut_13755

theorem selected_cut_13756 : selected 8 ⟨360177, by decide⟩
    (prefixPartial 13 107629) = some ⟨13, 2, 0, 360177, 107629, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_107629_360177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107629 ⟨360177, by decide⟩ :=
  accepted_of_selected 13 107629 ⟨360177, by decide⟩ ⟨13, 2, 0, 360177, 107629, 2605, 16384⟩
    (by decide) selected_cut_13756

theorem selected_cut_13757 : selected 8 ⟨360197, by decide⟩
    (prefixPartial 13 107630) = some ⟨13, 2, 0, 360197, 107630, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_107630_360197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107630 ⟨360197, by decide⟩ :=
  accepted_of_selected 13 107630 ⟨360197, by decide⟩ ⟨13, 2, 0, 360197, 107630, 1537, 16384⟩
    (by decide) selected_cut_13757

theorem selected_cut_13758 : selected 8 ⟨360206, by decide⟩
    (prefixPartial 13 107631) = some ⟨13, 2, 0, 360206, 107631, 889, 16384⟩ := by
  decide +kernel

theorem context_13_107631_360206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107631 ⟨360206, by decide⟩ :=
  accepted_of_selected 13 107631 ⟨360206, by decide⟩ ⟨13, 2, 0, 360206, 107631, 889, 16384⟩
    (by decide) selected_cut_13758

theorem unmarked_context_12_26907_360207 : frontier 9 ⟨360207, by decide⟩
    (prefixCache 12 26907) (prefixPartial 12 26907) = false := by
  decide +kernel

theorem node_context_12_26907_360207 : EJMOriginalGlobalDAGData.nodes 9 ⟨360207, by decide⟩ =
    .split (coordinate 12) (![⟨360144, by decide⟩,⟨360177, by decide⟩,⟨360197, by decide⟩,⟨360206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26907_360207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26907 ⟨360207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26907
    ⟨360207, by decide⟩ (by decide) (![⟨360144, by decide⟩,⟨360177, by decide⟩,⟨360197, by decide⟩,⟨360206, by decide⟩]) unmarked_context_12_26907_360207 node_context_12_26907_360207
  intro a
  fin_cases a
  · exact context_13_107628_360144
  · exact context_13_107629_360177
  · exact context_13_107630_360197
  · exact context_13_107631_360206

theorem unmarked_context_11_6726_360208 : frontier 10 ⟨360208, by decide⟩
    (prefixCache 11 6726) (prefixPartial 11 6726) = false := by
  decide +kernel

theorem node_context_11_6726_360208 : EJMOriginalGlobalDAGData.nodes 10 ⟨360208, by decide⟩ =
    .split (coordinate 11) (![⟨359983, by decide⟩,⟨360045, by decide⟩,⟨360117, by decide⟩,⟨360207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6726_360208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6726 ⟨360208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6726
    ⟨360208, by decide⟩ (by decide) (![⟨359983, by decide⟩,⟨360045, by decide⟩,⟨360117, by decide⟩,⟨360207, by decide⟩]) unmarked_context_11_6726_360208 node_context_11_6726_360208
  intro a
  fin_cases a
  · exact context_12_26904_359983
  · exact context_12_26905_360045
  · exact context_12_26906_360117
  · exact context_12_26907_360207

theorem selected_cut_13759 : selected 8 ⟨360226, by decide⟩
    (prefixPartial 13 107632) = some ⟨13, 2, 0, 360226, 107632, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_107632_360226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107632 ⟨360226, by decide⟩ :=
  accepted_of_selected 13 107632 ⟨360226, by decide⟩ ⟨13, 2, 0, 360226, 107632, 1253, 16384⟩
    (by decide) selected_cut_13759

theorem selected_cut_13760 : selected 8 ⟨360250, by decide⟩
    (prefixPartial 13 107633) = some ⟨13, 2, 0, 360250, 107633, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_107633_360250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107633 ⟨360250, by decide⟩ :=
  accepted_of_selected 13 107633 ⟨360250, by decide⟩ ⟨13, 2, 0, 360250, 107633, 2245, 16384⟩
    (by decide) selected_cut_13760

theorem selected_cut_13761 : selected 8 ⟨360267, by decide⟩
    (prefixPartial 13 107634) = some ⟨13, 2, 0, 360267, 107634, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_107634_360267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107634 ⟨360267, by decide⟩ :=
  accepted_of_selected 13 107634 ⟨360267, by decide⟩ ⟨13, 2, 0, 360267, 107634, 1345, 16384⟩
    (by decide) selected_cut_13761

theorem selected_cut_13762 : selected 8 ⟨360274, by decide⟩
    (prefixPartial 13 107635) = some ⟨13, 2, 0, 360274, 107635, 861, 16384⟩ := by
  decide +kernel

theorem context_13_107635_360274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107635 ⟨360274, by decide⟩ :=
  accepted_of_selected 13 107635 ⟨360274, by decide⟩ ⟨13, 2, 0, 360274, 107635, 861, 16384⟩
    (by decide) selected_cut_13762

theorem unmarked_context_12_26908_360275 : frontier 9 ⟨360275, by decide⟩
    (prefixCache 12 26908) (prefixPartial 12 26908) = false := by
  decide +kernel

theorem node_context_12_26908_360275 : EJMOriginalGlobalDAGData.nodes 9 ⟨360275, by decide⟩ =
    .split (coordinate 12) (![⟨360226, by decide⟩,⟨360250, by decide⟩,⟨360267, by decide⟩,⟨360274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26908_360275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26908 ⟨360275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26908
    ⟨360275, by decide⟩ (by decide) (![⟨360226, by decide⟩,⟨360250, by decide⟩,⟨360267, by decide⟩,⟨360274, by decide⟩]) unmarked_context_12_26908_360275 node_context_12_26908_360275
  intro a
  fin_cases a
  · exact context_13_107632_360226
  · exact context_13_107633_360250
  · exact context_13_107634_360267
  · exact context_13_107635_360274

theorem selected_cut_13763 : selected 8 ⟨360292, by decide⟩
    (prefixPartial 13 107636) = some ⟨13, 2, 0, 360292, 107636, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_107636_360292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107636 ⟨360292, by decide⟩ :=
  accepted_of_selected 13 107636 ⟨360292, by decide⟩ ⟨13, 2, 0, 360292, 107636, 1265, 16384⟩
    (by decide) selected_cut_13763

theorem selected_cut_13764 : selected 8 ⟨360313, by decide⟩
    (prefixPartial 13 107637) = some ⟨13, 2, 0, 360313, 107637, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_107637_360313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107637 ⟨360313, by decide⟩ :=
  accepted_of_selected 13 107637 ⟨360313, by decide⟩ ⟨13, 2, 0, 360313, 107637, 1717, 16384⟩
    (by decide) selected_cut_13764

theorem selected_cut_13765 : selected 8 ⟨360331, by decide⟩
    (prefixPartial 13 107638) = some ⟨13, 2, 0, 360331, 107638, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_107638_360331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107638 ⟨360331, by decide⟩ :=
  accepted_of_selected 13 107638 ⟨360331, by decide⟩ ⟨13, 2, 0, 360331, 107638, 1297, 16384⟩
    (by decide) selected_cut_13765

theorem selected_cut_13766 : selected 8 ⟨360336, by decide⟩
    (prefixPartial 13 107639) = some ⟨13, 2, 0, 360336, 107639, 725, 16384⟩ := by
  decide +kernel

theorem context_13_107639_360336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107639 ⟨360336, by decide⟩ :=
  accepted_of_selected 13 107639 ⟨360336, by decide⟩ ⟨13, 2, 0, 360336, 107639, 725, 16384⟩
    (by decide) selected_cut_13766

theorem unmarked_context_12_26909_360337 : frontier 9 ⟨360337, by decide⟩
    (prefixCache 12 26909) (prefixPartial 12 26909) = false := by
  decide +kernel

theorem node_context_12_26909_360337 : EJMOriginalGlobalDAGData.nodes 9 ⟨360337, by decide⟩ =
    .split (coordinate 12) (![⟨360292, by decide⟩,⟨360313, by decide⟩,⟨360331, by decide⟩,⟨360336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26909_360337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26909 ⟨360337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26909
    ⟨360337, by decide⟩ (by decide) (![⟨360292, by decide⟩,⟨360313, by decide⟩,⟨360331, by decide⟩,⟨360336, by decide⟩]) unmarked_context_12_26909_360337 node_context_12_26909_360337
  intro a
  fin_cases a
  · exact context_13_107636_360292
  · exact context_13_107637_360313
  · exact context_13_107638_360331
  · exact context_13_107639_360336

theorem selected_cut_13767 : selected 8 ⟨360366, by decide⟩
    (prefixPartial 13 107640) = some ⟨13, 2, 0, 360366, 107640, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_107640_360366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107640 ⟨360366, by decide⟩ :=
  accepted_of_selected 13 107640 ⟨360366, by decide⟩ ⟨13, 2, 0, 360366, 107640, 1581, 16384⟩
    (by decide) selected_cut_13767

theorem selected_cut_13768 : selected 8 ⟨360397, by decide⟩
    (prefixPartial 13 107641) = some ⟨13, 2, 0, 360397, 107641, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_107641_360397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107641 ⟨360397, by decide⟩ :=
  accepted_of_selected 13 107641 ⟨360397, by decide⟩ ⟨13, 2, 0, 360397, 107641, 2449, 16384⟩
    (by decide) selected_cut_13768

theorem selected_cut_13769 : selected 8 ⟨360416, by decide⟩
    (prefixPartial 13 107642) = some ⟨13, 2, 0, 360416, 107642, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_107642_360416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107642 ⟨360416, by decide⟩ :=
  accepted_of_selected 13 107642 ⟨360416, by decide⟩ ⟨13, 2, 0, 360416, 107642, 1489, 16384⟩
    (by decide) selected_cut_13769

theorem selected_cut_13770 : selected 8 ⟨360422, by decide⟩
    (prefixPartial 13 107643) = some ⟨13, 2, 0, 360422, 107643, 865, 16384⟩ := by
  decide +kernel

theorem context_13_107643_360422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107643 ⟨360422, by decide⟩ :=
  accepted_of_selected 13 107643 ⟨360422, by decide⟩ ⟨13, 2, 0, 360422, 107643, 865, 16384⟩
    (by decide) selected_cut_13770

theorem unmarked_context_12_26910_360423 : frontier 9 ⟨360423, by decide⟩
    (prefixCache 12 26910) (prefixPartial 12 26910) = false := by
  decide +kernel

theorem node_context_12_26910_360423 : EJMOriginalGlobalDAGData.nodes 9 ⟨360423, by decide⟩ =
    .split (coordinate 12) (![⟨360366, by decide⟩,⟨360397, by decide⟩,⟨360416, by decide⟩,⟨360422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26910_360423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26910 ⟨360423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26910
    ⟨360423, by decide⟩ (by decide) (![⟨360366, by decide⟩,⟨360397, by decide⟩,⟨360416, by decide⟩,⟨360422, by decide⟩]) unmarked_context_12_26910_360423 node_context_12_26910_360423
  intro a
  fin_cases a
  · exact context_13_107640_360366
  · exact context_13_107641_360397
  · exact context_13_107642_360416
  · exact context_13_107643_360422

theorem selected_cut_13771 : selected 8 ⟨360451, by decide⟩
    (prefixPartial 13 107644) = some ⟨13, 2, 0, 360451, 107644, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_107644_360451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107644 ⟨360451, by decide⟩ :=
  accepted_of_selected 13 107644 ⟨360451, by decide⟩ ⟨13, 2, 0, 360451, 107644, 1653, 16384⟩
    (by decide) selected_cut_13771

theorem selected_cut_13772 : selected 8 ⟨360478, by decide⟩
    (prefixPartial 13 107645) = some ⟨13, 2, 0, 360478, 107645, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_107645_360478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107645 ⟨360478, by decide⟩ :=
  accepted_of_selected 13 107645 ⟨360478, by decide⟩ ⟨13, 2, 0, 360478, 107645, 2409, 16384⟩
    (by decide) selected_cut_13772

theorem selected_cut_13773 : selected 8 ⟨360498, by decide⟩
    (prefixPartial 13 107646) = some ⟨13, 2, 0, 360498, 107646, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_107646_360498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107646 ⟨360498, by decide⟩ :=
  accepted_of_selected 13 107646 ⟨360498, by decide⟩ ⟨13, 2, 0, 360498, 107646, 1437, 16384⟩
    (by decide) selected_cut_13773

theorem selected_cut_13774 : selected 8 ⟨360507, by decide⟩
    (prefixPartial 13 107647) = some ⟨13, 2, 0, 360507, 107647, 877, 16384⟩ := by
  decide +kernel

theorem context_13_107647_360507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107647 ⟨360507, by decide⟩ :=
  accepted_of_selected 13 107647 ⟨360507, by decide⟩ ⟨13, 2, 0, 360507, 107647, 877, 16384⟩
    (by decide) selected_cut_13774

theorem unmarked_context_12_26911_360508 : frontier 9 ⟨360508, by decide⟩
    (prefixCache 12 26911) (prefixPartial 12 26911) = false := by
  decide +kernel

theorem node_context_12_26911_360508 : EJMOriginalGlobalDAGData.nodes 9 ⟨360508, by decide⟩ =
    .split (coordinate 12) (![⟨360451, by decide⟩,⟨360478, by decide⟩,⟨360498, by decide⟩,⟨360507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26911_360508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26911 ⟨360508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26911
    ⟨360508, by decide⟩ (by decide) (![⟨360451, by decide⟩,⟨360478, by decide⟩,⟨360498, by decide⟩,⟨360507, by decide⟩]) unmarked_context_12_26911_360508 node_context_12_26911_360508
  intro a
  fin_cases a
  · exact context_13_107644_360451
  · exact context_13_107645_360478
  · exact context_13_107646_360498
  · exact context_13_107647_360507

theorem unmarked_context_11_6727_360509 : frontier 10 ⟨360509, by decide⟩
    (prefixCache 11 6727) (prefixPartial 11 6727) = false := by
  decide +kernel

theorem node_context_11_6727_360509 : EJMOriginalGlobalDAGData.nodes 10 ⟨360509, by decide⟩ =
    .split (coordinate 11) (![⟨360275, by decide⟩,⟨360337, by decide⟩,⟨360423, by decide⟩,⟨360508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6727_360509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6727 ⟨360509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6727
    ⟨360509, by decide⟩ (by decide) (![⟨360275, by decide⟩,⟨360337, by decide⟩,⟨360423, by decide⟩,⟨360508, by decide⟩]) unmarked_context_11_6727_360509 node_context_11_6727_360509
  intro a
  fin_cases a
  · exact context_12_26908_360275
  · exact context_12_26909_360337
  · exact context_12_26910_360423
  · exact context_12_26911_360508

theorem unmarked_context_10_1681_360510 : frontier 11 ⟨360510, by decide⟩
    (prefixCache 10 1681) (prefixPartial 10 1681) = false := by
  decide +kernel

theorem node_context_10_1681_360510 : EJMOriginalGlobalDAGData.nodes 11 ⟨360510, by decide⟩ =
    .split (coordinate 10) (![⟨359705, by decide⟩,⟨359911, by decide⟩,⟨360208, by decide⟩,⟨360509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1681_360510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1681 ⟨360510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1681
    ⟨360510, by decide⟩ (by decide) (![⟨359705, by decide⟩,⟨359911, by decide⟩,⟨360208, by decide⟩,⟨360509, by decide⟩]) unmarked_context_10_1681_360510 node_context_10_1681_360510
  intro a
  fin_cases a
  · exact context_11_6724_359705
  · exact context_11_6725_359911
  · exact context_11_6726_360208
  · exact context_11_6727_360509

theorem selected_cut_13775 : selected 8 ⟨360522, by decide⟩
    (prefixPartial 13 107648) = some ⟨13, 2, 0, 360522, 107648, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_107648_360522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107648 ⟨360522, by decide⟩ :=
  accepted_of_selected 13 107648 ⟨360522, by decide⟩ ⟨13, 2, 0, 360522, 107648, 1073, 16384⟩
    (by decide) selected_cut_13775

theorem selected_cut_13776 : selected 8 ⟨360543, by decide⟩
    (prefixPartial 13 107649) = some ⟨13, 2, 0, 360543, 107649, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_107649_360543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107649 ⟨360543, by decide⟩ :=
  accepted_of_selected 13 107649 ⟨360543, by decide⟩ ⟨13, 2, 0, 360543, 107649, 2221, 16384⟩
    (by decide) selected_cut_13776

theorem selected_cut_13777 : selected 8 ⟨360561, by decide⟩
    (prefixPartial 13 107650) = some ⟨13, 2, 0, 360561, 107650, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_107650_360561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107650 ⟨360561, by decide⟩ :=
  accepted_of_selected 13 107650 ⟨360561, by decide⟩ ⟨13, 2, 0, 360561, 107650, 1161, 16384⟩
    (by decide) selected_cut_13777

theorem selected_cut_13778 : selected 8 ⟨360567, by decide⟩
    (prefixPartial 13 107651) = some ⟨13, 2, 0, 360567, 107651, 845, 16384⟩ := by
  decide +kernel

theorem context_13_107651_360567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107651 ⟨360567, by decide⟩ :=
  accepted_of_selected 13 107651 ⟨360567, by decide⟩ ⟨13, 2, 0, 360567, 107651, 845, 16384⟩
    (by decide) selected_cut_13778

theorem unmarked_context_12_26912_360568 : frontier 9 ⟨360568, by decide⟩
    (prefixCache 12 26912) (prefixPartial 12 26912) = false := by
  decide +kernel

theorem node_context_12_26912_360568 : EJMOriginalGlobalDAGData.nodes 9 ⟨360568, by decide⟩ =
    .split (coordinate 12) (![⟨360522, by decide⟩,⟨360543, by decide⟩,⟨360561, by decide⟩,⟨360567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26912_360568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26912 ⟨360568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26912
    ⟨360568, by decide⟩ (by decide) (![⟨360522, by decide⟩,⟨360543, by decide⟩,⟨360561, by decide⟩,⟨360567, by decide⟩]) unmarked_context_12_26912_360568 node_context_12_26912_360568
  intro a
  fin_cases a
  · exact context_13_107648_360522
  · exact context_13_107649_360543
  · exact context_13_107650_360561
  · exact context_13_107651_360567

theorem selected_cut_13779 : selected 8 ⟨360580, by decide⟩
    (prefixPartial 13 107652) = some ⟨13, 2, 0, 360580, 107652, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_107652_360580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107652 ⟨360580, by decide⟩ :=
  accepted_of_selected 13 107652 ⟨360580, by decide⟩ ⟨13, 2, 0, 360580, 107652, 1097, 16384⟩
    (by decide) selected_cut_13779

theorem selected_cut_13780 : selected 8 ⟨360602, by decide⟩
    (prefixPartial 13 107653) = some ⟨13, 2, 0, 360602, 107653, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_107653_360602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107653 ⟨360602, by decide⟩ :=
  accepted_of_selected 13 107653 ⟨360602, by decide⟩ ⟨13, 2, 0, 360602, 107653, 1913, 16384⟩
    (by decide) selected_cut_13780

theorem selected_cut_13781 : selected 8 ⟨360621, by decide⟩
    (prefixPartial 13 107654) = some ⟨13, 2, 0, 360621, 107654, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_107654_360621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107654 ⟨360621, by decide⟩ :=
  accepted_of_selected 13 107654 ⟨360621, by decide⟩ ⟨13, 2, 0, 360621, 107654, 1317, 16384⟩
    (by decide) selected_cut_13781

theorem selected_cut_13782 : selected 8 ⟨360627, by decide⟩
    (prefixPartial 13 107655) = some ⟨13, 2, 0, 360627, 107655, 909, 16384⟩ := by
  decide +kernel

theorem context_13_107655_360627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107655 ⟨360627, by decide⟩ :=
  accepted_of_selected 13 107655 ⟨360627, by decide⟩ ⟨13, 2, 0, 360627, 107655, 909, 16384⟩
    (by decide) selected_cut_13782

theorem unmarked_context_12_26913_360628 : frontier 9 ⟨360628, by decide⟩
    (prefixCache 12 26913) (prefixPartial 12 26913) = false := by
  decide +kernel

theorem node_context_12_26913_360628 : EJMOriginalGlobalDAGData.nodes 9 ⟨360628, by decide⟩ =
    .split (coordinate 12) (![⟨360580, by decide⟩,⟨360602, by decide⟩,⟨360621, by decide⟩,⟨360627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26913_360628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26913 ⟨360628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26913
    ⟨360628, by decide⟩ (by decide) (![⟨360580, by decide⟩,⟨360602, by decide⟩,⟨360621, by decide⟩,⟨360627, by decide⟩]) unmarked_context_12_26913_360628 node_context_12_26913_360628
  intro a
  fin_cases a
  · exact context_13_107652_360580
  · exact context_13_107653_360602
  · exact context_13_107654_360621
  · exact context_13_107655_360627

theorem selected_cut_13783 : selected 8 ⟨360646, by decide⟩
    (prefixPartial 13 107656) = some ⟨13, 2, 0, 360646, 107656, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_107656_360646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107656 ⟨360646, by decide⟩ :=
  accepted_of_selected 13 107656 ⟨360646, by decide⟩ ⟨13, 2, 0, 360646, 107656, 1277, 16384⟩
    (by decide) selected_cut_13783

theorem selected_cut_13784 : selected 8 ⟨360669, by decide⟩
    (prefixPartial 13 107657) = some ⟨13, 2, 0, 360669, 107657, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_107657_360669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107657 ⟨360669, by decide⟩ :=
  accepted_of_selected 13 107657 ⟨360669, by decide⟩ ⟨13, 2, 0, 360669, 107657, 2137, 16384⟩
    (by decide) selected_cut_13784

theorem selected_cut_13785 : selected 8 ⟨360687, by decide⟩
    (prefixPartial 13 107658) = some ⟨13, 2, 0, 360687, 107658, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_107658_360687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107658 ⟨360687, by decide⟩ :=
  accepted_of_selected 13 107658 ⟨360687, by decide⟩ ⟨13, 2, 0, 360687, 107658, 1341, 16384⟩
    (by decide) selected_cut_13785

theorem selected_cut_13786 : selected 8 ⟨360693, by decide⟩
    (prefixPartial 13 107659) = some ⟨13, 2, 0, 360693, 107659, 957, 16384⟩ := by
  decide +kernel

theorem context_13_107659_360693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107659 ⟨360693, by decide⟩ :=
  accepted_of_selected 13 107659 ⟨360693, by decide⟩ ⟨13, 2, 0, 360693, 107659, 957, 16384⟩
    (by decide) selected_cut_13786

theorem unmarked_context_12_26914_360694 : frontier 9 ⟨360694, by decide⟩
    (prefixCache 12 26914) (prefixPartial 12 26914) = false := by
  decide +kernel

theorem node_context_12_26914_360694 : EJMOriginalGlobalDAGData.nodes 9 ⟨360694, by decide⟩ =
    .split (coordinate 12) (![⟨360646, by decide⟩,⟨360669, by decide⟩,⟨360687, by decide⟩,⟨360693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26914_360694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26914 ⟨360694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26914
    ⟨360694, by decide⟩ (by decide) (![⟨360646, by decide⟩,⟨360669, by decide⟩,⟨360687, by decide⟩,⟨360693, by decide⟩]) unmarked_context_12_26914_360694 node_context_12_26914_360694
  intro a
  fin_cases a
  · exact context_13_107656_360646
  · exact context_13_107657_360669
  · exact context_13_107658_360687
  · exact context_13_107659_360693

theorem selected_cut_13787 : selected 8 ⟨360709, by decide⟩
    (prefixPartial 13 107660) = some ⟨13, 2, 0, 360709, 107660, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_107660_360709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107660 ⟨360709, by decide⟩ :=
  accepted_of_selected 13 107660 ⟨360709, by decide⟩ ⟨13, 2, 0, 360709, 107660, 1417, 16384⟩
    (by decide) selected_cut_13787

theorem selected_cut_13788 : selected 8 ⟨360749, by decide⟩
    (prefixPartial 13 107661) = some ⟨13, 2, 0, 360749, 107661, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_107661_360749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107661 ⟨360749, by decide⟩ :=
  accepted_of_selected 13 107661 ⟨360749, by decide⟩ ⟨13, 2, 0, 360749, 107661, 2365, 16384⟩
    (by decide) selected_cut_13788

theorem selected_cut_13789 : selected 8 ⟨360771, by decide⟩
    (prefixPartial 13 107662) = some ⟨13, 2, 0, 360771, 107662, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_107662_360771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107662 ⟨360771, by decide⟩ :=
  accepted_of_selected 13 107662 ⟨360771, by decide⟩ ⟨13, 2, 0, 360771, 107662, 1473, 16384⟩
    (by decide) selected_cut_13789

theorem selected_cut_13790 : selected 8 ⟨360780, by decide⟩
    (prefixPartial 13 107663) = some ⟨13, 2, 0, 360780, 107663, 989, 16384⟩ := by
  decide +kernel

theorem context_13_107663_360780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107663 ⟨360780, by decide⟩ :=
  accepted_of_selected 13 107663 ⟨360780, by decide⟩ ⟨13, 2, 0, 360780, 107663, 989, 16384⟩
    (by decide) selected_cut_13790

theorem unmarked_context_12_26915_360781 : frontier 9 ⟨360781, by decide⟩
    (prefixCache 12 26915) (prefixPartial 12 26915) = false := by
  decide +kernel

theorem node_context_12_26915_360781 : EJMOriginalGlobalDAGData.nodes 9 ⟨360781, by decide⟩ =
    .split (coordinate 12) (![⟨360709, by decide⟩,⟨360749, by decide⟩,⟨360771, by decide⟩,⟨360780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26915_360781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26915 ⟨360781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26915
    ⟨360781, by decide⟩ (by decide) (![⟨360709, by decide⟩,⟨360749, by decide⟩,⟨360771, by decide⟩,⟨360780, by decide⟩]) unmarked_context_12_26915_360781 node_context_12_26915_360781
  intro a
  fin_cases a
  · exact context_13_107660_360709
  · exact context_13_107661_360749
  · exact context_13_107662_360771
  · exact context_13_107663_360780

theorem unmarked_context_11_6728_360782 : frontier 10 ⟨360782, by decide⟩
    (prefixCache 11 6728) (prefixPartial 11 6728) = false := by
  decide +kernel

theorem node_context_11_6728_360782 : EJMOriginalGlobalDAGData.nodes 10 ⟨360782, by decide⟩ =
    .split (coordinate 11) (![⟨360568, by decide⟩,⟨360628, by decide⟩,⟨360694, by decide⟩,⟨360781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6728_360782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6728 ⟨360782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6728
    ⟨360782, by decide⟩ (by decide) (![⟨360568, by decide⟩,⟨360628, by decide⟩,⟨360694, by decide⟩,⟨360781, by decide⟩]) unmarked_context_11_6728_360782 node_context_11_6728_360782
  intro a
  fin_cases a
  · exact context_12_26912_360568
  · exact context_12_26913_360628
  · exact context_12_26914_360694
  · exact context_12_26915_360781

theorem selected_cut_13791 : selected 8 ⟨360791, by decide⟩
    (prefixPartial 13 107664) = some ⟨13, 2, 0, 360791, 107664, 805, 16384⟩ := by
  decide +kernel

theorem context_13_107664_360791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107664 ⟨360791, by decide⟩ :=
  accepted_of_selected 13 107664 ⟨360791, by decide⟩ ⟨13, 2, 0, 360791, 107664, 805, 16384⟩
    (by decide) selected_cut_13791

theorem selected_cut_13792 : selected 8 ⟨360813, by decide⟩
    (prefixPartial 13 107665) = some ⟨13, 2, 0, 360813, 107665, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_107665_360813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107665 ⟨360813, by decide⟩ :=
  accepted_of_selected 13 107665 ⟨360813, by decide⟩ ⟨13, 2, 0, 360813, 107665, 1893, 16384⟩
    (by decide) selected_cut_13792

theorem selected_cut_13793 : selected 8 ⟨360831, by decide⟩
    (prefixPartial 13 107666) = some ⟨13, 2, 0, 360831, 107666, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_107666_360831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107666 ⟨360831, by decide⟩ :=
  accepted_of_selected 13 107666 ⟨360831, by decide⟩ ⟨13, 2, 0, 360831, 107666, 1269, 16384⟩
    (by decide) selected_cut_13793

theorem selected_cut_13794 : selected 8 ⟨360837, by decide⟩
    (prefixPartial 13 107667) = some ⟨13, 2, 0, 360837, 107667, 865, 16384⟩ := by
  decide +kernel

theorem context_13_107667_360837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107667 ⟨360837, by decide⟩ :=
  accepted_of_selected 13 107667 ⟨360837, by decide⟩ ⟨13, 2, 0, 360837, 107667, 865, 16384⟩
    (by decide) selected_cut_13794

theorem unmarked_context_12_26916_360838 : frontier 9 ⟨360838, by decide⟩
    (prefixCache 12 26916) (prefixPartial 12 26916) = false := by
  decide +kernel

theorem node_context_12_26916_360838 : EJMOriginalGlobalDAGData.nodes 9 ⟨360838, by decide⟩ =
    .split (coordinate 12) (![⟨360791, by decide⟩,⟨360813, by decide⟩,⟨360831, by decide⟩,⟨360837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26916_360838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26916 ⟨360838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26916
    ⟨360838, by decide⟩ (by decide) (![⟨360791, by decide⟩,⟨360813, by decide⟩,⟨360831, by decide⟩,⟨360837, by decide⟩]) unmarked_context_12_26916_360838 node_context_12_26916_360838
  intro a
  fin_cases a
  · exact context_13_107664_360791
  · exact context_13_107665_360813
  · exact context_13_107666_360831
  · exact context_13_107667_360837

theorem selected_cut_13795 : selected 8 ⟨360853, by decide⟩
    (prefixPartial 13 107668) = some ⟨13, 2, 0, 360853, 107668, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_107668_360853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107668 ⟨360853, by decide⟩ :=
  accepted_of_selected 13 107668 ⟨360853, by decide⟩ ⟨13, 2, 0, 360853, 107668, 1441, 16384⟩
    (by decide) selected_cut_13795

theorem selected_cut_13796 : selected 8 ⟨360879, by decide⟩
    (prefixPartial 13 107669) = some ⟨13, 2, 0, 360879, 107669, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_107669_360879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107669 ⟨360879, by decide⟩ :=
  accepted_of_selected 13 107669 ⟨360879, by decide⟩ ⟨13, 2, 0, 360879, 107669, 2829, 16384⟩
    (by decide) selected_cut_13796

theorem selected_cut_13797 : selected 8 ⟨360897, by decide⟩
    (prefixPartial 13 107670) = some ⟨13, 2, 0, 360897, 107670, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_107670_360897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107670 ⟨360897, by decide⟩ :=
  accepted_of_selected 13 107670 ⟨360897, by decide⟩ ⟨13, 2, 0, 360897, 107670, 2073, 16384⟩
    (by decide) selected_cut_13797

theorem selected_cut_13798 : selected 8 ⟨360904, by decide⟩
    (prefixPartial 13 107671) = some ⟨13, 2, 0, 360904, 107671, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_107671_360904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107671 ⟨360904, by decide⟩ :=
  accepted_of_selected 13 107671 ⟨360904, by decide⟩ ⟨13, 2, 0, 360904, 107671, 1161, 16384⟩
    (by decide) selected_cut_13798

theorem unmarked_context_12_26917_360905 : frontier 9 ⟨360905, by decide⟩
    (prefixCache 12 26917) (prefixPartial 12 26917) = false := by
  decide +kernel

theorem node_context_12_26917_360905 : EJMOriginalGlobalDAGData.nodes 9 ⟨360905, by decide⟩ =
    .split (coordinate 12) (![⟨360853, by decide⟩,⟨360879, by decide⟩,⟨360897, by decide⟩,⟨360904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26917_360905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26917 ⟨360905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26917
    ⟨360905, by decide⟩ (by decide) (![⟨360853, by decide⟩,⟨360879, by decide⟩,⟨360897, by decide⟩,⟨360904, by decide⟩]) unmarked_context_12_26917_360905 node_context_12_26917_360905
  intro a
  fin_cases a
  · exact context_13_107668_360853
  · exact context_13_107669_360879
  · exact context_13_107670_360897
  · exact context_13_107671_360904

theorem selected_cut_13799 : selected 8 ⟨360919, by decide⟩
    (prefixPartial 13 107672) = some ⟨13, 2, 0, 360919, 107672, 961, 16384⟩ := by
  decide +kernel

theorem context_13_107672_360919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107672 ⟨360919, by decide⟩ :=
  accepted_of_selected 13 107672 ⟨360919, by decide⟩ ⟨13, 2, 0, 360919, 107672, 961, 16384⟩
    (by decide) selected_cut_13799

theorem selected_cut_13800 : selected 8 ⟨360940, by decide⟩
    (prefixPartial 13 107673) = some ⟨13, 2, 0, 360940, 107673, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_107673_360940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107673 ⟨360940, by decide⟩ :=
  accepted_of_selected 13 107673 ⟨360940, by decide⟩ ⟨13, 2, 0, 360940, 107673, 1809, 16384⟩
    (by decide) selected_cut_13800

theorem selected_cut_13801 : selected 8 ⟨360958, by decide⟩
    (prefixPartial 13 107674) = some ⟨13, 2, 0, 360958, 107674, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_107674_360958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107674 ⟨360958, by decide⟩ :=
  accepted_of_selected 13 107674 ⟨360958, by decide⟩ ⟨13, 2, 0, 360958, 107674, 1281, 16384⟩
    (by decide) selected_cut_13801

theorem selected_cut_13802 : selected 8 ⟨360964, by decide⟩
    (prefixPartial 13 107675) = some ⟨13, 2, 0, 360964, 107675, 933, 16384⟩ := by
  decide +kernel

theorem context_13_107675_360964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107675 ⟨360964, by decide⟩ :=
  accepted_of_selected 13 107675 ⟨360964, by decide⟩ ⟨13, 2, 0, 360964, 107675, 933, 16384⟩
    (by decide) selected_cut_13802

theorem unmarked_context_12_26918_360965 : frontier 9 ⟨360965, by decide⟩
    (prefixCache 12 26918) (prefixPartial 12 26918) = false := by
  decide +kernel

theorem node_context_12_26918_360965 : EJMOriginalGlobalDAGData.nodes 9 ⟨360965, by decide⟩ =
    .split (coordinate 12) (![⟨360919, by decide⟩,⟨360940, by decide⟩,⟨360958, by decide⟩,⟨360964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26918_360965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26918 ⟨360965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26918
    ⟨360965, by decide⟩ (by decide) (![⟨360919, by decide⟩,⟨360940, by decide⟩,⟨360958, by decide⟩,⟨360964, by decide⟩]) unmarked_context_12_26918_360965 node_context_12_26918_360965
  intro a
  fin_cases a
  · exact context_13_107672_360919
  · exact context_13_107673_360940
  · exact context_13_107674_360958
  · exact context_13_107675_360964

theorem selected_cut_13803 : selected 8 ⟨360979, by decide⟩
    (prefixPartial 13 107676) = some ⟨13, 2, 0, 360979, 107676, 993, 16384⟩ := by
  decide +kernel

theorem context_13_107676_360979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107676 ⟨360979, by decide⟩ :=
  accepted_of_selected 13 107676 ⟨360979, by decide⟩ ⟨13, 2, 0, 360979, 107676, 993, 16384⟩
    (by decide) selected_cut_13803

theorem selected_cut_13804 : selected 8 ⟨361000, by decide⟩
    (prefixPartial 13 107677) = some ⟨13, 2, 0, 361000, 107677, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_107677_361000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107677 ⟨361000, by decide⟩ :=
  accepted_of_selected 13 107677 ⟨361000, by decide⟩ ⟨13, 2, 0, 361000, 107677, 2041, 16384⟩
    (by decide) selected_cut_13804

theorem selected_cut_13805 : selected 8 ⟨361019, by decide⟩
    (prefixPartial 13 107678) = some ⟨13, 2, 0, 361019, 107678, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_107678_361019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107678 ⟨361019, by decide⟩ :=
  accepted_of_selected 13 107678 ⟨361019, by decide⟩ ⟨13, 2, 0, 361019, 107678, 1349, 16384⟩
    (by decide) selected_cut_13805

theorem selected_cut_13806 : selected 8 ⟨361023, by decide⟩
    (prefixPartial 13 107679) = some ⟨13, 2, 0, 361023, 107679, 961, 16384⟩ := by
  decide +kernel

theorem context_13_107679_361023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107679 ⟨361023, by decide⟩ :=
  accepted_of_selected 13 107679 ⟨361023, by decide⟩ ⟨13, 2, 0, 361023, 107679, 961, 16384⟩
    (by decide) selected_cut_13806

theorem unmarked_context_12_26919_361024 : frontier 9 ⟨361024, by decide⟩
    (prefixCache 12 26919) (prefixPartial 12 26919) = false := by
  decide +kernel

theorem node_context_12_26919_361024 : EJMOriginalGlobalDAGData.nodes 9 ⟨361024, by decide⟩ =
    .split (coordinate 12) (![⟨360979, by decide⟩,⟨361000, by decide⟩,⟨361019, by decide⟩,⟨361023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26919_361024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26919 ⟨361024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26919
    ⟨361024, by decide⟩ (by decide) (![⟨360979, by decide⟩,⟨361000, by decide⟩,⟨361019, by decide⟩,⟨361023, by decide⟩]) unmarked_context_12_26919_361024 node_context_12_26919_361024
  intro a
  fin_cases a
  · exact context_13_107676_360979
  · exact context_13_107677_361000
  · exact context_13_107678_361019
  · exact context_13_107679_361023

theorem unmarked_context_11_6729_361025 : frontier 10 ⟨361025, by decide⟩
    (prefixCache 11 6729) (prefixPartial 11 6729) = false := by
  decide +kernel

theorem node_context_11_6729_361025 : EJMOriginalGlobalDAGData.nodes 10 ⟨361025, by decide⟩ =
    .split (coordinate 11) (![⟨360838, by decide⟩,⟨360905, by decide⟩,⟨360965, by decide⟩,⟨361024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6729_361025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6729 ⟨361025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6729
    ⟨361025, by decide⟩ (by decide) (![⟨360838, by decide⟩,⟨360905, by decide⟩,⟨360965, by decide⟩,⟨361024, by decide⟩]) unmarked_context_11_6729_361025 node_context_11_6729_361025
  intro a
  fin_cases a
  · exact context_12_26916_360838
  · exact context_12_26917_360905
  · exact context_12_26918_360965
  · exact context_12_26919_361024

theorem selected_cut_13807 : selected 8 ⟨361042, by decide⟩
    (prefixPartial 13 107680) = some ⟨13, 2, 0, 361042, 107680, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_107680_361042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107680 ⟨361042, by decide⟩ :=
  accepted_of_selected 13 107680 ⟨361042, by decide⟩ ⟨13, 2, 0, 361042, 107680, 1221, 16384⟩
    (by decide) selected_cut_13807

theorem selected_cut_13808 : selected 8 ⟨361092, by decide⟩
    (prefixPartial 13 107681) = some ⟨13, 2, 0, 361092, 107681, 3197, 16384⟩ := by
  decide +kernel

theorem context_13_107681_361092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107681 ⟨361092, by decide⟩ :=
  accepted_of_selected 13 107681 ⟨361092, by decide⟩ ⟨13, 2, 0, 361092, 107681, 3197, 16384⟩
    (by decide) selected_cut_13808

theorem selected_cut_13809 : selected 8 ⟨361112, by decide⟩
    (prefixPartial 13 107682) = some ⟨13, 2, 0, 361112, 107682, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_107682_361112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107682 ⟨361112, by decide⟩ :=
  accepted_of_selected 13 107682 ⟨361112, by decide⟩ ⟨13, 2, 0, 361112, 107682, 1869, 16384⟩
    (by decide) selected_cut_13809

theorem selected_cut_13810 : selected 8 ⟨361120, by decide⟩
    (prefixPartial 13 107683) = some ⟨13, 2, 0, 361120, 107683, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_107683_361120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107683 ⟨361120, by decide⟩ :=
  accepted_of_selected 13 107683 ⟨361120, by decide⟩ ⟨13, 2, 0, 361120, 107683, 1105, 16384⟩
    (by decide) selected_cut_13810

theorem unmarked_context_12_26920_361121 : frontier 9 ⟨361121, by decide⟩
    (prefixCache 12 26920) (prefixPartial 12 26920) = false := by
  decide +kernel

theorem node_context_12_26920_361121 : EJMOriginalGlobalDAGData.nodes 9 ⟨361121, by decide⟩ =
    .split (coordinate 12) (![⟨361042, by decide⟩,⟨361092, by decide⟩,⟨361112, by decide⟩,⟨361120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26920_361121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26920 ⟨361121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26920
    ⟨361121, by decide⟩ (by decide) (![⟨361042, by decide⟩,⟨361092, by decide⟩,⟨361112, by decide⟩,⟨361120, by decide⟩]) unmarked_context_12_26920_361121 node_context_12_26920_361121
  intro a
  fin_cases a
  · exact context_13_107680_361042
  · exact context_13_107681_361092
  · exact context_13_107682_361112
  · exact context_13_107683_361120

theorem selected_cut_13811 : selected 8 ⟨361134, by decide⟩
    (prefixPartial 13 107684) = some ⟨13, 2, 0, 361134, 107684, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_107684_361134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107684 ⟨361134, by decide⟩ :=
  accepted_of_selected 13 107684 ⟨361134, by decide⟩ ⟨13, 2, 0, 361134, 107684, 1213, 16384⟩
    (by decide) selected_cut_13811

theorem selected_cut_13812 : selected 8 ⟨361159, by decide⟩
    (prefixPartial 13 107685) = some ⟨13, 2, 0, 361159, 107685, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_107685_361159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107685 ⟨361159, by decide⟩ :=
  accepted_of_selected 13 107685 ⟨361159, by decide⟩ ⟨13, 2, 0, 361159, 107685, 2637, 16384⟩
    (by decide) selected_cut_13812

theorem selected_cut_13813 : selected 8 ⟨361176, by decide⟩
    (prefixPartial 13 107686) = some ⟨13, 2, 0, 361176, 107686, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_107686_361176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107686 ⟨361176, by decide⟩ :=
  accepted_of_selected 13 107686 ⟨361176, by decide⟩ ⟨13, 2, 0, 361176, 107686, 1905, 16384⟩
    (by decide) selected_cut_13813

theorem selected_cut_13814 : selected 8 ⟨361181, by decide⟩
    (prefixPartial 13 107687) = some ⟨13, 2, 0, 361181, 107687, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_107687_361181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107687 ⟨361181, by decide⟩ :=
  accepted_of_selected 13 107687 ⟨361181, by decide⟩ ⟨13, 2, 0, 361181, 107687, 1141, 16384⟩
    (by decide) selected_cut_13814

theorem unmarked_context_12_26921_361182 : frontier 9 ⟨361182, by decide⟩
    (prefixCache 12 26921) (prefixPartial 12 26921) = false := by
  decide +kernel

theorem node_context_12_26921_361182 : EJMOriginalGlobalDAGData.nodes 9 ⟨361182, by decide⟩ =
    .split (coordinate 12) (![⟨361134, by decide⟩,⟨361159, by decide⟩,⟨361176, by decide⟩,⟨361181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26921_361182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26921 ⟨361182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26921
    ⟨361182, by decide⟩ (by decide) (![⟨361134, by decide⟩,⟨361159, by decide⟩,⟨361176, by decide⟩,⟨361181, by decide⟩]) unmarked_context_12_26921_361182 node_context_12_26921_361182
  intro a
  fin_cases a
  · exact context_13_107684_361134
  · exact context_13_107685_361159
  · exact context_13_107686_361176
  · exact context_13_107687_361181

theorem selected_cut_13815 : selected 8 ⟨361237, by decide⟩
    (prefixPartial 13 107688) = some ⟨13, 2, 0, 361237, 107688, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_107688_361237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107688 ⟨361237, by decide⟩ :=
  accepted_of_selected 13 107688 ⟨361237, by decide⟩ ⟨13, 2, 0, 361237, 107688, 1201, 16384⟩
    (by decide) selected_cut_13815

theorem selected_cut_13816 : selected 8 ⟨361310, by decide⟩
    (prefixPartial 13 107689) = some ⟨13, 2, 0, 361310, 107689, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_107689_361310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107689 ⟨361310, by decide⟩ :=
  accepted_of_selected 13 107689 ⟨361310, by decide⟩ ⟨13, 2, 0, 361310, 107689, 2113, 16384⟩
    (by decide) selected_cut_13816

theorem selected_cut_13817 : selected 8 ⟨361355, by decide⟩
    (prefixPartial 13 107690) = some ⟨13, 2, 0, 361355, 107690, 877, 16384⟩ := by
  decide +kernel

theorem context_13_107690_361355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107690 ⟨361355, by decide⟩ :=
  accepted_of_selected 13 107690 ⟨361355, by decide⟩ ⟨13, 2, 0, 361355, 107690, 877, 16384⟩
    (by decide) selected_cut_13817

theorem selected_cut_13818 : selected 8 ⟨361358, by decide⟩
    (prefixPartial 13 107691) = some ⟨13, 2, 0, 361358, 107691, 213, 16384⟩ := by
  decide +kernel

theorem context_13_107691_361358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107691 ⟨361358, by decide⟩ :=
  accepted_of_selected 13 107691 ⟨361358, by decide⟩ ⟨13, 2, 0, 361358, 107691, 213, 16384⟩
    (by decide) selected_cut_13818

theorem unmarked_context_12_26922_361359 : frontier 9 ⟨361359, by decide⟩
    (prefixCache 12 26922) (prefixPartial 12 26922) = false := by
  decide +kernel

theorem node_context_12_26922_361359 : EJMOriginalGlobalDAGData.nodes 9 ⟨361359, by decide⟩ =
    .split (coordinate 12) (![⟨361237, by decide⟩,⟨361310, by decide⟩,⟨361355, by decide⟩,⟨361358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26922_361359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26922 ⟨361359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26922
    ⟨361359, by decide⟩ (by decide) (![⟨361237, by decide⟩,⟨361310, by decide⟩,⟨361355, by decide⟩,⟨361358, by decide⟩]) unmarked_context_12_26922_361359 node_context_12_26922_361359
  intro a
  fin_cases a
  · exact context_13_107688_361237
  · exact context_13_107689_361310
  · exact context_13_107690_361355
  · exact context_13_107691_361358

theorem selected_cut_13819 : selected 8 ⟨361383, by decide⟩
    (prefixPartial 13 107692) = some ⟨13, 2, 0, 361383, 107692, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_107692_361383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107692 ⟨361383, by decide⟩ :=
  accepted_of_selected 13 107692 ⟨361383, by decide⟩ ⟨13, 2, 0, 361383, 107692, 1537, 16384⟩
    (by decide) selected_cut_13819

theorem selected_cut_13820 : selected 8 ⟨361438, by decide⟩
    (prefixPartial 13 107693) = some ⟨13, 2, 0, 361438, 107693, 3601, 16384⟩ := by
  decide +kernel

theorem context_13_107693_361438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107693 ⟨361438, by decide⟩ :=
  accepted_of_selected 13 107693 ⟨361438, by decide⟩ ⟨13, 2, 0, 361438, 107693, 3601, 16384⟩
    (by decide) selected_cut_13820

theorem selected_cut_13821 : selected 8 ⟨361461, by decide⟩
    (prefixPartial 13 107694) = some ⟨13, 2, 0, 361461, 107694, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_107694_361461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107694 ⟨361461, by decide⟩ :=
  accepted_of_selected 13 107694 ⟨361461, by decide⟩ ⟨13, 2, 0, 361461, 107694, 1973, 16384⟩
    (by decide) selected_cut_13821

theorem selected_cut_13822 : selected 8 ⟨361473, by decide⟩
    (prefixPartial 13 107695) = some ⟨13, 2, 0, 361473, 107695, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_107695_361473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107695 ⟨361473, by decide⟩ :=
  accepted_of_selected 13 107695 ⟨361473, by decide⟩ ⟨13, 2, 0, 361473, 107695, 1173, 16384⟩
    (by decide) selected_cut_13822

theorem unmarked_context_12_26923_361474 : frontier 9 ⟨361474, by decide⟩
    (prefixCache 12 26923) (prefixPartial 12 26923) = false := by
  decide +kernel

theorem node_context_12_26923_361474 : EJMOriginalGlobalDAGData.nodes 9 ⟨361474, by decide⟩ =
    .split (coordinate 12) (![⟨361383, by decide⟩,⟨361438, by decide⟩,⟨361461, by decide⟩,⟨361473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26923_361474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26923 ⟨361474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26923
    ⟨361474, by decide⟩ (by decide) (![⟨361383, by decide⟩,⟨361438, by decide⟩,⟨361461, by decide⟩,⟨361473, by decide⟩]) unmarked_context_12_26923_361474 node_context_12_26923_361474
  intro a
  fin_cases a
  · exact context_13_107692_361383
  · exact context_13_107693_361438
  · exact context_13_107694_361461
  · exact context_13_107695_361473

theorem unmarked_context_11_6730_361475 : frontier 10 ⟨361475, by decide⟩
    (prefixCache 11 6730) (prefixPartial 11 6730) = false := by
  decide +kernel

theorem node_context_11_6730_361475 : EJMOriginalGlobalDAGData.nodes 10 ⟨361475, by decide⟩ =
    .split (coordinate 11) (![⟨361121, by decide⟩,⟨361182, by decide⟩,⟨361359, by decide⟩,⟨361474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6730_361475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6730 ⟨361475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6730
    ⟨361475, by decide⟩ (by decide) (![⟨361121, by decide⟩,⟨361182, by decide⟩,⟨361359, by decide⟩,⟨361474, by decide⟩]) unmarked_context_11_6730_361475 node_context_11_6730_361475
  intro a
  fin_cases a
  · exact context_12_26920_361121
  · exact context_12_26921_361182
  · exact context_12_26922_361359
  · exact context_12_26923_361474

theorem selected_cut_13823 : selected 8 ⟨361484, by decide⟩
    (prefixPartial 13 107696) = some ⟨13, 2, 0, 361484, 107696, 661, 16384⟩ := by
  decide +kernel

theorem context_13_107696_361484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107696 ⟨361484, by decide⟩ :=
  accepted_of_selected 13 107696 ⟨361484, by decide⟩ ⟨13, 2, 0, 361484, 107696, 661, 16384⟩
    (by decide) selected_cut_13823

theorem selected_cut_13824 : selected 8 ⟨361516, by decide⟩
    (prefixPartial 13 107697) = some ⟨13, 2, 0, 361516, 107697, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_107697_361516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107697 ⟨361516, by decide⟩ :=
  accepted_of_selected 13 107697 ⟨361516, by decide⟩ ⟨13, 2, 0, 361516, 107697, 2473, 16384⟩
    (by decide) selected_cut_13824

theorem selected_cut_13825 : selected 8 ⟨361533, by decide⟩
    (prefixPartial 13 107698) = some ⟨13, 2, 0, 361533, 107698, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_107698_361533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107698 ⟨361533, by decide⟩ :=
  accepted_of_selected 13 107698 ⟨361533, by decide⟩ ⟨13, 2, 0, 361533, 107698, 1413, 16384⟩
    (by decide) selected_cut_13825

theorem selected_cut_13826 : selected 8 ⟨361539, by decide⟩
    (prefixPartial 13 107699) = some ⟨13, 2, 0, 361539, 107699, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_107699_361539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107699 ⟨361539, by decide⟩ :=
  accepted_of_selected 13 107699 ⟨361539, by decide⟩ ⟨13, 2, 0, 361539, 107699, 1009, 16384⟩
    (by decide) selected_cut_13826

theorem unmarked_context_12_26924_361540 : frontier 9 ⟨361540, by decide⟩
    (prefixCache 12 26924) (prefixPartial 12 26924) = false := by
  decide +kernel

theorem node_context_12_26924_361540 : EJMOriginalGlobalDAGData.nodes 9 ⟨361540, by decide⟩ =
    .split (coordinate 12) (![⟨361484, by decide⟩,⟨361516, by decide⟩,⟨361533, by decide⟩,⟨361539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26924_361540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26924 ⟨361540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26924
    ⟨361540, by decide⟩ (by decide) (![⟨361484, by decide⟩,⟨361516, by decide⟩,⟨361533, by decide⟩,⟨361539, by decide⟩]) unmarked_context_12_26924_361540 node_context_12_26924_361540
  intro a
  fin_cases a
  · exact context_13_107696_361484
  · exact context_13_107697_361516
  · exact context_13_107698_361533
  · exact context_13_107699_361539

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
