/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover195
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18819 : selected 7 ⟨481501, by decide⟩
    (prefixPartial 14 1151091) = some ⟨14, 2, 0, 481501, 1151091, 1601, 4096⟩ := by
  decide +kernel

theorem context_14_1151091_481501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151091 ⟨481501, by decide⟩ :=
  accepted_of_selected 14 1151091 ⟨481501, by decide⟩ ⟨14, 2, 0, 481501, 1151091, 1601, 4096⟩
    (by decide) selected_cut_18819

theorem unmarked_context_13_287772_481502 : frontier 8 ⟨481502, by decide⟩
    (prefixCache 13 287772) (prefixPartial 13 287772) = false := by
  decide +kernel

theorem node_context_13_287772_481502 : EJMOriginalGlobalDAGData.nodes 8 ⟨481502, by decide⟩ =
    .split (coordinate 13) (![⟨481407, by decide⟩,⟨481437, by decide⟩,⟨481469, by decide⟩,⟨481501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287772_481502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287772 ⟨481502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287772
    ⟨481502, by decide⟩ (by decide) (![⟨481407, by decide⟩,⟨481437, by decide⟩,⟨481469, by decide⟩,⟨481501, by decide⟩]) unmarked_context_13_287772_481502 node_context_13_287772_481502
  intro a
  fin_cases a
  · exact context_14_1151088_481407
  · exact context_14_1151089_481437
  · exact context_14_1151090_481469
  · exact context_14_1151091_481501

theorem selected_cut_18820 : selected 7 ⟨481515, by decide⟩
    (prefixPartial 14 1151092) = some ⟨14, 2, 0, 481515, 1151092, 941, 4096⟩ := by
  decide +kernel

theorem context_14_1151092_481515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151092 ⟨481515, by decide⟩ :=
  accepted_of_selected 14 1151092 ⟨481515, by decide⟩ ⟨14, 2, 0, 481515, 1151092, 941, 4096⟩
    (by decide) selected_cut_18820

theorem selected_cut_18821 : selected 7 ⟨481537, by decide⟩
    (prefixPartial 14 1151093) = some ⟨14, 2, 0, 481537, 1151093, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_1151093_481537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151093 ⟨481537, by decide⟩ :=
  accepted_of_selected 14 1151093 ⟨481537, by decide⟩ ⟨14, 2, 0, 481537, 1151093, 1101, 4096⟩
    (by decide) selected_cut_18821

theorem selected_cut_18822 : selected 7 ⟨481569, by decide⟩
    (prefixPartial 14 1151094) = some ⟨14, 2, 0, 481569, 1151094, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_1151094_481569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151094 ⟨481569, by decide⟩ :=
  accepted_of_selected 14 1151094 ⟨481569, by decide⟩ ⟨14, 2, 0, 481569, 1151094, 1229, 4096⟩
    (by decide) selected_cut_18822

theorem selected_cut_18823 : selected 7 ⟨481601, by decide⟩
    (prefixPartial 14 1151095) = some ⟨14, 2, 0, 481601, 1151095, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_1151095_481601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151095 ⟨481601, by decide⟩ :=
  accepted_of_selected 14 1151095 ⟨481601, by decide⟩ ⟨14, 2, 0, 481601, 1151095, 1245, 4096⟩
    (by decide) selected_cut_18823

theorem unmarked_context_13_287773_481602 : frontier 8 ⟨481602, by decide⟩
    (prefixCache 13 287773) (prefixPartial 13 287773) = false := by
  decide +kernel

theorem node_context_13_287773_481602 : EJMOriginalGlobalDAGData.nodes 8 ⟨481602, by decide⟩ =
    .split (coordinate 13) (![⟨481515, by decide⟩,⟨481537, by decide⟩,⟨481569, by decide⟩,⟨481601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287773_481602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287773 ⟨481602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287773
    ⟨481602, by decide⟩ (by decide) (![⟨481515, by decide⟩,⟨481537, by decide⟩,⟨481569, by decide⟩,⟨481601, by decide⟩]) unmarked_context_13_287773_481602 node_context_13_287773_481602
  intro a
  fin_cases a
  · exact context_14_1151092_481515
  · exact context_14_1151093_481537
  · exact context_14_1151094_481569
  · exact context_14_1151095_481601

theorem selected_cut_18824 : selected 8 ⟨481690, by decide⟩
    (prefixPartial 13 287774) = some ⟨13, 2, 0, 481690, 287774, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_287774_481690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287774 ⟨481690, by decide⟩ :=
  accepted_of_selected 13 287774 ⟨481690, by decide⟩ ⟨13, 2, 0, 481690, 287774, 3221, 16384⟩
    (by decide) selected_cut_18824

theorem selected_cut_18825 : selected 8 ⟨481708, by decide⟩
    (prefixPartial 13 287775) = some ⟨13, 2, 0, 481708, 287775, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_287775_481708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287775 ⟨481708, by decide⟩ :=
  accepted_of_selected 13 287775 ⟨481708, by decide⟩ ⟨13, 2, 0, 481708, 287775, 1337, 16384⟩
    (by decide) selected_cut_18825

theorem unmarked_context_12_71943_481709 : frontier 9 ⟨481709, by decide⟩
    (prefixCache 12 71943) (prefixPartial 12 71943) = false := by
  decide +kernel

theorem node_context_12_71943_481709 : EJMOriginalGlobalDAGData.nodes 9 ⟨481709, by decide⟩ =
    .split (coordinate 12) (![⟨481502, by decide⟩,⟨481602, by decide⟩,⟨481690, by decide⟩,⟨481708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71943_481709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71943 ⟨481709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71943
    ⟨481709, by decide⟩ (by decide) (![⟨481502, by decide⟩,⟨481602, by decide⟩,⟨481690, by decide⟩,⟨481708, by decide⟩]) unmarked_context_12_71943_481709 node_context_12_71943_481709
  intro a
  fin_cases a
  · exact context_13_287772_481502
  · exact context_13_287773_481602
  · exact context_13_287774_481690
  · exact context_13_287775_481708

theorem unmarked_context_11_17985_481710 : frontier 10 ⟨481710, by decide⟩
    (prefixCache 11 17985) (prefixPartial 11 17985) = false := by
  decide +kernel

theorem node_context_11_17985_481710 : EJMOriginalGlobalDAGData.nodes 10 ⟨481710, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨481022, by decide⟩,⟨481386, by decide⟩,⟨481709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17985_481710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17985 ⟨481710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17985
    ⟨481710, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨481022, by decide⟩,⟨481386, by decide⟩,⟨481709, by decide⟩]) unmarked_context_11_17985_481710 node_context_11_17985_481710
  intro a
  fin_cases a
  · exact context_12_71940_448748
  · exact context_12_71941_481022
  · exact context_12_71942_481386
  · exact context_12_71943_481709

theorem selected_cut_18826 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71944) = some ⟨12, 1, 0, 448748, 71944, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71944_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71944 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71944 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71944, 1, 65536⟩
    (by decide) selected_cut_18826

theorem selected_cut_18827 : selected 7 ⟨481725, by decide⟩
    (prefixPartial 14 1151120) = some ⟨14, 2, 0, 481725, 1151120, 585, 4096⟩ := by
  decide +kernel

theorem context_14_1151120_481725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151120 ⟨481725, by decide⟩ :=
  accepted_of_selected 14 1151120 ⟨481725, by decide⟩ ⟨14, 2, 0, 481725, 1151120, 585, 4096⟩
    (by decide) selected_cut_18827

theorem selected_cut_18828 : selected 7 ⟨481746, by decide⟩
    (prefixPartial 14 1151121) = some ⟨14, 2, 0, 481746, 1151121, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_1151121_481746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151121 ⟨481746, by decide⟩ :=
  accepted_of_selected 14 1151121 ⟨481746, by decide⟩ ⟨14, 2, 0, 481746, 1151121, 1173, 4096⟩
    (by decide) selected_cut_18828

theorem selected_cut_18829 : selected 7 ⟨481772, by decide⟩
    (prefixPartial 14 1151122) = some ⟨14, 2, 0, 481772, 1151122, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_1151122_481772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151122 ⟨481772, by decide⟩ :=
  accepted_of_selected 14 1151122 ⟨481772, by decide⟩ ⟨14, 2, 0, 481772, 1151122, 1265, 4096⟩
    (by decide) selected_cut_18829

theorem selected_cut_18830 : selected 7 ⟨481803, by decide⟩
    (prefixPartial 14 1151123) = some ⟨14, 2, 0, 481803, 1151123, 1517, 4096⟩ := by
  decide +kernel

theorem context_14_1151123_481803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151123 ⟨481803, by decide⟩ :=
  accepted_of_selected 14 1151123 ⟨481803, by decide⟩ ⟨14, 2, 0, 481803, 1151123, 1517, 4096⟩
    (by decide) selected_cut_18830

theorem unmarked_context_13_287780_481804 : frontier 8 ⟨481804, by decide⟩
    (prefixCache 13 287780) (prefixPartial 13 287780) = false := by
  decide +kernel

theorem node_context_13_287780_481804 : EJMOriginalGlobalDAGData.nodes 8 ⟨481804, by decide⟩ =
    .split (coordinate 13) (![⟨481725, by decide⟩,⟨481746, by decide⟩,⟨481772, by decide⟩,⟨481803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287780_481804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287780 ⟨481804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287780
    ⟨481804, by decide⟩ (by decide) (![⟨481725, by decide⟩,⟨481746, by decide⟩,⟨481772, by decide⟩,⟨481803, by decide⟩]) unmarked_context_13_287780_481804 node_context_13_287780_481804
  intro a
  fin_cases a
  · exact context_14_1151120_481725
  · exact context_14_1151121_481746
  · exact context_14_1151122_481772
  · exact context_14_1151123_481803

theorem selected_cut_18831 : selected 8 ⟨481854, by decide⟩
    (prefixPartial 13 287781) = some ⟨13, 2, 0, 481854, 287781, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_287781_481854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287781 ⟨481854, by decide⟩ :=
  accepted_of_selected 13 287781 ⟨481854, by decide⟩ ⟨13, 2, 0, 481854, 287781, 3317, 16384⟩
    (by decide) selected_cut_18831

theorem selected_cut_18832 : selected 8 ⟨481893, by decide⟩
    (prefixPartial 13 287782) = some ⟨13, 2, 0, 481893, 287782, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_287782_481893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287782 ⟨481893, by decide⟩ :=
  accepted_of_selected 13 287782 ⟨481893, by decide⟩ ⟨13, 2, 0, 481893, 287782, 2437, 16384⟩
    (by decide) selected_cut_18832

theorem selected_cut_18833 : selected 8 ⟨481913, by decide⟩
    (prefixPartial 13 287783) = some ⟨13, 2, 0, 481913, 287783, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_287783_481913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287783 ⟨481913, by decide⟩ :=
  accepted_of_selected 13 287783 ⟨481913, by decide⟩ ⟨13, 2, 0, 481913, 287783, 1369, 16384⟩
    (by decide) selected_cut_18833

theorem unmarked_context_12_71945_481914 : frontier 9 ⟨481914, by decide⟩
    (prefixCache 12 71945) (prefixPartial 12 71945) = false := by
  decide +kernel

theorem node_context_12_71945_481914 : EJMOriginalGlobalDAGData.nodes 9 ⟨481914, by decide⟩ =
    .split (coordinate 12) (![⟨481804, by decide⟩,⟨481854, by decide⟩,⟨481893, by decide⟩,⟨481913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71945_481914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71945 ⟨481914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71945
    ⟨481914, by decide⟩ (by decide) (![⟨481804, by decide⟩,⟨481854, by decide⟩,⟨481893, by decide⟩,⟨481913, by decide⟩]) unmarked_context_12_71945_481914 node_context_12_71945_481914
  intro a
  fin_cases a
  · exact context_13_287780_481804
  · exact context_13_287781_481854
  · exact context_13_287782_481893
  · exact context_13_287783_481913

theorem selected_cut_18834 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 71946) = some ⟨12, 1, 0, 88909, 71946, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71946_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71946 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 71946 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 71946, 1, 65536⟩
    (by decide) selected_cut_18834

theorem selected_cut_18835 : selected 7 ⟨481931, by decide⟩
    (prefixPartial 14 1151152) = some ⟨14, 2, 0, 481931, 1151152, 597, 4096⟩ := by
  decide +kernel

theorem context_14_1151152_481931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151152 ⟨481931, by decide⟩ :=
  accepted_of_selected 14 1151152 ⟨481931, by decide⟩ ⟨14, 2, 0, 481931, 1151152, 597, 4096⟩
    (by decide) selected_cut_18835

theorem selected_cut_18836 : selected 7 ⟨481959, by decide⟩
    (prefixPartial 14 1151153) = some ⟨14, 2, 0, 481959, 1151153, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_1151153_481959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151153 ⟨481959, by decide⟩ :=
  accepted_of_selected 14 1151153 ⟨481959, by decide⟩ ⟨14, 2, 0, 481959, 1151153, 1361, 4096⟩
    (by decide) selected_cut_18836

theorem selected_cut_18837 : selected 7 ⟨481986, by decide⟩
    (prefixPartial 14 1151154) = some ⟨14, 2, 0, 481986, 1151154, 1477, 4096⟩ := by
  decide +kernel

theorem context_14_1151154_481986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151154 ⟨481986, by decide⟩ :=
  accepted_of_selected 14 1151154 ⟨481986, by decide⟩ ⟨14, 2, 0, 481986, 1151154, 1477, 4096⟩
    (by decide) selected_cut_18837

theorem selected_cut_18838 : selected 7 ⟨482018, by decide⟩
    (prefixPartial 14 1151155) = some ⟨14, 2, 0, 482018, 1151155, 1637, 4096⟩ := by
  decide +kernel

theorem context_14_1151155_482018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151155 ⟨482018, by decide⟩ :=
  accepted_of_selected 14 1151155 ⟨482018, by decide⟩ ⟨14, 2, 0, 482018, 1151155, 1637, 4096⟩
    (by decide) selected_cut_18838

theorem unmarked_context_13_287788_482019 : frontier 8 ⟨482019, by decide⟩
    (prefixCache 13 287788) (prefixPartial 13 287788) = false := by
  decide +kernel

theorem node_context_13_287788_482019 : EJMOriginalGlobalDAGData.nodes 8 ⟨482019, by decide⟩ =
    .split (coordinate 13) (![⟨481931, by decide⟩,⟨481959, by decide⟩,⟨481986, by decide⟩,⟨482018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287788_482019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287788 ⟨482019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287788
    ⟨482019, by decide⟩ (by decide) (![⟨481931, by decide⟩,⟨481959, by decide⟩,⟨481986, by decide⟩,⟨482018, by decide⟩]) unmarked_context_13_287788_482019 node_context_13_287788_482019
  intro a
  fin_cases a
  · exact context_14_1151152_481931
  · exact context_14_1151153_481959
  · exact context_14_1151154_481986
  · exact context_14_1151155_482018

theorem selected_cut_18839 : selected 8 ⟨482082, by decide⟩
    (prefixPartial 13 287789) = some ⟨13, 2, 0, 482082, 287789, 4025, 16384⟩ := by
  decide +kernel

theorem context_13_287789_482082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287789 ⟨482082, by decide⟩ :=
  accepted_of_selected 13 287789 ⟨482082, by decide⟩ ⟨13, 2, 0, 482082, 287789, 4025, 16384⟩
    (by decide) selected_cut_18839

theorem selected_cut_18840 : selected 8 ⟨482143, by decide⟩
    (prefixPartial 13 287790) = some ⟨13, 2, 0, 482143, 287790, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_287790_482143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287790 ⟨482143, by decide⟩ :=
  accepted_of_selected 13 287790 ⟨482143, by decide⟩ ⟨13, 2, 0, 482143, 287790, 2917, 16384⟩
    (by decide) selected_cut_18840

theorem selected_cut_18841 : selected 8 ⟨482162, by decide⟩
    (prefixPartial 13 287791) = some ⟨13, 2, 0, 482162, 287791, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_287791_482162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287791 ⟨482162, by decide⟩ :=
  accepted_of_selected 13 287791 ⟨482162, by decide⟩ ⟨13, 2, 0, 482162, 287791, 1401, 16384⟩
    (by decide) selected_cut_18841

theorem unmarked_context_12_71947_482163 : frontier 9 ⟨482163, by decide⟩
    (prefixCache 12 71947) (prefixPartial 12 71947) = false := by
  decide +kernel

theorem node_context_12_71947_482163 : EJMOriginalGlobalDAGData.nodes 9 ⟨482163, by decide⟩ =
    .split (coordinate 12) (![⟨482019, by decide⟩,⟨482082, by decide⟩,⟨482143, by decide⟩,⟨482162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71947_482163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71947 ⟨482163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71947
    ⟨482163, by decide⟩ (by decide) (![⟨482019, by decide⟩,⟨482082, by decide⟩,⟨482143, by decide⟩,⟨482162, by decide⟩]) unmarked_context_12_71947_482163 node_context_12_71947_482163
  intro a
  fin_cases a
  · exact context_13_287788_482019
  · exact context_13_287789_482082
  · exact context_13_287790_482143
  · exact context_13_287791_482162

theorem unmarked_context_11_17986_482164 : frontier 10 ⟨482164, by decide⟩
    (prefixCache 11 17986) (prefixPartial 11 17986) = false := by
  decide +kernel

theorem node_context_11_17986_482164 : EJMOriginalGlobalDAGData.nodes 10 ⟨482164, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨481914, by decide⟩,⟨88909, by decide⟩,⟨482163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17986_482164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17986 ⟨482164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17986
    ⟨482164, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨481914, by decide⟩,⟨88909, by decide⟩,⟨482163, by decide⟩]) unmarked_context_11_17986_482164 node_context_11_17986_482164
  intro a
  fin_cases a
  · exact context_12_71944_448748
  · exact context_12_71945_481914
  · exact context_12_71946_88909
  · exact context_12_71947_482163

theorem selected_cut_18842 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71948) = some ⟨12, 1, 0, 448748, 71948, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71948_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71948 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71948 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71948, 1, 65536⟩
    (by decide) selected_cut_18842

theorem selected_cut_18843 : selected 7 ⟨482174, by decide⟩
    (prefixPartial 14 1151184) = some ⟨14, 2, 0, 482174, 1151184, 421, 4096⟩ := by
  decide +kernel

theorem context_14_1151184_482174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151184 ⟨482174, by decide⟩ :=
  accepted_of_selected 14 1151184 ⟨482174, by decide⟩ ⟨14, 2, 0, 482174, 1151184, 421, 4096⟩
    (by decide) selected_cut_18843

theorem selected_cut_18844 : selected 7 ⟨482197, by decide⟩
    (prefixPartial 14 1151185) = some ⟨14, 2, 0, 482197, 1151185, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_1151185_482197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151185 ⟨482197, by decide⟩ :=
  accepted_of_selected 14 1151185 ⟨482197, by decide⟩ ⟨14, 2, 0, 482197, 1151185, 1181, 4096⟩
    (by decide) selected_cut_18844

theorem selected_cut_18845 : selected 7 ⟨482235, by decide⟩
    (prefixPartial 14 1151186) = some ⟨14, 2, 0, 482235, 1151186, 1697, 4096⟩ := by
  decide +kernel

theorem context_14_1151186_482235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151186 ⟨482235, by decide⟩ :=
  accepted_of_selected 14 1151186 ⟨482235, by decide⟩ ⟨14, 2, 0, 482235, 1151186, 1697, 4096⟩
    (by decide) selected_cut_18845

theorem selected_cut_18846 : selected 7 ⟨482259, by decide⟩
    (prefixPartial 14 1151187) = some ⟨14, 2, 0, 482259, 1151187, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_1151187_482259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151187 ⟨482259, by decide⟩ :=
  accepted_of_selected 14 1151187 ⟨482259, by decide⟩ ⟨14, 2, 0, 482259, 1151187, 1129, 4096⟩
    (by decide) selected_cut_18846

theorem unmarked_context_13_287796_482260 : frontier 8 ⟨482260, by decide⟩
    (prefixCache 13 287796) (prefixPartial 13 287796) = false := by
  decide +kernel

theorem node_context_13_287796_482260 : EJMOriginalGlobalDAGData.nodes 8 ⟨482260, by decide⟩ =
    .split (coordinate 13) (![⟨482174, by decide⟩,⟨482197, by decide⟩,⟨482235, by decide⟩,⟨482259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287796_482260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287796 ⟨482260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287796
    ⟨482260, by decide⟩ (by decide) (![⟨482174, by decide⟩,⟨482197, by decide⟩,⟨482235, by decide⟩,⟨482259, by decide⟩]) unmarked_context_13_287796_482260 node_context_13_287796_482260
  intro a
  fin_cases a
  · exact context_14_1151184_482174
  · exact context_14_1151185_482197
  · exact context_14_1151186_482235
  · exact context_14_1151187_482259

theorem selected_cut_18847 : selected 8 ⟨482314, by decide⟩
    (prefixPartial 13 287797) = some ⟨13, 2, 0, 482314, 287797, 3485, 16384⟩ := by
  decide +kernel

theorem context_13_287797_482314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287797 ⟨482314, by decide⟩ :=
  accepted_of_selected 13 287797 ⟨482314, by decide⟩ ⟨13, 2, 0, 482314, 287797, 3485, 16384⟩
    (by decide) selected_cut_18847

theorem selected_cut_18848 : selected 8 ⟨482362, by decide⟩
    (prefixPartial 13 287798) = some ⟨13, 2, 0, 482362, 287798, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_287798_482362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287798 ⟨482362, by decide⟩ :=
  accepted_of_selected 13 287798 ⟨482362, by decide⟩ ⟨13, 2, 0, 482362, 287798, 2625, 16384⟩
    (by decide) selected_cut_18848

theorem selected_cut_18849 : selected 8 ⟨482403, by decide⟩
    (prefixPartial 13 287799) = some ⟨13, 2, 0, 482403, 287799, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_287799_482403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287799 ⟨482403, by decide⟩ :=
  accepted_of_selected 13 287799 ⟨482403, by decide⟩ ⟨13, 2, 0, 482403, 287799, 1481, 16384⟩
    (by decide) selected_cut_18849

theorem unmarked_context_12_71949_482404 : frontier 9 ⟨482404, by decide⟩
    (prefixCache 12 71949) (prefixPartial 12 71949) = false := by
  decide +kernel

theorem node_context_12_71949_482404 : EJMOriginalGlobalDAGData.nodes 9 ⟨482404, by decide⟩ =
    .split (coordinate 12) (![⟨482260, by decide⟩,⟨482314, by decide⟩,⟨482362, by decide⟩,⟨482403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71949_482404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71949 ⟨482404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71949
    ⟨482404, by decide⟩ (by decide) (![⟨482260, by decide⟩,⟨482314, by decide⟩,⟨482362, by decide⟩,⟨482403, by decide⟩]) unmarked_context_12_71949_482404 node_context_12_71949_482404
  intro a
  fin_cases a
  · exact context_13_287796_482260
  · exact context_13_287797_482314
  · exact context_13_287798_482362
  · exact context_13_287799_482403

theorem selected_cut_18850 : selected 7 ⟨482415, by decide⟩
    (prefixPartial 14 1151200) = some ⟨14, 2, 0, 482415, 1151200, 357, 4096⟩ := by
  decide +kernel

theorem context_14_1151200_482415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151200 ⟨482415, by decide⟩ :=
  accepted_of_selected 14 1151200 ⟨482415, by decide⟩ ⟨14, 2, 0, 482415, 1151200, 357, 4096⟩
    (by decide) selected_cut_18850

theorem selected_cut_18851 : selected 7 ⟨482440, by decide⟩
    (prefixPartial 14 1151201) = some ⟨14, 2, 0, 482440, 1151201, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_1151201_482440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151201 ⟨482440, by decide⟩ :=
  accepted_of_selected 14 1151201 ⟨482440, by decide⟩ ⟨14, 2, 0, 482440, 1151201, 1269, 4096⟩
    (by decide) selected_cut_18851

theorem selected_cut_18852 : selected 7 ⟨482474, by decide⟩
    (prefixPartial 14 1151202) = some ⟨14, 2, 0, 482474, 1151202, 1777, 4096⟩ := by
  decide +kernel

theorem context_14_1151202_482474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151202 ⟨482474, by decide⟩ :=
  accepted_of_selected 14 1151202 ⟨482474, by decide⟩ ⟨14, 2, 0, 482474, 1151202, 1777, 4096⟩
    (by decide) selected_cut_18852

theorem selected_cut_18853 : selected 7 ⟨482502, by decide⟩
    (prefixPartial 14 1151203) = some ⟨14, 2, 0, 482502, 1151203, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_1151203_482502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151203 ⟨482502, by decide⟩ :=
  accepted_of_selected 14 1151203 ⟨482502, by decide⟩ ⟨14, 2, 0, 482502, 1151203, 1429, 4096⟩
    (by decide) selected_cut_18853

theorem unmarked_context_13_287800_482503 : frontier 8 ⟨482503, by decide⟩
    (prefixCache 13 287800) (prefixPartial 13 287800) = false := by
  decide +kernel

theorem node_context_13_287800_482503 : EJMOriginalGlobalDAGData.nodes 8 ⟨482503, by decide⟩ =
    .split (coordinate 13) (![⟨482415, by decide⟩,⟨482440, by decide⟩,⟨482474, by decide⟩,⟨482502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287800_482503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287800 ⟨482503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287800
    ⟨482503, by decide⟩ (by decide) (![⟨482415, by decide⟩,⟨482440, by decide⟩,⟨482474, by decide⟩,⟨482502, by decide⟩]) unmarked_context_13_287800_482503 node_context_13_287800_482503
  intro a
  fin_cases a
  · exact context_14_1151200_482415
  · exact context_14_1151201_482440
  · exact context_14_1151202_482474
  · exact context_14_1151203_482502

theorem selected_cut_18854 : selected 7 ⟨482517, by decide⟩
    (prefixPartial 14 1151204) = some ⟨14, 2, 0, 482517, 1151204, 945, 4096⟩ := by
  decide +kernel

theorem context_14_1151204_482517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151204 ⟨482517, by decide⟩ :=
  accepted_of_selected 14 1151204 ⟨482517, by decide⟩ ⟨14, 2, 0, 482517, 1151204, 945, 4096⟩
    (by decide) selected_cut_18854

theorem selected_cut_18855 : selected 7 ⟨482536, by decide⟩
    (prefixPartial 14 1151205) = some ⟨14, 2, 0, 482536, 1151205, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_1151205_482536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151205 ⟨482536, by decide⟩ :=
  accepted_of_selected 14 1151205 ⟨482536, by decide⟩ ⟨14, 2, 0, 482536, 1151205, 1085, 4096⟩
    (by decide) selected_cut_18855

theorem selected_cut_18856 : selected 7 ⟨482571, by decide⟩
    (prefixPartial 14 1151206) = some ⟨14, 2, 0, 482571, 1151206, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_1151206_482571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151206 ⟨482571, by decide⟩ :=
  accepted_of_selected 14 1151206 ⟨482571, by decide⟩ ⟨14, 2, 0, 482571, 1151206, 1333, 4096⟩
    (by decide) selected_cut_18856

theorem selected_cut_18857 : selected 7 ⟨482591, by decide⟩
    (prefixPartial 14 1151207) = some ⟨14, 2, 0, 482591, 1151207, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_1151207_482591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151207 ⟨482591, by decide⟩ :=
  accepted_of_selected 14 1151207 ⟨482591, by decide⟩ ⟨14, 2, 0, 482591, 1151207, 1093, 4096⟩
    (by decide) selected_cut_18857

theorem unmarked_context_13_287801_482592 : frontier 8 ⟨482592, by decide⟩
    (prefixCache 13 287801) (prefixPartial 13 287801) = false := by
  decide +kernel

theorem node_context_13_287801_482592 : EJMOriginalGlobalDAGData.nodes 8 ⟨482592, by decide⟩ =
    .split (coordinate 13) (![⟨482517, by decide⟩,⟨482536, by decide⟩,⟨482571, by decide⟩,⟨482591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287801_482592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287801 ⟨482592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287801
    ⟨482592, by decide⟩ (by decide) (![⟨482517, by decide⟩,⟨482536, by decide⟩,⟨482571, by decide⟩,⟨482591, by decide⟩]) unmarked_context_13_287801_482592 node_context_13_287801_482592
  intro a
  fin_cases a
  · exact context_14_1151204_482517
  · exact context_14_1151205_482536
  · exact context_14_1151206_482571
  · exact context_14_1151207_482591

theorem selected_cut_18858 : selected 8 ⟨482716, by decide⟩
    (prefixPartial 13 287802) = some ⟨13, 2, 0, 482716, 287802, 3741, 16384⟩ := by
  decide +kernel

theorem context_13_287802_482716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287802 ⟨482716, by decide⟩ :=
  accepted_of_selected 13 287802 ⟨482716, by decide⟩ ⟨13, 2, 0, 482716, 287802, 3741, 16384⟩
    (by decide) selected_cut_18858

theorem selected_cut_18859 : selected 8 ⟨482762, by decide⟩
    (prefixPartial 13 287803) = some ⟨13, 2, 0, 482762, 287803, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_287803_482762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287803 ⟨482762, by decide⟩ :=
  accepted_of_selected 13 287803 ⟨482762, by decide⟩ ⟨13, 2, 0, 482762, 287803, 1765, 16384⟩
    (by decide) selected_cut_18859

theorem unmarked_context_12_71950_482763 : frontier 9 ⟨482763, by decide⟩
    (prefixCache 12 71950) (prefixPartial 12 71950) = false := by
  decide +kernel

theorem node_context_12_71950_482763 : EJMOriginalGlobalDAGData.nodes 9 ⟨482763, by decide⟩ =
    .split (coordinate 12) (![⟨482503, by decide⟩,⟨482592, by decide⟩,⟨482716, by decide⟩,⟨482762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71950_482763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71950 ⟨482763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71950
    ⟨482763, by decide⟩ (by decide) (![⟨482503, by decide⟩,⟨482592, by decide⟩,⟨482716, by decide⟩,⟨482762, by decide⟩]) unmarked_context_12_71950_482763 node_context_12_71950_482763
  intro a
  fin_cases a
  · exact context_13_287800_482503
  · exact context_13_287801_482592
  · exact context_13_287802_482716
  · exact context_13_287803_482762

theorem selected_cut_18860 : selected 7 ⟨482769, by decide⟩
    (prefixPartial 14 1151216) = some ⟨14, 2, 0, 482769, 1151216, 169, 4096⟩ := by
  decide +kernel

theorem context_14_1151216_482769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151216 ⟨482769, by decide⟩ :=
  accepted_of_selected 14 1151216 ⟨482769, by decide⟩ ⟨14, 2, 0, 482769, 1151216, 169, 4096⟩
    (by decide) selected_cut_18860

theorem selected_cut_18861 : selected 7 ⟨482787, by decide⟩
    (prefixPartial 14 1151217) = some ⟨14, 2, 0, 482787, 1151217, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_1151217_482787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151217 ⟨482787, by decide⟩ :=
  accepted_of_selected 14 1151217 ⟨482787, by decide⟩ ⟨14, 2, 0, 482787, 1151217, 1269, 4096⟩
    (by decide) selected_cut_18861

theorem selected_cut_18862 : selected 7 ⟨482813, by decide⟩
    (prefixPartial 14 1151218) = some ⟨14, 2, 0, 482813, 1151218, 1669, 4096⟩ := by
  decide +kernel

theorem context_14_1151218_482813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151218 ⟨482813, by decide⟩ :=
  accepted_of_selected 14 1151218 ⟨482813, by decide⟩ ⟨14, 2, 0, 482813, 1151218, 1669, 4096⟩
    (by decide) selected_cut_18862

theorem selected_cut_18863 : selected 7 ⟨482833, by decide⟩
    (prefixPartial 14 1151219) = some ⟨14, 2, 0, 482833, 1151219, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_1151219_482833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151219 ⟨482833, by decide⟩ :=
  accepted_of_selected 14 1151219 ⟨482833, by decide⟩ ⟨14, 2, 0, 482833, 1151219, 1353, 4096⟩
    (by decide) selected_cut_18863

theorem unmarked_context_13_287804_482834 : frontier 8 ⟨482834, by decide⟩
    (prefixCache 13 287804) (prefixPartial 13 287804) = false := by
  decide +kernel

theorem node_context_13_287804_482834 : EJMOriginalGlobalDAGData.nodes 8 ⟨482834, by decide⟩ =
    .split (coordinate 13) (![⟨482769, by decide⟩,⟨482787, by decide⟩,⟨482813, by decide⟩,⟨482833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287804_482834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287804 ⟨482834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287804
    ⟨482834, by decide⟩ (by decide) (![⟨482769, by decide⟩,⟨482787, by decide⟩,⟨482813, by decide⟩,⟨482833, by decide⟩]) unmarked_context_13_287804_482834 node_context_13_287804_482834
  intro a
  fin_cases a
  · exact context_14_1151216_482769
  · exact context_14_1151217_482787
  · exact context_14_1151218_482813
  · exact context_14_1151219_482833

theorem selected_cut_18864 : selected 7 ⟨482843, by decide⟩
    (prefixPartial 14 1151220) = some ⟨14, 2, 0, 482843, 1151220, 957, 4096⟩ := by
  decide +kernel

theorem context_14_1151220_482843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151220 ⟨482843, by decide⟩ :=
  accepted_of_selected 14 1151220 ⟨482843, by decide⟩ ⟨14, 2, 0, 482843, 1151220, 957, 4096⟩
    (by decide) selected_cut_18864

theorem selected_cut_18865 : selected 7 ⟨482857, by decide⟩
    (prefixPartial 14 1151221) = some ⟨14, 2, 0, 482857, 1151221, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_1151221_482857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151221 ⟨482857, by decide⟩ :=
  accepted_of_selected 14 1151221 ⟨482857, by decide⟩ ⟨14, 2, 0, 482857, 1151221, 1105, 4096⟩
    (by decide) selected_cut_18865

theorem selected_cut_18866 : selected 7 ⟨482878, by decide⟩
    (prefixPartial 14 1151222) = some ⟨14, 2, 0, 482878, 1151222, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_1151222_482878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151222 ⟨482878, by decide⟩ :=
  accepted_of_selected 14 1151222 ⟨482878, by decide⟩ ⟨14, 2, 0, 482878, 1151222, 1037, 4096⟩
    (by decide) selected_cut_18866

theorem selected_cut_18867 : selected 7 ⟨482897, by decide⟩
    (prefixPartial 14 1151223) = some ⟨14, 2, 0, 482897, 1151223, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_1151223_482897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151223 ⟨482897, by decide⟩ :=
  accepted_of_selected 14 1151223 ⟨482897, by decide⟩ ⟨14, 2, 0, 482897, 1151223, 1097, 4096⟩
    (by decide) selected_cut_18867

theorem unmarked_context_13_287805_482898 : frontier 8 ⟨482898, by decide⟩
    (prefixCache 13 287805) (prefixPartial 13 287805) = false := by
  decide +kernel

theorem node_context_13_287805_482898 : EJMOriginalGlobalDAGData.nodes 8 ⟨482898, by decide⟩ =
    .split (coordinate 13) (![⟨482843, by decide⟩,⟨482857, by decide⟩,⟨482878, by decide⟩,⟨482897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287805_482898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287805 ⟨482898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287805
    ⟨482898, by decide⟩ (by decide) (![⟨482843, by decide⟩,⟨482857, by decide⟩,⟨482878, by decide⟩,⟨482897, by decide⟩]) unmarked_context_13_287805_482898 node_context_13_287805_482898
  intro a
  fin_cases a
  · exact context_14_1151220_482843
  · exact context_14_1151221_482857
  · exact context_14_1151222_482878
  · exact context_14_1151223_482897

theorem selected_cut_18868 : selected 8 ⟨482984, by decide⟩
    (prefixPartial 13 287806) = some ⟨13, 2, 0, 482984, 287806, 3345, 16384⟩ := by
  decide +kernel

theorem context_13_287806_482984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287806 ⟨482984, by decide⟩ :=
  accepted_of_selected 13 287806 ⟨482984, by decide⟩ ⟨13, 2, 0, 482984, 287806, 3345, 16384⟩
    (by decide) selected_cut_18868

theorem selected_cut_18869 : selected 8 ⟨483011, by decide⟩
    (prefixPartial 13 287807) = some ⟨13, 2, 0, 483011, 287807, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_287807_483011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287807 ⟨483011, by decide⟩ :=
  accepted_of_selected 13 287807 ⟨483011, by decide⟩ ⟨13, 2, 0, 483011, 287807, 1445, 16384⟩
    (by decide) selected_cut_18869

theorem unmarked_context_12_71951_483012 : frontier 9 ⟨483012, by decide⟩
    (prefixCache 12 71951) (prefixPartial 12 71951) = false := by
  decide +kernel

theorem node_context_12_71951_483012 : EJMOriginalGlobalDAGData.nodes 9 ⟨483012, by decide⟩ =
    .split (coordinate 12) (![⟨482834, by decide⟩,⟨482898, by decide⟩,⟨482984, by decide⟩,⟨483011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71951_483012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71951 ⟨483012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71951
    ⟨483012, by decide⟩ (by decide) (![⟨482834, by decide⟩,⟨482898, by decide⟩,⟨482984, by decide⟩,⟨483011, by decide⟩]) unmarked_context_12_71951_483012 node_context_12_71951_483012
  intro a
  fin_cases a
  · exact context_13_287804_482834
  · exact context_13_287805_482898
  · exact context_13_287806_482984
  · exact context_13_287807_483011

theorem unmarked_context_11_17987_483013 : frontier 10 ⟨483013, by decide⟩
    (prefixCache 11 17987) (prefixPartial 11 17987) = false := by
  decide +kernel

theorem node_context_11_17987_483013 : EJMOriginalGlobalDAGData.nodes 10 ⟨483013, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨482404, by decide⟩,⟨482763, by decide⟩,⟨483012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17987_483013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17987 ⟨483013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17987
    ⟨483013, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨482404, by decide⟩,⟨482763, by decide⟩,⟨483012, by decide⟩]) unmarked_context_11_17987_483013 node_context_11_17987_483013
  intro a
  fin_cases a
  · exact context_12_71948_448748
  · exact context_12_71949_482404
  · exact context_12_71950_482763
  · exact context_12_71951_483012

theorem unmarked_context_10_4496_483014 : frontier 11 ⟨483014, by decide⟩
    (prefixCache 10 4496) (prefixPartial 10 4496) = false := by
  decide +kernel

theorem node_context_10_4496_483014 : EJMOriginalGlobalDAGData.nodes 11 ⟨483014, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨481710, by decide⟩,⟨482164, by decide⟩,⟨483013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4496_483014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4496 ⟨483014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4496
    ⟨483014, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨481710, by decide⟩,⟨482164, by decide⟩,⟨483013, by decide⟩]) unmarked_context_10_4496_483014 node_context_10_4496_483014
  intro a
  fin_cases a
  · exact context_11_17984_434745
  · exact context_11_17985_481710
  · exact context_11_17986_482164
  · exact context_11_17987_483013

theorem selected_cut_18870 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 71952) = some ⟨12, 1, 0, 435160, 71952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71952_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71952 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 71952 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 71952, 1, 65536⟩
    (by decide) selected_cut_18870

theorem selected_cut_18871 : selected 8 ⟨483074, by decide⟩
    (prefixPartial 13 287812) = some ⟨13, 2, 0, 483074, 287812, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_287812_483074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287812 ⟨483074, by decide⟩ :=
  accepted_of_selected 13 287812 ⟨483074, by decide⟩ ⟨13, 2, 0, 483074, 287812, 2673, 16384⟩
    (by decide) selected_cut_18871

theorem selected_cut_18872 : selected 8 ⟨483114, by decide⟩
    (prefixPartial 13 287813) = some ⟨13, 2, 0, 483114, 287813, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_287813_483114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287813 ⟨483114, by decide⟩ :=
  accepted_of_selected 13 287813 ⟨483114, by decide⟩ ⟨13, 2, 0, 483114, 287813, 2185, 16384⟩
    (by decide) selected_cut_18872

theorem selected_cut_18873 : selected 8 ⟨483135, by decide⟩
    (prefixPartial 13 287814) = some ⟨13, 2, 0, 483135, 287814, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_287814_483135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287814 ⟨483135, by decide⟩ :=
  accepted_of_selected 13 287814 ⟨483135, by decide⟩ ⟨13, 2, 0, 483135, 287814, 1773, 16384⟩
    (by decide) selected_cut_18873

theorem selected_cut_18874 : selected 8 ⟨483144, by decide⟩
    (prefixPartial 13 287815) = some ⟨13, 2, 0, 483144, 287815, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_287815_483144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287815 ⟨483144, by decide⟩ :=
  accepted_of_selected 13 287815 ⟨483144, by decide⟩ ⟨13, 2, 0, 483144, 287815, 1049, 16384⟩
    (by decide) selected_cut_18874

theorem unmarked_context_12_71953_483145 : frontier 9 ⟨483145, by decide⟩
    (prefixCache 12 71953) (prefixPartial 12 71953) = false := by
  decide +kernel

theorem node_context_12_71953_483145 : EJMOriginalGlobalDAGData.nodes 9 ⟨483145, by decide⟩ =
    .split (coordinate 12) (![⟨483074, by decide⟩,⟨483114, by decide⟩,⟨483135, by decide⟩,⟨483144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71953_483145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71953 ⟨483145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71953
    ⟨483145, by decide⟩ (by decide) (![⟨483074, by decide⟩,⟨483114, by decide⟩,⟨483135, by decide⟩,⟨483144, by decide⟩]) unmarked_context_12_71953_483145 node_context_12_71953_483145
  intro a
  fin_cases a
  · exact context_13_287812_483074
  · exact context_13_287813_483114
  · exact context_13_287814_483135
  · exact context_13_287815_483144

theorem selected_cut_18875 : selected 8 ⟨483219, by decide⟩
    (prefixPartial 13 287816) = some ⟨13, 2, 0, 483219, 287816, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_287816_483219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287816 ⟨483219, by decide⟩ :=
  accepted_of_selected 13 287816 ⟨483219, by decide⟩ ⟨13, 2, 0, 483219, 287816, 3109, 16384⟩
    (by decide) selected_cut_18875

theorem selected_cut_18876 : selected 8 ⟨483273, by decide⟩
    (prefixPartial 13 287817) = some ⟨13, 2, 0, 483273, 287817, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_287817_483273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287817 ⟨483273, by decide⟩ :=
  accepted_of_selected 13 287817 ⟨483273, by decide⟩ ⟨13, 2, 0, 483273, 287817, 2745, 16384⟩
    (by decide) selected_cut_18876

theorem selected_cut_18877 : selected 8 ⟨483313, by decide⟩
    (prefixPartial 13 287818) = some ⟨13, 2, 0, 483313, 287818, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_287818_483313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287818 ⟨483313, by decide⟩ :=
  accepted_of_selected 13 287818 ⟨483313, by decide⟩ ⟨13, 2, 0, 483313, 287818, 2129, 16384⟩
    (by decide) selected_cut_18877

theorem selected_cut_18878 : selected 8 ⟨483329, by decide⟩
    (prefixPartial 13 287819) = some ⟨13, 2, 0, 483329, 287819, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_287819_483329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287819 ⟨483329, by decide⟩ :=
  accepted_of_selected 13 287819 ⟨483329, by decide⟩ ⟨13, 2, 0, 483329, 287819, 1217, 16384⟩
    (by decide) selected_cut_18878

theorem unmarked_context_12_71954_483330 : frontier 9 ⟨483330, by decide⟩
    (prefixCache 12 71954) (prefixPartial 12 71954) = false := by
  decide +kernel

theorem node_context_12_71954_483330 : EJMOriginalGlobalDAGData.nodes 9 ⟨483330, by decide⟩ =
    .split (coordinate 12) (![⟨483219, by decide⟩,⟨483273, by decide⟩,⟨483313, by decide⟩,⟨483329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71954_483330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71954 ⟨483330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71954
    ⟨483330, by decide⟩ (by decide) (![⟨483219, by decide⟩,⟨483273, by decide⟩,⟨483313, by decide⟩,⟨483329, by decide⟩]) unmarked_context_12_71954_483330 node_context_12_71954_483330
  intro a
  fin_cases a
  · exact context_13_287816_483219
  · exact context_13_287817_483273
  · exact context_13_287818_483313
  · exact context_13_287819_483329

theorem selected_cut_18879 : selected 8 ⟨483386, by decide⟩
    (prefixPartial 13 287820) = some ⟨13, 2, 0, 483386, 287820, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_287820_483386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287820 ⟨483386, by decide⟩ :=
  accepted_of_selected 13 287820 ⟨483386, by decide⟩ ⟨13, 2, 0, 483386, 287820, 3185, 16384⟩
    (by decide) selected_cut_18879

theorem selected_cut_18880 : selected 8 ⟨483441, by decide⟩
    (prefixPartial 13 287821) = some ⟨13, 2, 0, 483441, 287821, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_287821_483441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287821 ⟨483441, by decide⟩ :=
  accepted_of_selected 13 287821 ⟨483441, by decide⟩ ⟨13, 2, 0, 483441, 287821, 2813, 16384⟩
    (by decide) selected_cut_18880

theorem selected_cut_18881 : selected 8 ⟨483477, by decide⟩
    (prefixPartial 13 287822) = some ⟨13, 2, 0, 483477, 287822, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_287822_483477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287822 ⟨483477, by decide⟩ :=
  accepted_of_selected 13 287822 ⟨483477, by decide⟩ ⟨13, 2, 0, 483477, 287822, 2245, 16384⟩
    (by decide) selected_cut_18881

theorem selected_cut_18882 : selected 8 ⟨483486, by decide⟩
    (prefixPartial 13 287823) = some ⟨13, 2, 0, 483486, 287823, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_287823_483486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287823 ⟨483486, by decide⟩ :=
  accepted_of_selected 13 287823 ⟨483486, by decide⟩ ⟨13, 2, 0, 483486, 287823, 1057, 16384⟩
    (by decide) selected_cut_18882

theorem unmarked_context_12_71955_483487 : frontier 9 ⟨483487, by decide⟩
    (prefixCache 12 71955) (prefixPartial 12 71955) = false := by
  decide +kernel

theorem node_context_12_71955_483487 : EJMOriginalGlobalDAGData.nodes 9 ⟨483487, by decide⟩ =
    .split (coordinate 12) (![⟨483386, by decide⟩,⟨483441, by decide⟩,⟨483477, by decide⟩,⟨483486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71955_483487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71955 ⟨483487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71955
    ⟨483487, by decide⟩ (by decide) (![⟨483386, by decide⟩,⟨483441, by decide⟩,⟨483477, by decide⟩,⟨483486, by decide⟩]) unmarked_context_12_71955_483487 node_context_12_71955_483487
  intro a
  fin_cases a
  · exact context_13_287820_483386
  · exact context_13_287821_483441
  · exact context_13_287822_483477
  · exact context_13_287823_483486

theorem unmarked_context_11_17988_483488 : frontier 10 ⟨483488, by decide⟩
    (prefixCache 11 17988) (prefixPartial 11 17988) = false := by
  decide +kernel

theorem node_context_11_17988_483488 : EJMOriginalGlobalDAGData.nodes 10 ⟨483488, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨483145, by decide⟩,⟨483330, by decide⟩,⟨483487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17988_483488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17988 ⟨483488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17988
    ⟨483488, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨483145, by decide⟩,⟨483330, by decide⟩,⟨483487, by decide⟩]) unmarked_context_11_17988_483488 node_context_11_17988_483488
  intro a
  fin_cases a
  · exact context_12_71952_435160
  · exact context_12_71953_483145
  · exact context_12_71954_483330
  · exact context_12_71955_483487

theorem selected_cut_18883 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 71956) = some ⟨12, 1, 0, 449505, 71956, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71956_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71956 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 71956 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 71956, 1, 65536⟩
    (by decide) selected_cut_18883

theorem selected_cut_18884 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 71957) = some ⟨12, 1, 0, 439069, 71957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71957_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71957 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 71957 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 71957, 1, 65536⟩
    (by decide) selected_cut_18884

theorem selected_cut_18885 : selected 8 ⟨483542, by decide⟩
    (prefixPartial 13 287832) = some ⟨13, 2, 0, 483542, 287832, 2985, 16384⟩ := by
  decide +kernel

theorem context_13_287832_483542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287832 ⟨483542, by decide⟩ :=
  accepted_of_selected 13 287832 ⟨483542, by decide⟩ ⟨13, 2, 0, 483542, 287832, 2985, 16384⟩
    (by decide) selected_cut_18885

theorem selected_cut_18886 : selected 8 ⟨483579, by decide⟩
    (prefixPartial 13 287833) = some ⟨13, 2, 0, 483579, 287833, 2989, 16384⟩ := by
  decide +kernel

theorem context_13_287833_483579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287833 ⟨483579, by decide⟩ :=
  accepted_of_selected 13 287833 ⟨483579, by decide⟩ ⟨13, 2, 0, 483579, 287833, 2989, 16384⟩
    (by decide) selected_cut_18886

theorem selected_cut_18887 : selected 8 ⟨483603, by decide⟩
    (prefixPartial 13 287834) = some ⟨13, 2, 0, 483603, 287834, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_287834_483603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287834 ⟨483603, by decide⟩ :=
  accepted_of_selected 13 287834 ⟨483603, by decide⟩ ⟨13, 2, 0, 483603, 287834, 1941, 16384⟩
    (by decide) selected_cut_18887

theorem selected_cut_18888 : selected 8 ⟨483620, by decide⟩
    (prefixPartial 13 287835) = some ⟨13, 2, 0, 483620, 287835, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_287835_483620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287835 ⟨483620, by decide⟩ :=
  accepted_of_selected 13 287835 ⟨483620, by decide⟩ ⟨13, 2, 0, 483620, 287835, 1245, 16384⟩
    (by decide) selected_cut_18888

theorem unmarked_context_12_71958_483621 : frontier 9 ⟨483621, by decide⟩
    (prefixCache 12 71958) (prefixPartial 12 71958) = false := by
  decide +kernel

theorem node_context_12_71958_483621 : EJMOriginalGlobalDAGData.nodes 9 ⟨483621, by decide⟩ =
    .split (coordinate 12) (![⟨483542, by decide⟩,⟨483579, by decide⟩,⟨483603, by decide⟩,⟨483620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71958_483621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71958 ⟨483621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71958
    ⟨483621, by decide⟩ (by decide) (![⟨483542, by decide⟩,⟨483579, by decide⟩,⟨483603, by decide⟩,⟨483620, by decide⟩]) unmarked_context_12_71958_483621 node_context_12_71958_483621
  intro a
  fin_cases a
  · exact context_13_287832_483542
  · exact context_13_287833_483579
  · exact context_13_287834_483603
  · exact context_13_287835_483620

theorem selected_cut_18889 : selected 8 ⟨483675, by decide⟩
    (prefixPartial 13 287836) = some ⟨13, 2, 0, 483675, 287836, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_287836_483675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287836 ⟨483675, by decide⟩ :=
  accepted_of_selected 13 287836 ⟨483675, by decide⟩ ⟨13, 2, 0, 483675, 287836, 2981, 16384⟩
    (by decide) selected_cut_18889

theorem selected_cut_18890 : selected 8 ⟨483720, by decide⟩
    (prefixPartial 13 287837) = some ⟨13, 2, 0, 483720, 287837, 3129, 16384⟩ := by
  decide +kernel

theorem context_13_287837_483720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287837 ⟨483720, by decide⟩ :=
  accepted_of_selected 13 287837 ⟨483720, by decide⟩ ⟨13, 2, 0, 483720, 287837, 3129, 16384⟩
    (by decide) selected_cut_18890

theorem selected_cut_18891 : selected 8 ⟨483750, by decide⟩
    (prefixPartial 13 287838) = some ⟨13, 2, 0, 483750, 287838, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_287838_483750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287838 ⟨483750, by decide⟩ :=
  accepted_of_selected 13 287838 ⟨483750, by decide⟩ ⟨13, 2, 0, 483750, 287838, 2121, 16384⟩
    (by decide) selected_cut_18891

theorem selected_cut_18892 : selected 8 ⟨483757, by decide⟩
    (prefixPartial 13 287839) = some ⟨13, 2, 0, 483757, 287839, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_287839_483757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287839 ⟨483757, by decide⟩ :=
  accepted_of_selected 13 287839 ⟨483757, by decide⟩ ⟨13, 2, 0, 483757, 287839, 1005, 16384⟩
    (by decide) selected_cut_18892

theorem unmarked_context_12_71959_483758 : frontier 9 ⟨483758, by decide⟩
    (prefixCache 12 71959) (prefixPartial 12 71959) = false := by
  decide +kernel

theorem node_context_12_71959_483758 : EJMOriginalGlobalDAGData.nodes 9 ⟨483758, by decide⟩ =
    .split (coordinate 12) (![⟨483675, by decide⟩,⟨483720, by decide⟩,⟨483750, by decide⟩,⟨483757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71959_483758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71959 ⟨483758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71959
    ⟨483758, by decide⟩ (by decide) (![⟨483675, by decide⟩,⟨483720, by decide⟩,⟨483750, by decide⟩,⟨483757, by decide⟩]) unmarked_context_12_71959_483758 node_context_12_71959_483758
  intro a
  fin_cases a
  · exact context_13_287836_483675
  · exact context_13_287837_483720
  · exact context_13_287838_483750
  · exact context_13_287839_483757

theorem unmarked_context_11_17989_483759 : frontier 10 ⟨483759, by decide⟩
    (prefixCache 11 17989) (prefixPartial 11 17989) = false := by
  decide +kernel

theorem node_context_11_17989_483759 : EJMOriginalGlobalDAGData.nodes 10 ⟨483759, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨439069, by decide⟩,⟨483621, by decide⟩,⟨483758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17989_483759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17989 ⟨483759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17989
    ⟨483759, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨439069, by decide⟩,⟨483621, by decide⟩,⟨483758, by decide⟩]) unmarked_context_11_17989_483759 node_context_11_17989_483759
  intro a
  fin_cases a
  · exact context_12_71956_449505
  · exact context_12_71957_439069
  · exact context_12_71958_483621
  · exact context_12_71959_483758

theorem selected_cut_18893 : selected 8 ⟨483828, by decide⟩
    (prefixPartial 13 287840) = some ⟨13, 2, 0, 483828, 287840, 3429, 16384⟩ := by
  decide +kernel

theorem context_13_287840_483828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287840 ⟨483828, by decide⟩ :=
  accepted_of_selected 13 287840 ⟨483828, by decide⟩ ⟨13, 2, 0, 483828, 287840, 3429, 16384⟩
    (by decide) selected_cut_18893

theorem selected_cut_18894 : selected 8 ⟨483878, by decide⟩
    (prefixPartial 13 287841) = some ⟨13, 2, 0, 483878, 287841, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_287841_483878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287841 ⟨483878, by decide⟩ :=
  accepted_of_selected 13 287841 ⟨483878, by decide⟩ ⟨13, 2, 0, 483878, 287841, 3389, 16384⟩
    (by decide) selected_cut_18894

theorem selected_cut_18895 : selected 8 ⟨483921, by decide⟩
    (prefixPartial 13 287842) = some ⟨13, 2, 0, 483921, 287842, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_287842_483921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287842 ⟨483921, by decide⟩ :=
  accepted_of_selected 13 287842 ⟨483921, by decide⟩ ⟨13, 2, 0, 483921, 287842, 2457, 16384⟩
    (by decide) selected_cut_18895

theorem selected_cut_18896 : selected 8 ⟨483962, by decide⟩
    (prefixPartial 13 287843) = some ⟨13, 2, 0, 483962, 287843, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_287843_483962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287843 ⟨483962, by decide⟩ :=
  accepted_of_selected 13 287843 ⟨483962, by decide⟩ ⟨13, 2, 0, 483962, 287843, 1473, 16384⟩
    (by decide) selected_cut_18896

theorem unmarked_context_12_71960_483963 : frontier 9 ⟨483963, by decide⟩
    (prefixCache 12 71960) (prefixPartial 12 71960) = false := by
  decide +kernel

theorem node_context_12_71960_483963 : EJMOriginalGlobalDAGData.nodes 9 ⟨483963, by decide⟩ =
    .split (coordinate 12) (![⟨483828, by decide⟩,⟨483878, by decide⟩,⟨483921, by decide⟩,⟨483962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71960_483963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71960 ⟨483963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71960
    ⟨483963, by decide⟩ (by decide) (![⟨483828, by decide⟩,⟨483878, by decide⟩,⟨483921, by decide⟩,⟨483962, by decide⟩]) unmarked_context_12_71960_483963 node_context_12_71960_483963
  intro a
  fin_cases a
  · exact context_13_287840_483828
  · exact context_13_287841_483878
  · exact context_13_287842_483921
  · exact context_13_287843_483962

theorem selected_cut_18897 : selected 8 ⟨484005, by decide⟩
    (prefixPartial 13 287844) = some ⟨13, 2, 0, 484005, 287844, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_287844_484005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287844 ⟨484005, by decide⟩ :=
  accepted_of_selected 13 287844 ⟨484005, by decide⟩ ⟨13, 2, 0, 484005, 287844, 2153, 16384⟩
    (by decide) selected_cut_18897

theorem selected_cut_18898 : selected 8 ⟨484027, by decide⟩
    (prefixPartial 13 287845) = some ⟨13, 2, 0, 484027, 287845, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_287845_484027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287845 ⟨484027, by decide⟩ :=
  accepted_of_selected 13 287845 ⟨484027, by decide⟩ ⟨13, 2, 0, 484027, 287845, 2225, 16384⟩
    (by decide) selected_cut_18898

theorem selected_cut_18899 : selected 8 ⟨484044, by decide⟩
    (prefixPartial 13 287846) = some ⟨13, 2, 0, 484044, 287846, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_287846_484044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287846 ⟨484044, by decide⟩ :=
  accepted_of_selected 13 287846 ⟨484044, by decide⟩ ⟨13, 2, 0, 484044, 287846, 1861, 16384⟩
    (by decide) selected_cut_18899

theorem selected_cut_18900 : selected 8 ⟨484047, by decide⟩
    (prefixPartial 13 287847) = some ⟨13, 2, 0, 484047, 287847, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_287847_484047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287847 ⟨484047, by decide⟩ :=
  accepted_of_selected 13 287847 ⟨484047, by decide⟩ ⟨13, 2, 0, 484047, 287847, 1077, 16384⟩
    (by decide) selected_cut_18900

theorem unmarked_context_12_71961_484048 : frontier 9 ⟨484048, by decide⟩
    (prefixCache 12 71961) (prefixPartial 12 71961) = false := by
  decide +kernel

theorem node_context_12_71961_484048 : EJMOriginalGlobalDAGData.nodes 9 ⟨484048, by decide⟩ =
    .split (coordinate 12) (![⟨484005, by decide⟩,⟨484027, by decide⟩,⟨484044, by decide⟩,⟨484047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71961_484048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71961 ⟨484048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71961
    ⟨484048, by decide⟩ (by decide) (![⟨484005, by decide⟩,⟨484027, by decide⟩,⟨484044, by decide⟩,⟨484047, by decide⟩]) unmarked_context_12_71961_484048 node_context_12_71961_484048
  intro a
  fin_cases a
  · exact context_13_287844_484005
  · exact context_13_287845_484027
  · exact context_13_287846_484044
  · exact context_13_287847_484047

theorem selected_cut_18901 : selected 8 ⟨484099, by decide⟩
    (prefixPartial 13 287848) = some ⟨13, 2, 0, 484099, 287848, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_287848_484099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287848 ⟨484099, by decide⟩ :=
  accepted_of_selected 13 287848 ⟨484099, by decide⟩ ⟨13, 2, 0, 484099, 287848, 2561, 16384⟩
    (by decide) selected_cut_18901

theorem selected_cut_18902 : selected 8 ⟨484127, by decide⟩
    (prefixPartial 13 287849) = some ⟨13, 2, 0, 484127, 287849, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_287849_484127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287849 ⟨484127, by decide⟩ :=
  accepted_of_selected 13 287849 ⟨484127, by decide⟩ ⟨13, 2, 0, 484127, 287849, 2713, 16384⟩
    (by decide) selected_cut_18902

theorem selected_cut_18903 : selected 8 ⟨484154, by decide⟩
    (prefixPartial 13 287850) = some ⟨13, 2, 0, 484154, 287850, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_287850_484154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287850 ⟨484154, by decide⟩ :=
  accepted_of_selected 13 287850 ⟨484154, by decide⟩ ⟨13, 2, 0, 484154, 287850, 2065, 16384⟩
    (by decide) selected_cut_18903

theorem selected_cut_18904 : selected 8 ⟨484170, by decide⟩
    (prefixPartial 13 287851) = some ⟨13, 2, 0, 484170, 287851, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_287851_484170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287851 ⟨484170, by decide⟩ :=
  accepted_of_selected 13 287851 ⟨484170, by decide⟩ ⟨13, 2, 0, 484170, 287851, 1221, 16384⟩
    (by decide) selected_cut_18904

theorem unmarked_context_12_71962_484171 : frontier 9 ⟨484171, by decide⟩
    (prefixCache 12 71962) (prefixPartial 12 71962) = false := by
  decide +kernel

theorem node_context_12_71962_484171 : EJMOriginalGlobalDAGData.nodes 9 ⟨484171, by decide⟩ =
    .split (coordinate 12) (![⟨484099, by decide⟩,⟨484127, by decide⟩,⟨484154, by decide⟩,⟨484170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71962_484171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71962 ⟨484171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71962
    ⟨484171, by decide⟩ (by decide) (![⟨484099, by decide⟩,⟨484127, by decide⟩,⟨484154, by decide⟩,⟨484170, by decide⟩]) unmarked_context_12_71962_484171 node_context_12_71962_484171
  intro a
  fin_cases a
  · exact context_13_287848_484099
  · exact context_13_287849_484127
  · exact context_13_287850_484154
  · exact context_13_287851_484170

theorem selected_cut_18905 : selected 8 ⟨484221, by decide⟩
    (prefixPartial 13 287852) = some ⟨13, 2, 0, 484221, 287852, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_287852_484221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287852 ⟨484221, by decide⟩ :=
  accepted_of_selected 13 287852 ⟨484221, by decide⟩ ⟨13, 2, 0, 484221, 287852, 2601, 16384⟩
    (by decide) selected_cut_18905

theorem selected_cut_18906 : selected 8 ⟨484261, by decide⟩
    (prefixPartial 13 287853) = some ⟨13, 2, 0, 484261, 287853, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_287853_484261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287853 ⟨484261, by decide⟩ :=
  accepted_of_selected 13 287853 ⟨484261, by decide⟩ ⟨13, 2, 0, 484261, 287853, 2869, 16384⟩
    (by decide) selected_cut_18906

theorem selected_cut_18907 : selected 8 ⟨484283, by decide⟩
    (prefixPartial 13 287854) = some ⟨13, 2, 0, 484283, 287854, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_287854_484283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287854 ⟨484283, by decide⟩ :=
  accepted_of_selected 13 287854 ⟨484283, by decide⟩ ⟨13, 2, 0, 484283, 287854, 2137, 16384⟩
    (by decide) selected_cut_18907

theorem selected_cut_18908 : selected 8 ⟨484291, by decide⟩
    (prefixPartial 13 287855) = some ⟨13, 2, 0, 484291, 287855, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_287855_484291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287855 ⟨484291, by decide⟩ :=
  accepted_of_selected 13 287855 ⟨484291, by decide⟩ ⟨13, 2, 0, 484291, 287855, 1057, 16384⟩
    (by decide) selected_cut_18908

theorem unmarked_context_12_71963_484292 : frontier 9 ⟨484292, by decide⟩
    (prefixCache 12 71963) (prefixPartial 12 71963) = false := by
  decide +kernel

theorem node_context_12_71963_484292 : EJMOriginalGlobalDAGData.nodes 9 ⟨484292, by decide⟩ =
    .split (coordinate 12) (![⟨484221, by decide⟩,⟨484261, by decide⟩,⟨484283, by decide⟩,⟨484291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71963_484292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71963 ⟨484292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71963
    ⟨484292, by decide⟩ (by decide) (![⟨484221, by decide⟩,⟨484261, by decide⟩,⟨484283, by decide⟩,⟨484291, by decide⟩]) unmarked_context_12_71963_484292 node_context_12_71963_484292
  intro a
  fin_cases a
  · exact context_13_287852_484221
  · exact context_13_287853_484261
  · exact context_13_287854_484283
  · exact context_13_287855_484291

theorem unmarked_context_11_17990_484293 : frontier 10 ⟨484293, by decide⟩
    (prefixCache 11 17990) (prefixPartial 11 17990) = false := by
  decide +kernel

theorem node_context_11_17990_484293 : EJMOriginalGlobalDAGData.nodes 10 ⟨484293, by decide⟩ =
    .split (coordinate 11) (![⟨483963, by decide⟩,⟨484048, by decide⟩,⟨484171, by decide⟩,⟨484292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17990_484293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17990 ⟨484293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17990
    ⟨484293, by decide⟩ (by decide) (![⟨483963, by decide⟩,⟨484048, by decide⟩,⟨484171, by decide⟩,⟨484292, by decide⟩]) unmarked_context_11_17990_484293 node_context_11_17990_484293
  intro a
  fin_cases a
  · exact context_12_71960_483963
  · exact context_12_71961_484048
  · exact context_12_71962_484171
  · exact context_12_71963_484292

theorem selected_cut_18909 : selected 8 ⟨484358, by decide⟩
    (prefixPartial 13 287856) = some ⟨13, 2, 0, 484358, 287856, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_287856_484358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287856 ⟨484358, by decide⟩ :=
  accepted_of_selected 13 287856 ⟨484358, by decide⟩ ⟨13, 2, 0, 484358, 287856, 3161, 16384⟩
    (by decide) selected_cut_18909

theorem selected_cut_18910 : selected 8 ⟨484413, by decide⟩
    (prefixPartial 13 287857) = some ⟨13, 2, 0, 484413, 287857, 3653, 16384⟩ := by
  decide +kernel

theorem context_13_287857_484413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287857 ⟨484413, by decide⟩ :=
  accepted_of_selected 13 287857 ⟨484413, by decide⟩ ⟨13, 2, 0, 484413, 287857, 3653, 16384⟩
    (by decide) selected_cut_18910

theorem selected_cut_18911 : selected 8 ⟨484472, by decide⟩
    (prefixPartial 13 287858) = some ⟨13, 2, 0, 484472, 287858, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_287858_484472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287858 ⟨484472, by decide⟩ :=
  accepted_of_selected 13 287858 ⟨484472, by decide⟩ ⟨13, 2, 0, 484472, 287858, 2893, 16384⟩
    (by decide) selected_cut_18911

theorem selected_cut_18912 : selected 8 ⟨484507, by decide⟩
    (prefixPartial 13 287859) = some ⟨13, 2, 0, 484507, 287859, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_287859_484507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287859 ⟨484507, by decide⟩ :=
  accepted_of_selected 13 287859 ⟨484507, by decide⟩ ⟨13, 2, 0, 484507, 287859, 1521, 16384⟩
    (by decide) selected_cut_18912

theorem unmarked_context_12_71964_484508 : frontier 9 ⟨484508, by decide⟩
    (prefixCache 12 71964) (prefixPartial 12 71964) = false := by
  decide +kernel

theorem node_context_12_71964_484508 : EJMOriginalGlobalDAGData.nodes 9 ⟨484508, by decide⟩ =
    .split (coordinate 12) (![⟨484358, by decide⟩,⟨484413, by decide⟩,⟨484472, by decide⟩,⟨484507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71964_484508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71964 ⟨484508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71964
    ⟨484508, by decide⟩ (by decide) (![⟨484358, by decide⟩,⟨484413, by decide⟩,⟨484472, by decide⟩,⟨484507, by decide⟩]) unmarked_context_12_71964_484508 node_context_12_71964_484508
  intro a
  fin_cases a
  · exact context_13_287856_484358
  · exact context_13_287857_484413
  · exact context_13_287858_484472
  · exact context_13_287859_484507

theorem selected_cut_18913 : selected 8 ⟨484547, by decide⟩
    (prefixPartial 13 287860) = some ⟨13, 2, 0, 484547, 287860, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_287860_484547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287860 ⟨484547, by decide⟩ :=
  accepted_of_selected 13 287860 ⟨484547, by decide⟩ ⟨13, 2, 0, 484547, 287860, 1965, 16384⟩
    (by decide) selected_cut_18913

theorem selected_cut_18914 : selected 8 ⟨484582, by decide⟩
    (prefixPartial 13 287861) = some ⟨13, 2, 0, 484582, 287861, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_287861_484582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287861 ⟨484582, by decide⟩ :=
  accepted_of_selected 13 287861 ⟨484582, by decide⟩ ⟨13, 2, 0, 484582, 287861, 2321, 16384⟩
    (by decide) selected_cut_18914

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
