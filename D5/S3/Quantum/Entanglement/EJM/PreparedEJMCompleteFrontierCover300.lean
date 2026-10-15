/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover299
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28803 : selected 9 ⟨726393, by decide⟩
    (prefixPartial 12 92976) = some ⟨12, 2, 0, 726393, 92976, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_92976_726393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92976 ⟨726393, by decide⟩ :=
  accepted_of_selected 12 92976 ⟨726393, by decide⟩ ⟨12, 2, 0, 726393, 92976, 4053, 65536⟩
    (by decide) selected_cut_28803

theorem selected_cut_28804 : selected 8 ⟨726406, by decide⟩
    (prefixPartial 13 371908) = some ⟨13, 2, 0, 726406, 371908, 633, 16384⟩ := by
  decide +kernel

theorem context_13_371908_726406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371908 ⟨726406, by decide⟩ :=
  accepted_of_selected 13 371908 ⟨726406, by decide⟩ ⟨13, 2, 0, 726406, 371908, 633, 16384⟩
    (by decide) selected_cut_28804

theorem selected_cut_28805 : selected 8 ⟨726444, by decide⟩
    (prefixPartial 13 371909) = some ⟨13, 2, 0, 726444, 371909, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_371909_726444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371909 ⟨726444, by decide⟩ :=
  accepted_of_selected 13 371909 ⟨726444, by decide⟩ ⟨13, 2, 0, 726444, 371909, 1669, 16384⟩
    (by decide) selected_cut_28805

theorem selected_cut_28806 : selected 8 ⟨726457, by decide⟩
    (prefixPartial 13 371910) = some ⟨13, 2, 0, 726457, 371910, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_371910_726457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371910 ⟨726457, by decide⟩ :=
  accepted_of_selected 13 371910 ⟨726457, by decide⟩ ⟨13, 2, 0, 726457, 371910, 1053, 16384⟩
    (by decide) selected_cut_28806

theorem selected_cut_28807 : selected 8 ⟨726465, by decide⟩
    (prefixPartial 13 371911) = some ⟨13, 2, 0, 726465, 371911, 753, 16384⟩ := by
  decide +kernel

theorem context_13_371911_726465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371911 ⟨726465, by decide⟩ :=
  accepted_of_selected 13 371911 ⟨726465, by decide⟩ ⟨13, 2, 0, 726465, 371911, 753, 16384⟩
    (by decide) selected_cut_28807

theorem unmarked_context_12_92977_726466 : frontier 9 ⟨726466, by decide⟩
    (prefixCache 12 92977) (prefixPartial 12 92977) = false := by
  decide +kernel

theorem node_context_12_92977_726466 : EJMOriginalGlobalDAGData.nodes 9 ⟨726466, by decide⟩ =
    .split (coordinate 12) (![⟨726406, by decide⟩,⟨726444, by decide⟩,⟨726457, by decide⟩,⟨726465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92977_726466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92977 ⟨726466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92977
    ⟨726466, by decide⟩ (by decide) (![⟨726406, by decide⟩,⟨726444, by decide⟩,⟨726457, by decide⟩,⟨726465, by decide⟩]) unmarked_context_12_92977_726466 node_context_12_92977_726466
  intro a
  fin_cases a
  · exact context_13_371908_726406
  · exact context_13_371909_726444
  · exact context_13_371910_726457
  · exact context_13_371911_726465

theorem selected_cut_28808 : selected 8 ⟨726479, by decide⟩
    (prefixPartial 13 371912) = some ⟨13, 2, 0, 726479, 371912, 585, 16384⟩ := by
  decide +kernel

theorem context_13_371912_726479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371912 ⟨726479, by decide⟩ :=
  accepted_of_selected 13 371912 ⟨726479, by decide⟩ ⟨13, 2, 0, 726479, 371912, 585, 16384⟩
    (by decide) selected_cut_28808

theorem selected_cut_28809 : selected 8 ⟨726507, by decide⟩
    (prefixPartial 13 371913) = some ⟨13, 2, 0, 726507, 371913, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_371913_726507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371913 ⟨726507, by decide⟩ :=
  accepted_of_selected 13 371913 ⟨726507, by decide⟩ ⟨13, 2, 0, 726507, 371913, 1637, 16384⟩
    (by decide) selected_cut_28809

theorem selected_cut_28810 : selected 8 ⟨726520, by decide⟩
    (prefixPartial 13 371914) = some ⟨13, 2, 0, 726520, 371914, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_371914_726520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371914 ⟨726520, by decide⟩ :=
  accepted_of_selected 13 371914 ⟨726520, by decide⟩ ⟨13, 2, 0, 726520, 371914, 1253, 16384⟩
    (by decide) selected_cut_28810

theorem selected_cut_28811 : selected 8 ⟨726525, by decide⟩
    (prefixPartial 13 371915) = some ⟨13, 2, 0, 726525, 371915, 761, 16384⟩ := by
  decide +kernel

theorem context_13_371915_726525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371915 ⟨726525, by decide⟩ :=
  accepted_of_selected 13 371915 ⟨726525, by decide⟩ ⟨13, 2, 0, 726525, 371915, 761, 16384⟩
    (by decide) selected_cut_28811

theorem unmarked_context_12_92978_726526 : frontier 9 ⟨726526, by decide⟩
    (prefixCache 12 92978) (prefixPartial 12 92978) = false := by
  decide +kernel

theorem node_context_12_92978_726526 : EJMOriginalGlobalDAGData.nodes 9 ⟨726526, by decide⟩ =
    .split (coordinate 12) (![⟨726479, by decide⟩,⟨726507, by decide⟩,⟨726520, by decide⟩,⟨726525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92978_726526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92978 ⟨726526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92978
    ⟨726526, by decide⟩ (by decide) (![⟨726479, by decide⟩,⟨726507, by decide⟩,⟨726520, by decide⟩,⟨726525, by decide⟩]) unmarked_context_12_92978_726526 node_context_12_92978_726526
  intro a
  fin_cases a
  · exact context_13_371912_726479
  · exact context_13_371913_726507
  · exact context_13_371914_726520
  · exact context_13_371915_726525

theorem selected_cut_28812 : selected 9 ⟨726579, by decide⟩
    (prefixPartial 12 92979) = some ⟨12, 2, 0, 726579, 92979, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_92979_726579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92979 ⟨726579, by decide⟩ :=
  accepted_of_selected 12 92979 ⟨726579, by decide⟩ ⟨12, 2, 0, 726579, 92979, 3957, 65536⟩
    (by decide) selected_cut_28812

theorem unmarked_context_11_23244_726580 : frontier 10 ⟨726580, by decide⟩
    (prefixCache 11 23244) (prefixPartial 11 23244) = false := by
  decide +kernel

theorem node_context_11_23244_726580 : EJMOriginalGlobalDAGData.nodes 10 ⟨726580, by decide⟩ =
    .split (coordinate 11) (![⟨726393, by decide⟩,⟨726466, by decide⟩,⟨726526, by decide⟩,⟨726579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23244_726580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23244 ⟨726580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23244
    ⟨726580, by decide⟩ (by decide) (![⟨726393, by decide⟩,⟨726466, by decide⟩,⟨726526, by decide⟩,⟨726579, by decide⟩]) unmarked_context_11_23244_726580 node_context_11_23244_726580
  intro a
  fin_cases a
  · exact context_12_92976_726393
  · exact context_12_92977_726466
  · exact context_12_92978_726526
  · exact context_12_92979_726579

theorem selected_cut_28813 : selected 9 ⟨726643, by decide⟩
    (prefixPartial 12 92980) = some ⟨12, 2, 0, 726643, 92980, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_92980_726643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92980 ⟨726643, by decide⟩ :=
  accepted_of_selected 12 92980 ⟨726643, by decide⟩ ⟨12, 2, 0, 726643, 92980, 4093, 65536⟩
    (by decide) selected_cut_28813

theorem selected_cut_28814 : selected 9 ⟨726700, by decide⟩
    (prefixPartial 12 92981) = some ⟨12, 2, 0, 726700, 92981, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_92981_726700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92981 ⟨726700, by decide⟩ :=
  accepted_of_selected 12 92981 ⟨726700, by decide⟩ ⟨12, 2, 0, 726700, 92981, 3853, 65536⟩
    (by decide) selected_cut_28814

theorem selected_cut_28815 : selected 8 ⟨726707, by decide⟩
    (prefixPartial 13 371928) = some ⟨13, 2, 0, 726707, 371928, 453, 16384⟩ := by
  decide +kernel

theorem context_13_371928_726707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371928 ⟨726707, by decide⟩ :=
  accepted_of_selected 13 371928 ⟨726707, by decide⟩ ⟨13, 2, 0, 726707, 371928, 453, 16384⟩
    (by decide) selected_cut_28815

theorem selected_cut_28816 : selected 8 ⟨726737, by decide⟩
    (prefixPartial 13 371929) = some ⟨13, 2, 0, 726737, 371929, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_371929_726737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371929 ⟨726737, by decide⟩ :=
  accepted_of_selected 13 371929 ⟨726737, by decide⟩ ⟨13, 2, 0, 726737, 371929, 1641, 16384⟩
    (by decide) selected_cut_28816

theorem selected_cut_28817 : selected 8 ⟨726750, by decide⟩
    (prefixPartial 13 371930) = some ⟨13, 2, 0, 726750, 371930, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_371930_726750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371930 ⟨726750, by decide⟩ :=
  accepted_of_selected 13 371930 ⟨726750, by decide⟩ ⟨13, 2, 0, 726750, 371930, 1245, 16384⟩
    (by decide) selected_cut_28817

theorem selected_cut_28818 : selected 8 ⟨726757, by decide⟩
    (prefixPartial 13 371931) = some ⟨13, 2, 0, 726757, 371931, 821, 16384⟩ := by
  decide +kernel

theorem context_13_371931_726757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371931 ⟨726757, by decide⟩ :=
  accepted_of_selected 13 371931 ⟨726757, by decide⟩ ⟨13, 2, 0, 726757, 371931, 821, 16384⟩
    (by decide) selected_cut_28818

theorem unmarked_context_12_92982_726758 : frontier 9 ⟨726758, by decide⟩
    (prefixCache 12 92982) (prefixPartial 12 92982) = false := by
  decide +kernel

theorem node_context_12_92982_726758 : EJMOriginalGlobalDAGData.nodes 9 ⟨726758, by decide⟩ =
    .split (coordinate 12) (![⟨726707, by decide⟩,⟨726737, by decide⟩,⟨726750, by decide⟩,⟨726757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92982_726758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92982 ⟨726758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92982
    ⟨726758, by decide⟩ (by decide) (![⟨726707, by decide⟩,⟨726737, by decide⟩,⟨726750, by decide⟩,⟨726757, by decide⟩]) unmarked_context_12_92982_726758 node_context_12_92982_726758
  intro a
  fin_cases a
  · exact context_13_371928_726707
  · exact context_13_371929_726737
  · exact context_13_371930_726750
  · exact context_13_371931_726757

theorem selected_cut_28819 : selected 9 ⟨726811, by decide⟩
    (prefixPartial 12 92983) = some ⟨12, 2, 0, 726811, 92983, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_92983_726811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92983 ⟨726811, by decide⟩ :=
  accepted_of_selected 12 92983 ⟨726811, by decide⟩ ⟨12, 2, 0, 726811, 92983, 3797, 65536⟩
    (by decide) selected_cut_28819

theorem unmarked_context_11_23245_726812 : frontier 10 ⟨726812, by decide⟩
    (prefixCache 11 23245) (prefixPartial 11 23245) = false := by
  decide +kernel

theorem node_context_11_23245_726812 : EJMOriginalGlobalDAGData.nodes 10 ⟨726812, by decide⟩ =
    .split (coordinate 11) (![⟨726643, by decide⟩,⟨726700, by decide⟩,⟨726758, by decide⟩,⟨726811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23245_726812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23245 ⟨726812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23245
    ⟨726812, by decide⟩ (by decide) (![⟨726643, by decide⟩,⟨726700, by decide⟩,⟨726758, by decide⟩,⟨726811, by decide⟩]) unmarked_context_11_23245_726812 node_context_11_23245_726812
  intro a
  fin_cases a
  · exact context_12_92980_726643
  · exact context_12_92981_726700
  · exact context_12_92982_726758
  · exact context_12_92983_726811

theorem selected_cut_28820 : selected 9 ⟨726866, by decide⟩
    (prefixPartial 12 92984) = some ⟨12, 2, 0, 726866, 92984, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_92984_726866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92984 ⟨726866, by decide⟩ :=
  accepted_of_selected 12 92984 ⟨726866, by decide⟩ ⟨12, 2, 0, 726866, 92984, 3597, 65536⟩
    (by decide) selected_cut_28820

theorem selected_cut_28821 : selected 9 ⟨726921, by decide⟩
    (prefixPartial 12 92985) = some ⟨12, 2, 0, 726921, 92985, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_92985_726921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92985 ⟨726921, by decide⟩ :=
  accepted_of_selected 12 92985 ⟨726921, by decide⟩ ⟨12, 2, 0, 726921, 92985, 3341, 65536⟩
    (by decide) selected_cut_28821

theorem selected_cut_28822 : selected 9 ⟨726972, by decide⟩
    (prefixPartial 12 92986) = some ⟨12, 2, 0, 726972, 92986, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_92986_726972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92986 ⟨726972, by decide⟩ :=
  accepted_of_selected 12 92986 ⟨726972, by decide⟩ ⟨12, 2, 0, 726972, 92986, 3369, 65536⟩
    (by decide) selected_cut_28822

theorem selected_cut_28823 : selected 9 ⟨727022, by decide⟩
    (prefixPartial 12 92987) = some ⟨12, 2, 0, 727022, 92987, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_92987_727022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92987 ⟨727022, by decide⟩ :=
  accepted_of_selected 12 92987 ⟨727022, by decide⟩ ⟨12, 2, 0, 727022, 92987, 3209, 65536⟩
    (by decide) selected_cut_28823

theorem unmarked_context_11_23246_727023 : frontier 10 ⟨727023, by decide⟩
    (prefixCache 11 23246) (prefixPartial 11 23246) = false := by
  decide +kernel

theorem node_context_11_23246_727023 : EJMOriginalGlobalDAGData.nodes 10 ⟨727023, by decide⟩ =
    .split (coordinate 11) (![⟨726866, by decide⟩,⟨726921, by decide⟩,⟨726972, by decide⟩,⟨727022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23246_727023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23246 ⟨727023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23246
    ⟨727023, by decide⟩ (by decide) (![⟨726866, by decide⟩,⟨726921, by decide⟩,⟨726972, by decide⟩,⟨727022, by decide⟩]) unmarked_context_11_23246_727023 node_context_11_23246_727023
  intro a
  fin_cases a
  · exact context_12_92984_726866
  · exact context_12_92985_726921
  · exact context_12_92986_726972
  · exact context_12_92987_727022

theorem selected_cut_28824 : selected 9 ⟨727078, by decide⟩
    (prefixPartial 12 92988) = some ⟨12, 2, 0, 727078, 92988, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_92988_727078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92988 ⟨727078, by decide⟩ :=
  accepted_of_selected 12 92988 ⟨727078, by decide⟩ ⟨12, 2, 0, 727078, 92988, 3453, 65536⟩
    (by decide) selected_cut_28824

theorem selected_cut_28825 : selected 9 ⟨727130, by decide⟩
    (prefixPartial 12 92989) = some ⟨12, 2, 0, 727130, 92989, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_92989_727130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92989 ⟨727130, by decide⟩ :=
  accepted_of_selected 12 92989 ⟨727130, by decide⟩ ⟨12, 2, 0, 727130, 92989, 3357, 65536⟩
    (by decide) selected_cut_28825

theorem selected_cut_28826 : selected 9 ⟨727182, by decide⟩
    (prefixPartial 12 92990) = some ⟨12, 2, 0, 727182, 92990, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_92990_727182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92990 ⟨727182, by decide⟩ :=
  accepted_of_selected 12 92990 ⟨727182, by decide⟩ ⟨12, 2, 0, 727182, 92990, 3413, 65536⟩
    (by decide) selected_cut_28826

theorem selected_cut_28827 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 92991) = some ⟨12, 1, 0, 512556, 92991, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92991_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92991 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 92991 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 92991, 1, 65536⟩
    (by decide) selected_cut_28827

theorem unmarked_context_11_23247_727183 : frontier 10 ⟨727183, by decide⟩
    (prefixCache 11 23247) (prefixPartial 11 23247) = false := by
  decide +kernel

theorem node_context_11_23247_727183 : EJMOriginalGlobalDAGData.nodes 10 ⟨727183, by decide⟩ =
    .split (coordinate 11) (![⟨727078, by decide⟩,⟨727130, by decide⟩,⟨727182, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23247_727183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23247 ⟨727183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23247
    ⟨727183, by decide⟩ (by decide) (![⟨727078, by decide⟩,⟨727130, by decide⟩,⟨727182, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_23247_727183 node_context_11_23247_727183
  intro a
  fin_cases a
  · exact context_12_92988_727078
  · exact context_12_92989_727130
  · exact context_12_92990_727182
  · exact context_12_92991_512556

theorem unmarked_context_10_5811_727184 : frontier 11 ⟨727184, by decide⟩
    (prefixCache 10 5811) (prefixPartial 10 5811) = false := by
  decide +kernel

theorem node_context_10_5811_727184 : EJMOriginalGlobalDAGData.nodes 11 ⟨727184, by decide⟩ =
    .split (coordinate 10) (![⟨726580, by decide⟩,⟨726812, by decide⟩,⟨727023, by decide⟩,⟨727183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5811_727184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5811 ⟨727184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5811
    ⟨727184, by decide⟩ (by decide) (![⟨726580, by decide⟩,⟨726812, by decide⟩,⟨727023, by decide⟩,⟨727183, by decide⟩]) unmarked_context_10_5811_727184 node_context_10_5811_727184
  intro a
  fin_cases a
  · exact context_11_23244_726580
  · exact context_11_23245_726812
  · exact context_11_23246_727023
  · exact context_11_23247_727183

theorem unmarked_context_9_1452_727185 : frontier 12 ⟨727185, by decide⟩
    (prefixCache 9 1452) (prefixPartial 9 1452) = false := by
  decide +kernel

theorem node_context_9_1452_727185 : EJMOriginalGlobalDAGData.nodes 12 ⟨727185, by decide⟩ =
    .split (coordinate 9) (![⟨723920, by decide⟩,⟨725254, by decide⟩,⟨726341, by decide⟩,⟨727184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1452_727185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1452 ⟨727185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1452
    ⟨727185, by decide⟩ (by decide) (![⟨723920, by decide⟩,⟨725254, by decide⟩,⟨726341, by decide⟩,⟨727184, by decide⟩]) unmarked_context_9_1452_727185 node_context_9_1452_727185
  intro a
  fin_cases a
  · exact context_10_5808_723920
  · exact context_10_5809_725254
  · exact context_10_5810_726341
  · exact context_10_5811_727184

theorem selected_cut_28828 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 5812) = some ⟨10, 1, 0, 145424, 5812, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5812_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5812 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 5812 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 5812, 1, 1048576⟩
    (by decide) selected_cut_28828

theorem selected_cut_28829 : selected 9 ⟨727242, by decide⟩
    (prefixPartial 12 93008) = some ⟨12, 2, 0, 727242, 93008, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_93008_727242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93008 ⟨727242, by decide⟩ :=
  accepted_of_selected 12 93008 ⟨727242, by decide⟩ ⟨12, 2, 0, 727242, 93008, 2701, 65536⟩
    (by decide) selected_cut_28829

theorem selected_cut_28830 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93009) = some ⟨12, 1, 0, 642341, 93009, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93009_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93009 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93009 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93009, 1, 65536⟩
    (by decide) selected_cut_28830

theorem selected_cut_28831 : selected 9 ⟨727310, by decide⟩
    (prefixPartial 12 93010) = some ⟨12, 2, 0, 727310, 93010, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_93010_727310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93010 ⟨727310, by decide⟩ :=
  accepted_of_selected 12 93010 ⟨727310, by decide⟩ ⟨12, 2, 0, 727310, 93010, 3057, 65536⟩
    (by decide) selected_cut_28831

theorem selected_cut_28832 : selected 9 ⟨727361, by decide⟩
    (prefixPartial 12 93011) = some ⟨12, 2, 0, 727361, 93011, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_93011_727361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93011 ⟨727361, by decide⟩ :=
  accepted_of_selected 12 93011 ⟨727361, by decide⟩ ⟨12, 2, 0, 727361, 93011, 2649, 65536⟩
    (by decide) selected_cut_28832

theorem unmarked_context_11_23252_727362 : frontier 10 ⟨727362, by decide⟩
    (prefixCache 11 23252) (prefixPartial 11 23252) = false := by
  decide +kernel

theorem node_context_11_23252_727362 : EJMOriginalGlobalDAGData.nodes 10 ⟨727362, by decide⟩ =
    .split (coordinate 11) (![⟨727242, by decide⟩,⟨642341, by decide⟩,⟨727310, by decide⟩,⟨727361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23252_727362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23252 ⟨727362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23252
    ⟨727362, by decide⟩ (by decide) (![⟨727242, by decide⟩,⟨642341, by decide⟩,⟨727310, by decide⟩,⟨727361, by decide⟩]) unmarked_context_11_23252_727362 node_context_11_23252_727362
  intro a
  fin_cases a
  · exact context_12_93008_727242
  · exact context_12_93009_642341
  · exact context_12_93010_727310
  · exact context_12_93011_727361

theorem selected_cut_28833 : selected 9 ⟨727427, by decide⟩
    (prefixPartial 12 93012) = some ⟨12, 2, 0, 727427, 93012, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_93012_727427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93012 ⟨727427, by decide⟩ :=
  accepted_of_selected 12 93012 ⟨727427, by decide⟩ ⟨12, 2, 0, 727427, 93012, 2801, 65536⟩
    (by decide) selected_cut_28833

theorem selected_cut_28834 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93013) = some ⟨12, 1, 0, 642341, 93013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93013_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93013 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93013 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93013, 1, 65536⟩
    (by decide) selected_cut_28834

theorem selected_cut_28835 : selected 9 ⟨727476, by decide⟩
    (prefixPartial 12 93014) = some ⟨12, 2, 0, 727476, 93014, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_93014_727476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93014 ⟨727476, by decide⟩ :=
  accepted_of_selected 12 93014 ⟨727476, by decide⟩ ⟨12, 2, 0, 727476, 93014, 2821, 65536⟩
    (by decide) selected_cut_28835

theorem selected_cut_28836 : selected 9 ⟨727533, by decide⟩
    (prefixPartial 12 93015) = some ⟨12, 2, 0, 727533, 93015, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_93015_727533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93015 ⟨727533, by decide⟩ :=
  accepted_of_selected 12 93015 ⟨727533, by decide⟩ ⟨12, 2, 0, 727533, 93015, 2537, 65536⟩
    (by decide) selected_cut_28836

theorem unmarked_context_11_23253_727534 : frontier 10 ⟨727534, by decide⟩
    (prefixCache 11 23253) (prefixPartial 11 23253) = false := by
  decide +kernel

theorem node_context_11_23253_727534 : EJMOriginalGlobalDAGData.nodes 10 ⟨727534, by decide⟩ =
    .split (coordinate 11) (![⟨727427, by decide⟩,⟨642341, by decide⟩,⟨727476, by decide⟩,⟨727533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23253_727534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23253 ⟨727534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23253
    ⟨727534, by decide⟩ (by decide) (![⟨727427, by decide⟩,⟨642341, by decide⟩,⟨727476, by decide⟩,⟨727533, by decide⟩]) unmarked_context_11_23253_727534 node_context_11_23253_727534
  intro a
  fin_cases a
  · exact context_12_93012_727427
  · exact context_12_93013_642341
  · exact context_12_93014_727476
  · exact context_12_93015_727533

theorem selected_cut_28837 : selected 9 ⟨727582, by decide⟩
    (prefixPartial 12 93016) = some ⟨12, 2, 0, 727582, 93016, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_93016_727582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93016 ⟨727582, by decide⟩ :=
  accepted_of_selected 12 93016 ⟨727582, by decide⟩ ⟨12, 2, 0, 727582, 93016, 2201, 65536⟩
    (by decide) selected_cut_28837

theorem selected_cut_28838 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93017) = some ⟨12, 1, 0, 642341, 93017, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93017_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93017 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93017 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93017, 1, 65536⟩
    (by decide) selected_cut_28838

theorem selected_cut_28839 : selected 9 ⟨727626, by decide⟩
    (prefixPartial 12 93018) = some ⟨12, 2, 0, 727626, 93018, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_93018_727626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93018 ⟨727626, by decide⟩ :=
  accepted_of_selected 12 93018 ⟨727626, by decide⟩ ⟨12, 2, 0, 727626, 93018, 2321, 65536⟩
    (by decide) selected_cut_28839

theorem selected_cut_28840 : selected 9 ⟨727666, by decide⟩
    (prefixPartial 12 93019) = some ⟨12, 2, 0, 727666, 93019, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_93019_727666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93019 ⟨727666, by decide⟩ :=
  accepted_of_selected 12 93019 ⟨727666, by decide⟩ ⟨12, 2, 0, 727666, 93019, 2165, 65536⟩
    (by decide) selected_cut_28840

theorem unmarked_context_11_23254_727667 : frontier 10 ⟨727667, by decide⟩
    (prefixCache 11 23254) (prefixPartial 11 23254) = false := by
  decide +kernel

theorem node_context_11_23254_727667 : EJMOriginalGlobalDAGData.nodes 10 ⟨727667, by decide⟩ =
    .split (coordinate 11) (![⟨727582, by decide⟩,⟨642341, by decide⟩,⟨727626, by decide⟩,⟨727666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23254_727667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23254 ⟨727667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23254
    ⟨727667, by decide⟩ (by decide) (![⟨727582, by decide⟩,⟨642341, by decide⟩,⟨727626, by decide⟩,⟨727666, by decide⟩]) unmarked_context_11_23254_727667 node_context_11_23254_727667
  intro a
  fin_cases a
  · exact context_12_93016_727582
  · exact context_12_93017_642341
  · exact context_12_93018_727626
  · exact context_12_93019_727666

theorem selected_cut_28841 : selected 10 ⟨727738, by decide⟩
    (prefixPartial 11 23255) = some ⟨11, 2, 0, 727738, 23255, 4013, 262144⟩ := by
  decide +kernel

theorem context_11_23255_727738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23255 ⟨727738, by decide⟩ :=
  accepted_of_selected 11 23255 ⟨727738, by decide⟩ ⟨11, 2, 0, 727738, 23255, 4013, 262144⟩
    (by decide) selected_cut_28841

theorem unmarked_context_10_5813_727739 : frontier 11 ⟨727739, by decide⟩
    (prefixCache 10 5813) (prefixPartial 10 5813) = false := by
  decide +kernel

theorem node_context_10_5813_727739 : EJMOriginalGlobalDAGData.nodes 11 ⟨727739, by decide⟩ =
    .split (coordinate 10) (![⟨727362, by decide⟩,⟨727534, by decide⟩,⟨727667, by decide⟩,⟨727738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5813_727739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5813 ⟨727739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5813
    ⟨727739, by decide⟩ (by decide) (![⟨727362, by decide⟩,⟨727534, by decide⟩,⟨727667, by decide⟩,⟨727738, by decide⟩]) unmarked_context_10_5813_727739 node_context_10_5813_727739
  intro a
  fin_cases a
  · exact context_11_23252_727362
  · exact context_11_23253_727534
  · exact context_11_23254_727667
  · exact context_11_23255_727738

theorem selected_cut_28842 : selected 9 ⟨727778, by decide⟩
    (prefixPartial 12 93024) = some ⟨12, 2, 0, 727778, 93024, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_93024_727778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93024 ⟨727778, by decide⟩ :=
  accepted_of_selected 12 93024 ⟨727778, by decide⟩ ⟨12, 2, 0, 727778, 93024, 1281, 65536⟩
    (by decide) selected_cut_28842

theorem selected_cut_28843 : selected 9 ⟨727828, by decide⟩
    (prefixPartial 12 93025) = some ⟨12, 2, 0, 727828, 93025, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_93025_727828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93025 ⟨727828, by decide⟩ :=
  accepted_of_selected 12 93025 ⟨727828, by decide⟩ ⟨12, 2, 0, 727828, 93025, 2465, 65536⟩
    (by decide) selected_cut_28843

theorem selected_cut_28844 : selected 9 ⟨727865, by decide⟩
    (prefixPartial 12 93026) = some ⟨12, 2, 0, 727865, 93026, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_93026_727865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93026 ⟨727865, by decide⟩ :=
  accepted_of_selected 12 93026 ⟨727865, by decide⟩ ⟨12, 2, 0, 727865, 93026, 2029, 65536⟩
    (by decide) selected_cut_28844

theorem selected_cut_28845 : selected 9 ⟨727896, by decide⟩
    (prefixPartial 12 93027) = some ⟨12, 2, 0, 727896, 93027, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_93027_727896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93027 ⟨727896, by decide⟩ :=
  accepted_of_selected 12 93027 ⟨727896, by decide⟩ ⟨12, 2, 0, 727896, 93027, 1669, 65536⟩
    (by decide) selected_cut_28845

theorem unmarked_context_11_23256_727897 : frontier 10 ⟨727897, by decide⟩
    (prefixCache 11 23256) (prefixPartial 11 23256) = false := by
  decide +kernel

theorem node_context_11_23256_727897 : EJMOriginalGlobalDAGData.nodes 10 ⟨727897, by decide⟩ =
    .split (coordinate 11) (![⟨727778, by decide⟩,⟨727828, by decide⟩,⟨727865, by decide⟩,⟨727896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23256_727897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23256 ⟨727897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23256
    ⟨727897, by decide⟩ (by decide) (![⟨727778, by decide⟩,⟨727828, by decide⟩,⟨727865, by decide⟩,⟨727896, by decide⟩]) unmarked_context_11_23256_727897 node_context_11_23256_727897
  intro a
  fin_cases a
  · exact context_12_93024_727778
  · exact context_12_93025_727828
  · exact context_12_93026_727865
  · exact context_12_93027_727896

theorem selected_cut_28846 : selected 10 ⟨727953, by decide⟩
    (prefixPartial 11 23257) = some ⟨11, 2, 0, 727953, 23257, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_23257_727953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23257 ⟨727953, by decide⟩ :=
  accepted_of_selected 11 23257 ⟨727953, by decide⟩ ⟨11, 2, 0, 727953, 23257, 2885, 262144⟩
    (by decide) selected_cut_28846

theorem selected_cut_28847 : selected 10 ⟨728036, by decide⟩
    (prefixPartial 11 23258) = some ⟨11, 2, 0, 728036, 23258, 3733, 262144⟩ := by
  decide +kernel

theorem context_11_23258_728036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23258 ⟨728036, by decide⟩ :=
  accepted_of_selected 11 23258 ⟨728036, by decide⟩ ⟨11, 2, 0, 728036, 23258, 3733, 262144⟩
    (by decide) selected_cut_28847

theorem selected_cut_28848 : selected 10 ⟨728088, by decide⟩
    (prefixPartial 11 23259) = some ⟨11, 2, 0, 728088, 23259, 497, 262144⟩ := by
  decide +kernel

theorem context_11_23259_728088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23259 ⟨728088, by decide⟩ :=
  accepted_of_selected 11 23259 ⟨728088, by decide⟩ ⟨11, 2, 0, 728088, 23259, 497, 262144⟩
    (by decide) selected_cut_28848

theorem unmarked_context_10_5814_728089 : frontier 11 ⟨728089, by decide⟩
    (prefixCache 10 5814) (prefixPartial 10 5814) = false := by
  decide +kernel

theorem node_context_10_5814_728089 : EJMOriginalGlobalDAGData.nodes 11 ⟨728089, by decide⟩ =
    .split (coordinate 10) (![⟨727897, by decide⟩,⟨727953, by decide⟩,⟨728036, by decide⟩,⟨728088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5814_728089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5814 ⟨728089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5814
    ⟨728089, by decide⟩ (by decide) (![⟨727897, by decide⟩,⟨727953, by decide⟩,⟨728036, by decide⟩,⟨728088, by decide⟩]) unmarked_context_10_5814_728089 node_context_10_5814_728089
  intro a
  fin_cases a
  · exact context_11_23256_727897
  · exact context_11_23257_727953
  · exact context_11_23258_728036
  · exact context_11_23259_728088

theorem selected_cut_28849 : selected 9 ⟨728117, by decide⟩
    (prefixPartial 12 93040) = some ⟨12, 2, 0, 728117, 93040, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_93040_728117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93040 ⟨728117, by decide⟩ :=
  accepted_of_selected 12 93040 ⟨728117, by decide⟩ ⟨12, 2, 0, 728117, 93040, 1845, 65536⟩
    (by decide) selected_cut_28849

theorem selected_cut_28850 : selected 9 ⟨728174, by decide⟩
    (prefixPartial 12 93041) = some ⟨12, 2, 0, 728174, 93041, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_93041_728174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93041 ⟨728174, by decide⟩ :=
  accepted_of_selected 12 93041 ⟨728174, by decide⟩ ⟨12, 2, 0, 728174, 93041, 2245, 65536⟩
    (by decide) selected_cut_28850

theorem selected_cut_28851 : selected 9 ⟨728209, by decide⟩
    (prefixPartial 12 93042) = some ⟨12, 2, 0, 728209, 93042, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_93042_728209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93042 ⟨728209, by decide⟩ :=
  accepted_of_selected 12 93042 ⟨728209, by decide⟩ ⟨12, 2, 0, 728209, 93042, 1921, 65536⟩
    (by decide) selected_cut_28851

theorem selected_cut_28852 : selected 9 ⟨728234, by decide⟩
    (prefixPartial 12 93043) = some ⟨12, 2, 0, 728234, 93043, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_93043_728234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93043 ⟨728234, by decide⟩ :=
  accepted_of_selected 12 93043 ⟨728234, by decide⟩ ⟨12, 2, 0, 728234, 93043, 1609, 65536⟩
    (by decide) selected_cut_28852

theorem unmarked_context_11_23260_728235 : frontier 10 ⟨728235, by decide⟩
    (prefixCache 11 23260) (prefixPartial 11 23260) = false := by
  decide +kernel

theorem node_context_11_23260_728235 : EJMOriginalGlobalDAGData.nodes 10 ⟨728235, by decide⟩ =
    .split (coordinate 11) (![⟨728117, by decide⟩,⟨728174, by decide⟩,⟨728209, by decide⟩,⟨728234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23260_728235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23260 ⟨728235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23260
    ⟨728235, by decide⟩ (by decide) (![⟨728117, by decide⟩,⟨728174, by decide⟩,⟨728209, by decide⟩,⟨728234, by decide⟩]) unmarked_context_11_23260_728235 node_context_11_23260_728235
  intro a
  fin_cases a
  · exact context_12_93040_728117
  · exact context_12_93041_728174
  · exact context_12_93042_728209
  · exact context_12_93043_728234

theorem selected_cut_28853 : selected 9 ⟨728277, by decide⟩
    (prefixPartial 12 93044) = some ⟨12, 2, 0, 728277, 93044, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_93044_728277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93044 ⟨728277, by decide⟩ :=
  accepted_of_selected 12 93044 ⟨728277, by decide⟩ ⟨12, 2, 0, 728277, 93044, 1777, 65536⟩
    (by decide) selected_cut_28853

theorem selected_cut_28854 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 93045) = some ⟨12, 1, 0, 642794, 93045, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93045_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93045 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 93045 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 93045, 1, 65536⟩
    (by decide) selected_cut_28854

theorem selected_cut_28855 : selected 9 ⟨728321, by decide⟩
    (prefixPartial 12 93046) = some ⟨12, 2, 0, 728321, 93046, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_93046_728321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93046 ⟨728321, by decide⟩ :=
  accepted_of_selected 12 93046 ⟨728321, by decide⟩ ⟨12, 2, 0, 728321, 93046, 1877, 65536⟩
    (by decide) selected_cut_28855

theorem selected_cut_28856 : selected 9 ⟨728346, by decide⟩
    (prefixPartial 12 93047) = some ⟨12, 2, 0, 728346, 93047, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_93047_728346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93047 ⟨728346, by decide⟩ :=
  accepted_of_selected 12 93047 ⟨728346, by decide⟩ ⟨12, 2, 0, 728346, 93047, 1609, 65536⟩
    (by decide) selected_cut_28856

theorem unmarked_context_11_23261_728347 : frontier 10 ⟨728347, by decide⟩
    (prefixCache 11 23261) (prefixPartial 11 23261) = false := by
  decide +kernel

theorem node_context_11_23261_728347 : EJMOriginalGlobalDAGData.nodes 10 ⟨728347, by decide⟩ =
    .split (coordinate 11) (![⟨728277, by decide⟩,⟨642794, by decide⟩,⟨728321, by decide⟩,⟨728346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23261_728347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23261 ⟨728347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23261
    ⟨728347, by decide⟩ (by decide) (![⟨728277, by decide⟩,⟨642794, by decide⟩,⟨728321, by decide⟩,⟨728346, by decide⟩]) unmarked_context_11_23261_728347 node_context_11_23261_728347
  intro a
  fin_cases a
  · exact context_12_93044_728277
  · exact context_12_93045_642794
  · exact context_12_93046_728321
  · exact context_12_93047_728346

theorem selected_cut_28857 : selected 9 ⟨728397, by decide⟩
    (prefixPartial 12 93048) = some ⟨12, 2, 0, 728397, 93048, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_93048_728397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93048 ⟨728397, by decide⟩ :=
  accepted_of_selected 12 93048 ⟨728397, by decide⟩ ⟨12, 2, 0, 728397, 93048, 1521, 65536⟩
    (by decide) selected_cut_28857

theorem selected_cut_28858 : selected 9 ⟨728468, by decide⟩
    (prefixPartial 12 93049) = some ⟨12, 2, 0, 728468, 93049, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_93049_728468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93049 ⟨728468, by decide⟩ :=
  accepted_of_selected 12 93049 ⟨728468, by decide⟩ ⟨12, 2, 0, 728468, 93049, 1893, 65536⟩
    (by decide) selected_cut_28858

theorem selected_cut_28859 : selected 9 ⟨728498, by decide⟩
    (prefixPartial 12 93050) = some ⟨12, 2, 0, 728498, 93050, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_93050_728498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93050 ⟨728498, by decide⟩ :=
  accepted_of_selected 12 93050 ⟨728498, by decide⟩ ⟨12, 2, 0, 728498, 93050, 1537, 65536⟩
    (by decide) selected_cut_28859

theorem selected_cut_28860 : selected 9 ⟨728514, by decide⟩
    (prefixPartial 12 93051) = some ⟨12, 2, 0, 728514, 93051, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_93051_728514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93051 ⟨728514, by decide⟩ :=
  accepted_of_selected 12 93051 ⟨728514, by decide⟩ ⟨12, 2, 0, 728514, 93051, 1385, 65536⟩
    (by decide) selected_cut_28860

theorem unmarked_context_11_23262_728515 : frontier 10 ⟨728515, by decide⟩
    (prefixCache 11 23262) (prefixPartial 11 23262) = false := by
  decide +kernel

theorem node_context_11_23262_728515 : EJMOriginalGlobalDAGData.nodes 10 ⟨728515, by decide⟩ =
    .split (coordinate 11) (![⟨728397, by decide⟩,⟨728468, by decide⟩,⟨728498, by decide⟩,⟨728514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23262_728515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23262 ⟨728515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23262
    ⟨728515, by decide⟩ (by decide) (![⟨728397, by decide⟩,⟨728468, by decide⟩,⟨728498, by decide⟩,⟨728514, by decide⟩]) unmarked_context_11_23262_728515 node_context_11_23262_728515
  intro a
  fin_cases a
  · exact context_12_93048_728397
  · exact context_12_93049_728468
  · exact context_12_93050_728498
  · exact context_12_93051_728514

theorem selected_cut_28861 : selected 10 ⟨728559, by decide⟩
    (prefixPartial 11 23263) = some ⟨11, 2, 0, 728559, 23263, 2633, 262144⟩ := by
  decide +kernel

theorem context_11_23263_728559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23263 ⟨728559, by decide⟩ :=
  accepted_of_selected 11 23263 ⟨728559, by decide⟩ ⟨11, 2, 0, 728559, 23263, 2633, 262144⟩
    (by decide) selected_cut_28861

theorem unmarked_context_10_5815_728560 : frontier 11 ⟨728560, by decide⟩
    (prefixCache 10 5815) (prefixPartial 10 5815) = false := by
  decide +kernel

theorem node_context_10_5815_728560 : EJMOriginalGlobalDAGData.nodes 11 ⟨728560, by decide⟩ =
    .split (coordinate 10) (![⟨728235, by decide⟩,⟨728347, by decide⟩,⟨728515, by decide⟩,⟨728559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5815_728560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5815 ⟨728560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5815
    ⟨728560, by decide⟩ (by decide) (![⟨728235, by decide⟩,⟨728347, by decide⟩,⟨728515, by decide⟩,⟨728559, by decide⟩]) unmarked_context_10_5815_728560 node_context_10_5815_728560
  intro a
  fin_cases a
  · exact context_11_23260_728235
  · exact context_11_23261_728347
  · exact context_11_23262_728515
  · exact context_11_23263_728559

theorem unmarked_context_9_1453_728561 : frontier 12 ⟨728561, by decide⟩
    (prefixCache 9 1453) (prefixPartial 9 1453) = false := by
  decide +kernel

theorem node_context_9_1453_728561 : EJMOriginalGlobalDAGData.nodes 12 ⟨728561, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨727739, by decide⟩,⟨728089, by decide⟩,⟨728560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1453_728561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1453 ⟨728561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1453
    ⟨728561, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨727739, by decide⟩,⟨728089, by decide⟩,⟨728560, by decide⟩]) unmarked_context_9_1453_728561 node_context_9_1453_728561
  intro a
  fin_cases a
  · exact context_10_5812_145424
  · exact context_10_5813_727739
  · exact context_10_5814_728089
  · exact context_10_5815_728560

theorem selected_cut_28862 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 5816) = some ⟨10, 1, 0, 145424, 5816, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5816_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5816 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 5816 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 5816, 1, 1048576⟩
    (by decide) selected_cut_28862

theorem selected_cut_28863 : selected 10 ⟨728645, by decide⟩
    (prefixPartial 11 23268) = some ⟨11, 2, 0, 728645, 23268, 3661, 262144⟩ := by
  decide +kernel

theorem context_11_23268_728645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23268 ⟨728645, by decide⟩ :=
  accepted_of_selected 11 23268 ⟨728645, by decide⟩ ⟨11, 2, 0, 728645, 23268, 3661, 262144⟩
    (by decide) selected_cut_28863

theorem selected_cut_28864 : selected 10 ⟨728694, by decide⟩
    (prefixPartial 11 23269) = some ⟨11, 2, 0, 728694, 23269, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_23269_728694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23269 ⟨728694, by decide⟩ :=
  accepted_of_selected 11 23269 ⟨728694, by decide⟩ ⟨11, 2, 0, 728694, 23269, 2405, 262144⟩
    (by decide) selected_cut_28864

theorem selected_cut_28865 : selected 10 ⟨728719, by decide⟩
    (prefixPartial 11 23270) = some ⟨11, 2, 0, 728719, 23270, 1317, 262144⟩ := by
  decide +kernel

theorem context_11_23270_728719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23270 ⟨728719, by decide⟩ :=
  accepted_of_selected 11 23270 ⟨728719, by decide⟩ ⟨11, 2, 0, 728719, 23270, 1317, 262144⟩
    (by decide) selected_cut_28865

theorem selected_cut_28866 : selected 10 ⟨728729, by decide⟩
    (prefixPartial 11 23271) = some ⟨11, 2, 0, 728729, 23271, 561, 262144⟩ := by
  decide +kernel

theorem context_11_23271_728729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23271 ⟨728729, by decide⟩ :=
  accepted_of_selected 11 23271 ⟨728729, by decide⟩ ⟨11, 2, 0, 728729, 23271, 561, 262144⟩
    (by decide) selected_cut_28866

theorem unmarked_context_10_5817_728730 : frontier 11 ⟨728730, by decide⟩
    (prefixCache 10 5817) (prefixPartial 10 5817) = false := by
  decide +kernel

theorem node_context_10_5817_728730 : EJMOriginalGlobalDAGData.nodes 11 ⟨728730, by decide⟩ =
    .split (coordinate 10) (![⟨728645, by decide⟩,⟨728694, by decide⟩,⟨728719, by decide⟩,⟨728729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5817_728730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5817 ⟨728730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5817
    ⟨728730, by decide⟩ (by decide) (![⟨728645, by decide⟩,⟨728694, by decide⟩,⟨728719, by decide⟩,⟨728729, by decide⟩]) unmarked_context_10_5817_728730 node_context_10_5817_728730
  intro a
  fin_cases a
  · exact context_11_23268_728645
  · exact context_11_23269_728694
  · exact context_11_23270_728719
  · exact context_11_23271_728729

theorem selected_cut_28867 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 5818) = some ⟨10, 1, 0, 145424, 5818, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5818_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5818 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 5818 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 5818, 1, 1048576⟩
    (by decide) selected_cut_28867

theorem selected_cut_28868 : selected 10 ⟨728785, by decide⟩
    (prefixPartial 11 23276) = some ⟨11, 2, 0, 728785, 23276, 2941, 262144⟩ := by
  decide +kernel

theorem context_11_23276_728785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23276 ⟨728785, by decide⟩ :=
  accepted_of_selected 11 23276 ⟨728785, by decide⟩ ⟨11, 2, 0, 728785, 23276, 2941, 262144⟩
    (by decide) selected_cut_28868

theorem selected_cut_28869 : selected 10 ⟨728836, by decide⟩
    (prefixPartial 11 23277) = some ⟨11, 2, 0, 728836, 23277, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_23277_728836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23277 ⟨728836, by decide⟩ :=
  accepted_of_selected 11 23277 ⟨728836, by decide⟩ ⟨11, 2, 0, 728836, 23277, 2429, 262144⟩
    (by decide) selected_cut_28869

theorem selected_cut_28870 : selected 10 ⟨728861, by decide⟩
    (prefixPartial 11 23278) = some ⟨11, 2, 0, 728861, 23278, 1681, 262144⟩ := by
  decide +kernel

theorem context_11_23278_728861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23278 ⟨728861, by decide⟩ :=
  accepted_of_selected 11 23278 ⟨728861, by decide⟩ ⟨11, 2, 0, 728861, 23278, 1681, 262144⟩
    (by decide) selected_cut_28870

theorem selected_cut_28871 : selected 10 ⟨728875, by decide⟩
    (prefixPartial 11 23279) = some ⟨11, 2, 0, 728875, 23279, 917, 262144⟩ := by
  decide +kernel

theorem context_11_23279_728875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23279 ⟨728875, by decide⟩ :=
  accepted_of_selected 11 23279 ⟨728875, by decide⟩ ⟨11, 2, 0, 728875, 23279, 917, 262144⟩
    (by decide) selected_cut_28871

theorem unmarked_context_10_5819_728876 : frontier 11 ⟨728876, by decide⟩
    (prefixCache 10 5819) (prefixPartial 10 5819) = false := by
  decide +kernel

theorem node_context_10_5819_728876 : EJMOriginalGlobalDAGData.nodes 11 ⟨728876, by decide⟩ =
    .split (coordinate 10) (![⟨728785, by decide⟩,⟨728836, by decide⟩,⟨728861, by decide⟩,⟨728875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5819_728876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5819 ⟨728876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5819
    ⟨728876, by decide⟩ (by decide) (![⟨728785, by decide⟩,⟨728836, by decide⟩,⟨728861, by decide⟩,⟨728875, by decide⟩]) unmarked_context_10_5819_728876 node_context_10_5819_728876
  intro a
  fin_cases a
  · exact context_11_23276_728785
  · exact context_11_23277_728836
  · exact context_11_23278_728861
  · exact context_11_23279_728875

theorem unmarked_context_9_1454_728877 : frontier 12 ⟨728877, by decide⟩
    (prefixCache 9 1454) (prefixPartial 9 1454) = false := by
  decide +kernel

theorem node_context_9_1454_728877 : EJMOriginalGlobalDAGData.nodes 12 ⟨728877, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨728730, by decide⟩,⟨145424, by decide⟩,⟨728876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1454_728877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1454 ⟨728877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1454
    ⟨728877, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨728730, by decide⟩,⟨145424, by decide⟩,⟨728876, by decide⟩]) unmarked_context_9_1454_728877 node_context_9_1454_728877
  intro a
  fin_cases a
  · exact context_10_5816_145424
  · exact context_10_5817_728730
  · exact context_10_5818_145424
  · exact context_10_5819_728876

theorem selected_cut_28872 : selected 12 ⟨728913, by decide⟩
    (prefixPartial 9 1455) = some ⟨9, 2, 0, 728913, 1455, 921, 4194304⟩ := by
  decide +kernel

theorem context_9_1455_728913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1455 ⟨728913, by decide⟩ :=
  accepted_of_selected 9 1455 ⟨728913, by decide⟩ ⟨9, 2, 0, 728913, 1455, 921, 4194304⟩
    (by decide) selected_cut_28872

theorem unmarked_context_8_363_728914 : frontier 13 ⟨728914, by decide⟩
    (prefixCache 8 363) (prefixPartial 8 363) = false := by
  decide +kernel

theorem node_context_8_363_728914 : EJMOriginalGlobalDAGData.nodes 13 ⟨728914, by decide⟩ =
    .split (coordinate 8) (![⟨727185, by decide⟩,⟨728561, by decide⟩,⟨728877, by decide⟩,⟨728913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_363_728914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 363 ⟨728914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 363
    ⟨728914, by decide⟩ (by decide) (![⟨727185, by decide⟩,⟨728561, by decide⟩,⟨728877, by decide⟩,⟨728913, by decide⟩]) unmarked_context_8_363_728914 node_context_8_363_728914
  intro a
  fin_cases a
  · exact context_9_1452_727185
  · exact context_9_1453_728561
  · exact context_9_1454_728877
  · exact context_9_1455_728913

theorem unmarked_context_7_90_728915 : frontier 14 ⟨728915, by decide⟩
    (prefixCache 7 90) (prefixPartial 7 90) = false := by
  decide +kernel

theorem node_context_7_90_728915 : EJMOriginalGlobalDAGData.nodes 14 ⟨728915, by decide⟩ =
    .split (coordinate 7) (![⟨716007, by decide⟩,⟨723013, by decide⟩,⟨158379, by decide⟩,⟨728914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_90_728915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 90 ⟨728915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 90
    ⟨728915, by decide⟩ (by decide) (![⟨716007, by decide⟩,⟨723013, by decide⟩,⟨158379, by decide⟩,⟨728914, by decide⟩]) unmarked_context_7_90_728915 node_context_7_90_728915
  intro a
  fin_cases a
  · exact context_8_360_716007
  · exact context_8_361_723013
  · exact context_8_362_158379
  · exact context_8_363_728914

theorem selected_cut_28873 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23296) = some ⟨11, 1, 0, 434745, 23296, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23296_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23296 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23296 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23296, 1, 262144⟩
    (by decide) selected_cut_28873

theorem selected_cut_28874 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93188) = some ⟨12, 1, 0, 448748, 93188, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93188_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93188 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93188 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93188, 1, 65536⟩
    (by decide) selected_cut_28874

theorem selected_cut_28875 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 93189) = some ⟨12, 1, 0, 34034, 93189, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93189_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93189 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 93189 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 93189, 1, 65536⟩
    (by decide) selected_cut_28875

theorem selected_cut_28876 : selected 8 ⟨729011, by decide⟩
    (prefixPartial 13 372760) = some ⟨13, 2, 0, 729011, 372760, 3545, 16384⟩ := by
  decide +kernel

theorem context_13_372760_729011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372760 ⟨729011, by decide⟩ :=
  accepted_of_selected 13 372760 ⟨729011, by decide⟩ ⟨13, 2, 0, 729011, 372760, 3545, 16384⟩
    (by decide) selected_cut_28876

theorem selected_cut_28877 : selected 8 ⟨729100, by decide⟩
    (prefixPartial 13 372761) = some ⟨13, 2, 0, 729100, 372761, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_372761_729100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372761 ⟨729100, by decide⟩ :=
  accepted_of_selected 13 372761 ⟨729100, by decide⟩ ⟨13, 2, 0, 729100, 372761, 2953, 16384⟩
    (by decide) selected_cut_28877

theorem selected_cut_28878 : selected 8 ⟨729157, by decide⟩
    (prefixPartial 13 372762) = some ⟨13, 2, 0, 729157, 372762, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_372762_729157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372762 ⟨729157, by decide⟩ :=
  accepted_of_selected 13 372762 ⟨729157, by decide⟩ ⟨13, 2, 0, 729157, 372762, 2541, 16384⟩
    (by decide) selected_cut_28878

theorem selected_cut_28879 : selected 8 ⟨729182, by decide⟩
    (prefixPartial 13 372763) = some ⟨13, 2, 0, 729182, 372763, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_372763_729182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372763 ⟨729182, by decide⟩ :=
  accepted_of_selected 13 372763 ⟨729182, by decide⟩ ⟨13, 2, 0, 729182, 372763, 1085, 16384⟩
    (by decide) selected_cut_28879

theorem unmarked_context_12_93190_729183 : frontier 9 ⟨729183, by decide⟩
    (prefixCache 12 93190) (prefixPartial 12 93190) = false := by
  decide +kernel

theorem node_context_12_93190_729183 : EJMOriginalGlobalDAGData.nodes 9 ⟨729183, by decide⟩ =
    .split (coordinate 12) (![⟨729011, by decide⟩,⟨729100, by decide⟩,⟨729157, by decide⟩,⟨729182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93190_729183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93190 ⟨729183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93190
    ⟨729183, by decide⟩ (by decide) (![⟨729011, by decide⟩,⟨729100, by decide⟩,⟨729157, by decide⟩,⟨729182, by decide⟩]) unmarked_context_12_93190_729183 node_context_12_93190_729183
  intro a
  fin_cases a
  · exact context_13_372760_729011
  · exact context_13_372761_729100
  · exact context_13_372762_729157
  · exact context_13_372763_729182

theorem selected_cut_28880 : selected 8 ⟨729271, by decide⟩
    (prefixPartial 13 372764) = some ⟨13, 2, 0, 729271, 372764, 3845, 16384⟩ := by
  decide +kernel

theorem context_13_372764_729271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372764 ⟨729271, by decide⟩ :=
  accepted_of_selected 13 372764 ⟨729271, by decide⟩ ⟨13, 2, 0, 729271, 372764, 3845, 16384⟩
    (by decide) selected_cut_28880

theorem selected_cut_28881 : selected 8 ⟨729326, by decide⟩
    (prefixPartial 13 372765) = some ⟨13, 2, 0, 729326, 372765, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_372765_729326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372765 ⟨729326, by decide⟩ :=
  accepted_of_selected 13 372765 ⟨729326, by decide⟩ ⟨13, 2, 0, 729326, 372765, 2721, 16384⟩
    (by decide) selected_cut_28881

theorem selected_cut_28882 : selected 8 ⟨729369, by decide⟩
    (prefixPartial 13 372766) = some ⟨13, 2, 0, 729369, 372766, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_372766_729369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372766 ⟨729369, by decide⟩ :=
  accepted_of_selected 13 372766 ⟨729369, by decide⟩ ⟨13, 2, 0, 729369, 372766, 2673, 16384⟩
    (by decide) selected_cut_28882

theorem selected_cut_28883 : selected 8 ⟨729389, by decide⟩
    (prefixPartial 13 372767) = some ⟨13, 2, 0, 729389, 372767, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_372767_729389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372767 ⟨729389, by decide⟩ :=
  accepted_of_selected 13 372767 ⟨729389, by decide⟩ ⟨13, 2, 0, 729389, 372767, 1093, 16384⟩
    (by decide) selected_cut_28883

theorem unmarked_context_12_93191_729390 : frontier 9 ⟨729390, by decide⟩
    (prefixCache 12 93191) (prefixPartial 12 93191) = false := by
  decide +kernel

theorem node_context_12_93191_729390 : EJMOriginalGlobalDAGData.nodes 9 ⟨729390, by decide⟩ =
    .split (coordinate 12) (![⟨729271, by decide⟩,⟨729326, by decide⟩,⟨729369, by decide⟩,⟨729389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93191_729390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93191 ⟨729390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93191
    ⟨729390, by decide⟩ (by decide) (![⟨729271, by decide⟩,⟨729326, by decide⟩,⟨729369, by decide⟩,⟨729389, by decide⟩]) unmarked_context_12_93191_729390 node_context_12_93191_729390
  intro a
  fin_cases a
  · exact context_13_372764_729271
  · exact context_13_372765_729326
  · exact context_13_372766_729369
  · exact context_13_372767_729389

theorem unmarked_context_11_23297_729391 : frontier 10 ⟨729391, by decide⟩
    (prefixCache 11 23297) (prefixPartial 11 23297) = false := by
  decide +kernel

theorem node_context_11_23297_729391 : EJMOriginalGlobalDAGData.nodes 10 ⟨729391, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨729183, by decide⟩,⟨729390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23297_729391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23297 ⟨729391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23297
    ⟨729391, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨729183, by decide⟩,⟨729390, by decide⟩]) unmarked_context_11_23297_729391 node_context_11_23297_729391
  intro a
  fin_cases a
  · exact context_12_93188_448748
  · exact context_12_93189_34034
  · exact context_12_93190_729183
  · exact context_12_93191_729390

theorem selected_cut_28884 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93192) = some ⟨12, 1, 0, 448748, 93192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93192_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93192 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93192 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93192, 1, 65536⟩
    (by decide) selected_cut_28884

theorem selected_cut_28885 : selected 8 ⟨729497, by decide⟩
    (prefixPartial 13 372772) = some ⟨13, 2, 0, 729497, 372772, 3917, 16384⟩ := by
  decide +kernel

theorem context_13_372772_729497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372772 ⟨729497, by decide⟩ :=
  accepted_of_selected 13 372772 ⟨729497, by decide⟩ ⟨13, 2, 0, 729497, 372772, 3917, 16384⟩
    (by decide) selected_cut_28885

theorem selected_cut_28886 : selected 8 ⟨729568, by decide⟩
    (prefixPartial 13 372773) = some ⟨13, 2, 0, 729568, 372773, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_372773_729568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372773 ⟨729568, by decide⟩ :=
  accepted_of_selected 13 372773 ⟨729568, by decide⟩ ⟨13, 2, 0, 729568, 372773, 2837, 16384⟩
    (by decide) selected_cut_28886

theorem selected_cut_28887 : selected 8 ⟨729659, by decide⟩
    (prefixPartial 13 372774) = some ⟨13, 2, 0, 729659, 372774, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_372774_729659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372774 ⟨729659, by decide⟩ :=
  accepted_of_selected 13 372774 ⟨729659, by decide⟩ ⟨13, 2, 0, 729659, 372774, 3005, 16384⟩
    (by decide) selected_cut_28887

theorem selected_cut_28888 : selected 8 ⟨729689, by decide⟩
    (prefixPartial 13 372775) = some ⟨13, 2, 0, 729689, 372775, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_372775_729689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372775 ⟨729689, by decide⟩ :=
  accepted_of_selected 13 372775 ⟨729689, by decide⟩ ⟨13, 2, 0, 729689, 372775, 1241, 16384⟩
    (by decide) selected_cut_28888

theorem unmarked_context_12_93193_729690 : frontier 9 ⟨729690, by decide⟩
    (prefixCache 12 93193) (prefixPartial 12 93193) = false := by
  decide +kernel

theorem node_context_12_93193_729690 : EJMOriginalGlobalDAGData.nodes 9 ⟨729690, by decide⟩ =
    .split (coordinate 12) (![⟨729497, by decide⟩,⟨729568, by decide⟩,⟨729659, by decide⟩,⟨729689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93193_729690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93193 ⟨729690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93193
    ⟨729690, by decide⟩ (by decide) (![⟨729497, by decide⟩,⟨729568, by decide⟩,⟨729659, by decide⟩,⟨729689, by decide⟩]) unmarked_context_12_93193_729690 node_context_12_93193_729690
  intro a
  fin_cases a
  · exact context_13_372772_729497
  · exact context_13_372773_729568
  · exact context_13_372774_729659
  · exact context_13_372775_729689

theorem selected_cut_28889 : selected 8 ⟨729767, by decide⟩
    (prefixPartial 13 372776) = some ⟨13, 2, 0, 729767, 372776, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_372776_729767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372776 ⟨729767, by decide⟩ :=
  accepted_of_selected 13 372776 ⟨729767, by decide⟩ ⟨13, 2, 0, 729767, 372776, 2933, 16384⟩
    (by decide) selected_cut_28889

theorem selected_cut_28890 : selected 8 ⟨729838, by decide⟩
    (prefixPartial 13 372777) = some ⟨13, 2, 0, 729838, 372777, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_372777_729838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372777 ⟨729838, by decide⟩ :=
  accepted_of_selected 13 372777 ⟨729838, by decide⟩ ⟨13, 2, 0, 729838, 372777, 2997, 16384⟩
    (by decide) selected_cut_28890

theorem selected_cut_28891 : selected 8 ⟨729887, by decide⟩
    (prefixPartial 13 372778) = some ⟨13, 2, 0, 729887, 372778, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_372778_729887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372778 ⟨729887, by decide⟩ :=
  accepted_of_selected 13 372778 ⟨729887, by decide⟩ ⟨13, 2, 0, 729887, 372778, 2461, 16384⟩
    (by decide) selected_cut_28891

theorem selected_cut_28892 : selected 8 ⟨729907, by decide⟩
    (prefixPartial 13 372779) = some ⟨13, 2, 0, 729907, 372779, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_372779_729907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372779 ⟨729907, by decide⟩ :=
  accepted_of_selected 13 372779 ⟨729907, by decide⟩ ⟨13, 2, 0, 729907, 372779, 1225, 16384⟩
    (by decide) selected_cut_28892

theorem unmarked_context_12_93194_729908 : frontier 9 ⟨729908, by decide⟩
    (prefixCache 12 93194) (prefixPartial 12 93194) = false := by
  decide +kernel

theorem node_context_12_93194_729908 : EJMOriginalGlobalDAGData.nodes 9 ⟨729908, by decide⟩ =
    .split (coordinate 12) (![⟨729767, by decide⟩,⟨729838, by decide⟩,⟨729887, by decide⟩,⟨729907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93194_729908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93194 ⟨729908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93194
    ⟨729908, by decide⟩ (by decide) (![⟨729767, by decide⟩,⟨729838, by decide⟩,⟨729887, by decide⟩,⟨729907, by decide⟩]) unmarked_context_12_93194_729908 node_context_12_93194_729908
  intro a
  fin_cases a
  · exact context_13_372776_729767
  · exact context_13_372777_729838
  · exact context_13_372778_729887
  · exact context_13_372779_729907

theorem selected_cut_28893 : selected 8 ⟨729984, by decide⟩
    (prefixPartial 13 372780) = some ⟨13, 2, 0, 729984, 372780, 3541, 16384⟩ := by
  decide +kernel

theorem context_13_372780_729984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372780 ⟨729984, by decide⟩ :=
  accepted_of_selected 13 372780 ⟨729984, by decide⟩ ⟨13, 2, 0, 729984, 372780, 3541, 16384⟩
    (by decide) selected_cut_28893

theorem selected_cut_28894 : selected 8 ⟨730046, by decide⟩
    (prefixPartial 13 372781) = some ⟨13, 2, 0, 730046, 372781, 3121, 16384⟩ := by
  decide +kernel

theorem context_13_372781_730046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372781 ⟨730046, by decide⟩ :=
  accepted_of_selected 13 372781 ⟨730046, by decide⟩ ⟨13, 2, 0, 730046, 372781, 3121, 16384⟩
    (by decide) selected_cut_28894

theorem selected_cut_28895 : selected 8 ⟨730111, by decide⟩
    (prefixPartial 13 372782) = some ⟨13, 2, 0, 730111, 372782, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_372782_730111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372782 ⟨730111, by decide⟩ :=
  accepted_of_selected 13 372782 ⟨730111, by decide⟩ ⟨13, 2, 0, 730111, 372782, 2805, 16384⟩
    (by decide) selected_cut_28895

theorem selected_cut_28896 : selected 8 ⟨730134, by decide⟩
    (prefixPartial 13 372783) = some ⟨13, 2, 0, 730134, 372783, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_372783_730134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372783 ⟨730134, by decide⟩ :=
  accepted_of_selected 13 372783 ⟨730134, by decide⟩ ⟨13, 2, 0, 730134, 372783, 1273, 16384⟩
    (by decide) selected_cut_28896

theorem unmarked_context_12_93195_730135 : frontier 9 ⟨730135, by decide⟩
    (prefixCache 12 93195) (prefixPartial 12 93195) = false := by
  decide +kernel

theorem node_context_12_93195_730135 : EJMOriginalGlobalDAGData.nodes 9 ⟨730135, by decide⟩ =
    .split (coordinate 12) (![⟨729984, by decide⟩,⟨730046, by decide⟩,⟨730111, by decide⟩,⟨730134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93195_730135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93195 ⟨730135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93195
    ⟨730135, by decide⟩ (by decide) (![⟨729984, by decide⟩,⟨730046, by decide⟩,⟨730111, by decide⟩,⟨730134, by decide⟩]) unmarked_context_12_93195_730135 node_context_12_93195_730135
  intro a
  fin_cases a
  · exact context_13_372780_729984
  · exact context_13_372781_730046
  · exact context_13_372782_730111
  · exact context_13_372783_730134

theorem unmarked_context_11_23298_730136 : frontier 10 ⟨730136, by decide⟩
    (prefixCache 11 23298) (prefixPartial 11 23298) = false := by
  decide +kernel

theorem node_context_11_23298_730136 : EJMOriginalGlobalDAGData.nodes 10 ⟨730136, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨729690, by decide⟩,⟨729908, by decide⟩,⟨730135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23298_730136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23298 ⟨730136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23298
    ⟨730136, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨729690, by decide⟩,⟨729908, by decide⟩,⟨730135, by decide⟩]) unmarked_context_11_23298_730136 node_context_11_23298_730136
  intro a
  fin_cases a
  · exact context_12_93192_448748
  · exact context_12_93193_729690
  · exact context_12_93194_729908
  · exact context_12_93195_730135

theorem selected_cut_28897 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93196) = some ⟨12, 1, 0, 448748, 93196, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93196_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93196 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93196 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93196, 1, 65536⟩
    (by decide) selected_cut_28897

theorem selected_cut_28898 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 93197) = some ⟨12, 1, 0, 390434, 93197, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93197_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93197 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 93197 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 93197, 1, 65536⟩
    (by decide) selected_cut_28898

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
