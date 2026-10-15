/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover040
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_17705_125798 : frontier 9 ⟨125798, by decide⟩
    (prefixCache 12 17705) (prefixPartial 12 17705) = false := by
  decide +kernel

theorem node_context_12_17705_125798 : EJMOriginalGlobalDAGData.nodes 9 ⟨125798, by decide⟩ =
    .split (coordinate 12) (![⟨125737, by decide⟩,⟨125764, by decide⟩,⟨125786, by decide⟩,⟨125797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17705_125798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17705 ⟨125798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17705
    ⟨125798, by decide⟩ (by decide) (![⟨125737, by decide⟩,⟨125764, by decide⟩,⟨125786, by decide⟩,⟨125797, by decide⟩]) unmarked_context_12_17705_125798 node_context_12_17705_125798
  intro a
  fin_cases a
  · exact context_13_70820_125737
  · exact context_13_70821_125764
  · exact context_13_70822_125786
  · exact context_13_70823_125797

theorem selected_cut_03939 : selected 8 ⟨125819, by decide⟩
    (prefixPartial 13 70824) = some ⟨13, 2, 0, 125819, 70824, 681, 16384⟩ := by
  decide +kernel

theorem context_13_70824_125819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70824 ⟨125819, by decide⟩ :=
  accepted_of_selected 13 70824 ⟨125819, by decide⟩ ⟨13, 2, 0, 125819, 70824, 681, 16384⟩
    (by decide) selected_cut_03939

theorem selected_cut_03940 : selected 8 ⟨125848, by decide⟩
    (prefixPartial 13 70825) = some ⟨13, 2, 0, 125848, 70825, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_70825_125848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70825 ⟨125848, by decide⟩ :=
  accepted_of_selected 13 70825 ⟨125848, by decide⟩ ⟨13, 2, 0, 125848, 70825, 1785, 16384⟩
    (by decide) selected_cut_03940

theorem selected_cut_03941 : selected 8 ⟨125869, by decide⟩
    (prefixPartial 13 70826) = some ⟨13, 2, 0, 125869, 70826, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_70826_125869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70826 ⟨125869, by decide⟩ :=
  accepted_of_selected 13 70826 ⟨125869, by decide⟩ ⟨13, 2, 0, 125869, 70826, 1269, 16384⟩
    (by decide) selected_cut_03941

theorem selected_cut_03942 : selected 8 ⟨125881, by decide⟩
    (prefixPartial 13 70827) = some ⟨13, 2, 0, 125881, 70827, 733, 16384⟩ := by
  decide +kernel

theorem context_13_70827_125881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70827 ⟨125881, by decide⟩ :=
  accepted_of_selected 13 70827 ⟨125881, by decide⟩ ⟨13, 2, 0, 125881, 70827, 733, 16384⟩
    (by decide) selected_cut_03942

theorem unmarked_context_12_17706_125882 : frontier 9 ⟨125882, by decide⟩
    (prefixCache 12 17706) (prefixPartial 12 17706) = false := by
  decide +kernel

theorem node_context_12_17706_125882 : EJMOriginalGlobalDAGData.nodes 9 ⟨125882, by decide⟩ =
    .split (coordinate 12) (![⟨125819, by decide⟩,⟨125848, by decide⟩,⟨125869, by decide⟩,⟨125881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17706_125882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17706 ⟨125882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17706
    ⟨125882, by decide⟩ (by decide) (![⟨125819, by decide⟩,⟨125848, by decide⟩,⟨125869, by decide⟩,⟨125881, by decide⟩]) unmarked_context_12_17706_125882 node_context_12_17706_125882
  intro a
  fin_cases a
  · exact context_13_70824_125819
  · exact context_13_70825_125848
  · exact context_13_70826_125869
  · exact context_13_70827_125881

theorem selected_cut_03943 : selected 8 ⟨125899, by decide⟩
    (prefixPartial 13 70828) = some ⟨13, 2, 0, 125899, 70828, 609, 16384⟩ := by
  decide +kernel

theorem context_13_70828_125899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70828 ⟨125899, by decide⟩ :=
  accepted_of_selected 13 70828 ⟨125899, by decide⟩ ⟨13, 2, 0, 125899, 70828, 609, 16384⟩
    (by decide) selected_cut_03943

theorem selected_cut_03944 : selected 8 ⟨125928, by decide⟩
    (prefixPartial 13 70829) = some ⟨13, 2, 0, 125928, 70829, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_70829_125928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70829 ⟨125928, by decide⟩ :=
  accepted_of_selected 13 70829 ⟨125928, by decide⟩ ⟨13, 2, 0, 125928, 70829, 2045, 16384⟩
    (by decide) selected_cut_03944

theorem selected_cut_03945 : selected 8 ⟨125951, by decide⟩
    (prefixPartial 13 70830) = some ⟨13, 2, 0, 125951, 70830, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_70830_125951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70830 ⟨125951, by decide⟩ :=
  accepted_of_selected 13 70830 ⟨125951, by decide⟩ ⟨13, 2, 0, 125951, 70830, 1361, 16384⟩
    (by decide) selected_cut_03945

theorem selected_cut_03946 : selected 8 ⟨125963, by decide⟩
    (prefixPartial 13 70831) = some ⟨13, 2, 0, 125963, 70831, 821, 16384⟩ := by
  decide +kernel

theorem context_13_70831_125963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70831 ⟨125963, by decide⟩ :=
  accepted_of_selected 13 70831 ⟨125963, by decide⟩ ⟨13, 2, 0, 125963, 70831, 821, 16384⟩
    (by decide) selected_cut_03946

theorem unmarked_context_12_17707_125964 : frontier 9 ⟨125964, by decide⟩
    (prefixCache 12 17707) (prefixPartial 12 17707) = false := by
  decide +kernel

theorem node_context_12_17707_125964 : EJMOriginalGlobalDAGData.nodes 9 ⟨125964, by decide⟩ =
    .split (coordinate 12) (![⟨125899, by decide⟩,⟨125928, by decide⟩,⟨125951, by decide⟩,⟨125963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17707_125964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17707 ⟨125964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17707
    ⟨125964, by decide⟩ (by decide) (![⟨125899, by decide⟩,⟨125928, by decide⟩,⟨125951, by decide⟩,⟨125963, by decide⟩]) unmarked_context_12_17707_125964 node_context_12_17707_125964
  intro a
  fin_cases a
  · exact context_13_70828_125899
  · exact context_13_70829_125928
  · exact context_13_70830_125951
  · exact context_13_70831_125963

theorem unmarked_context_11_4426_125965 : frontier 10 ⟨125965, by decide⟩
    (prefixCache 11 4426) (prefixPartial 11 4426) = false := by
  decide +kernel

theorem node_context_11_4426_125965 : EJMOriginalGlobalDAGData.nodes 10 ⟨125965, by decide⟩ =
    .split (coordinate 11) (![⟨125721, by decide⟩,⟨125798, by decide⟩,⟨125882, by decide⟩,⟨125964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4426_125965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4426 ⟨125965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4426
    ⟨125965, by decide⟩ (by decide) (![⟨125721, by decide⟩,⟨125798, by decide⟩,⟨125882, by decide⟩,⟨125964, by decide⟩]) unmarked_context_11_4426_125965 node_context_11_4426_125965
  intro a
  fin_cases a
  · exact context_12_17704_125721
  · exact context_12_17705_125798
  · exact context_12_17706_125882
  · exact context_12_17707_125964

theorem selected_cut_03947 : selected 8 ⟨125976, by decide⟩
    (prefixPartial 13 70832) = some ⟨13, 2, 0, 125976, 70832, 385, 16384⟩ := by
  decide +kernel

theorem context_13_70832_125976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70832 ⟨125976, by decide⟩ :=
  accepted_of_selected 13 70832 ⟨125976, by decide⟩ ⟨13, 2, 0, 125976, 70832, 385, 16384⟩
    (by decide) selected_cut_03947

theorem selected_cut_03948 : selected 8 ⟨125998, by decide⟩
    (prefixPartial 13 70833) = some ⟨13, 2, 0, 125998, 70833, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_70833_125998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70833 ⟨125998, by decide⟩ :=
  accepted_of_selected 13 70833 ⟨125998, by decide⟩ ⟨13, 2, 0, 125998, 70833, 1893, 16384⟩
    (by decide) selected_cut_03948

theorem selected_cut_03949 : selected 8 ⟨126020, by decide⟩
    (prefixPartial 13 70834) = some ⟨13, 2, 0, 126020, 70834, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_70834_126020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70834 ⟨126020, by decide⟩ :=
  accepted_of_selected 13 70834 ⟨126020, by decide⟩ ⟨13, 2, 0, 126020, 70834, 1445, 16384⟩
    (by decide) selected_cut_03949

theorem selected_cut_03950 : selected 8 ⟨126028, by decide⟩
    (prefixPartial 13 70835) = some ⟨13, 2, 0, 126028, 70835, 809, 16384⟩ := by
  decide +kernel

theorem context_13_70835_126028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70835 ⟨126028, by decide⟩ :=
  accepted_of_selected 13 70835 ⟨126028, by decide⟩ ⟨13, 2, 0, 126028, 70835, 809, 16384⟩
    (by decide) selected_cut_03950

theorem unmarked_context_12_17708_126029 : frontier 9 ⟨126029, by decide⟩
    (prefixCache 12 17708) (prefixPartial 12 17708) = false := by
  decide +kernel

theorem node_context_12_17708_126029 : EJMOriginalGlobalDAGData.nodes 9 ⟨126029, by decide⟩ =
    .split (coordinate 12) (![⟨125976, by decide⟩,⟨125998, by decide⟩,⟨126020, by decide⟩,⟨126028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17708_126029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17708 ⟨126029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17708
    ⟨126029, by decide⟩ (by decide) (![⟨125976, by decide⟩,⟨125998, by decide⟩,⟨126020, by decide⟩,⟨126028, by decide⟩]) unmarked_context_12_17708_126029 node_context_12_17708_126029
  intro a
  fin_cases a
  · exact context_13_70832_125976
  · exact context_13_70833_125998
  · exact context_13_70834_126020
  · exact context_13_70835_126028

theorem selected_cut_03951 : selected 8 ⟨126040, by decide⟩
    (prefixPartial 13 70836) = some ⟨13, 2, 0, 126040, 70836, 357, 16384⟩ := by
  decide +kernel

theorem context_13_70836_126040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70836 ⟨126040, by decide⟩ :=
  accepted_of_selected 13 70836 ⟨126040, by decide⟩ ⟨13, 2, 0, 126040, 70836, 357, 16384⟩
    (by decide) selected_cut_03951

theorem selected_cut_03952 : selected 8 ⟨126065, by decide⟩
    (prefixPartial 13 70837) = some ⟨13, 2, 0, 126065, 70837, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_70837_126065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70837 ⟨126065, by decide⟩ :=
  accepted_of_selected 13 70837 ⟨126065, by decide⟩ ⟨13, 2, 0, 126065, 70837, 1741, 16384⟩
    (by decide) selected_cut_03952

theorem selected_cut_03953 : selected 8 ⟨126084, by decide⟩
    (prefixPartial 13 70838) = some ⟨13, 2, 0, 126084, 70838, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_70838_126084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70838 ⟨126084, by decide⟩ :=
  accepted_of_selected 13 70838 ⟨126084, by decide⟩ ⟨13, 2, 0, 126084, 70838, 1329, 16384⟩
    (by decide) selected_cut_03953

theorem selected_cut_03954 : selected 8 ⟨126093, by decide⟩
    (prefixPartial 13 70839) = some ⟨13, 2, 0, 126093, 70839, 733, 16384⟩ := by
  decide +kernel

theorem context_13_70839_126093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70839 ⟨126093, by decide⟩ :=
  accepted_of_selected 13 70839 ⟨126093, by decide⟩ ⟨13, 2, 0, 126093, 70839, 733, 16384⟩
    (by decide) selected_cut_03954

theorem unmarked_context_12_17709_126094 : frontier 9 ⟨126094, by decide⟩
    (prefixCache 12 17709) (prefixPartial 12 17709) = false := by
  decide +kernel

theorem node_context_12_17709_126094 : EJMOriginalGlobalDAGData.nodes 9 ⟨126094, by decide⟩ =
    .split (coordinate 12) (![⟨126040, by decide⟩,⟨126065, by decide⟩,⟨126084, by decide⟩,⟨126093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17709_126094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17709 ⟨126094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17709
    ⟨126094, by decide⟩ (by decide) (![⟨126040, by decide⟩,⟨126065, by decide⟩,⟨126084, by decide⟩,⟨126093, by decide⟩]) unmarked_context_12_17709_126094 node_context_12_17709_126094
  intro a
  fin_cases a
  · exact context_13_70836_126040
  · exact context_13_70837_126065
  · exact context_13_70838_126084
  · exact context_13_70839_126093

theorem selected_cut_03955 : selected 8 ⟨126105, by decide⟩
    (prefixPartial 13 70840) = some ⟨13, 2, 0, 126105, 70840, 309, 16384⟩ := by
  decide +kernel

theorem context_13_70840_126105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70840 ⟨126105, by decide⟩ :=
  accepted_of_selected 13 70840 ⟨126105, by decide⟩ ⟨13, 2, 0, 126105, 70840, 309, 16384⟩
    (by decide) selected_cut_03955

theorem selected_cut_03956 : selected 8 ⟨126148, by decide⟩
    (prefixPartial 13 70841) = some ⟨13, 2, 0, 126148, 70841, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_70841_126148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70841 ⟨126148, by decide⟩ :=
  accepted_of_selected 13 70841 ⟨126148, by decide⟩ ⟨13, 2, 0, 126148, 70841, 2185, 16384⟩
    (by decide) selected_cut_03956

theorem selected_cut_03957 : selected 8 ⟨126173, by decide⟩
    (prefixPartial 13 70842) = some ⟨13, 2, 0, 126173, 70842, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_70842_126173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70842 ⟨126173, by decide⟩ :=
  accepted_of_selected 13 70842 ⟨126173, by decide⟩ ⟨13, 2, 0, 126173, 70842, 1425, 16384⟩
    (by decide) selected_cut_03957

theorem selected_cut_03958 : selected 8 ⟨126181, by decide⟩
    (prefixPartial 13 70843) = some ⟨13, 2, 0, 126181, 70843, 781, 16384⟩ := by
  decide +kernel

theorem context_13_70843_126181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70843 ⟨126181, by decide⟩ :=
  accepted_of_selected 13 70843 ⟨126181, by decide⟩ ⟨13, 2, 0, 126181, 70843, 781, 16384⟩
    (by decide) selected_cut_03958

theorem unmarked_context_12_17710_126182 : frontier 9 ⟨126182, by decide⟩
    (prefixCache 12 17710) (prefixPartial 12 17710) = false := by
  decide +kernel

theorem node_context_12_17710_126182 : EJMOriginalGlobalDAGData.nodes 9 ⟨126182, by decide⟩ =
    .split (coordinate 12) (![⟨126105, by decide⟩,⟨126148, by decide⟩,⟨126173, by decide⟩,⟨126181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17710_126182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17710 ⟨126182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17710
    ⟨126182, by decide⟩ (by decide) (![⟨126105, by decide⟩,⟨126148, by decide⟩,⟨126173, by decide⟩,⟨126181, by decide⟩]) unmarked_context_12_17710_126182 node_context_12_17710_126182
  intro a
  fin_cases a
  · exact context_13_70840_126105
  · exact context_13_70841_126148
  · exact context_13_70842_126173
  · exact context_13_70843_126181

theorem selected_cut_03959 : selected 9 ⟨126239, by decide⟩
    (prefixPartial 12 17711) = some ⟨12, 2, 0, 126239, 17711, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_17711_126239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17711 ⟨126239, by decide⟩ :=
  accepted_of_selected 12 17711 ⟨126239, by decide⟩ ⟨12, 2, 0, 126239, 17711, 3701, 65536⟩
    (by decide) selected_cut_03959

theorem unmarked_context_11_4427_126240 : frontier 10 ⟨126240, by decide⟩
    (prefixCache 11 4427) (prefixPartial 11 4427) = false := by
  decide +kernel

theorem node_context_11_4427_126240 : EJMOriginalGlobalDAGData.nodes 10 ⟨126240, by decide⟩ =
    .split (coordinate 11) (![⟨126029, by decide⟩,⟨126094, by decide⟩,⟨126182, by decide⟩,⟨126239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4427_126240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4427 ⟨126240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4427
    ⟨126240, by decide⟩ (by decide) (![⟨126029, by decide⟩,⟨126094, by decide⟩,⟨126182, by decide⟩,⟨126239, by decide⟩]) unmarked_context_11_4427_126240 node_context_11_4427_126240
  intro a
  fin_cases a
  · exact context_12_17708_126029
  · exact context_12_17709_126094
  · exact context_12_17710_126182
  · exact context_12_17711_126239

theorem unmarked_context_10_1106_126241 : frontier 11 ⟨126241, by decide⟩
    (prefixCache 10 1106) (prefixPartial 10 1106) = false := by
  decide +kernel

theorem node_context_10_1106_126241 : EJMOriginalGlobalDAGData.nodes 11 ⟨126241, by decide⟩ =
    .split (coordinate 10) (![⟨125306, by decide⟩,⟨125652, by decide⟩,⟨125965, by decide⟩,⟨126240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1106_126241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1106 ⟨126241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1106
    ⟨126241, by decide⟩ (by decide) (![⟨125306, by decide⟩,⟨125652, by decide⟩,⟨125965, by decide⟩,⟨126240, by decide⟩]) unmarked_context_10_1106_126241 node_context_10_1106_126241
  intro a
  fin_cases a
  · exact context_11_4424_125306
  · exact context_11_4425_125652
  · exact context_11_4426_125965
  · exact context_11_4427_126240

theorem selected_cut_03960 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1107) = some ⟨10, 1, 0, 3440, 1107, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1107_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1107 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1107 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1107, 1, 1048576⟩
    (by decide) selected_cut_03960

theorem unmarked_context_9_276_126242 : frontier 12 ⟨126242, by decide⟩
    (prefixCache 9 276) (prefixPartial 9 276) = false := by
  decide +kernel

theorem node_context_9_276_126242 : EJMOriginalGlobalDAGData.nodes 12 ⟨126242, by decide⟩ =
    .split (coordinate 9) (![⟨123992, by decide⟩,⟨124888, by decide⟩,⟨126241, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_276_126242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 276 ⟨126242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 276
    ⟨126242, by decide⟩ (by decide) (![⟨123992, by decide⟩,⟨124888, by decide⟩,⟨126241, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_276_126242 node_context_9_276_126242
  intro a
  fin_cases a
  · exact context_10_1104_123992
  · exact context_10_1105_124888
  · exact context_10_1106_126241
  · exact context_10_1107_3440

theorem selected_cut_03961 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1108) = some ⟨10, 1, 0, 3442, 1108, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1108_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1108 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1108 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1108, 1, 1048576⟩
    (by decide) selected_cut_03961

theorem selected_cut_03962 : selected 9 ⟨126270, by decide⟩
    (prefixPartial 12 17744) = some ⟨12, 2, 0, 126270, 17744, 993, 65536⟩ := by
  decide +kernel

theorem context_12_17744_126270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17744 ⟨126270, by decide⟩ :=
  accepted_of_selected 12 17744 ⟨126270, by decide⟩ ⟨12, 2, 0, 126270, 17744, 993, 65536⟩
    (by decide) selected_cut_03962

theorem selected_cut_03963 : selected 9 ⟨126308, by decide⟩
    (prefixPartial 12 17745) = some ⟨12, 2, 0, 126308, 17745, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_17745_126308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17745 ⟨126308, by decide⟩ :=
  accepted_of_selected 12 17745 ⟨126308, by decide⟩ ⟨12, 2, 0, 126308, 17745, 1829, 65536⟩
    (by decide) selected_cut_03963

theorem selected_cut_03964 : selected 9 ⟨126369, by decide⟩
    (prefixPartial 12 17746) = some ⟨12, 2, 0, 126369, 17746, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_17746_126369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17746 ⟨126369, by decide⟩ :=
  accepted_of_selected 12 17746 ⟨126369, by decide⟩ ⟨12, 2, 0, 126369, 17746, 3081, 65536⟩
    (by decide) selected_cut_03964

theorem selected_cut_03965 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17747) = some ⟨12, 1, 0, 893, 17747, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17747_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17747 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17747 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17747, 1, 65536⟩
    (by decide) selected_cut_03965

theorem unmarked_context_11_4436_126370 : frontier 10 ⟨126370, by decide⟩
    (prefixCache 11 4436) (prefixPartial 11 4436) = false := by
  decide +kernel

theorem node_context_11_4436_126370 : EJMOriginalGlobalDAGData.nodes 10 ⟨126370, by decide⟩ =
    .split (coordinate 11) (![⟨126270, by decide⟩,⟨126308, by decide⟩,⟨126369, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4436_126370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4436 ⟨126370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4436
    ⟨126370, by decide⟩ (by decide) (![⟨126270, by decide⟩,⟨126308, by decide⟩,⟨126369, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4436_126370 node_context_11_4436_126370
  intro a
  fin_cases a
  · exact context_12_17744_126270
  · exact context_12_17745_126308
  · exact context_12_17746_126369
  · exact context_12_17747_893

theorem selected_cut_03966 : selected 10 ⟨126444, by decide⟩
    (prefixPartial 11 4437) = some ⟨11, 2, 0, 126444, 4437, 3361, 262144⟩ := by
  decide +kernel

theorem context_11_4437_126444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4437 ⟨126444, by decide⟩ :=
  accepted_of_selected 11 4437 ⟨126444, by decide⟩ ⟨11, 2, 0, 126444, 4437, 3361, 262144⟩
    (by decide) selected_cut_03966

theorem selected_cut_03967 : selected 10 ⟨126577, by decide⟩
    (prefixPartial 11 4438) = some ⟨11, 2, 0, 126577, 4438, 3373, 262144⟩ := by
  decide +kernel

theorem context_11_4438_126577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4438 ⟨126577, by decide⟩ :=
  accepted_of_selected 11 4438 ⟨126577, by decide⟩ ⟨11, 2, 0, 126577, 4438, 3373, 262144⟩
    (by decide) selected_cut_03967

theorem selected_cut_03968 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 4439) = some ⟨11, 1, 0, 1736, 4439, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4439_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4439 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 4439 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 4439, 1, 262144⟩
    (by decide) selected_cut_03968

theorem unmarked_context_10_1109_126578 : frontier 11 ⟨126578, by decide⟩
    (prefixCache 10 1109) (prefixPartial 10 1109) = false := by
  decide +kernel

theorem node_context_10_1109_126578 : EJMOriginalGlobalDAGData.nodes 11 ⟨126578, by decide⟩ =
    .split (coordinate 10) (![⟨126370, by decide⟩,⟨126444, by decide⟩,⟨126577, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1109_126578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1109 ⟨126578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1109
    ⟨126578, by decide⟩ (by decide) (![⟨126370, by decide⟩,⟨126444, by decide⟩,⟨126577, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1109_126578 node_context_10_1109_126578
  intro a
  fin_cases a
  · exact context_11_4436_126370
  · exact context_11_4437_126444
  · exact context_11_4438_126577
  · exact context_11_4439_1736

theorem selected_cut_03969 : selected 9 ⟨126630, by decide⟩
    (prefixPartial 12 17760) = some ⟨12, 2, 0, 126630, 17760, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_17760_126630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17760 ⟨126630, by decide⟩ :=
  accepted_of_selected 12 17760 ⟨126630, by decide⟩ ⟨12, 2, 0, 126630, 17760, 3161, 65536⟩
    (by decide) selected_cut_03969

theorem selected_cut_03970 : selected 9 ⟨126704, by decide⟩
    (prefixPartial 12 17761) = some ⟨12, 2, 0, 126704, 17761, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_17761_126704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17761 ⟨126704, by decide⟩ :=
  accepted_of_selected 12 17761 ⟨126704, by decide⟩ ⟨12, 2, 0, 126704, 17761, 3585, 65536⟩
    (by decide) selected_cut_03970

theorem selected_cut_03971 : selected 9 ⟨126777, by decide⟩
    (prefixPartial 12 17762) = some ⟨12, 2, 0, 126777, 17762, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_17762_126777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17762 ⟨126777, by decide⟩ :=
  accepted_of_selected 12 17762 ⟨126777, by decide⟩ ⟨12, 2, 0, 126777, 17762, 2881, 65536⟩
    (by decide) selected_cut_03971

theorem selected_cut_03972 : selected 9 ⟨126834, by decide⟩
    (prefixPartial 12 17763) = some ⟨12, 2, 0, 126834, 17763, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_17763_126834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17763 ⟨126834, by decide⟩ :=
  accepted_of_selected 12 17763 ⟨126834, by decide⟩ ⟨12, 2, 0, 126834, 17763, 2785, 65536⟩
    (by decide) selected_cut_03972

theorem unmarked_context_11_4440_126835 : frontier 10 ⟨126835, by decide⟩
    (prefixCache 11 4440) (prefixPartial 11 4440) = false := by
  decide +kernel

theorem node_context_11_4440_126835 : EJMOriginalGlobalDAGData.nodes 10 ⟨126835, by decide⟩ =
    .split (coordinate 11) (![⟨126630, by decide⟩,⟨126704, by decide⟩,⟨126777, by decide⟩,⟨126834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4440_126835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4440 ⟨126835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4440
    ⟨126835, by decide⟩ (by decide) (![⟨126630, by decide⟩,⟨126704, by decide⟩,⟨126777, by decide⟩,⟨126834, by decide⟩]) unmarked_context_11_4440_126835 node_context_11_4440_126835
  intro a
  fin_cases a
  · exact context_12_17760_126630
  · exact context_12_17761_126704
  · exact context_12_17762_126777
  · exact context_12_17763_126834

theorem selected_cut_03973 : selected 9 ⟨126883, by decide⟩
    (prefixPartial 12 17764) = some ⟨12, 2, 0, 126883, 17764, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_17764_126883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17764 ⟨126883, by decide⟩ :=
  accepted_of_selected 12 17764 ⟨126883, by decide⟩ ⟨12, 2, 0, 126883, 17764, 2297, 65536⟩
    (by decide) selected_cut_03973

theorem selected_cut_03974 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 17765) = some ⟨12, 1, 0, 126884, 17765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17765_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17765 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 17765 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 17765, 1, 65536⟩
    (by decide) selected_cut_03974

theorem selected_cut_03975 : selected 9 ⟨126936, by decide⟩
    (prefixPartial 12 17766) = some ⟨12, 2, 0, 126936, 17766, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_17766_126936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17766 ⟨126936, by decide⟩ :=
  accepted_of_selected 12 17766 ⟨126936, by decide⟩ ⟨12, 2, 0, 126936, 17766, 2281, 65536⟩
    (by decide) selected_cut_03975

theorem selected_cut_03976 : selected 9 ⟨126984, by decide⟩
    (prefixPartial 12 17767) = some ⟨12, 2, 0, 126984, 17767, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_17767_126984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17767 ⟨126984, by decide⟩ :=
  accepted_of_selected 12 17767 ⟨126984, by decide⟩ ⟨12, 2, 0, 126984, 17767, 2237, 65536⟩
    (by decide) selected_cut_03976

theorem unmarked_context_11_4441_126985 : frontier 10 ⟨126985, by decide⟩
    (prefixCache 11 4441) (prefixPartial 11 4441) = false := by
  decide +kernel

theorem node_context_11_4441_126985 : EJMOriginalGlobalDAGData.nodes 10 ⟨126985, by decide⟩ =
    .split (coordinate 11) (![⟨126883, by decide⟩,⟨126884, by decide⟩,⟨126936, by decide⟩,⟨126984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4441_126985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4441 ⟨126985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4441
    ⟨126985, by decide⟩ (by decide) (![⟨126883, by decide⟩,⟨126884, by decide⟩,⟨126936, by decide⟩,⟨126984, by decide⟩]) unmarked_context_11_4441_126985 node_context_11_4441_126985
  intro a
  fin_cases a
  · exact context_12_17764_126883
  · exact context_12_17765_126884
  · exact context_12_17766_126936
  · exact context_12_17767_126984

theorem selected_cut_03977 : selected 9 ⟨127029, by decide⟩
    (prefixPartial 12 17768) = some ⟨12, 2, 0, 127029, 17768, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_17768_127029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17768 ⟨127029, by decide⟩ :=
  accepted_of_selected 12 17768 ⟨127029, by decide⟩ ⟨12, 2, 0, 127029, 17768, 2385, 65536⟩
    (by decide) selected_cut_03977

theorem selected_cut_03978 : selected 9 ⟨127098, by decide⟩
    (prefixPartial 12 17769) = some ⟨12, 2, 0, 127098, 17769, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_17769_127098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17769 ⟨127098, by decide⟩ :=
  accepted_of_selected 12 17769 ⟨127098, by decide⟩ ⟨12, 2, 0, 127098, 17769, 2693, 65536⟩
    (by decide) selected_cut_03978

theorem selected_cut_03979 : selected 9 ⟨127141, by decide⟩
    (prefixPartial 12 17770) = some ⟨12, 2, 0, 127141, 17770, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_17770_127141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17770 ⟨127141, by decide⟩ :=
  accepted_of_selected 12 17770 ⟨127141, by decide⟩ ⟨12, 2, 0, 127141, 17770, 1929, 65536⟩
    (by decide) selected_cut_03979

theorem selected_cut_03980 : selected 9 ⟨127184, by decide⟩
    (prefixPartial 12 17771) = some ⟨12, 2, 0, 127184, 17771, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_17771_127184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17771 ⟨127184, by decide⟩ :=
  accepted_of_selected 12 17771 ⟨127184, by decide⟩ ⟨12, 2, 0, 127184, 17771, 2077, 65536⟩
    (by decide) selected_cut_03980

theorem unmarked_context_11_4442_127185 : frontier 10 ⟨127185, by decide⟩
    (prefixCache 11 4442) (prefixPartial 11 4442) = false := by
  decide +kernel

theorem node_context_11_4442_127185 : EJMOriginalGlobalDAGData.nodes 10 ⟨127185, by decide⟩ =
    .split (coordinate 11) (![⟨127029, by decide⟩,⟨127098, by decide⟩,⟨127141, by decide⟩,⟨127184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4442_127185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4442 ⟨127185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4442
    ⟨127185, by decide⟩ (by decide) (![⟨127029, by decide⟩,⟨127098, by decide⟩,⟨127141, by decide⟩,⟨127184, by decide⟩]) unmarked_context_11_4442_127185 node_context_11_4442_127185
  intro a
  fin_cases a
  · exact context_12_17768_127029
  · exact context_12_17769_127098
  · exact context_12_17770_127141
  · exact context_12_17771_127184

theorem selected_cut_03981 : selected 9 ⟨127221, by decide⟩
    (prefixPartial 12 17772) = some ⟨12, 2, 0, 127221, 17772, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_17772_127221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17772 ⟨127221, by decide⟩ :=
  accepted_of_selected 12 17772 ⟨127221, by decide⟩ ⟨12, 2, 0, 127221, 17772, 1905, 65536⟩
    (by decide) selected_cut_03981

theorem selected_cut_03982 : selected 9 ⟨127274, by decide⟩
    (prefixPartial 12 17773) = some ⟨12, 2, 0, 127274, 17773, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_17773_127274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17773 ⟨127274, by decide⟩ :=
  accepted_of_selected 12 17773 ⟨127274, by decide⟩ ⟨12, 2, 0, 127274, 17773, 2129, 65536⟩
    (by decide) selected_cut_03982

theorem selected_cut_03983 : selected 9 ⟨127308, by decide⟩
    (prefixPartial 12 17774) = some ⟨12, 2, 0, 127308, 17774, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_17774_127308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17774 ⟨127308, by decide⟩ :=
  accepted_of_selected 12 17774 ⟨127308, by decide⟩ ⟨12, 2, 0, 127308, 17774, 1669, 65536⟩
    (by decide) selected_cut_03983

theorem selected_cut_03984 : selected 9 ⟨127333, by decide⟩
    (prefixPartial 12 17775) = some ⟨12, 2, 0, 127333, 17775, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_17775_127333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17775 ⟨127333, by decide⟩ :=
  accepted_of_selected 12 17775 ⟨127333, by decide⟩ ⟨12, 2, 0, 127333, 17775, 1517, 65536⟩
    (by decide) selected_cut_03984

theorem unmarked_context_11_4443_127334 : frontier 10 ⟨127334, by decide⟩
    (prefixCache 11 4443) (prefixPartial 11 4443) = false := by
  decide +kernel

theorem node_context_11_4443_127334 : EJMOriginalGlobalDAGData.nodes 10 ⟨127334, by decide⟩ =
    .split (coordinate 11) (![⟨127221, by decide⟩,⟨127274, by decide⟩,⟨127308, by decide⟩,⟨127333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4443_127334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4443 ⟨127334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4443
    ⟨127334, by decide⟩ (by decide) (![⟨127221, by decide⟩,⟨127274, by decide⟩,⟨127308, by decide⟩,⟨127333, by decide⟩]) unmarked_context_11_4443_127334 node_context_11_4443_127334
  intro a
  fin_cases a
  · exact context_12_17772_127221
  · exact context_12_17773_127274
  · exact context_12_17774_127308
  · exact context_12_17775_127333

theorem unmarked_context_10_1110_127335 : frontier 11 ⟨127335, by decide⟩
    (prefixCache 10 1110) (prefixPartial 10 1110) = false := by
  decide +kernel

theorem node_context_10_1110_127335 : EJMOriginalGlobalDAGData.nodes 11 ⟨127335, by decide⟩ =
    .split (coordinate 10) (![⟨126835, by decide⟩,⟨126985, by decide⟩,⟨127185, by decide⟩,⟨127334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1110_127335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1110 ⟨127335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1110
    ⟨127335, by decide⟩ (by decide) (![⟨126835, by decide⟩,⟨126985, by decide⟩,⟨127185, by decide⟩,⟨127334, by decide⟩]) unmarked_context_10_1110_127335 node_context_10_1110_127335
  intro a
  fin_cases a
  · exact context_11_4440_126835
  · exact context_11_4441_126985
  · exact context_11_4442_127185
  · exact context_11_4443_127334

theorem selected_cut_03985 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1111) = some ⟨10, 1, 0, 3440, 1111, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1111_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1111 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1111 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1111, 1, 1048576⟩
    (by decide) selected_cut_03985

theorem unmarked_context_9_277_127336 : frontier 12 ⟨127336, by decide⟩
    (prefixCache 9 277) (prefixPartial 9 277) = false := by
  decide +kernel

theorem node_context_9_277_127336 : EJMOriginalGlobalDAGData.nodes 12 ⟨127336, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨126578, by decide⟩,⟨127335, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_277_127336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 277 ⟨127336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 277
    ⟨127336, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨126578, by decide⟩,⟨127335, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_277_127336 node_context_9_277_127336
  intro a
  fin_cases a
  · exact context_10_1108_3442
  · exact context_10_1109_126578
  · exact context_10_1110_127335
  · exact context_10_1111_3440

theorem selected_cut_03986 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1112) = some ⟨10, 1, 0, 3442, 1112, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1112_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1112 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1112 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1112, 1, 1048576⟩
    (by decide) selected_cut_03986

theorem selected_cut_03987 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1113) = some ⟨10, 1, 0, 3442, 1113, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1113_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1113 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1113 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1113, 1, 1048576⟩
    (by decide) selected_cut_03987

theorem selected_cut_03988 : selected 9 ⟨127354, by decide⟩
    (prefixPartial 12 17824) = some ⟨12, 2, 0, 127354, 17824, 757, 65536⟩ := by
  decide +kernel

theorem context_12_17824_127354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17824 ⟨127354, by decide⟩ :=
  accepted_of_selected 12 17824 ⟨127354, by decide⟩ ⟨12, 2, 0, 127354, 17824, 757, 65536⟩
    (by decide) selected_cut_03988

theorem selected_cut_03989 : selected 9 ⟨127367, by decide⟩
    (prefixPartial 12 17825) = some ⟨12, 2, 0, 127367, 17825, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_17825_127367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17825 ⟨127367, by decide⟩ :=
  accepted_of_selected 12 17825 ⟨127367, by decide⟩ ⟨12, 2, 0, 127367, 17825, 1201, 65536⟩
    (by decide) selected_cut_03989

theorem selected_cut_03990 : selected 9 ⟨127389, by decide⟩
    (prefixPartial 12 17826) = some ⟨12, 2, 0, 127389, 17826, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_17826_127389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17826 ⟨127389, by decide⟩ :=
  accepted_of_selected 12 17826 ⟨127389, by decide⟩ ⟨12, 2, 0, 127389, 17826, 1161, 65536⟩
    (by decide) selected_cut_03990

theorem selected_cut_03991 : selected 9 ⟨127410, by decide⟩
    (prefixPartial 12 17827) = some ⟨12, 2, 0, 127410, 17827, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_17827_127410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17827 ⟨127410, by decide⟩ :=
  accepted_of_selected 12 17827 ⟨127410, by decide⟩ ⟨12, 2, 0, 127410, 17827, 1101, 65536⟩
    (by decide) selected_cut_03991

theorem unmarked_context_11_4456_127411 : frontier 10 ⟨127411, by decide⟩
    (prefixCache 11 4456) (prefixPartial 11 4456) = false := by
  decide +kernel

theorem node_context_11_4456_127411 : EJMOriginalGlobalDAGData.nodes 10 ⟨127411, by decide⟩ =
    .split (coordinate 11) (![⟨127354, by decide⟩,⟨127367, by decide⟩,⟨127389, by decide⟩,⟨127410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4456_127411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4456 ⟨127411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4456
    ⟨127411, by decide⟩ (by decide) (![⟨127354, by decide⟩,⟨127367, by decide⟩,⟨127389, by decide⟩,⟨127410, by decide⟩]) unmarked_context_11_4456_127411 node_context_11_4456_127411
  intro a
  fin_cases a
  · exact context_12_17824_127354
  · exact context_12_17825_127367
  · exact context_12_17826_127389
  · exact context_12_17827_127410

theorem selected_cut_03992 : selected 10 ⟨127475, by decide⟩
    (prefixPartial 11 4457) = some ⟨11, 2, 0, 127475, 4457, 2473, 262144⟩ := by
  decide +kernel

theorem context_11_4457_127475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4457 ⟨127475, by decide⟩ :=
  accepted_of_selected 11 4457 ⟨127475, by decide⟩ ⟨11, 2, 0, 127475, 4457, 2473, 262144⟩
    (by decide) selected_cut_03992

theorem selected_cut_03993 : selected 10 ⟨127504, by decide⟩
    (prefixPartial 11 4458) = some ⟨11, 2, 0, 127504, 4458, 1133, 262144⟩ := by
  decide +kernel

theorem context_11_4458_127504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4458 ⟨127504, by decide⟩ :=
  accepted_of_selected 11 4458 ⟨127504, by decide⟩ ⟨11, 2, 0, 127504, 4458, 1133, 262144⟩
    (by decide) selected_cut_03993

theorem selected_cut_03994 : selected 10 ⟨127512, by decide⟩
    (prefixPartial 11 4459) = some ⟨11, 2, 0, 127512, 4459, 393, 262144⟩ := by
  decide +kernel

theorem context_11_4459_127512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4459 ⟨127512, by decide⟩ :=
  accepted_of_selected 11 4459 ⟨127512, by decide⟩ ⟨11, 2, 0, 127512, 4459, 393, 262144⟩
    (by decide) selected_cut_03994

theorem unmarked_context_10_1114_127513 : frontier 11 ⟨127513, by decide⟩
    (prefixCache 10 1114) (prefixPartial 10 1114) = false := by
  decide +kernel

theorem node_context_10_1114_127513 : EJMOriginalGlobalDAGData.nodes 11 ⟨127513, by decide⟩ =
    .split (coordinate 10) (![⟨127411, by decide⟩,⟨127475, by decide⟩,⟨127504, by decide⟩,⟨127512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1114_127513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1114 ⟨127513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1114
    ⟨127513, by decide⟩ (by decide) (![⟨127411, by decide⟩,⟨127475, by decide⟩,⟨127504, by decide⟩,⟨127512, by decide⟩]) unmarked_context_10_1114_127513 node_context_10_1114_127513
  intro a
  fin_cases a
  · exact context_11_4456_127411
  · exact context_11_4457_127475
  · exact context_11_4458_127504
  · exact context_11_4459_127512

theorem selected_cut_03995 : selected 11 ⟨127624, by decide⟩
    (prefixPartial 10 1115) = some ⟨10, 2, 0, 127624, 1115, 2645, 1048576⟩ := by
  decide +kernel

theorem context_10_1115_127624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1115 ⟨127624, by decide⟩ :=
  accepted_of_selected 10 1115 ⟨127624, by decide⟩ ⟨10, 2, 0, 127624, 1115, 2645, 1048576⟩
    (by decide) selected_cut_03995

theorem unmarked_context_9_278_127625 : frontier 12 ⟨127625, by decide⟩
    (prefixCache 9 278) (prefixPartial 9 278) = false := by
  decide +kernel

theorem node_context_9_278_127625 : EJMOriginalGlobalDAGData.nodes 12 ⟨127625, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨127513, by decide⟩,⟨127624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_278_127625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 278 ⟨127625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 278
    ⟨127625, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨127513, by decide⟩,⟨127624, by decide⟩]) unmarked_context_9_278_127625 node_context_9_278_127625
  intro a
  fin_cases a
  · exact context_10_1112_3442
  · exact context_10_1113_3442
  · exact context_10_1114_127513
  · exact context_10_1115_127624

theorem selected_cut_03996 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 279) = some ⟨9, 1, 0, 4601, 279, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_279_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 279 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 279 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 279, 1, 4194304⟩
    (by decide) selected_cut_03996

theorem unmarked_context_8_69_127626 : frontier 13 ⟨127626, by decide⟩
    (prefixCache 8 69) (prefixPartial 8 69) = false := by
  decide +kernel

theorem node_context_8_69_127626 : EJMOriginalGlobalDAGData.nodes 13 ⟨127626, by decide⟩ =
    .split (coordinate 8) (![⟨126242, by decide⟩,⟨127336, by decide⟩,⟨127625, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_69_127626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 69 ⟨127626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 69
    ⟨127626, by decide⟩ (by decide) (![⟨126242, by decide⟩,⟨127336, by decide⟩,⟨127625, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_69_127626 node_context_8_69_127626
  intro a
  fin_cases a
  · exact context_9_276_126242
  · exact context_9_277_127336
  · exact context_9_278_127625
  · exact context_9_279_4601

theorem selected_cut_03997 : selected 8 ⟨127706, by decide⟩
    (prefixPartial 13 71680) = some ⟨13, 2, 0, 127706, 71680, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_71680_127706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71680 ⟨127706, by decide⟩ :=
  accepted_of_selected 13 71680 ⟨127706, by decide⟩ ⟨13, 2, 0, 127706, 71680, 3097, 16384⟩
    (by decide) selected_cut_03997

theorem selected_cut_03998 : selected 8 ⟨127758, by decide⟩
    (prefixPartial 13 71681) = some ⟨13, 2, 0, 127758, 71681, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_71681_127758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71681 ⟨127758, by decide⟩ :=
  accepted_of_selected 13 71681 ⟨127758, by decide⟩ ⟨13, 2, 0, 127758, 71681, 1789, 16384⟩
    (by decide) selected_cut_03998

theorem selected_cut_03999 : selected 8 ⟨127780, by decide⟩
    (prefixPartial 13 71682) = some ⟨13, 2, 0, 127780, 71682, 625, 16384⟩ := by
  decide +kernel

theorem context_13_71682_127780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71682 ⟨127780, by decide⟩ :=
  accepted_of_selected 13 71682 ⟨127780, by decide⟩ ⟨13, 2, 0, 127780, 71682, 625, 16384⟩
    (by decide) selected_cut_03999

theorem selected_cut_04000 : selected 8 ⟨127782, by decide⟩
    (prefixPartial 13 71683) = some ⟨13, 2, 0, 127782, 71683, 109, 16384⟩ := by
  decide +kernel

theorem context_13_71683_127782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71683 ⟨127782, by decide⟩ :=
  accepted_of_selected 13 71683 ⟨127782, by decide⟩ ⟨13, 2, 0, 127782, 71683, 109, 16384⟩
    (by decide) selected_cut_04000

theorem unmarked_context_12_17920_127783 : frontier 9 ⟨127783, by decide⟩
    (prefixCache 12 17920) (prefixPartial 12 17920) = false := by
  decide +kernel

theorem node_context_12_17920_127783 : EJMOriginalGlobalDAGData.nodes 9 ⟨127783, by decide⟩ =
    .split (coordinate 12) (![⟨127706, by decide⟩,⟨127758, by decide⟩,⟨127780, by decide⟩,⟨127782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17920_127783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17920 ⟨127783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17920
    ⟨127783, by decide⟩ (by decide) (![⟨127706, by decide⟩,⟨127758, by decide⟩,⟨127780, by decide⟩,⟨127782, by decide⟩]) unmarked_context_12_17920_127783 node_context_12_17920_127783
  intro a
  fin_cases a
  · exact context_13_71680_127706
  · exact context_13_71681_127758
  · exact context_13_71682_127780
  · exact context_13_71683_127782

theorem selected_cut_04001 : selected 7 ⟨127801, by decide⟩
    (prefixPartial 14 286736) = some ⟨14, 2, 0, 127801, 286736, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_286736_127801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286736 ⟨127801, by decide⟩ :=
  accepted_of_selected 14 286736 ⟨127801, by decide⟩ ⟨14, 2, 0, 127801, 286736, 1137, 4096⟩
    (by decide) selected_cut_04001

theorem selected_cut_04002 : selected 7 ⟨127820, by decide⟩
    (prefixPartial 14 286737) = some ⟨14, 2, 0, 127820, 286737, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_286737_127820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286737 ⟨127820, by decide⟩ :=
  accepted_of_selected 14 286737 ⟨127820, by decide⟩ ⟨14, 2, 0, 127820, 286737, 1125, 4096⟩
    (by decide) selected_cut_04002

theorem selected_cut_04003 : selected 7 ⟨127830, by decide⟩
    (prefixPartial 14 286738) = some ⟨14, 2, 0, 127830, 286738, 949, 4096⟩ := by
  decide +kernel

theorem context_14_286738_127830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286738 ⟨127830, by decide⟩ :=
  accepted_of_selected 14 286738 ⟨127830, by decide⟩ ⟨14, 2, 0, 127830, 286738, 949, 4096⟩
    (by decide) selected_cut_04003

theorem selected_cut_04004 : selected 7 ⟨127840, by decide⟩
    (prefixPartial 14 286739) = some ⟨14, 2, 0, 127840, 286739, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_286739_127840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286739 ⟨127840, by decide⟩ :=
  accepted_of_selected 14 286739 ⟨127840, by decide⟩ ⟨14, 2, 0, 127840, 286739, 1017, 4096⟩
    (by decide) selected_cut_04004

theorem unmarked_context_13_71684_127841 : frontier 8 ⟨127841, by decide⟩
    (prefixCache 13 71684) (prefixPartial 13 71684) = false := by
  decide +kernel

theorem node_context_13_71684_127841 : EJMOriginalGlobalDAGData.nodes 8 ⟨127841, by decide⟩ =
    .split (coordinate 13) (![⟨127801, by decide⟩,⟨127820, by decide⟩,⟨127830, by decide⟩,⟨127840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_71684_127841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71684 ⟨127841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 71684
    ⟨127841, by decide⟩ (by decide) (![⟨127801, by decide⟩,⟨127820, by decide⟩,⟨127830, by decide⟩,⟨127840, by decide⟩]) unmarked_context_13_71684_127841 node_context_13_71684_127841
  intro a
  fin_cases a
  · exact context_14_286736_127801
  · exact context_14_286737_127820
  · exact context_14_286738_127830
  · exact context_14_286739_127840

theorem selected_cut_04005 : selected 8 ⟨127884, by decide⟩
    (prefixPartial 13 71685) = some ⟨13, 2, 0, 127884, 71685, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_71685_127884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71685 ⟨127884, by decide⟩ :=
  accepted_of_selected 13 71685 ⟨127884, by decide⟩ ⟨13, 2, 0, 127884, 71685, 2893, 16384⟩
    (by decide) selected_cut_04005

theorem selected_cut_04006 : selected 8 ⟨127909, by decide⟩
    (prefixPartial 13 71686) = some ⟨13, 2, 0, 127909, 71686, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_71686_127909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71686 ⟨127909, by decide⟩ :=
  accepted_of_selected 13 71686 ⟨127909, by decide⟩ ⟨13, 2, 0, 127909, 71686, 1677, 16384⟩
    (by decide) selected_cut_04006

theorem selected_cut_04007 : selected 8 ⟨127919, by decide⟩
    (prefixPartial 13 71687) = some ⟨13, 2, 0, 127919, 71687, 985, 16384⟩ := by
  decide +kernel

theorem context_13_71687_127919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71687 ⟨127919, by decide⟩ :=
  accepted_of_selected 13 71687 ⟨127919, by decide⟩ ⟨13, 2, 0, 127919, 71687, 985, 16384⟩
    (by decide) selected_cut_04007

theorem unmarked_context_12_17921_127920 : frontier 9 ⟨127920, by decide⟩
    (prefixCache 12 17921) (prefixPartial 12 17921) = false := by
  decide +kernel

theorem node_context_12_17921_127920 : EJMOriginalGlobalDAGData.nodes 9 ⟨127920, by decide⟩ =
    .split (coordinate 12) (![⟨127841, by decide⟩,⟨127884, by decide⟩,⟨127909, by decide⟩,⟨127919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17921_127920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17921 ⟨127920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17921
    ⟨127920, by decide⟩ (by decide) (![⟨127841, by decide⟩,⟨127884, by decide⟩,⟨127909, by decide⟩,⟨127919, by decide⟩]) unmarked_context_12_17921_127920 node_context_12_17921_127920
  intro a
  fin_cases a
  · exact context_13_71684_127841
  · exact context_13_71685_127884
  · exact context_13_71686_127909
  · exact context_13_71687_127919

theorem selected_cut_04008 : selected 8 ⟨127972, by decide⟩
    (prefixPartial 13 71688) = some ⟨13, 2, 0, 127972, 71688, 3565, 16384⟩ := by
  decide +kernel

theorem context_13_71688_127972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71688 ⟨127972, by decide⟩ :=
  accepted_of_selected 13 71688 ⟨127972, by decide⟩ ⟨13, 2, 0, 127972, 71688, 3565, 16384⟩
    (by decide) selected_cut_04008

theorem selected_cut_04009 : selected 8 ⟨128010, by decide⟩
    (prefixPartial 13 71689) = some ⟨13, 2, 0, 128010, 71689, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_71689_128010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71689 ⟨128010, by decide⟩ :=
  accepted_of_selected 13 71689 ⟨128010, by decide⟩ ⟨13, 2, 0, 128010, 71689, 2829, 16384⟩
    (by decide) selected_cut_04009

theorem selected_cut_04010 : selected 8 ⟨128031, by decide⟩
    (prefixPartial 13 71690) = some ⟨13, 2, 0, 128031, 71690, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_71690_128031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71690 ⟨128031, by decide⟩ :=
  accepted_of_selected 13 71690 ⟨128031, by decide⟩ ⟨13, 2, 0, 128031, 71690, 1421, 16384⟩
    (by decide) selected_cut_04010

theorem selected_cut_04011 : selected 8 ⟨128039, by decide⟩
    (prefixPartial 13 71691) = some ⟨13, 2, 0, 128039, 71691, 941, 16384⟩ := by
  decide +kernel

theorem context_13_71691_128039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71691 ⟨128039, by decide⟩ :=
  accepted_of_selected 13 71691 ⟨128039, by decide⟩ ⟨13, 2, 0, 128039, 71691, 941, 16384⟩
    (by decide) selected_cut_04011

theorem unmarked_context_12_17922_128040 : frontier 9 ⟨128040, by decide⟩
    (prefixCache 12 17922) (prefixPartial 12 17922) = false := by
  decide +kernel

theorem node_context_12_17922_128040 : EJMOriginalGlobalDAGData.nodes 9 ⟨128040, by decide⟩ =
    .split (coordinate 12) (![⟨127972, by decide⟩,⟨128010, by decide⟩,⟨128031, by decide⟩,⟨128039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17922_128040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17922 ⟨128040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17922
    ⟨128040, by decide⟩ (by decide) (![⟨127972, by decide⟩,⟨128010, by decide⟩,⟨128031, by decide⟩,⟨128039, by decide⟩]) unmarked_context_12_17922_128040 node_context_12_17922_128040
  intro a
  fin_cases a
  · exact context_13_71688_127972
  · exact context_13_71689_128010
  · exact context_13_71690_128031
  · exact context_13_71691_128039

theorem selected_cut_04012 : selected 7 ⟨128053, by decide⟩
    (prefixPartial 14 286768) = some ⟨14, 2, 0, 128053, 286768, 989, 4096⟩ := by
  decide +kernel

theorem context_14_286768_128053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286768 ⟨128053, by decide⟩ :=
  accepted_of_selected 14 286768 ⟨128053, by decide⟩ ⟨14, 2, 0, 128053, 286768, 989, 4096⟩
    (by decide) selected_cut_04012

theorem selected_cut_04013 : selected 7 ⟨128073, by decide⟩
    (prefixPartial 14 286769) = some ⟨14, 2, 0, 128073, 286769, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_286769_128073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286769 ⟨128073, by decide⟩ :=
  accepted_of_selected 14 286769 ⟨128073, by decide⟩ ⟨14, 2, 0, 128073, 286769, 1145, 4096⟩
    (by decide) selected_cut_04013

theorem selected_cut_04014 : selected 7 ⟨128087, by decide⟩
    (prefixPartial 14 286770) = some ⟨14, 2, 0, 128087, 286770, 977, 4096⟩ := by
  decide +kernel

theorem context_14_286770_128087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286770 ⟨128087, by decide⟩ :=
  accepted_of_selected 14 286770 ⟨128087, by decide⟩ ⟨14, 2, 0, 128087, 286770, 977, 4096⟩
    (by decide) selected_cut_04014

theorem selected_cut_04015 : selected 7 ⟨128094, by decide⟩
    (prefixPartial 14 286771) = some ⟨14, 2, 0, 128094, 286771, 1013, 4096⟩ := by
  decide +kernel

theorem context_14_286771_128094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 286771 ⟨128094, by decide⟩ :=
  accepted_of_selected 14 286771 ⟨128094, by decide⟩ ⟨14, 2, 0, 128094, 286771, 1013, 4096⟩
    (by decide) selected_cut_04015

theorem unmarked_context_13_71692_128095 : frontier 8 ⟨128095, by decide⟩
    (prefixCache 13 71692) (prefixPartial 13 71692) = false := by
  decide +kernel

theorem node_context_13_71692_128095 : EJMOriginalGlobalDAGData.nodes 8 ⟨128095, by decide⟩ =
    .split (coordinate 13) (![⟨128053, by decide⟩,⟨128073, by decide⟩,⟨128087, by decide⟩,⟨128094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_71692_128095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71692 ⟨128095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 71692
    ⟨128095, by decide⟩ (by decide) (![⟨128053, by decide⟩,⟨128073, by decide⟩,⟨128087, by decide⟩,⟨128094, by decide⟩]) unmarked_context_13_71692_128095 node_context_13_71692_128095
  intro a
  fin_cases a
  · exact context_14_286768_128053
  · exact context_14_286769_128073
  · exact context_14_286770_128087
  · exact context_14_286771_128094

theorem selected_cut_04016 : selected 8 ⟨128149, by decide⟩
    (prefixPartial 13 71693) = some ⟨13, 2, 0, 128149, 71693, 3281, 16384⟩ := by
  decide +kernel

theorem context_13_71693_128149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71693 ⟨128149, by decide⟩ :=
  accepted_of_selected 13 71693 ⟨128149, by decide⟩ ⟨13, 2, 0, 128149, 71693, 3281, 16384⟩
    (by decide) selected_cut_04016

theorem selected_cut_04017 : selected 8 ⟨128169, by decide⟩
    (prefixPartial 13 71694) = some ⟨13, 2, 0, 128169, 71694, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_71694_128169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71694 ⟨128169, by decide⟩ :=
  accepted_of_selected 13 71694 ⟨128169, by decide⟩ ⟨13, 2, 0, 128169, 71694, 1625, 16384⟩
    (by decide) selected_cut_04017

theorem selected_cut_04018 : selected 8 ⟨128176, by decide⟩
    (prefixPartial 13 71695) = some ⟨13, 2, 0, 128176, 71695, 893, 16384⟩ := by
  decide +kernel

theorem context_13_71695_128176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71695 ⟨128176, by decide⟩ :=
  accepted_of_selected 13 71695 ⟨128176, by decide⟩ ⟨13, 2, 0, 128176, 71695, 893, 16384⟩
    (by decide) selected_cut_04018

theorem unmarked_context_12_17923_128177 : frontier 9 ⟨128177, by decide⟩
    (prefixCache 12 17923) (prefixPartial 12 17923) = false := by
  decide +kernel

theorem node_context_12_17923_128177 : EJMOriginalGlobalDAGData.nodes 9 ⟨128177, by decide⟩ =
    .split (coordinate 12) (![⟨128095, by decide⟩,⟨128149, by decide⟩,⟨128169, by decide⟩,⟨128176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17923_128177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17923 ⟨128177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17923
    ⟨128177, by decide⟩ (by decide) (![⟨128095, by decide⟩,⟨128149, by decide⟩,⟨128169, by decide⟩,⟨128176, by decide⟩]) unmarked_context_12_17923_128177 node_context_12_17923_128177
  intro a
  fin_cases a
  · exact context_13_71692_128095
  · exact context_13_71693_128149
  · exact context_13_71694_128169
  · exact context_13_71695_128176

theorem unmarked_context_11_4480_128178 : frontier 10 ⟨128178, by decide⟩
    (prefixCache 11 4480) (prefixPartial 11 4480) = false := by
  decide +kernel

theorem node_context_11_4480_128178 : EJMOriginalGlobalDAGData.nodes 10 ⟨128178, by decide⟩ =
    .split (coordinate 11) (![⟨127783, by decide⟩,⟨127920, by decide⟩,⟨128040, by decide⟩,⟨128177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4480_128178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4480 ⟨128178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4480
    ⟨128178, by decide⟩ (by decide) (![⟨127783, by decide⟩,⟨127920, by decide⟩,⟨128040, by decide⟩,⟨128177, by decide⟩]) unmarked_context_11_4480_128178 node_context_11_4480_128178
  intro a
  fin_cases a
  · exact context_12_17920_127783
  · exact context_12_17921_127920
  · exact context_12_17922_128040
  · exact context_12_17923_128177

theorem selected_cut_04019 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17924) = some ⟨12, 1, 0, 895, 17924, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17924_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17924 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17924 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17924, 1, 65536⟩
    (by decide) selected_cut_04019

theorem selected_cut_04020 : selected 8 ⟨128246, by decide⟩
    (prefixPartial 13 71700) = some ⟨13, 2, 0, 128246, 71700, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_71700_128246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71700 ⟨128246, by decide⟩ :=
  accepted_of_selected 13 71700 ⟨128246, by decide⟩ ⟨13, 2, 0, 128246, 71700, 3097, 16384⟩
    (by decide) selected_cut_04020

theorem selected_cut_04021 : selected 8 ⟨128292, by decide⟩
    (prefixPartial 13 71701) = some ⟨13, 2, 0, 128292, 71701, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_71701_128292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71701 ⟨128292, by decide⟩ :=
  accepted_of_selected 13 71701 ⟨128292, by decide⟩ ⟨13, 2, 0, 128292, 71701, 1793, 16384⟩
    (by decide) selected_cut_04021

theorem selected_cut_04022 : selected 8 ⟨128306, by decide⟩
    (prefixPartial 13 71702) = some ⟨13, 2, 0, 128306, 71702, 577, 16384⟩ := by
  decide +kernel

theorem context_13_71702_128306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71702 ⟨128306, by decide⟩ :=
  accepted_of_selected 13 71702 ⟨128306, by decide⟩ ⟨13, 2, 0, 128306, 71702, 577, 16384⟩
    (by decide) selected_cut_04022

theorem selected_cut_04023 : selected 8 ⟨128308, by decide⟩
    (prefixPartial 13 71703) = some ⟨13, 2, 0, 128308, 71703, 113, 16384⟩ := by
  decide +kernel

theorem context_13_71703_128308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71703 ⟨128308, by decide⟩ :=
  accepted_of_selected 13 71703 ⟨128308, by decide⟩ ⟨13, 2, 0, 128308, 71703, 113, 16384⟩
    (by decide) selected_cut_04023

theorem unmarked_context_12_17925_128309 : frontier 9 ⟨128309, by decide⟩
    (prefixCache 12 17925) (prefixPartial 12 17925) = false := by
  decide +kernel

theorem node_context_12_17925_128309 : EJMOriginalGlobalDAGData.nodes 9 ⟨128309, by decide⟩ =
    .split (coordinate 12) (![⟨128246, by decide⟩,⟨128292, by decide⟩,⟨128306, by decide⟩,⟨128308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17925_128309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17925 ⟨128309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17925
    ⟨128309, by decide⟩ (by decide) (![⟨128246, by decide⟩,⟨128292, by decide⟩,⟨128306, by decide⟩,⟨128308, by decide⟩]) unmarked_context_12_17925_128309 node_context_12_17925_128309
  intro a
  fin_cases a
  · exact context_13_71700_128246
  · exact context_13_71701_128292
  · exact context_13_71702_128306
  · exact context_13_71703_128308

theorem selected_cut_04024 : selected 8 ⟨128363, by decide⟩
    (prefixPartial 13 71704) = some ⟨13, 2, 0, 128363, 71704, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_71704_128363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71704 ⟨128363, by decide⟩ :=
  accepted_of_selected 13 71704 ⟨128363, by decide⟩ ⟨13, 2, 0, 128363, 71704, 3141, 16384⟩
    (by decide) selected_cut_04024

theorem selected_cut_04025 : selected 8 ⟨128394, by decide⟩
    (prefixPartial 13 71705) = some ⟨13, 2, 0, 128394, 71705, 3413, 16384⟩ := by
  decide +kernel

theorem context_13_71705_128394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71705 ⟨128394, by decide⟩ :=
  accepted_of_selected 13 71705 ⟨128394, by decide⟩ ⟨13, 2, 0, 128394, 71705, 3413, 16384⟩
    (by decide) selected_cut_04025

theorem selected_cut_04026 : selected 8 ⟨128419, by decide⟩
    (prefixPartial 13 71706) = some ⟨13, 2, 0, 128419, 71706, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_71706_128419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71706 ⟨128419, by decide⟩ :=
  accepted_of_selected 13 71706 ⟨128419, by decide⟩ ⟨13, 2, 0, 128419, 71706, 1973, 16384⟩
    (by decide) selected_cut_04026

theorem selected_cut_04027 : selected 8 ⟨128427, by decide⟩
    (prefixPartial 13 71707) = some ⟨13, 2, 0, 128427, 71707, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_71707_128427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71707 ⟨128427, by decide⟩ :=
  accepted_of_selected 13 71707 ⟨128427, by decide⟩ ⟨13, 2, 0, 128427, 71707, 1085, 16384⟩
    (by decide) selected_cut_04027

theorem unmarked_context_12_17926_128428 : frontier 9 ⟨128428, by decide⟩
    (prefixCache 12 17926) (prefixPartial 12 17926) = false := by
  decide +kernel

theorem node_context_12_17926_128428 : EJMOriginalGlobalDAGData.nodes 9 ⟨128428, by decide⟩ =
    .split (coordinate 12) (![⟨128363, by decide⟩,⟨128394, by decide⟩,⟨128419, by decide⟩,⟨128427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17926_128428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17926 ⟨128428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17926
    ⟨128428, by decide⟩ (by decide) (![⟨128363, by decide⟩,⟨128394, by decide⟩,⟨128419, by decide⟩,⟨128427, by decide⟩]) unmarked_context_12_17926_128428 node_context_12_17926_128428
  intro a
  fin_cases a
  · exact context_13_71704_128363
  · exact context_13_71705_128394
  · exact context_13_71706_128419
  · exact context_13_71707_128427

theorem selected_cut_04028 : selected 8 ⟨128483, by decide⟩
    (prefixPartial 13 71708) = some ⟨13, 2, 0, 128483, 71708, 3521, 16384⟩ := by
  decide +kernel

theorem context_13_71708_128483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71708 ⟨128483, by decide⟩ :=
  accepted_of_selected 13 71708 ⟨128483, by decide⟩ ⟨13, 2, 0, 128483, 71708, 3521, 16384⟩
    (by decide) selected_cut_04028

theorem selected_cut_04029 : selected 8 ⟨128530, by decide⟩
    (prefixPartial 13 71709) = some ⟨13, 2, 0, 128530, 71709, 3669, 16384⟩ := by
  decide +kernel

theorem context_13_71709_128530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71709 ⟨128530, by decide⟩ :=
  accepted_of_selected 13 71709 ⟨128530, by decide⟩ ⟨13, 2, 0, 128530, 71709, 3669, 16384⟩
    (by decide) selected_cut_04029

theorem selected_cut_04030 : selected 8 ⟨128557, by decide⟩
    (prefixPartial 13 71710) = some ⟨13, 2, 0, 128557, 71710, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_71710_128557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71710 ⟨128557, by decide⟩ :=
  accepted_of_selected 13 71710 ⟨128557, by decide⟩ ⟨13, 2, 0, 128557, 71710, 2125, 16384⟩
    (by decide) selected_cut_04030

theorem selected_cut_04031 : selected 8 ⟨128568, by decide⟩
    (prefixPartial 13 71711) = some ⟨13, 2, 0, 128568, 71711, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_71711_128568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71711 ⟨128568, by decide⟩ :=
  accepted_of_selected 13 71711 ⟨128568, by decide⟩ ⟨13, 2, 0, 128568, 71711, 1077, 16384⟩
    (by decide) selected_cut_04031

theorem unmarked_context_12_17927_128569 : frontier 9 ⟨128569, by decide⟩
    (prefixCache 12 17927) (prefixPartial 12 17927) = false := by
  decide +kernel

theorem node_context_12_17927_128569 : EJMOriginalGlobalDAGData.nodes 9 ⟨128569, by decide⟩ =
    .split (coordinate 12) (![⟨128483, by decide⟩,⟨128530, by decide⟩,⟨128557, by decide⟩,⟨128568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17927_128569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17927 ⟨128569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17927
    ⟨128569, by decide⟩ (by decide) (![⟨128483, by decide⟩,⟨128530, by decide⟩,⟨128557, by decide⟩,⟨128568, by decide⟩]) unmarked_context_12_17927_128569 node_context_12_17927_128569
  intro a
  fin_cases a
  · exact context_13_71708_128483
  · exact context_13_71709_128530
  · exact context_13_71710_128557
  · exact context_13_71711_128568

theorem unmarked_context_11_4481_128570 : frontier 10 ⟨128570, by decide⟩
    (prefixCache 11 4481) (prefixPartial 11 4481) = false := by
  decide +kernel

theorem node_context_11_4481_128570 : EJMOriginalGlobalDAGData.nodes 10 ⟨128570, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨128309, by decide⟩,⟨128428, by decide⟩,⟨128569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4481_128570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4481 ⟨128570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4481
    ⟨128570, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨128309, by decide⟩,⟨128428, by decide⟩,⟨128569, by decide⟩]) unmarked_context_11_4481_128570 node_context_11_4481_128570
  intro a
  fin_cases a
  · exact context_12_17924_895
  · exact context_12_17925_128309
  · exact context_12_17926_128428
  · exact context_12_17927_128569

theorem selected_cut_04032 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17928) = some ⟨12, 1, 0, 895, 17928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17928_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17928 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17928 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17928, 1, 65536⟩
    (by decide) selected_cut_04032

theorem selected_cut_04033 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17929) = some ⟨12, 1, 0, 895, 17929, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17929_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17929 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17929 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17929, 1, 65536⟩
    (by decide) selected_cut_04033

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
