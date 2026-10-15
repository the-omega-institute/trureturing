/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover061
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05954 : selected 8 ⟨181697, by decide⟩
    (prefixPartial 13 84104) = some ⟨13, 2, 0, 181697, 84104, 989, 16384⟩ := by
  decide +kernel

theorem context_13_84104_181697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84104 ⟨181697, by decide⟩ :=
  accepted_of_selected 13 84104 ⟨181697, by decide⟩ ⟨13, 2, 0, 181697, 84104, 989, 16384⟩
    (by decide) selected_cut_05954

theorem selected_cut_05955 : selected 8 ⟨181728, by decide⟩
    (prefixPartial 13 84105) = some ⟨13, 2, 0, 181728, 84105, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_84105_181728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84105 ⟨181728, by decide⟩ :=
  accepted_of_selected 13 84105 ⟨181728, by decide⟩ ⟨13, 2, 0, 181728, 84105, 2049, 16384⟩
    (by decide) selected_cut_05955

theorem selected_cut_05956 : selected 8 ⟨181745, by decide⟩
    (prefixPartial 13 84106) = some ⟨13, 2, 0, 181745, 84106, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_84106_181745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84106 ⟨181745, by decide⟩ :=
  accepted_of_selected 13 84106 ⟨181745, by decide⟩ ⟨13, 2, 0, 181745, 84106, 1149, 16384⟩
    (by decide) selected_cut_05956

theorem selected_cut_05957 : selected 8 ⟨181752, by decide⟩
    (prefixPartial 13 84107) = some ⟨13, 2, 0, 181752, 84107, 633, 16384⟩ := by
  decide +kernel

theorem context_13_84107_181752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84107 ⟨181752, by decide⟩ :=
  accepted_of_selected 13 84107 ⟨181752, by decide⟩ ⟨13, 2, 0, 181752, 84107, 633, 16384⟩
    (by decide) selected_cut_05957

theorem unmarked_context_12_21026_181753 : frontier 9 ⟨181753, by decide⟩
    (prefixCache 12 21026) (prefixPartial 12 21026) = false := by
  decide +kernel

theorem node_context_12_21026_181753 : EJMOriginalGlobalDAGData.nodes 9 ⟨181753, by decide⟩ =
    .split (coordinate 12) (![⟨181697, by decide⟩,⟨181728, by decide⟩,⟨181745, by decide⟩,⟨181752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21026_181753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21026 ⟨181753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21026
    ⟨181753, by decide⟩ (by decide) (![⟨181697, by decide⟩,⟨181728, by decide⟩,⟨181745, by decide⟩,⟨181752, by decide⟩]) unmarked_context_12_21026_181753 node_context_12_21026_181753
  intro a
  fin_cases a
  · exact context_13_84104_181697
  · exact context_13_84105_181728
  · exact context_13_84106_181745
  · exact context_13_84107_181752

theorem selected_cut_05958 : selected 8 ⟨181771, by decide⟩
    (prefixPartial 13 84108) = some ⟨13, 2, 0, 181771, 84108, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_84108_181771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84108 ⟨181771, by decide⟩ :=
  accepted_of_selected 13 84108 ⟨181771, by decide⟩ ⟨13, 2, 0, 181771, 84108, 1085, 16384⟩
    (by decide) selected_cut_05958

theorem selected_cut_05959 : selected 8 ⟨181803, by decide⟩
    (prefixPartial 13 84109) = some ⟨13, 2, 0, 181803, 84109, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_84109_181803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84109 ⟨181803, by decide⟩ :=
  accepted_of_selected 13 84109 ⟨181803, by decide⟩ ⟨13, 2, 0, 181803, 84109, 2289, 16384⟩
    (by decide) selected_cut_05959

theorem selected_cut_05960 : selected 8 ⟨181822, by decide⟩
    (prefixPartial 13 84110) = some ⟨13, 2, 0, 181822, 84110, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_84110_181822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84110 ⟨181822, by decide⟩ :=
  accepted_of_selected 13 84110 ⟨181822, by decide⟩ ⟨13, 2, 0, 181822, 84110, 1265, 16384⟩
    (by decide) selected_cut_05960

theorem selected_cut_05961 : selected 8 ⟨181828, by decide⟩
    (prefixPartial 13 84111) = some ⟨13, 2, 0, 181828, 84111, 645, 16384⟩ := by
  decide +kernel

theorem context_13_84111_181828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84111 ⟨181828, by decide⟩ :=
  accepted_of_selected 13 84111 ⟨181828, by decide⟩ ⟨13, 2, 0, 181828, 84111, 645, 16384⟩
    (by decide) selected_cut_05961

theorem unmarked_context_12_21027_181829 : frontier 9 ⟨181829, by decide⟩
    (prefixCache 12 21027) (prefixPartial 12 21027) = false := by
  decide +kernel

theorem node_context_12_21027_181829 : EJMOriginalGlobalDAGData.nodes 9 ⟨181829, by decide⟩ =
    .split (coordinate 12) (![⟨181771, by decide⟩,⟨181803, by decide⟩,⟨181822, by decide⟩,⟨181828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21027_181829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21027 ⟨181829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21027
    ⟨181829, by decide⟩ (by decide) (![⟨181771, by decide⟩,⟨181803, by decide⟩,⟨181822, by decide⟩,⟨181828, by decide⟩]) unmarked_context_12_21027_181829 node_context_12_21027_181829
  intro a
  fin_cases a
  · exact context_13_84108_181771
  · exact context_13_84109_181803
  · exact context_13_84110_181822
  · exact context_13_84111_181828

theorem unmarked_context_11_5256_181830 : frontier 10 ⟨181830, by decide⟩
    (prefixCache 11 5256) (prefixPartial 11 5256) = false := by
  decide +kernel

theorem node_context_11_5256_181830 : EJMOriginalGlobalDAGData.nodes 10 ⟨181830, by decide⟩ =
    .split (coordinate 11) (![⟨181612, by decide⟩,⟨181680, by decide⟩,⟨181753, by decide⟩,⟨181829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5256_181830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5256 ⟨181830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5256
    ⟨181830, by decide⟩ (by decide) (![⟨181612, by decide⟩,⟨181680, by decide⟩,⟨181753, by decide⟩,⟨181829, by decide⟩]) unmarked_context_11_5256_181830 node_context_11_5256_181830
  intro a
  fin_cases a
  · exact context_12_21024_181612
  · exact context_12_21025_181680
  · exact context_12_21026_181753
  · exact context_12_21027_181829

theorem selected_cut_05962 : selected 8 ⟨181847, by decide⟩
    (prefixPartial 13 84112) = some ⟨13, 2, 0, 181847, 84112, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_84112_181847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84112 ⟨181847, by decide⟩ :=
  accepted_of_selected 13 84112 ⟨181847, by decide⟩ ⟨13, 2, 0, 181847, 84112, 1001, 16384⟩
    (by decide) selected_cut_05962

theorem selected_cut_05963 : selected 8 ⟨181880, by decide⟩
    (prefixPartial 13 84113) = some ⟨13, 2, 0, 181880, 84113, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_84113_181880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84113 ⟨181880, by decide⟩ :=
  accepted_of_selected 13 84113 ⟨181880, by decide⟩ ⟨13, 2, 0, 181880, 84113, 2129, 16384⟩
    (by decide) selected_cut_05963

theorem selected_cut_05964 : selected 8 ⟨181896, by decide⟩
    (prefixPartial 13 84114) = some ⟨13, 2, 0, 181896, 84114, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_84114_181896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84114 ⟨181896, by decide⟩ :=
  accepted_of_selected 13 84114 ⟨181896, by decide⟩ ⟨13, 2, 0, 181896, 84114, 1281, 16384⟩
    (by decide) selected_cut_05964

theorem selected_cut_05965 : selected 8 ⟨181901, by decide⟩
    (prefixPartial 13 84115) = some ⟨13, 2, 0, 181901, 84115, 677, 16384⟩ := by
  decide +kernel

theorem context_13_84115_181901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84115 ⟨181901, by decide⟩ :=
  accepted_of_selected 13 84115 ⟨181901, by decide⟩ ⟨13, 2, 0, 181901, 84115, 677, 16384⟩
    (by decide) selected_cut_05965

theorem unmarked_context_12_21028_181902 : frontier 9 ⟨181902, by decide⟩
    (prefixCache 12 21028) (prefixPartial 12 21028) = false := by
  decide +kernel

theorem node_context_12_21028_181902 : EJMOriginalGlobalDAGData.nodes 9 ⟨181902, by decide⟩ =
    .split (coordinate 12) (![⟨181847, by decide⟩,⟨181880, by decide⟩,⟨181896, by decide⟩,⟨181901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21028_181902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21028 ⟨181902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21028
    ⟨181902, by decide⟩ (by decide) (![⟨181847, by decide⟩,⟨181880, by decide⟩,⟨181896, by decide⟩,⟨181901, by decide⟩]) unmarked_context_12_21028_181902 node_context_12_21028_181902
  intro a
  fin_cases a
  · exact context_13_84112_181847
  · exact context_13_84113_181880
  · exact context_13_84114_181896
  · exact context_13_84115_181901

theorem selected_cut_05966 : selected 8 ⟨181916, by decide⟩
    (prefixPartial 13 84116) = some ⟨13, 2, 0, 181916, 84116, 897, 16384⟩ := by
  decide +kernel

theorem context_13_84116_181916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84116 ⟨181916, by decide⟩ :=
  accepted_of_selected 13 84116 ⟨181916, by decide⟩ ⟨13, 2, 0, 181916, 84116, 897, 16384⟩
    (by decide) selected_cut_05966

theorem selected_cut_05967 : selected 8 ⟨181947, by decide⟩
    (prefixPartial 13 84117) = some ⟨13, 2, 0, 181947, 84117, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_84117_181947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84117 ⟨181947, by decide⟩ :=
  accepted_of_selected 13 84117 ⟨181947, by decide⟩ ⟨13, 2, 0, 181947, 84117, 2169, 16384⟩
    (by decide) selected_cut_05967

theorem selected_cut_05968 : selected 8 ⟨181965, by decide⟩
    (prefixPartial 13 84118) = some ⟨13, 2, 0, 181965, 84118, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_84118_181965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84118 ⟨181965, by decide⟩ :=
  accepted_of_selected 13 84118 ⟨181965, by decide⟩ ⟨13, 2, 0, 181965, 84118, 1393, 16384⟩
    (by decide) selected_cut_05968

theorem selected_cut_05969 : selected 8 ⟨181970, by decide⟩
    (prefixPartial 13 84119) = some ⟨13, 2, 0, 181970, 84119, 709, 16384⟩ := by
  decide +kernel

theorem context_13_84119_181970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84119 ⟨181970, by decide⟩ :=
  accepted_of_selected 13 84119 ⟨181970, by decide⟩ ⟨13, 2, 0, 181970, 84119, 709, 16384⟩
    (by decide) selected_cut_05969

theorem unmarked_context_12_21029_181971 : frontier 9 ⟨181971, by decide⟩
    (prefixCache 12 21029) (prefixPartial 12 21029) = false := by
  decide +kernel

theorem node_context_12_21029_181971 : EJMOriginalGlobalDAGData.nodes 9 ⟨181971, by decide⟩ =
    .split (coordinate 12) (![⟨181916, by decide⟩,⟨181947, by decide⟩,⟨181965, by decide⟩,⟨181970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21029_181971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21029 ⟨181971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21029
    ⟨181971, by decide⟩ (by decide) (![⟨181916, by decide⟩,⟨181947, by decide⟩,⟨181965, by decide⟩,⟨181970, by decide⟩]) unmarked_context_12_21029_181971 node_context_12_21029_181971
  intro a
  fin_cases a
  · exact context_13_84116_181916
  · exact context_13_84117_181947
  · exact context_13_84118_181965
  · exact context_13_84119_181970

theorem selected_cut_05970 : selected 8 ⟨181987, by decide⟩
    (prefixPartial 13 84120) = some ⟨13, 2, 0, 181987, 84120, 913, 16384⟩ := by
  decide +kernel

theorem context_13_84120_181987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84120 ⟨181987, by decide⟩ :=
  accepted_of_selected 13 84120 ⟨181987, by decide⟩ ⟨13, 2, 0, 181987, 84120, 913, 16384⟩
    (by decide) selected_cut_05970

theorem selected_cut_05971 : selected 8 ⟨182020, by decide⟩
    (prefixPartial 13 84121) = some ⟨13, 2, 0, 182020, 84121, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_84121_182020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84121 ⟨182020, by decide⟩ :=
  accepted_of_selected 13 84121 ⟨182020, by decide⟩ ⟨13, 2, 0, 182020, 84121, 2317, 16384⟩
    (by decide) selected_cut_05971

theorem selected_cut_05972 : selected 8 ⟨182036, by decide⟩
    (prefixPartial 13 84122) = some ⟨13, 2, 0, 182036, 84122, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_84122_182036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84122 ⟨182036, by decide⟩ :=
  accepted_of_selected 13 84122 ⟨182036, by decide⟩ ⟨13, 2, 0, 182036, 84122, 1125, 16384⟩
    (by decide) selected_cut_05972

theorem selected_cut_05973 : selected 8 ⟨182043, by decide⟩
    (prefixPartial 13 84123) = some ⟨13, 2, 0, 182043, 84123, 689, 16384⟩ := by
  decide +kernel

theorem context_13_84123_182043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84123 ⟨182043, by decide⟩ :=
  accepted_of_selected 13 84123 ⟨182043, by decide⟩ ⟨13, 2, 0, 182043, 84123, 689, 16384⟩
    (by decide) selected_cut_05973

theorem unmarked_context_12_21030_182044 : frontier 9 ⟨182044, by decide⟩
    (prefixCache 12 21030) (prefixPartial 12 21030) = false := by
  decide +kernel

theorem node_context_12_21030_182044 : EJMOriginalGlobalDAGData.nodes 9 ⟨182044, by decide⟩ =
    .split (coordinate 12) (![⟨181987, by decide⟩,⟨182020, by decide⟩,⟨182036, by decide⟩,⟨182043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21030_182044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21030 ⟨182044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21030
    ⟨182044, by decide⟩ (by decide) (![⟨181987, by decide⟩,⟨182020, by decide⟩,⟨182036, by decide⟩,⟨182043, by decide⟩]) unmarked_context_12_21030_182044 node_context_12_21030_182044
  intro a
  fin_cases a
  · exact context_13_84120_181987
  · exact context_13_84121_182020
  · exact context_13_84122_182036
  · exact context_13_84123_182043

theorem selected_cut_05974 : selected 8 ⟨182063, by decide⟩
    (prefixPartial 13 84124) = some ⟨13, 2, 0, 182063, 84124, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_84124_182063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84124 ⟨182063, by decide⟩ :=
  accepted_of_selected 13 84124 ⟨182063, by decide⟩ ⟨13, 2, 0, 182063, 84124, 1005, 16384⟩
    (by decide) selected_cut_05974

theorem selected_cut_05975 : selected 8 ⟨182103, by decide⟩
    (prefixPartial 13 84125) = some ⟨13, 2, 0, 182103, 84125, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_84125_182103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84125 ⟨182103, by decide⟩ :=
  accepted_of_selected 13 84125 ⟨182103, by decide⟩ ⟨13, 2, 0, 182103, 84125, 2561, 16384⟩
    (by decide) selected_cut_05975

theorem selected_cut_05976 : selected 8 ⟨182124, by decide⟩
    (prefixPartial 13 84126) = some ⟨13, 2, 0, 182124, 84126, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_84126_182124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84126 ⟨182124, by decide⟩ :=
  accepted_of_selected 13 84126 ⟨182124, by decide⟩ ⟨13, 2, 0, 182124, 84126, 1397, 16384⟩
    (by decide) selected_cut_05976

theorem selected_cut_05977 : selected 8 ⟨182128, by decide⟩
    (prefixPartial 13 84127) = some ⟨13, 2, 0, 182128, 84127, 661, 16384⟩ := by
  decide +kernel

theorem context_13_84127_182128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84127 ⟨182128, by decide⟩ :=
  accepted_of_selected 13 84127 ⟨182128, by decide⟩ ⟨13, 2, 0, 182128, 84127, 661, 16384⟩
    (by decide) selected_cut_05977

theorem unmarked_context_12_21031_182129 : frontier 9 ⟨182129, by decide⟩
    (prefixCache 12 21031) (prefixPartial 12 21031) = false := by
  decide +kernel

theorem node_context_12_21031_182129 : EJMOriginalGlobalDAGData.nodes 9 ⟨182129, by decide⟩ =
    .split (coordinate 12) (![⟨182063, by decide⟩,⟨182103, by decide⟩,⟨182124, by decide⟩,⟨182128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21031_182129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21031 ⟨182129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21031
    ⟨182129, by decide⟩ (by decide) (![⟨182063, by decide⟩,⟨182103, by decide⟩,⟨182124, by decide⟩,⟨182128, by decide⟩]) unmarked_context_12_21031_182129 node_context_12_21031_182129
  intro a
  fin_cases a
  · exact context_13_84124_182063
  · exact context_13_84125_182103
  · exact context_13_84126_182124
  · exact context_13_84127_182128

theorem unmarked_context_11_5257_182130 : frontier 10 ⟨182130, by decide⟩
    (prefixCache 11 5257) (prefixPartial 11 5257) = false := by
  decide +kernel

theorem node_context_11_5257_182130 : EJMOriginalGlobalDAGData.nodes 10 ⟨182130, by decide⟩ =
    .split (coordinate 11) (![⟨181902, by decide⟩,⟨181971, by decide⟩,⟨182044, by decide⟩,⟨182129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5257_182130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5257 ⟨182130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5257
    ⟨182130, by decide⟩ (by decide) (![⟨181902, by decide⟩,⟨181971, by decide⟩,⟨182044, by decide⟩,⟨182129, by decide⟩]) unmarked_context_11_5257_182130 node_context_11_5257_182130
  intro a
  fin_cases a
  · exact context_12_21028_181902
  · exact context_12_21029_181971
  · exact context_12_21030_182044
  · exact context_12_21031_182129

theorem selected_cut_05978 : selected 8 ⟨182147, by decide⟩
    (prefixPartial 13 84128) = some ⟨13, 2, 0, 182147, 84128, 889, 16384⟩ := by
  decide +kernel

theorem context_13_84128_182147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84128 ⟨182147, by decide⟩ :=
  accepted_of_selected 13 84128 ⟨182147, by decide⟩ ⟨13, 2, 0, 182147, 84128, 889, 16384⟩
    (by decide) selected_cut_05978

theorem selected_cut_05979 : selected 8 ⟨182169, by decide⟩
    (prefixPartial 13 84129) = some ⟨13, 2, 0, 182169, 84129, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_84129_182169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84129 ⟨182169, by decide⟩ :=
  accepted_of_selected 13 84129 ⟨182169, by decide⟩ ⟨13, 2, 0, 182169, 84129, 1925, 16384⟩
    (by decide) selected_cut_05979

theorem selected_cut_05980 : selected 8 ⟨182185, by decide⟩
    (prefixPartial 13 84130) = some ⟨13, 2, 0, 182185, 84130, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_84130_182185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84130 ⟨182185, by decide⟩ :=
  accepted_of_selected 13 84130 ⟨182185, by decide⟩ ⟨13, 2, 0, 182185, 84130, 1297, 16384⟩
    (by decide) selected_cut_05980

theorem selected_cut_05981 : selected 8 ⟨182190, by decide⟩
    (prefixPartial 13 84131) = some ⟨13, 2, 0, 182190, 84131, 625, 16384⟩ := by
  decide +kernel

theorem context_13_84131_182190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84131 ⟨182190, by decide⟩ :=
  accepted_of_selected 13 84131 ⟨182190, by decide⟩ ⟨13, 2, 0, 182190, 84131, 625, 16384⟩
    (by decide) selected_cut_05981

theorem unmarked_context_12_21032_182191 : frontier 9 ⟨182191, by decide⟩
    (prefixCache 12 21032) (prefixPartial 12 21032) = false := by
  decide +kernel

theorem node_context_12_21032_182191 : EJMOriginalGlobalDAGData.nodes 9 ⟨182191, by decide⟩ =
    .split (coordinate 12) (![⟨182147, by decide⟩,⟨182169, by decide⟩,⟨182185, by decide⟩,⟨182190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21032_182191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21032 ⟨182191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21032
    ⟨182191, by decide⟩ (by decide) (![⟨182147, by decide⟩,⟨182169, by decide⟩,⟨182185, by decide⟩,⟨182190, by decide⟩]) unmarked_context_12_21032_182191 node_context_12_21032_182191
  intro a
  fin_cases a
  · exact context_13_84128_182147
  · exact context_13_84129_182169
  · exact context_13_84130_182185
  · exact context_13_84131_182190

theorem selected_cut_05982 : selected 8 ⟨182209, by decide⟩
    (prefixPartial 13 84132) = some ⟨13, 2, 0, 182209, 84132, 957, 16384⟩ := by
  decide +kernel

theorem context_13_84132_182209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84132 ⟨182209, by decide⟩ :=
  accepted_of_selected 13 84132 ⟨182209, by decide⟩ ⟨13, 2, 0, 182209, 84132, 957, 16384⟩
    (by decide) selected_cut_05982

theorem selected_cut_05983 : selected 8 ⟨182237, by decide⟩
    (prefixPartial 13 84133) = some ⟨13, 2, 0, 182237, 84133, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_84133_182237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84133 ⟨182237, by decide⟩ :=
  accepted_of_selected 13 84133 ⟨182237, by decide⟩ ⟨13, 2, 0, 182237, 84133, 2157, 16384⟩
    (by decide) selected_cut_05983

theorem selected_cut_05984 : selected 8 ⟨182255, by decide⟩
    (prefixPartial 13 84134) = some ⟨13, 2, 0, 182255, 84134, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_84134_182255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84134 ⟨182255, by decide⟩ :=
  accepted_of_selected 13 84134 ⟨182255, by decide⟩ ⟨13, 2, 0, 182255, 84134, 1481, 16384⟩
    (by decide) selected_cut_05984

theorem selected_cut_05985 : selected 8 ⟨182264, by decide⟩
    (prefixPartial 13 84135) = some ⟨13, 2, 0, 182264, 84135, 741, 16384⟩ := by
  decide +kernel

theorem context_13_84135_182264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84135 ⟨182264, by decide⟩ :=
  accepted_of_selected 13 84135 ⟨182264, by decide⟩ ⟨13, 2, 0, 182264, 84135, 741, 16384⟩
    (by decide) selected_cut_05985

theorem unmarked_context_12_21033_182265 : frontier 9 ⟨182265, by decide⟩
    (prefixCache 12 21033) (prefixPartial 12 21033) = false := by
  decide +kernel

theorem node_context_12_21033_182265 : EJMOriginalGlobalDAGData.nodes 9 ⟨182265, by decide⟩ =
    .split (coordinate 12) (![⟨182209, by decide⟩,⟨182237, by decide⟩,⟨182255, by decide⟩,⟨182264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21033_182265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21033 ⟨182265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21033
    ⟨182265, by decide⟩ (by decide) (![⟨182209, by decide⟩,⟨182237, by decide⟩,⟨182255, by decide⟩,⟨182264, by decide⟩]) unmarked_context_12_21033_182265 node_context_12_21033_182265
  intro a
  fin_cases a
  · exact context_13_84132_182209
  · exact context_13_84133_182237
  · exact context_13_84134_182255
  · exact context_13_84135_182264

theorem selected_cut_05986 : selected 8 ⟨182285, by decide⟩
    (prefixPartial 13 84136) = some ⟨13, 2, 0, 182285, 84136, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_84136_182285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84136 ⟨182285, by decide⟩ :=
  accepted_of_selected 13 84136 ⟨182285, by decide⟩ ⟨13, 2, 0, 182285, 84136, 1517, 16384⟩
    (by decide) selected_cut_05986

theorem selected_cut_05987 : selected 8 ⟨182350, by decide⟩
    (prefixPartial 13 84137) = some ⟨13, 2, 0, 182350, 84137, 3945, 16384⟩ := by
  decide +kernel

theorem context_13_84137_182350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84137 ⟨182350, by decide⟩ :=
  accepted_of_selected 13 84137 ⟨182350, by decide⟩ ⟨13, 2, 0, 182350, 84137, 3945, 16384⟩
    (by decide) selected_cut_05987

theorem selected_cut_05988 : selected 8 ⟨182386, by decide⟩
    (prefixPartial 13 84138) = some ⟨13, 2, 0, 182386, 84138, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_84138_182386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84138 ⟨182386, by decide⟩ :=
  accepted_of_selected 13 84138 ⟨182386, by decide⟩ ⟨13, 2, 0, 182386, 84138, 2353, 16384⟩
    (by decide) selected_cut_05988

theorem selected_cut_05989 : selected 8 ⟨182399, by decide⟩
    (prefixPartial 13 84139) = some ⟨13, 2, 0, 182399, 84139, 953, 16384⟩ := by
  decide +kernel

theorem context_13_84139_182399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84139 ⟨182399, by decide⟩ :=
  accepted_of_selected 13 84139 ⟨182399, by decide⟩ ⟨13, 2, 0, 182399, 84139, 953, 16384⟩
    (by decide) selected_cut_05989

theorem unmarked_context_12_21034_182400 : frontier 9 ⟨182400, by decide⟩
    (prefixCache 12 21034) (prefixPartial 12 21034) = false := by
  decide +kernel

theorem node_context_12_21034_182400 : EJMOriginalGlobalDAGData.nodes 9 ⟨182400, by decide⟩ =
    .split (coordinate 12) (![⟨182285, by decide⟩,⟨182350, by decide⟩,⟨182386, by decide⟩,⟨182399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21034_182400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21034 ⟨182400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21034
    ⟨182400, by decide⟩ (by decide) (![⟨182285, by decide⟩,⟨182350, by decide⟩,⟨182386, by decide⟩,⟨182399, by decide⟩]) unmarked_context_12_21034_182400 node_context_12_21034_182400
  intro a
  fin_cases a
  · exact context_13_84136_182285
  · exact context_13_84137_182350
  · exact context_13_84138_182386
  · exact context_13_84139_182399

theorem selected_cut_05990 : selected 8 ⟨182416, by decide⟩
    (prefixPartial 13 84140) = some ⟨13, 2, 0, 182416, 84140, 933, 16384⟩ := by
  decide +kernel

theorem context_13_84140_182416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84140 ⟨182416, by decide⟩ :=
  accepted_of_selected 13 84140 ⟨182416, by decide⟩ ⟨13, 2, 0, 182416, 84140, 933, 16384⟩
    (by decide) selected_cut_05990

theorem selected_cut_05991 : selected 8 ⟨182462, by decide⟩
    (prefixPartial 13 84141) = some ⟨13, 2, 0, 182462, 84141, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_84141_182462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84141 ⟨182462, by decide⟩ :=
  accepted_of_selected 13 84141 ⟨182462, by decide⟩ ⟨13, 2, 0, 182462, 84141, 2813, 16384⟩
    (by decide) selected_cut_05991

theorem selected_cut_05992 : selected 8 ⟨182480, by decide⟩
    (prefixPartial 13 84142) = some ⟨13, 2, 0, 182480, 84142, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_84142_182480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84142 ⟨182480, by decide⟩ :=
  accepted_of_selected 13 84142 ⟨182480, by decide⟩ ⟨13, 2, 0, 182480, 84142, 1465, 16384⟩
    (by decide) selected_cut_05992

theorem selected_cut_05993 : selected 8 ⟨182487, by decide⟩
    (prefixPartial 13 84143) = some ⟨13, 2, 0, 182487, 84143, 677, 16384⟩ := by
  decide +kernel

theorem context_13_84143_182487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84143 ⟨182487, by decide⟩ :=
  accepted_of_selected 13 84143 ⟨182487, by decide⟩ ⟨13, 2, 0, 182487, 84143, 677, 16384⟩
    (by decide) selected_cut_05993

theorem unmarked_context_12_21035_182488 : frontier 9 ⟨182488, by decide⟩
    (prefixCache 12 21035) (prefixPartial 12 21035) = false := by
  decide +kernel

theorem node_context_12_21035_182488 : EJMOriginalGlobalDAGData.nodes 9 ⟨182488, by decide⟩ =
    .split (coordinate 12) (![⟨182416, by decide⟩,⟨182462, by decide⟩,⟨182480, by decide⟩,⟨182487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21035_182488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21035 ⟨182488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21035
    ⟨182488, by decide⟩ (by decide) (![⟨182416, by decide⟩,⟨182462, by decide⟩,⟨182480, by decide⟩,⟨182487, by decide⟩]) unmarked_context_12_21035_182488 node_context_12_21035_182488
  intro a
  fin_cases a
  · exact context_13_84140_182416
  · exact context_13_84141_182462
  · exact context_13_84142_182480
  · exact context_13_84143_182487

theorem unmarked_context_11_5258_182489 : frontier 10 ⟨182489, by decide⟩
    (prefixCache 11 5258) (prefixPartial 11 5258) = false := by
  decide +kernel

theorem node_context_11_5258_182489 : EJMOriginalGlobalDAGData.nodes 10 ⟨182489, by decide⟩ =
    .split (coordinate 11) (![⟨182191, by decide⟩,⟨182265, by decide⟩,⟨182400, by decide⟩,⟨182488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5258_182489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5258 ⟨182489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5258
    ⟨182489, by decide⟩ (by decide) (![⟨182191, by decide⟩,⟨182265, by decide⟩,⟨182400, by decide⟩,⟨182488, by decide⟩]) unmarked_context_11_5258_182489 node_context_11_5258_182489
  intro a
  fin_cases a
  · exact context_12_21032_182191
  · exact context_12_21033_182265
  · exact context_12_21034_182400
  · exact context_12_21035_182488

theorem selected_cut_05994 : selected 8 ⟨182500, by decide⟩
    (prefixPartial 13 84144) = some ⟨13, 2, 0, 182500, 84144, 693, 16384⟩ := by
  decide +kernel

theorem context_13_84144_182500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84144 ⟨182500, by decide⟩ :=
  accepted_of_selected 13 84144 ⟨182500, by decide⟩ ⟨13, 2, 0, 182500, 84144, 693, 16384⟩
    (by decide) selected_cut_05994

theorem selected_cut_05995 : selected 8 ⟨182526, by decide⟩
    (prefixPartial 13 84145) = some ⟨13, 2, 0, 182526, 84145, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_84145_182526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84145 ⟨182526, by decide⟩ :=
  accepted_of_selected 13 84145 ⟨182526, by decide⟩ ⟨13, 2, 0, 182526, 84145, 2313, 16384⟩
    (by decide) selected_cut_05995

theorem selected_cut_05996 : selected 8 ⟨182548, by decide⟩
    (prefixPartial 13 84146) = some ⟨13, 2, 0, 182548, 84146, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_84146_182548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84146 ⟨182548, by decide⟩ :=
  accepted_of_selected 13 84146 ⟨182548, by decide⟩ ⟨13, 2, 0, 182548, 84146, 1629, 16384⟩
    (by decide) selected_cut_05996

theorem selected_cut_05997 : selected 8 ⟨182554, by decide⟩
    (prefixPartial 13 84147) = some ⟨13, 2, 0, 182554, 84147, 773, 16384⟩ := by
  decide +kernel

theorem context_13_84147_182554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84147 ⟨182554, by decide⟩ :=
  accepted_of_selected 13 84147 ⟨182554, by decide⟩ ⟨13, 2, 0, 182554, 84147, 773, 16384⟩
    (by decide) selected_cut_05997

theorem unmarked_context_12_21036_182555 : frontier 9 ⟨182555, by decide⟩
    (prefixCache 12 21036) (prefixPartial 12 21036) = false := by
  decide +kernel

theorem node_context_12_21036_182555 : EJMOriginalGlobalDAGData.nodes 9 ⟨182555, by decide⟩ =
    .split (coordinate 12) (![⟨182500, by decide⟩,⟨182526, by decide⟩,⟨182548, by decide⟩,⟨182554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21036_182555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21036 ⟨182555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21036
    ⟨182555, by decide⟩ (by decide) (![⟨182500, by decide⟩,⟨182526, by decide⟩,⟨182548, by decide⟩,⟨182554, by decide⟩]) unmarked_context_12_21036_182555 node_context_12_21036_182555
  intro a
  fin_cases a
  · exact context_13_84144_182500
  · exact context_13_84145_182526
  · exact context_13_84146_182548
  · exact context_13_84147_182554

theorem selected_cut_05998 : selected 8 ⟨182565, by decide⟩
    (prefixPartial 13 84148) = some ⟨13, 2, 0, 182565, 84148, 757, 16384⟩ := by
  decide +kernel

theorem context_13_84148_182565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84148 ⟨182565, by decide⟩ :=
  accepted_of_selected 13 84148 ⟨182565, by decide⟩ ⟨13, 2, 0, 182565, 84148, 757, 16384⟩
    (by decide) selected_cut_05998

theorem selected_cut_05999 : selected 8 ⟨182592, by decide⟩
    (prefixPartial 13 84149) = some ⟨13, 2, 0, 182592, 84149, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_84149_182592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84149 ⟨182592, by decide⟩ :=
  accepted_of_selected 13 84149 ⟨182592, by decide⟩ ⟨13, 2, 0, 182592, 84149, 2417, 16384⟩
    (by decide) selected_cut_05999

theorem selected_cut_06000 : selected 8 ⟨182616, by decide⟩
    (prefixPartial 13 84150) = some ⟨13, 2, 0, 182616, 84150, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_84150_182616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84150 ⟨182616, by decide⟩ :=
  accepted_of_selected 13 84150 ⟨182616, by decide⟩ ⟨13, 2, 0, 182616, 84150, 1961, 16384⟩
    (by decide) selected_cut_06000

theorem selected_cut_06001 : selected 8 ⟨182627, by decide⟩
    (prefixPartial 13 84151) = some ⟨13, 2, 0, 182627, 84151, 817, 16384⟩ := by
  decide +kernel

theorem context_13_84151_182627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84151 ⟨182627, by decide⟩ :=
  accepted_of_selected 13 84151 ⟨182627, by decide⟩ ⟨13, 2, 0, 182627, 84151, 817, 16384⟩
    (by decide) selected_cut_06001

theorem unmarked_context_12_21037_182628 : frontier 9 ⟨182628, by decide⟩
    (prefixCache 12 21037) (prefixPartial 12 21037) = false := by
  decide +kernel

theorem node_context_12_21037_182628 : EJMOriginalGlobalDAGData.nodes 9 ⟨182628, by decide⟩ =
    .split (coordinate 12) (![⟨182565, by decide⟩,⟨182592, by decide⟩,⟨182616, by decide⟩,⟨182627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21037_182628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21037 ⟨182628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21037
    ⟨182628, by decide⟩ (by decide) (![⟨182565, by decide⟩,⟨182592, by decide⟩,⟨182616, by decide⟩,⟨182627, by decide⟩]) unmarked_context_12_21037_182628 node_context_12_21037_182628
  intro a
  fin_cases a
  · exact context_13_84148_182565
  · exact context_13_84149_182592
  · exact context_13_84150_182616
  · exact context_13_84151_182627

theorem selected_cut_06002 : selected 8 ⟨182640, by decide⟩
    (prefixPartial 13 84152) = some ⟨13, 2, 0, 182640, 84152, 721, 16384⟩ := by
  decide +kernel

theorem context_13_84152_182640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84152 ⟨182640, by decide⟩ :=
  accepted_of_selected 13 84152 ⟨182640, by decide⟩ ⟨13, 2, 0, 182640, 84152, 721, 16384⟩
    (by decide) selected_cut_06002

theorem selected_cut_06003 : selected 8 ⟨182674, by decide⟩
    (prefixPartial 13 84153) = some ⟨13, 2, 0, 182674, 84153, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_84153_182674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84153 ⟨182674, by decide⟩ :=
  accepted_of_selected 13 84153 ⟨182674, by decide⟩ ⟨13, 2, 0, 182674, 84153, 2745, 16384⟩
    (by decide) selected_cut_06003

theorem selected_cut_06004 : selected 8 ⟨182695, by decide⟩
    (prefixPartial 13 84154) = some ⟨13, 2, 0, 182695, 84154, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_84154_182695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84154 ⟨182695, by decide⟩ :=
  accepted_of_selected 13 84154 ⟨182695, by decide⟩ ⟨13, 2, 0, 182695, 84154, 1617, 16384⟩
    (by decide) selected_cut_06004

theorem selected_cut_06005 : selected 8 ⟨182700, by decide⟩
    (prefixPartial 13 84155) = some ⟨13, 2, 0, 182700, 84155, 757, 16384⟩ := by
  decide +kernel

theorem context_13_84155_182700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84155 ⟨182700, by decide⟩ :=
  accepted_of_selected 13 84155 ⟨182700, by decide⟩ ⟨13, 2, 0, 182700, 84155, 757, 16384⟩
    (by decide) selected_cut_06005

theorem unmarked_context_12_21038_182701 : frontier 9 ⟨182701, by decide⟩
    (prefixCache 12 21038) (prefixPartial 12 21038) = false := by
  decide +kernel

theorem node_context_12_21038_182701 : EJMOriginalGlobalDAGData.nodes 9 ⟨182701, by decide⟩ =
    .split (coordinate 12) (![⟨182640, by decide⟩,⟨182674, by decide⟩,⟨182695, by decide⟩,⟨182700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21038_182701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21038 ⟨182701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21038
    ⟨182701, by decide⟩ (by decide) (![⟨182640, by decide⟩,⟨182674, by decide⟩,⟨182695, by decide⟩,⟨182700, by decide⟩]) unmarked_context_12_21038_182701 node_context_12_21038_182701
  intro a
  fin_cases a
  · exact context_13_84152_182640
  · exact context_13_84153_182674
  · exact context_13_84154_182695
  · exact context_13_84155_182700

theorem selected_cut_06006 : selected 8 ⟨182710, by decide⟩
    (prefixPartial 13 84156) = some ⟨13, 2, 0, 182710, 84156, 745, 16384⟩ := by
  decide +kernel

theorem context_13_84156_182710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84156 ⟨182710, by decide⟩ :=
  accepted_of_selected 13 84156 ⟨182710, by decide⟩ ⟨13, 2, 0, 182710, 84156, 745, 16384⟩
    (by decide) selected_cut_06006

theorem selected_cut_06007 : selected 8 ⟨182745, by decide⟩
    (prefixPartial 13 84157) = some ⟨13, 2, 0, 182745, 84157, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_84157_182745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84157 ⟨182745, by decide⟩ :=
  accepted_of_selected 13 84157 ⟨182745, by decide⟩ ⟨13, 2, 0, 182745, 84157, 2785, 16384⟩
    (by decide) selected_cut_06007

theorem selected_cut_06008 : selected 8 ⟨182767, by decide⟩
    (prefixPartial 13 84158) = some ⟨13, 2, 0, 182767, 84158, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_84158_182767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84158 ⟨182767, by decide⟩ :=
  accepted_of_selected 13 84158 ⟨182767, by decide⟩ ⟨13, 2, 0, 182767, 84158, 1673, 16384⟩
    (by decide) selected_cut_06008

theorem selected_cut_06009 : selected 8 ⟨182775, by decide⟩
    (prefixPartial 13 84159) = some ⟨13, 2, 0, 182775, 84159, 809, 16384⟩ := by
  decide +kernel

theorem context_13_84159_182775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84159 ⟨182775, by decide⟩ :=
  accepted_of_selected 13 84159 ⟨182775, by decide⟩ ⟨13, 2, 0, 182775, 84159, 809, 16384⟩
    (by decide) selected_cut_06009

theorem unmarked_context_12_21039_182776 : frontier 9 ⟨182776, by decide⟩
    (prefixCache 12 21039) (prefixPartial 12 21039) = false := by
  decide +kernel

theorem node_context_12_21039_182776 : EJMOriginalGlobalDAGData.nodes 9 ⟨182776, by decide⟩ =
    .split (coordinate 12) (![⟨182710, by decide⟩,⟨182745, by decide⟩,⟨182767, by decide⟩,⟨182775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21039_182776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21039 ⟨182776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21039
    ⟨182776, by decide⟩ (by decide) (![⟨182710, by decide⟩,⟨182745, by decide⟩,⟨182767, by decide⟩,⟨182775, by decide⟩]) unmarked_context_12_21039_182776 node_context_12_21039_182776
  intro a
  fin_cases a
  · exact context_13_84156_182710
  · exact context_13_84157_182745
  · exact context_13_84158_182767
  · exact context_13_84159_182775

theorem unmarked_context_11_5259_182777 : frontier 10 ⟨182777, by decide⟩
    (prefixCache 11 5259) (prefixPartial 11 5259) = false := by
  decide +kernel

theorem node_context_11_5259_182777 : EJMOriginalGlobalDAGData.nodes 10 ⟨182777, by decide⟩ =
    .split (coordinate 11) (![⟨182555, by decide⟩,⟨182628, by decide⟩,⟨182701, by decide⟩,⟨182776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5259_182777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5259 ⟨182777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5259
    ⟨182777, by decide⟩ (by decide) (![⟨182555, by decide⟩,⟨182628, by decide⟩,⟨182701, by decide⟩,⟨182776, by decide⟩]) unmarked_context_11_5259_182777 node_context_11_5259_182777
  intro a
  fin_cases a
  · exact context_12_21036_182555
  · exact context_12_21037_182628
  · exact context_12_21038_182701
  · exact context_12_21039_182776

theorem unmarked_context_10_1314_182778 : frontier 11 ⟨182778, by decide⟩
    (prefixCache 10 1314) (prefixPartial 10 1314) = false := by
  decide +kernel

theorem node_context_10_1314_182778 : EJMOriginalGlobalDAGData.nodes 11 ⟨182778, by decide⟩ =
    .split (coordinate 10) (![⟨181830, by decide⟩,⟨182130, by decide⟩,⟨182489, by decide⟩,⟨182777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1314_182778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1314 ⟨182778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1314
    ⟨182778, by decide⟩ (by decide) (![⟨181830, by decide⟩,⟨182130, by decide⟩,⟨182489, by decide⟩,⟨182777, by decide⟩]) unmarked_context_10_1314_182778 node_context_10_1314_182778
  intro a
  fin_cases a
  · exact context_11_5256_181830
  · exact context_11_5257_182130
  · exact context_11_5258_182489
  · exact context_11_5259_182777

theorem selected_cut_06010 : selected 9 ⟨182829, by decide⟩
    (prefixPartial 12 21040) = some ⟨12, 2, 0, 182829, 21040, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_21040_182829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21040 ⟨182829, by decide⟩ :=
  accepted_of_selected 12 21040 ⟨182829, by decide⟩ ⟨12, 2, 0, 182829, 21040, 3753, 65536⟩
    (by decide) selected_cut_06010

theorem selected_cut_06011 : selected 8 ⟨182840, by decide⟩
    (prefixPartial 13 84164) = some ⟨13, 2, 0, 182840, 84164, 637, 16384⟩ := by
  decide +kernel

theorem context_13_84164_182840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84164 ⟨182840, by decide⟩ :=
  accepted_of_selected 13 84164 ⟨182840, by decide⟩ ⟨13, 2, 0, 182840, 84164, 637, 16384⟩
    (by decide) selected_cut_06011

theorem selected_cut_06012 : selected 8 ⟨182867, by decide⟩
    (prefixPartial 13 84165) = some ⟨13, 2, 0, 182867, 84165, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_84165_182867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84165 ⟨182867, by decide⟩ :=
  accepted_of_selected 13 84165 ⟨182867, by decide⟩ ⟨13, 2, 0, 182867, 84165, 1821, 16384⟩
    (by decide) selected_cut_06012

theorem selected_cut_06013 : selected 8 ⟨182883, by decide⟩
    (prefixPartial 13 84166) = some ⟨13, 2, 0, 182883, 84166, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_84166_182883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84166 ⟨182883, by decide⟩ :=
  accepted_of_selected 13 84166 ⟨182883, by decide⟩ ⟨13, 2, 0, 182883, 84166, 1197, 16384⟩
    (by decide) selected_cut_06013

theorem selected_cut_06014 : selected 8 ⟨182888, by decide⟩
    (prefixPartial 13 84167) = some ⟨13, 2, 0, 182888, 84167, 617, 16384⟩ := by
  decide +kernel

theorem context_13_84167_182888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84167 ⟨182888, by decide⟩ :=
  accepted_of_selected 13 84167 ⟨182888, by decide⟩ ⟨13, 2, 0, 182888, 84167, 617, 16384⟩
    (by decide) selected_cut_06014

theorem unmarked_context_12_21041_182889 : frontier 9 ⟨182889, by decide⟩
    (prefixCache 12 21041) (prefixPartial 12 21041) = false := by
  decide +kernel

theorem node_context_12_21041_182889 : EJMOriginalGlobalDAGData.nodes 9 ⟨182889, by decide⟩ =
    .split (coordinate 12) (![⟨182840, by decide⟩,⟨182867, by decide⟩,⟨182883, by decide⟩,⟨182888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21041_182889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21041 ⟨182889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21041
    ⟨182889, by decide⟩ (by decide) (![⟨182840, by decide⟩,⟨182867, by decide⟩,⟨182883, by decide⟩,⟨182888, by decide⟩]) unmarked_context_12_21041_182889 node_context_12_21041_182889
  intro a
  fin_cases a
  · exact context_13_84164_182840
  · exact context_13_84165_182867
  · exact context_13_84166_182883
  · exact context_13_84167_182888

theorem selected_cut_06015 : selected 8 ⟨182898, by decide⟩
    (prefixPartial 13 84168) = some ⟨13, 2, 0, 182898, 84168, 593, 16384⟩ := by
  decide +kernel

theorem context_13_84168_182898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84168 ⟨182898, by decide⟩ :=
  accepted_of_selected 13 84168 ⟨182898, by decide⟩ ⟨13, 2, 0, 182898, 84168, 593, 16384⟩
    (by decide) selected_cut_06015

theorem selected_cut_06016 : selected 8 ⟨182930, by decide⟩
    (prefixPartial 13 84169) = some ⟨13, 2, 0, 182930, 84169, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_84169_182930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84169 ⟨182930, by decide⟩ :=
  accepted_of_selected 13 84169 ⟨182930, by decide⟩ ⟨13, 2, 0, 182930, 84169, 2077, 16384⟩
    (by decide) selected_cut_06016

theorem selected_cut_06017 : selected 8 ⟨182943, by decide⟩
    (prefixPartial 13 84170) = some ⟨13, 2, 0, 182943, 84170, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_84170_182943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84170 ⟨182943, by decide⟩ :=
  accepted_of_selected 13 84170 ⟨182943, by decide⟩ ⟨13, 2, 0, 182943, 84170, 1169, 16384⟩
    (by decide) selected_cut_06017

theorem selected_cut_06018 : selected 8 ⟨182947, by decide⟩
    (prefixPartial 13 84171) = some ⟨13, 2, 0, 182947, 84171, 605, 16384⟩ := by
  decide +kernel

theorem context_13_84171_182947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84171 ⟨182947, by decide⟩ :=
  accepted_of_selected 13 84171 ⟨182947, by decide⟩ ⟨13, 2, 0, 182947, 84171, 605, 16384⟩
    (by decide) selected_cut_06018

theorem unmarked_context_12_21042_182948 : frontier 9 ⟨182948, by decide⟩
    (prefixCache 12 21042) (prefixPartial 12 21042) = false := by
  decide +kernel

theorem node_context_12_21042_182948 : EJMOriginalGlobalDAGData.nodes 9 ⟨182948, by decide⟩ =
    .split (coordinate 12) (![⟨182898, by decide⟩,⟨182930, by decide⟩,⟨182943, by decide⟩,⟨182947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21042_182948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21042 ⟨182948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21042
    ⟨182948, by decide⟩ (by decide) (![⟨182898, by decide⟩,⟨182930, by decide⟩,⟨182943, by decide⟩,⟨182947, by decide⟩]) unmarked_context_12_21042_182948 node_context_12_21042_182948
  intro a
  fin_cases a
  · exact context_13_84168_182898
  · exact context_13_84169_182930
  · exact context_13_84170_182943
  · exact context_13_84171_182947

theorem selected_cut_06019 : selected 8 ⟨182961, by decide⟩
    (prefixPartial 13 84172) = some ⟨13, 2, 0, 182961, 84172, 629, 16384⟩ := by
  decide +kernel

theorem context_13_84172_182961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84172 ⟨182961, by decide⟩ :=
  accepted_of_selected 13 84172 ⟨182961, by decide⟩ ⟨13, 2, 0, 182961, 84172, 629, 16384⟩
    (by decide) selected_cut_06019

theorem selected_cut_06020 : selected 8 ⟨182999, by decide⟩
    (prefixPartial 13 84173) = some ⟨13, 2, 0, 182999, 84173, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_84173_182999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84173 ⟨182999, by decide⟩ :=
  accepted_of_selected 13 84173 ⟨182999, by decide⟩ ⟨13, 2, 0, 182999, 84173, 2301, 16384⟩
    (by decide) selected_cut_06020

theorem selected_cut_06021 : selected 8 ⟨183016, by decide⟩
    (prefixPartial 13 84174) = some ⟨13, 2, 0, 183016, 84174, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_84174_183016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84174 ⟨183016, by decide⟩ :=
  accepted_of_selected 13 84174 ⟨183016, by decide⟩ ⟨13, 2, 0, 183016, 84174, 1321, 16384⟩
    (by decide) selected_cut_06021

theorem selected_cut_06022 : selected 8 ⟨183023, by decide⟩
    (prefixPartial 13 84175) = some ⟨13, 2, 0, 183023, 84175, 653, 16384⟩ := by
  decide +kernel

theorem context_13_84175_183023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84175 ⟨183023, by decide⟩ :=
  accepted_of_selected 13 84175 ⟨183023, by decide⟩ ⟨13, 2, 0, 183023, 84175, 653, 16384⟩
    (by decide) selected_cut_06022

theorem unmarked_context_12_21043_183024 : frontier 9 ⟨183024, by decide⟩
    (prefixCache 12 21043) (prefixPartial 12 21043) = false := by
  decide +kernel

theorem node_context_12_21043_183024 : EJMOriginalGlobalDAGData.nodes 9 ⟨183024, by decide⟩ =
    .split (coordinate 12) (![⟨182961, by decide⟩,⟨182999, by decide⟩,⟨183016, by decide⟩,⟨183023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21043_183024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21043 ⟨183024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21043
    ⟨183024, by decide⟩ (by decide) (![⟨182961, by decide⟩,⟨182999, by decide⟩,⟨183016, by decide⟩,⟨183023, by decide⟩]) unmarked_context_12_21043_183024 node_context_12_21043_183024
  intro a
  fin_cases a
  · exact context_13_84172_182961
  · exact context_13_84173_182999
  · exact context_13_84174_183016
  · exact context_13_84175_183023

theorem unmarked_context_11_5260_183025 : frontier 10 ⟨183025, by decide⟩
    (prefixCache 11 5260) (prefixPartial 11 5260) = false := by
  decide +kernel

theorem node_context_11_5260_183025 : EJMOriginalGlobalDAGData.nodes 10 ⟨183025, by decide⟩ =
    .split (coordinate 11) (![⟨182829, by decide⟩,⟨182889, by decide⟩,⟨182948, by decide⟩,⟨183024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5260_183025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5260 ⟨183025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5260
    ⟨183025, by decide⟩ (by decide) (![⟨182829, by decide⟩,⟨182889, by decide⟩,⟨182948, by decide⟩,⟨183024, by decide⟩]) unmarked_context_11_5260_183025 node_context_11_5260_183025
  intro a
  fin_cases a
  · exact context_12_21040_182829
  · exact context_12_21041_182889
  · exact context_12_21042_182948
  · exact context_12_21043_183024

theorem selected_cut_06023 : selected 8 ⟨183033, by decide⟩
    (prefixPartial 13 84176) = some ⟨13, 2, 0, 183033, 84176, 545, 16384⟩ := by
  decide +kernel

theorem context_13_84176_183033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84176 ⟨183033, by decide⟩ :=
  accepted_of_selected 13 84176 ⟨183033, by decide⟩ ⟨13, 2, 0, 183033, 84176, 545, 16384⟩
    (by decide) selected_cut_06023

theorem selected_cut_06024 : selected 8 ⟨183061, by decide⟩
    (prefixPartial 13 84177) = some ⟨13, 2, 0, 183061, 84177, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_84177_183061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84177 ⟨183061, by decide⟩ :=
  accepted_of_selected 13 84177 ⟨183061, by decide⟩ ⟨13, 2, 0, 183061, 84177, 2241, 16384⟩
    (by decide) selected_cut_06024

theorem selected_cut_06025 : selected 8 ⟨183075, by decide⟩
    (prefixPartial 13 84178) = some ⟨13, 2, 0, 183075, 84178, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_84178_183075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84178 ⟨183075, by decide⟩ :=
  accepted_of_selected 13 84178 ⟨183075, by decide⟩ ⟨13, 2, 0, 183075, 84178, 1149, 16384⟩
    (by decide) selected_cut_06025

theorem selected_cut_06026 : selected 8 ⟨183082, by decide⟩
    (prefixPartial 13 84179) = some ⟨13, 2, 0, 183082, 84179, 701, 16384⟩ := by
  decide +kernel

theorem context_13_84179_183082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84179 ⟨183082, by decide⟩ :=
  accepted_of_selected 13 84179 ⟨183082, by decide⟩ ⟨13, 2, 0, 183082, 84179, 701, 16384⟩
    (by decide) selected_cut_06026

theorem unmarked_context_12_21044_183083 : frontier 9 ⟨183083, by decide⟩
    (prefixCache 12 21044) (prefixPartial 12 21044) = false := by
  decide +kernel

theorem node_context_12_21044_183083 : EJMOriginalGlobalDAGData.nodes 9 ⟨183083, by decide⟩ =
    .split (coordinate 12) (![⟨183033, by decide⟩,⟨183061, by decide⟩,⟨183075, by decide⟩,⟨183082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21044_183083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21044 ⟨183083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21044
    ⟨183083, by decide⟩ (by decide) (![⟨183033, by decide⟩,⟨183061, by decide⟩,⟨183075, by decide⟩,⟨183082, by decide⟩]) unmarked_context_12_21044_183083 node_context_12_21044_183083
  intro a
  fin_cases a
  · exact context_13_84176_183033
  · exact context_13_84177_183061
  · exact context_13_84178_183075
  · exact context_13_84179_183082

theorem selected_cut_06027 : selected 8 ⟨183088, by decide⟩
    (prefixPartial 13 84180) = some ⟨13, 2, 0, 183088, 84180, 493, 16384⟩ := by
  decide +kernel

theorem context_13_84180_183088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84180 ⟨183088, by decide⟩ :=
  accepted_of_selected 13 84180 ⟨183088, by decide⟩ ⟨13, 2, 0, 183088, 84180, 493, 16384⟩
    (by decide) selected_cut_06027

theorem selected_cut_06028 : selected 8 ⟨183116, by decide⟩
    (prefixPartial 13 84181) = some ⟨13, 2, 0, 183116, 84181, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_84181_183116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84181 ⟨183116, by decide⟩ :=
  accepted_of_selected 13 84181 ⟨183116, by decide⟩ ⟨13, 2, 0, 183116, 84181, 2261, 16384⟩
    (by decide) selected_cut_06028

theorem selected_cut_06029 : selected 8 ⟨183134, by decide⟩
    (prefixPartial 13 84182) = some ⟨13, 2, 0, 183134, 84182, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_84182_183134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84182 ⟨183134, by decide⟩ :=
  accepted_of_selected 13 84182 ⟨183134, by decide⟩ ⟨13, 2, 0, 183134, 84182, 1197, 16384⟩
    (by decide) selected_cut_06029

theorem selected_cut_06030 : selected 8 ⟨183141, by decide⟩
    (prefixPartial 13 84183) = some ⟨13, 2, 0, 183141, 84183, 673, 16384⟩ := by
  decide +kernel

theorem context_13_84183_183141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84183 ⟨183141, by decide⟩ :=
  accepted_of_selected 13 84183 ⟨183141, by decide⟩ ⟨13, 2, 0, 183141, 84183, 673, 16384⟩
    (by decide) selected_cut_06030

theorem unmarked_context_12_21045_183142 : frontier 9 ⟨183142, by decide⟩
    (prefixCache 12 21045) (prefixPartial 12 21045) = false := by
  decide +kernel

theorem node_context_12_21045_183142 : EJMOriginalGlobalDAGData.nodes 9 ⟨183142, by decide⟩ =
    .split (coordinate 12) (![⟨183088, by decide⟩,⟨183116, by decide⟩,⟨183134, by decide⟩,⟨183141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21045_183142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21045 ⟨183142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21045
    ⟨183142, by decide⟩ (by decide) (![⟨183088, by decide⟩,⟨183116, by decide⟩,⟨183134, by decide⟩,⟨183141, by decide⟩]) unmarked_context_12_21045_183142 node_context_12_21045_183142
  intro a
  fin_cases a
  · exact context_13_84180_183088
  · exact context_13_84181_183116
  · exact context_13_84182_183134
  · exact context_13_84183_183141

theorem selected_cut_06031 : selected 8 ⟨183149, by decide⟩
    (prefixPartial 13 84184) = some ⟨13, 2, 0, 183149, 84184, 449, 16384⟩ := by
  decide +kernel

theorem context_13_84184_183149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84184 ⟨183149, by decide⟩ :=
  accepted_of_selected 13 84184 ⟨183149, by decide⟩ ⟨13, 2, 0, 183149, 84184, 449, 16384⟩
    (by decide) selected_cut_06031

theorem selected_cut_06032 : selected 8 ⟨183182, by decide⟩
    (prefixPartial 13 84185) = some ⟨13, 2, 0, 183182, 84185, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_84185_183182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84185 ⟨183182, by decide⟩ :=
  accepted_of_selected 13 84185 ⟨183182, by decide⟩ ⟨13, 2, 0, 183182, 84185, 2385, 16384⟩
    (by decide) selected_cut_06032

theorem selected_cut_06033 : selected 8 ⟨183198, by decide⟩
    (prefixPartial 13 84186) = some ⟨13, 2, 0, 183198, 84186, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_84186_183198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84186 ⟨183198, by decide⟩ :=
  accepted_of_selected 13 84186 ⟨183198, by decide⟩ ⟨13, 2, 0, 183198, 84186, 1057, 16384⟩
    (by decide) selected_cut_06033

theorem selected_cut_06034 : selected 8 ⟨183205, by decide⟩
    (prefixPartial 13 84187) = some ⟨13, 2, 0, 183205, 84187, 693, 16384⟩ := by
  decide +kernel

theorem context_13_84187_183205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84187 ⟨183205, by decide⟩ :=
  accepted_of_selected 13 84187 ⟨183205, by decide⟩ ⟨13, 2, 0, 183205, 84187, 693, 16384⟩
    (by decide) selected_cut_06034

theorem unmarked_context_12_21046_183206 : frontier 9 ⟨183206, by decide⟩
    (prefixCache 12 21046) (prefixPartial 12 21046) = false := by
  decide +kernel

theorem node_context_12_21046_183206 : EJMOriginalGlobalDAGData.nodes 9 ⟨183206, by decide⟩ =
    .split (coordinate 12) (![⟨183149, by decide⟩,⟨183182, by decide⟩,⟨183198, by decide⟩,⟨183205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21046_183206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21046 ⟨183206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21046
    ⟨183206, by decide⟩ (by decide) (![⟨183149, by decide⟩,⟨183182, by decide⟩,⟨183198, by decide⟩,⟨183205, by decide⟩]) unmarked_context_12_21046_183206 node_context_12_21046_183206
  intro a
  fin_cases a
  · exact context_13_84184_183149
  · exact context_13_84185_183182
  · exact context_13_84186_183198
  · exact context_13_84187_183205

theorem selected_cut_06035 : selected 8 ⟨183216, by decide⟩
    (prefixPartial 13 84188) = some ⟨13, 2, 0, 183216, 84188, 485, 16384⟩ := by
  decide +kernel

theorem context_13_84188_183216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84188 ⟨183216, by decide⟩ :=
  accepted_of_selected 13 84188 ⟨183216, by decide⟩ ⟨13, 2, 0, 183216, 84188, 485, 16384⟩
    (by decide) selected_cut_06035

theorem selected_cut_06036 : selected 8 ⟨183246, by decide⟩
    (prefixPartial 13 84189) = some ⟨13, 2, 0, 183246, 84189, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_84189_183246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84189 ⟨183246, by decide⟩ :=
  accepted_of_selected 13 84189 ⟨183246, by decide⟩ ⟨13, 2, 0, 183246, 84189, 2593, 16384⟩
    (by decide) selected_cut_06036

theorem selected_cut_06037 : selected 8 ⟨183264, by decide⟩
    (prefixPartial 13 84190) = some ⟨13, 2, 0, 183264, 84190, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_84190_183264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84190 ⟨183264, by decide⟩ :=
  accepted_of_selected 13 84190 ⟨183264, by decide⟩ ⟨13, 2, 0, 183264, 84190, 1317, 16384⟩
    (by decide) selected_cut_06037

theorem selected_cut_06038 : selected 8 ⟨183272, by decide⟩
    (prefixPartial 13 84191) = some ⟨13, 2, 0, 183272, 84191, 733, 16384⟩ := by
  decide +kernel

theorem context_13_84191_183272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84191 ⟨183272, by decide⟩ :=
  accepted_of_selected 13 84191 ⟨183272, by decide⟩ ⟨13, 2, 0, 183272, 84191, 733, 16384⟩
    (by decide) selected_cut_06038

theorem unmarked_context_12_21047_183273 : frontier 9 ⟨183273, by decide⟩
    (prefixCache 12 21047) (prefixPartial 12 21047) = false := by
  decide +kernel

theorem node_context_12_21047_183273 : EJMOriginalGlobalDAGData.nodes 9 ⟨183273, by decide⟩ =
    .split (coordinate 12) (![⟨183216, by decide⟩,⟨183246, by decide⟩,⟨183264, by decide⟩,⟨183272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21047_183273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21047 ⟨183273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21047
    ⟨183273, by decide⟩ (by decide) (![⟨183216, by decide⟩,⟨183246, by decide⟩,⟨183264, by decide⟩,⟨183272, by decide⟩]) unmarked_context_12_21047_183273 node_context_12_21047_183273
  intro a
  fin_cases a
  · exact context_13_84188_183216
  · exact context_13_84189_183246
  · exact context_13_84190_183264
  · exact context_13_84191_183272

theorem unmarked_context_11_5261_183274 : frontier 10 ⟨183274, by decide⟩
    (prefixCache 11 5261) (prefixPartial 11 5261) = false := by
  decide +kernel

theorem node_context_11_5261_183274 : EJMOriginalGlobalDAGData.nodes 10 ⟨183274, by decide⟩ =
    .split (coordinate 11) (![⟨183083, by decide⟩,⟨183142, by decide⟩,⟨183206, by decide⟩,⟨183273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5261_183274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5261 ⟨183274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5261
    ⟨183274, by decide⟩ (by decide) (![⟨183083, by decide⟩,⟨183142, by decide⟩,⟨183206, by decide⟩,⟨183273, by decide⟩]) unmarked_context_11_5261_183274 node_context_11_5261_183274
  intro a
  fin_cases a
  · exact context_12_21044_183083
  · exact context_12_21045_183142
  · exact context_12_21046_183206
  · exact context_12_21047_183273

theorem selected_cut_06039 : selected 8 ⟨183280, by decide⟩
    (prefixPartial 13 84192) = some ⟨13, 2, 0, 183280, 84192, 445, 16384⟩ := by
  decide +kernel

theorem context_13_84192_183280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84192 ⟨183280, by decide⟩ :=
  accepted_of_selected 13 84192 ⟨183280, by decide⟩ ⟨13, 2, 0, 183280, 84192, 445, 16384⟩
    (by decide) selected_cut_06039

theorem selected_cut_06040 : selected 8 ⟨183306, by decide⟩
    (prefixPartial 13 84193) = some ⟨13, 2, 0, 183306, 84193, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_84193_183306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84193 ⟨183306, by decide⟩ :=
  accepted_of_selected 13 84193 ⟨183306, by decide⟩ ⟨13, 2, 0, 183306, 84193, 1969, 16384⟩
    (by decide) selected_cut_06040

theorem selected_cut_06041 : selected 8 ⟨183324, by decide⟩
    (prefixPartial 13 84194) = some ⟨13, 2, 0, 183324, 84194, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_84194_183324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84194 ⟨183324, by decide⟩ :=
  accepted_of_selected 13 84194 ⟨183324, by decide⟩ ⟨13, 2, 0, 183324, 84194, 1297, 16384⟩
    (by decide) selected_cut_06041

theorem selected_cut_06042 : selected 8 ⟨183331, by decide⟩
    (prefixPartial 13 84195) = some ⟨13, 2, 0, 183331, 84195, 701, 16384⟩ := by
  decide +kernel

theorem context_13_84195_183331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84195 ⟨183331, by decide⟩ :=
  accepted_of_selected 13 84195 ⟨183331, by decide⟩ ⟨13, 2, 0, 183331, 84195, 701, 16384⟩
    (by decide) selected_cut_06042

theorem unmarked_context_12_21048_183332 : frontier 9 ⟨183332, by decide⟩
    (prefixCache 12 21048) (prefixPartial 12 21048) = false := by
  decide +kernel

theorem node_context_12_21048_183332 : EJMOriginalGlobalDAGData.nodes 9 ⟨183332, by decide⟩ =
    .split (coordinate 12) (![⟨183280, by decide⟩,⟨183306, by decide⟩,⟨183324, by decide⟩,⟨183331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21048_183332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21048 ⟨183332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21048
    ⟨183332, by decide⟩ (by decide) (![⟨183280, by decide⟩,⟨183306, by decide⟩,⟨183324, by decide⟩,⟨183331, by decide⟩]) unmarked_context_12_21048_183332 node_context_12_21048_183332
  intro a
  fin_cases a
  · exact context_13_84192_183280
  · exact context_13_84193_183306
  · exact context_13_84194_183324
  · exact context_13_84195_183331

theorem selected_cut_06043 : selected 8 ⟨183338, by decide⟩
    (prefixPartial 13 84196) = some ⟨13, 2, 0, 183338, 84196, 417, 16384⟩ := by
  decide +kernel

theorem context_13_84196_183338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84196 ⟨183338, by decide⟩ :=
  accepted_of_selected 13 84196 ⟨183338, by decide⟩ ⟨13, 2, 0, 183338, 84196, 417, 16384⟩
    (by decide) selected_cut_06043

theorem selected_cut_06044 : selected 8 ⟨183368, by decide⟩
    (prefixPartial 13 84197) = some ⟨13, 2, 0, 183368, 84197, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_84197_183368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84197 ⟨183368, by decide⟩ :=
  accepted_of_selected 13 84197 ⟨183368, by decide⟩ ⟨13, 2, 0, 183368, 84197, 2233, 16384⟩
    (by decide) selected_cut_06044

theorem selected_cut_06045 : selected 8 ⟨183388, by decide⟩
    (prefixPartial 13 84198) = some ⟨13, 2, 0, 183388, 84198, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_84198_183388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84198 ⟨183388, by decide⟩ :=
  accepted_of_selected 13 84198 ⟨183388, by decide⟩ ⟨13, 2, 0, 183388, 84198, 1509, 16384⟩
    (by decide) selected_cut_06045

theorem selected_cut_06046 : selected 8 ⟨183397, by decide⟩
    (prefixPartial 13 84199) = some ⟨13, 2, 0, 183397, 84199, 789, 16384⟩ := by
  decide +kernel

theorem context_13_84199_183397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84199 ⟨183397, by decide⟩ :=
  accepted_of_selected 13 84199 ⟨183397, by decide⟩ ⟨13, 2, 0, 183397, 84199, 789, 16384⟩
    (by decide) selected_cut_06046

theorem unmarked_context_12_21049_183398 : frontier 9 ⟨183398, by decide⟩
    (prefixCache 12 21049) (prefixPartial 12 21049) = false := by
  decide +kernel

theorem node_context_12_21049_183398 : EJMOriginalGlobalDAGData.nodes 9 ⟨183398, by decide⟩ =
    .split (coordinate 12) (![⟨183338, by decide⟩,⟨183368, by decide⟩,⟨183388, by decide⟩,⟨183397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21049_183398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21049 ⟨183398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21049
    ⟨183398, by decide⟩ (by decide) (![⟨183338, by decide⟩,⟨183368, by decide⟩,⟨183388, by decide⟩,⟨183397, by decide⟩]) unmarked_context_12_21049_183398 node_context_12_21049_183398
  intro a
  fin_cases a
  · exact context_13_84196_183338
  · exact context_13_84197_183368
  · exact context_13_84198_183388
  · exact context_13_84199_183397

theorem selected_cut_06047 : selected 8 ⟨183408, by decide⟩
    (prefixPartial 13 84200) = some ⟨13, 2, 0, 183408, 84200, 513, 16384⟩ := by
  decide +kernel

theorem context_13_84200_183408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84200 ⟨183408, by decide⟩ :=
  accepted_of_selected 13 84200 ⟨183408, by decide⟩ ⟨13, 2, 0, 183408, 84200, 513, 16384⟩
    (by decide) selected_cut_06047

theorem selected_cut_06048 : selected 7 ⟨183429, by decide⟩
    (prefixPartial 14 336804) = some ⟨14, 2, 0, 183429, 336804, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_336804_183429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336804 ⟨183429, by decide⟩ :=
  accepted_of_selected 14 336804 ⟨183429, by decide⟩ ⟨14, 2, 0, 183429, 336804, 1169, 4096⟩
    (by decide) selected_cut_06048

theorem selected_cut_06049 : selected 7 ⟨183450, by decide⟩
    (prefixPartial 14 336805) = some ⟨14, 2, 0, 183450, 336805, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_336805_183450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336805 ⟨183450, by decide⟩ :=
  accepted_of_selected 14 336805 ⟨183450, by decide⟩ ⟨14, 2, 0, 183450, 336805, 1161, 4096⟩
    (by decide) selected_cut_06049

theorem selected_cut_06050 : selected 7 ⟨183465, by decide⟩
    (prefixPartial 14 336806) = some ⟨14, 2, 0, 183465, 336806, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_336806_183465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336806 ⟨183465, by decide⟩ :=
  accepted_of_selected 14 336806 ⟨183465, by decide⟩ ⟨14, 2, 0, 183465, 336806, 1041, 4096⟩
    (by decide) selected_cut_06050

theorem selected_cut_06051 : selected 7 ⟨183476, by decide⟩
    (prefixPartial 14 336807) = some ⟨14, 2, 0, 183476, 336807, 913, 4096⟩ := by
  decide +kernel

theorem context_14_336807_183476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336807 ⟨183476, by decide⟩ :=
  accepted_of_selected 14 336807 ⟨183476, by decide⟩ ⟨14, 2, 0, 183476, 336807, 913, 4096⟩
    (by decide) selected_cut_06051

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
