/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover332
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_107787_821556 : frontier 9 ⟨821556, by decide⟩
    (prefixCache 12 107787) (prefixPartial 12 107787) = false := by
  decide +kernel

theorem node_context_12_107787_821556 : EJMOriginalGlobalDAGData.nodes 9 ⟨821556, by decide⟩ =
    .split (coordinate 12) (![⟨821328, by decide⟩,⟨821417, by decide⟩,⟨821520, by decide⟩,⟨821555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107787_821556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107787 ⟨821556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107787
    ⟨821556, by decide⟩ (by decide) (![⟨821328, by decide⟩,⟨821417, by decide⟩,⟨821520, by decide⟩,⟨821555, by decide⟩]) unmarked_context_12_107787_821556 node_context_12_107787_821556
  intro a
  fin_cases a
  · exact context_13_431148_821328
  · exact context_13_431149_821417
  · exact context_13_431150_821520
  · exact context_13_431151_821555

theorem unmarked_context_11_26946_821557 : frontier 10 ⟨821557, by decide⟩
    (prefixCache 11 26946) (prefixPartial 11 26946) = false := by
  decide +kernel

theorem node_context_11_26946_821557 : EJMOriginalGlobalDAGData.nodes 10 ⟨821557, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨821229, by decide⟩,⟨763842, by decide⟩,⟨821556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26946_821557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26946 ⟨821557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26946
    ⟨821557, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨821229, by decide⟩,⟨763842, by decide⟩,⟨821556, by decide⟩]) unmarked_context_11_26946_821557 node_context_11_26946_821557
  intro a
  fin_cases a
  · exact context_12_107784_448748
  · exact context_12_107785_821229
  · exact context_12_107786_763842
  · exact context_12_107787_821556

theorem selected_cut_31972 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 107788) = some ⟨12, 1, 0, 448748, 107788, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107788_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107788 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 107788 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 107788, 1, 65536⟩
    (by decide) selected_cut_31972

theorem selected_cut_31973 : selected 8 ⟨821621, by decide⟩
    (prefixPartial 13 431156) = some ⟨13, 2, 0, 821621, 431156, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_431156_821621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431156 ⟨821621, by decide⟩ :=
  accepted_of_selected 13 431156 ⟨821621, by decide⟩ ⟨13, 2, 0, 821621, 431156, 3209, 16384⟩
    (by decide) selected_cut_31973

theorem selected_cut_31974 : selected 8 ⟨821700, by decide⟩
    (prefixPartial 13 431157) = some ⟨13, 2, 0, 821700, 431157, 3701, 16384⟩ := by
  decide +kernel

theorem context_13_431157_821700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431157 ⟨821700, by decide⟩ :=
  accepted_of_selected 13 431157 ⟨821700, by decide⟩ ⟨13, 2, 0, 821700, 431157, 3701, 16384⟩
    (by decide) selected_cut_31974

theorem selected_cut_31975 : selected 8 ⟨821756, by decide⟩
    (prefixPartial 13 431158) = some ⟨13, 2, 0, 821756, 431158, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_431158_821756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431158 ⟨821756, by decide⟩ :=
  accepted_of_selected 13 431158 ⟨821756, by decide⟩ ⟨13, 2, 0, 821756, 431158, 1925, 16384⟩
    (by decide) selected_cut_31975

theorem selected_cut_31976 : selected 8 ⟨821770, by decide⟩
    (prefixPartial 13 431159) = some ⟨13, 2, 0, 821770, 431159, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_431159_821770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431159 ⟨821770, by decide⟩ :=
  accepted_of_selected 13 431159 ⟨821770, by decide⟩ ⟨13, 2, 0, 821770, 431159, 1141, 16384⟩
    (by decide) selected_cut_31976

theorem unmarked_context_12_107789_821771 : frontier 9 ⟨821771, by decide⟩
    (prefixCache 12 107789) (prefixPartial 12 107789) = false := by
  decide +kernel

theorem node_context_12_107789_821771 : EJMOriginalGlobalDAGData.nodes 9 ⟨821771, by decide⟩ =
    .split (coordinate 12) (![⟨821621, by decide⟩,⟨821700, by decide⟩,⟨821756, by decide⟩,⟨821770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107789_821771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107789 ⟨821771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107789
    ⟨821771, by decide⟩ (by decide) (![⟨821621, by decide⟩,⟨821700, by decide⟩,⟨821756, by decide⟩,⟨821770, by decide⟩]) unmarked_context_12_107789_821771 node_context_12_107789_821771
  intro a
  fin_cases a
  · exact context_13_431156_821621
  · exact context_13_431157_821700
  · exact context_13_431158_821756
  · exact context_13_431159_821770

theorem selected_cut_31977 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 107790) = some ⟨12, 1, 0, 763842, 107790, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107790_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107790 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 107790 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 107790, 1, 65536⟩
    (by decide) selected_cut_31977

theorem selected_cut_31978 : selected 9 ⟨815334, by decide⟩
    (prefixPartial 12 107791) = some ⟨12, 1, 0, 815334, 107791, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107791_815334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107791 ⟨815334, by decide⟩ :=
  accepted_of_selected 12 107791 ⟨815334, by decide⟩ ⟨12, 1, 0, 815334, 107791, 1, 65536⟩
    (by decide) selected_cut_31978

theorem unmarked_context_11_26947_821772 : frontier 10 ⟨821772, by decide⟩
    (prefixCache 11 26947) (prefixPartial 11 26947) = false := by
  decide +kernel

theorem node_context_11_26947_821772 : EJMOriginalGlobalDAGData.nodes 10 ⟨821772, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨821771, by decide⟩,⟨763842, by decide⟩,⟨815334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26947_821772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26947 ⟨821772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26947
    ⟨821772, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨821771, by decide⟩,⟨763842, by decide⟩,⟨815334, by decide⟩]) unmarked_context_11_26947_821772 node_context_11_26947_821772
  intro a
  fin_cases a
  · exact context_12_107788_448748
  · exact context_12_107789_821771
  · exact context_12_107790_763842
  · exact context_12_107791_815334

theorem unmarked_context_10_6736_821773 : frontier 11 ⟨821773, by decide⟩
    (prefixCache 10 6736) (prefixPartial 10 6736) = false := by
  decide +kernel

theorem node_context_10_6736_821773 : EJMOriginalGlobalDAGData.nodes 11 ⟨821773, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨821557, by decide⟩,⟨821772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6736_821773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6736 ⟨821773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6736
    ⟨821773, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨821557, by decide⟩,⟨821772, by decide⟩]) unmarked_context_10_6736_821773 node_context_10_6736_821773
  intro a
  fin_cases a
  · exact context_11_26944_434745
  · exact context_11_26945_167448
  · exact context_11_26946_821557
  · exact context_11_26947_821772

theorem selected_cut_31979 : selected 8 ⟨821802, by decide⟩
    (prefixPartial 13 431168) = some ⟨13, 2, 0, 821802, 431168, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_431168_821802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431168 ⟨821802, by decide⟩ :=
  accepted_of_selected 13 431168 ⟨821802, by decide⟩ ⟨13, 2, 0, 821802, 431168, 1765, 16384⟩
    (by decide) selected_cut_31979

theorem selected_cut_31980 : selected 8 ⟨821834, by decide⟩
    (prefixPartial 13 431169) = some ⟨13, 2, 0, 821834, 431169, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_431169_821834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431169 ⟨821834, by decide⟩ :=
  accepted_of_selected 13 431169 ⟨821834, by decide⟩ ⟨13, 2, 0, 821834, 431169, 2593, 16384⟩
    (by decide) selected_cut_31980

theorem selected_cut_31981 : selected 8 ⟨821859, by decide⟩
    (prefixPartial 13 431170) = some ⟨13, 2, 0, 821859, 431170, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_431170_821859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431170 ⟨821859, by decide⟩ :=
  accepted_of_selected 13 431170 ⟨821859, by decide⟩ ⟨13, 2, 0, 821859, 431170, 1325, 16384⟩
    (by decide) selected_cut_31981

theorem selected_cut_31982 : selected 8 ⟨821864, by decide⟩
    (prefixPartial 13 431171) = some ⟨13, 2, 0, 821864, 431171, 833, 16384⟩ := by
  decide +kernel

theorem context_13_431171_821864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431171 ⟨821864, by decide⟩ :=
  accepted_of_selected 13 431171 ⟨821864, by decide⟩ ⟨13, 2, 0, 821864, 431171, 833, 16384⟩
    (by decide) selected_cut_31982

theorem unmarked_context_12_107792_821865 : frontier 9 ⟨821865, by decide⟩
    (prefixCache 12 107792) (prefixPartial 12 107792) = false := by
  decide +kernel

theorem node_context_12_107792_821865 : EJMOriginalGlobalDAGData.nodes 9 ⟨821865, by decide⟩ =
    .split (coordinate 12) (![⟨821802, by decide⟩,⟨821834, by decide⟩,⟨821859, by decide⟩,⟨821864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107792_821865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107792 ⟨821865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107792
    ⟨821865, by decide⟩ (by decide) (![⟨821802, by decide⟩,⟨821834, by decide⟩,⟨821859, by decide⟩,⟨821864, by decide⟩]) unmarked_context_12_107792_821865 node_context_12_107792_821865
  intro a
  fin_cases a
  · exact context_13_431168_821802
  · exact context_13_431169_821834
  · exact context_13_431170_821859
  · exact context_13_431171_821864

theorem selected_cut_31983 : selected 8 ⟨821892, by decide⟩
    (prefixPartial 13 431172) = some ⟨13, 2, 0, 821892, 431172, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_431172_821892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431172 ⟨821892, by decide⟩ :=
  accepted_of_selected 13 431172 ⟨821892, by decide⟩ ⟨13, 2, 0, 821892, 431172, 1705, 16384⟩
    (by decide) selected_cut_31983

theorem selected_cut_31984 : selected 8 ⟨821915, by decide⟩
    (prefixPartial 13 431173) = some ⟨13, 2, 0, 821915, 431173, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_431173_821915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431173 ⟨821915, by decide⟩ :=
  accepted_of_selected 13 431173 ⟨821915, by decide⟩ ⟨13, 2, 0, 821915, 431173, 2353, 16384⟩
    (by decide) selected_cut_31984

theorem selected_cut_31985 : selected 8 ⟨821936, by decide⟩
    (prefixPartial 13 431174) = some ⟨13, 2, 0, 821936, 431174, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_431174_821936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431174 ⟨821936, by decide⟩ :=
  accepted_of_selected 13 431174 ⟨821936, by decide⟩ ⟨13, 2, 0, 821936, 431174, 1181, 16384⟩
    (by decide) selected_cut_31985

theorem selected_cut_31986 : selected 8 ⟨821942, by decide⟩
    (prefixPartial 13 431175) = some ⟨13, 2, 0, 821942, 431175, 717, 16384⟩ := by
  decide +kernel

theorem context_13_431175_821942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431175 ⟨821942, by decide⟩ :=
  accepted_of_selected 13 431175 ⟨821942, by decide⟩ ⟨13, 2, 0, 821942, 431175, 717, 16384⟩
    (by decide) selected_cut_31986

theorem unmarked_context_12_107793_821943 : frontier 9 ⟨821943, by decide⟩
    (prefixCache 12 107793) (prefixPartial 12 107793) = false := by
  decide +kernel

theorem node_context_12_107793_821943 : EJMOriginalGlobalDAGData.nodes 9 ⟨821943, by decide⟩ =
    .split (coordinate 12) (![⟨821892, by decide⟩,⟨821915, by decide⟩,⟨821936, by decide⟩,⟨821942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107793_821943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107793 ⟨821943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107793
    ⟨821943, by decide⟩ (by decide) (![⟨821892, by decide⟩,⟨821915, by decide⟩,⟨821936, by decide⟩,⟨821942, by decide⟩]) unmarked_context_12_107793_821943 node_context_12_107793_821943
  intro a
  fin_cases a
  · exact context_13_431172_821892
  · exact context_13_431173_821915
  · exact context_13_431174_821936
  · exact context_13_431175_821942

theorem selected_cut_31987 : selected 8 ⟨821968, by decide⟩
    (prefixPartial 13 431176) = some ⟨13, 2, 0, 821968, 431176, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_431176_821968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431176 ⟨821968, by decide⟩ :=
  accepted_of_selected 13 431176 ⟨821968, by decide⟩ ⟨13, 2, 0, 821968, 431176, 1733, 16384⟩
    (by decide) selected_cut_31987

theorem selected_cut_31988 : selected 8 ⟨822008, by decide⟩
    (prefixPartial 13 431177) = some ⟨13, 2, 0, 822008, 431177, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_431177_822008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431177 ⟨822008, by decide⟩ :=
  accepted_of_selected 13 431177 ⟨822008, by decide⟩ ⟨13, 2, 0, 822008, 431177, 2545, 16384⟩
    (by decide) selected_cut_31988

theorem selected_cut_31989 : selected 8 ⟨822027, by decide⟩
    (prefixPartial 13 431178) = some ⟨13, 2, 0, 822027, 431178, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_431178_822027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431178 ⟨822027, by decide⟩ :=
  accepted_of_selected 13 431178 ⟨822027, by decide⟩ ⟨13, 2, 0, 822027, 431178, 1173, 16384⟩
    (by decide) selected_cut_31989

theorem selected_cut_31990 : selected 8 ⟨822034, by decide⟩
    (prefixPartial 13 431179) = some ⟨13, 2, 0, 822034, 431179, 833, 16384⟩ := by
  decide +kernel

theorem context_13_431179_822034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431179 ⟨822034, by decide⟩ :=
  accepted_of_selected 13 431179 ⟨822034, by decide⟩ ⟨13, 2, 0, 822034, 431179, 833, 16384⟩
    (by decide) selected_cut_31990

theorem unmarked_context_12_107794_822035 : frontier 9 ⟨822035, by decide⟩
    (prefixCache 12 107794) (prefixPartial 12 107794) = false := by
  decide +kernel

theorem node_context_12_107794_822035 : EJMOriginalGlobalDAGData.nodes 9 ⟨822035, by decide⟩ =
    .split (coordinate 12) (![⟨821968, by decide⟩,⟨822008, by decide⟩,⟨822027, by decide⟩,⟨822034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107794_822035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107794 ⟨822035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107794
    ⟨822035, by decide⟩ (by decide) (![⟨821968, by decide⟩,⟨822008, by decide⟩,⟨822027, by decide⟩,⟨822034, by decide⟩]) unmarked_context_12_107794_822035 node_context_12_107794_822035
  intro a
  fin_cases a
  · exact context_13_431176_821968
  · exact context_13_431177_822008
  · exact context_13_431178_822027
  · exact context_13_431179_822034

theorem selected_cut_31991 : selected 8 ⟨822068, by decide⟩
    (prefixPartial 13 431180) = some ⟨13, 2, 0, 822068, 431180, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_431180_822068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431180 ⟨822068, by decide⟩ :=
  accepted_of_selected 13 431180 ⟨822068, by decide⟩ ⟨13, 2, 0, 822068, 431180, 2121, 16384⟩
    (by decide) selected_cut_31991

theorem selected_cut_31992 : selected 8 ⟨822113, by decide⟩
    (prefixPartial 13 431181) = some ⟨13, 2, 0, 822113, 431181, 3017, 16384⟩ := by
  decide +kernel

theorem context_13_431181_822113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431181 ⟨822113, by decide⟩ :=
  accepted_of_selected 13 431181 ⟨822113, by decide⟩ ⟨13, 2, 0, 822113, 431181, 3017, 16384⟩
    (by decide) selected_cut_31992

theorem selected_cut_31993 : selected 8 ⟨822138, by decide⟩
    (prefixPartial 13 431182) = some ⟨13, 2, 0, 822138, 431182, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_431182_822138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431182 ⟨822138, by decide⟩ :=
  accepted_of_selected 13 431182 ⟨822138, by decide⟩ ⟨13, 2, 0, 822138, 431182, 1437, 16384⟩
    (by decide) selected_cut_31993

theorem selected_cut_31994 : selected 8 ⟨822144, by decide⟩
    (prefixPartial 13 431183) = some ⟨13, 2, 0, 822144, 431183, 897, 16384⟩ := by
  decide +kernel

theorem context_13_431183_822144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431183 ⟨822144, by decide⟩ :=
  accepted_of_selected 13 431183 ⟨822144, by decide⟩ ⟨13, 2, 0, 822144, 431183, 897, 16384⟩
    (by decide) selected_cut_31994

theorem unmarked_context_12_107795_822145 : frontier 9 ⟨822145, by decide⟩
    (prefixCache 12 107795) (prefixPartial 12 107795) = false := by
  decide +kernel

theorem node_context_12_107795_822145 : EJMOriginalGlobalDAGData.nodes 9 ⟨822145, by decide⟩ =
    .split (coordinate 12) (![⟨822068, by decide⟩,⟨822113, by decide⟩,⟨822138, by decide⟩,⟨822144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107795_822145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107795 ⟨822145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107795
    ⟨822145, by decide⟩ (by decide) (![⟨822068, by decide⟩,⟨822113, by decide⟩,⟨822138, by decide⟩,⟨822144, by decide⟩]) unmarked_context_12_107795_822145 node_context_12_107795_822145
  intro a
  fin_cases a
  · exact context_13_431180_822068
  · exact context_13_431181_822113
  · exact context_13_431182_822138
  · exact context_13_431183_822144

theorem unmarked_context_11_26948_822146 : frontier 10 ⟨822146, by decide⟩
    (prefixCache 11 26948) (prefixPartial 11 26948) = false := by
  decide +kernel

theorem node_context_11_26948_822146 : EJMOriginalGlobalDAGData.nodes 10 ⟨822146, by decide⟩ =
    .split (coordinate 11) (![⟨821865, by decide⟩,⟨821943, by decide⟩,⟨822035, by decide⟩,⟨822145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26948_822146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26948 ⟨822146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26948
    ⟨822146, by decide⟩ (by decide) (![⟨821865, by decide⟩,⟨821943, by decide⟩,⟨822035, by decide⟩,⟨822145, by decide⟩]) unmarked_context_11_26948_822146 node_context_11_26948_822146
  intro a
  fin_cases a
  · exact context_12_107792_821865
  · exact context_12_107793_821943
  · exact context_12_107794_822035
  · exact context_12_107795_822145

theorem selected_cut_31995 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 26949) = some ⟨11, 1, 0, 815620, 26949, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26949_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26949 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 26949 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 26949, 1, 262144⟩
    (by decide) selected_cut_31995

theorem selected_cut_31996 : selected 8 ⟨822171, by decide⟩
    (prefixPartial 13 431200) = some ⟨13, 2, 0, 822171, 431200, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_431200_822171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431200 ⟨822171, by decide⟩ :=
  accepted_of_selected 13 431200 ⟨822171, by decide⟩ ⟨13, 2, 0, 822171, 431200, 1501, 16384⟩
    (by decide) selected_cut_31996

theorem selected_cut_31997 : selected 8 ⟨822205, by decide⟩
    (prefixPartial 13 431201) = some ⟨13, 2, 0, 822205, 431201, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_431201_822205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431201 ⟨822205, by decide⟩ :=
  accepted_of_selected 13 431201 ⟨822205, by decide⟩ ⟨13, 2, 0, 822205, 431201, 2441, 16384⟩
    (by decide) selected_cut_31997

theorem selected_cut_31998 : selected 8 ⟨822233, by decide⟩
    (prefixPartial 13 431202) = some ⟨13, 2, 0, 822233, 431202, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_431202_822233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431202 ⟨822233, by decide⟩ :=
  accepted_of_selected 13 431202 ⟨822233, by decide⟩ ⟨13, 2, 0, 822233, 431202, 1449, 16384⟩
    (by decide) selected_cut_31998

theorem selected_cut_31999 : selected 8 ⟨822241, by decide⟩
    (prefixPartial 13 431203) = some ⟨13, 2, 0, 822241, 431203, 885, 16384⟩ := by
  decide +kernel

theorem context_13_431203_822241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431203 ⟨822241, by decide⟩ :=
  accepted_of_selected 13 431203 ⟨822241, by decide⟩ ⟨13, 2, 0, 822241, 431203, 885, 16384⟩
    (by decide) selected_cut_31999

theorem unmarked_context_12_107800_822242 : frontier 9 ⟨822242, by decide⟩
    (prefixCache 12 107800) (prefixPartial 12 107800) = false := by
  decide +kernel

theorem node_context_12_107800_822242 : EJMOriginalGlobalDAGData.nodes 9 ⟨822242, by decide⟩ =
    .split (coordinate 12) (![⟨822171, by decide⟩,⟨822205, by decide⟩,⟨822233, by decide⟩,⟨822241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107800_822242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107800 ⟨822242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107800
    ⟨822242, by decide⟩ (by decide) (![⟨822171, by decide⟩,⟨822205, by decide⟩,⟨822233, by decide⟩,⟨822241, by decide⟩]) unmarked_context_12_107800_822242 node_context_12_107800_822242
  intro a
  fin_cases a
  · exact context_13_431200_822171
  · exact context_13_431201_822205
  · exact context_13_431202_822233
  · exact context_13_431203_822241

theorem selected_cut_32000 : selected 8 ⟨822267, by decide⟩
    (prefixPartial 13 431204) = some ⟨13, 2, 0, 822267, 431204, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_431204_822267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431204 ⟨822267, by decide⟩ :=
  accepted_of_selected 13 431204 ⟨822267, by decide⟩ ⟨13, 2, 0, 822267, 431204, 1649, 16384⟩
    (by decide) selected_cut_32000

theorem selected_cut_32001 : selected 8 ⟨822291, by decide⟩
    (prefixPartial 13 431205) = some ⟨13, 2, 0, 822291, 431205, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_431205_822291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431205 ⟨822291, by decide⟩ :=
  accepted_of_selected 13 431205 ⟨822291, by decide⟩ ⟨13, 2, 0, 822291, 431205, 1993, 16384⟩
    (by decide) selected_cut_32001

theorem selected_cut_32002 : selected 8 ⟨822312, by decide⟩
    (prefixPartial 13 431206) = some ⟨13, 2, 0, 822312, 431206, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_431206_822312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431206 ⟨822312, by decide⟩ :=
  accepted_of_selected 13 431206 ⟨822312, by decide⟩ ⟨13, 2, 0, 822312, 431206, 1397, 16384⟩
    (by decide) selected_cut_32002

theorem selected_cut_32003 : selected 8 ⟨822321, by decide⟩
    (prefixPartial 13 431207) = some ⟨13, 2, 0, 822321, 431207, 769, 16384⟩ := by
  decide +kernel

theorem context_13_431207_822321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431207 ⟨822321, by decide⟩ :=
  accepted_of_selected 13 431207 ⟨822321, by decide⟩ ⟨13, 2, 0, 822321, 431207, 769, 16384⟩
    (by decide) selected_cut_32003

theorem unmarked_context_12_107801_822322 : frontier 9 ⟨822322, by decide⟩
    (prefixCache 12 107801) (prefixPartial 12 107801) = false := by
  decide +kernel

theorem node_context_12_107801_822322 : EJMOriginalGlobalDAGData.nodes 9 ⟨822322, by decide⟩ =
    .split (coordinate 12) (![⟨822267, by decide⟩,⟨822291, by decide⟩,⟨822312, by decide⟩,⟨822321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107801_822322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107801 ⟨822322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107801
    ⟨822322, by decide⟩ (by decide) (![⟨822267, by decide⟩,⟨822291, by decide⟩,⟨822312, by decide⟩,⟨822321, by decide⟩]) unmarked_context_12_107801_822322 node_context_12_107801_822322
  intro a
  fin_cases a
  · exact context_13_431204_822267
  · exact context_13_431205_822291
  · exact context_13_431206_822312
  · exact context_13_431207_822321

theorem selected_cut_32004 : selected 8 ⟨822352, by decide⟩
    (prefixPartial 13 431208) = some ⟨13, 2, 0, 822352, 431208, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_431208_822352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431208 ⟨822352, by decide⟩ :=
  accepted_of_selected 13 431208 ⟨822352, by decide⟩ ⟨13, 2, 0, 822352, 431208, 1589, 16384⟩
    (by decide) selected_cut_32004

theorem selected_cut_32005 : selected 8 ⟨822382, by decide⟩
    (prefixPartial 13 431209) = some ⟨13, 2, 0, 822382, 431209, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_431209_822382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431209 ⟨822382, by decide⟩ :=
  accepted_of_selected 13 431209 ⟨822382, by decide⟩ ⟨13, 2, 0, 822382, 431209, 2157, 16384⟩
    (by decide) selected_cut_32005

theorem selected_cut_32006 : selected 8 ⟨822403, by decide⟩
    (prefixPartial 13 431210) = some ⟨13, 2, 0, 822403, 431210, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_431210_822403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431210 ⟨822403, by decide⟩ :=
  accepted_of_selected 13 431210 ⟨822403, by decide⟩ ⟨13, 2, 0, 822403, 431210, 1213, 16384⟩
    (by decide) selected_cut_32006

theorem selected_cut_32007 : selected 8 ⟨822417, by decide⟩
    (prefixPartial 13 431211) = some ⟨13, 2, 0, 822417, 431211, 821, 16384⟩ := by
  decide +kernel

theorem context_13_431211_822417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431211 ⟨822417, by decide⟩ :=
  accepted_of_selected 13 431211 ⟨822417, by decide⟩ ⟨13, 2, 0, 822417, 431211, 821, 16384⟩
    (by decide) selected_cut_32007

theorem unmarked_context_12_107802_822418 : frontier 9 ⟨822418, by decide⟩
    (prefixCache 12 107802) (prefixPartial 12 107802) = false := by
  decide +kernel

theorem node_context_12_107802_822418 : EJMOriginalGlobalDAGData.nodes 9 ⟨822418, by decide⟩ =
    .split (coordinate 12) (![⟨822352, by decide⟩,⟨822382, by decide⟩,⟨822403, by decide⟩,⟨822417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107802_822418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107802 ⟨822418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107802
    ⟨822418, by decide⟩ (by decide) (![⟨822352, by decide⟩,⟨822382, by decide⟩,⟨822403, by decide⟩,⟨822417, by decide⟩]) unmarked_context_12_107802_822418 node_context_12_107802_822418
  intro a
  fin_cases a
  · exact context_13_431208_822352
  · exact context_13_431209_822382
  · exact context_13_431210_822403
  · exact context_13_431211_822417

theorem selected_cut_32008 : selected 8 ⟨822449, by decide⟩
    (prefixPartial 13 431212) = some ⟨13, 2, 0, 822449, 431212, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_431212_822449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431212 ⟨822449, by decide⟩ :=
  accepted_of_selected 13 431212 ⟨822449, by decide⟩ ⟨13, 2, 0, 822449, 431212, 1861, 16384⟩
    (by decide) selected_cut_32008

theorem selected_cut_32009 : selected 8 ⟨822496, by decide⟩
    (prefixPartial 13 431213) = some ⟨13, 2, 0, 822496, 431213, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_431213_822496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431213 ⟨822496, by decide⟩ :=
  accepted_of_selected 13 431213 ⟨822496, by decide⟩ ⟨13, 2, 0, 822496, 431213, 2873, 16384⟩
    (by decide) selected_cut_32009

theorem selected_cut_32010 : selected 8 ⟨822518, by decide⟩
    (prefixPartial 13 431214) = some ⟨13, 2, 0, 822518, 431214, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_431214_822518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431214 ⟨822518, by decide⟩ :=
  accepted_of_selected 13 431214 ⟨822518, by decide⟩ ⟨13, 2, 0, 822518, 431214, 1489, 16384⟩
    (by decide) selected_cut_32010

theorem selected_cut_32011 : selected 8 ⟨822526, by decide⟩
    (prefixPartial 13 431215) = some ⟨13, 2, 0, 822526, 431215, 805, 16384⟩ := by
  decide +kernel

theorem context_13_431215_822526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431215 ⟨822526, by decide⟩ :=
  accepted_of_selected 13 431215 ⟨822526, by decide⟩ ⟨13, 2, 0, 822526, 431215, 805, 16384⟩
    (by decide) selected_cut_32011

theorem unmarked_context_12_107803_822527 : frontier 9 ⟨822527, by decide⟩
    (prefixCache 12 107803) (prefixPartial 12 107803) = false := by
  decide +kernel

theorem node_context_12_107803_822527 : EJMOriginalGlobalDAGData.nodes 9 ⟨822527, by decide⟩ =
    .split (coordinate 12) (![⟨822449, by decide⟩,⟨822496, by decide⟩,⟨822518, by decide⟩,⟨822526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107803_822527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107803 ⟨822527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107803
    ⟨822527, by decide⟩ (by decide) (![⟨822449, by decide⟩,⟨822496, by decide⟩,⟨822518, by decide⟩,⟨822526, by decide⟩]) unmarked_context_12_107803_822527 node_context_12_107803_822527
  intro a
  fin_cases a
  · exact context_13_431212_822449
  · exact context_13_431213_822496
  · exact context_13_431214_822518
  · exact context_13_431215_822526

theorem unmarked_context_11_26950_822528 : frontier 10 ⟨822528, by decide⟩
    (prefixCache 11 26950) (prefixPartial 11 26950) = false := by
  decide +kernel

theorem node_context_11_26950_822528 : EJMOriginalGlobalDAGData.nodes 10 ⟨822528, by decide⟩ =
    .split (coordinate 11) (![⟨822242, by decide⟩,⟨822322, by decide⟩,⟨822418, by decide⟩,⟨822527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26950_822528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26950 ⟨822528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26950
    ⟨822528, by decide⟩ (by decide) (![⟨822242, by decide⟩,⟨822322, by decide⟩,⟨822418, by decide⟩,⟨822527, by decide⟩]) unmarked_context_11_26950_822528 node_context_11_26950_822528
  intro a
  fin_cases a
  · exact context_12_107800_822242
  · exact context_12_107801_822322
  · exact context_12_107802_822418
  · exact context_12_107803_822527

theorem selected_cut_32012 : selected 8 ⟨822555, by decide⟩
    (prefixPartial 13 431216) = some ⟨13, 2, 0, 822555, 431216, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_431216_822555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431216 ⟨822555, by decide⟩ :=
  accepted_of_selected 13 431216 ⟨822555, by decide⟩ ⟨13, 2, 0, 822555, 431216, 1573, 16384⟩
    (by decide) selected_cut_32012

theorem selected_cut_32013 : selected 8 ⟨822616, by decide⟩
    (prefixPartial 13 431217) = some ⟨13, 2, 0, 822616, 431217, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_431217_822616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431217 ⟨822616, by decide⟩ :=
  accepted_of_selected 13 431217 ⟨822616, by decide⟩ ⟨13, 2, 0, 822616, 431217, 3225, 16384⟩
    (by decide) selected_cut_32013

theorem selected_cut_32014 : selected 8 ⟨822639, by decide⟩
    (prefixPartial 13 431218) = some ⟨13, 2, 0, 822639, 431218, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_431218_822639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431218 ⟨822639, by decide⟩ :=
  accepted_of_selected 13 431218 ⟨822639, by decide⟩ ⟨13, 2, 0, 822639, 431218, 1469, 16384⟩
    (by decide) selected_cut_32014

theorem selected_cut_32015 : selected 8 ⟨822647, by decide⟩
    (prefixPartial 13 431219) = some ⟨13, 2, 0, 822647, 431219, 957, 16384⟩ := by
  decide +kernel

theorem context_13_431219_822647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431219 ⟨822647, by decide⟩ :=
  accepted_of_selected 13 431219 ⟨822647, by decide⟩ ⟨13, 2, 0, 822647, 431219, 957, 16384⟩
    (by decide) selected_cut_32015

theorem unmarked_context_12_107804_822648 : frontier 9 ⟨822648, by decide⟩
    (prefixCache 12 107804) (prefixPartial 12 107804) = false := by
  decide +kernel

theorem node_context_12_107804_822648 : EJMOriginalGlobalDAGData.nodes 9 ⟨822648, by decide⟩ =
    .split (coordinate 12) (![⟨822555, by decide⟩,⟨822616, by decide⟩,⟨822639, by decide⟩,⟨822647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107804_822648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107804 ⟨822648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107804
    ⟨822648, by decide⟩ (by decide) (![⟨822555, by decide⟩,⟨822616, by decide⟩,⟨822639, by decide⟩,⟨822647, by decide⟩]) unmarked_context_12_107804_822648 node_context_12_107804_822648
  intro a
  fin_cases a
  · exact context_13_431216_822555
  · exact context_13_431217_822616
  · exact context_13_431218_822639
  · exact context_13_431219_822647

theorem selected_cut_32016 : selected 8 ⟨822668, by decide⟩
    (prefixPartial 13 431220) = some ⟨13, 2, 0, 822668, 431220, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_431220_822668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431220 ⟨822668, by decide⟩ :=
  accepted_of_selected 13 431220 ⟨822668, by decide⟩ ⟨13, 2, 0, 822668, 431220, 1577, 16384⟩
    (by decide) selected_cut_32016

theorem selected_cut_32017 : selected 8 ⟨822705, by decide⟩
    (prefixPartial 13 431221) = some ⟨13, 2, 0, 822705, 431221, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_431221_822705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431221 ⟨822705, by decide⟩ :=
  accepted_of_selected 13 431221 ⟨822705, by decide⟩ ⟨13, 2, 0, 822705, 431221, 2501, 16384⟩
    (by decide) selected_cut_32017

theorem selected_cut_32018 : selected 8 ⟨822729, by decide⟩
    (prefixPartial 13 431222) = some ⟨13, 2, 0, 822729, 431222, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_431222_822729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431222 ⟨822729, by decide⟩ :=
  accepted_of_selected 13 431222 ⟨822729, by decide⟩ ⟨13, 2, 0, 822729, 431222, 1293, 16384⟩
    (by decide) selected_cut_32018

theorem selected_cut_32019 : selected 8 ⟨822736, by decide⟩
    (prefixPartial 13 431223) = some ⟨13, 2, 0, 822736, 431223, 765, 16384⟩ := by
  decide +kernel

theorem context_13_431223_822736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431223 ⟨822736, by decide⟩ :=
  accepted_of_selected 13 431223 ⟨822736, by decide⟩ ⟨13, 2, 0, 822736, 431223, 765, 16384⟩
    (by decide) selected_cut_32019

theorem unmarked_context_12_107805_822737 : frontier 9 ⟨822737, by decide⟩
    (prefixCache 12 107805) (prefixPartial 12 107805) = false := by
  decide +kernel

theorem node_context_12_107805_822737 : EJMOriginalGlobalDAGData.nodes 9 ⟨822737, by decide⟩ =
    .split (coordinate 12) (![⟨822668, by decide⟩,⟨822705, by decide⟩,⟨822729, by decide⟩,⟨822736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107805_822737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107805 ⟨822737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107805
    ⟨822737, by decide⟩ (by decide) (![⟨822668, by decide⟩,⟨822705, by decide⟩,⟨822729, by decide⟩,⟨822736, by decide⟩]) unmarked_context_12_107805_822737 node_context_12_107805_822737
  intro a
  fin_cases a
  · exact context_13_431220_822668
  · exact context_13_431221_822705
  · exact context_13_431222_822729
  · exact context_13_431223_822736

theorem selected_cut_32020 : selected 8 ⟨822762, by decide⟩
    (prefixPartial 13 431224) = some ⟨13, 2, 0, 822762, 431224, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_431224_822762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431224 ⟨822762, by decide⟩ :=
  accepted_of_selected 13 431224 ⟨822762, by decide⟩ ⟨13, 2, 0, 822762, 431224, 1613, 16384⟩
    (by decide) selected_cut_32020

theorem selected_cut_32021 : selected 8 ⟨822800, by decide⟩
    (prefixPartial 13 431225) = some ⟨13, 2, 0, 822800, 431225, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_431225_822800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431225 ⟨822800, by decide⟩ :=
  accepted_of_selected 13 431225 ⟨822800, by decide⟩ ⟨13, 2, 0, 822800, 431225, 2805, 16384⟩
    (by decide) selected_cut_32021

theorem selected_cut_32022 : selected 8 ⟨822818, by decide⟩
    (prefixPartial 13 431226) = some ⟨13, 2, 0, 822818, 431226, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_431226_822818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431226 ⟨822818, by decide⟩ :=
  accepted_of_selected 13 431226 ⟨822818, by decide⟩ ⟨13, 2, 0, 822818, 431226, 1161, 16384⟩
    (by decide) selected_cut_32022

theorem selected_cut_32023 : selected 8 ⟨822830, by decide⟩
    (prefixPartial 13 431227) = some ⟨13, 2, 0, 822830, 431227, 953, 16384⟩ := by
  decide +kernel

theorem context_13_431227_822830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431227 ⟨822830, by decide⟩ :=
  accepted_of_selected 13 431227 ⟨822830, by decide⟩ ⟨13, 2, 0, 822830, 431227, 953, 16384⟩
    (by decide) selected_cut_32023

theorem unmarked_context_12_107806_822831 : frontier 9 ⟨822831, by decide⟩
    (prefixCache 12 107806) (prefixPartial 12 107806) = false := by
  decide +kernel

theorem node_context_12_107806_822831 : EJMOriginalGlobalDAGData.nodes 9 ⟨822831, by decide⟩ =
    .split (coordinate 12) (![⟨822762, by decide⟩,⟨822800, by decide⟩,⟨822818, by decide⟩,⟨822830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107806_822831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107806 ⟨822831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107806
    ⟨822831, by decide⟩ (by decide) (![⟨822762, by decide⟩,⟨822800, by decide⟩,⟨822818, by decide⟩,⟨822830, by decide⟩]) unmarked_context_12_107806_822831 node_context_12_107806_822831
  intro a
  fin_cases a
  · exact context_13_431224_822762
  · exact context_13_431225_822800
  · exact context_13_431226_822818
  · exact context_13_431227_822830

theorem selected_cut_32024 : selected 8 ⟨822869, by decide⟩
    (prefixPartial 13 431228) = some ⟨13, 2, 0, 822869, 431228, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_431228_822869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431228 ⟨822869, by decide⟩ :=
  accepted_of_selected 13 431228 ⟨822869, by decide⟩ ⟨13, 2, 0, 822869, 431228, 2013, 16384⟩
    (by decide) selected_cut_32024

theorem selected_cut_32025 : selected 8 ⟨822929, by decide⟩
    (prefixPartial 13 431229) = some ⟨13, 2, 0, 822929, 431229, 3377, 16384⟩ := by
  decide +kernel

theorem context_13_431229_822929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431229 ⟨822929, by decide⟩ :=
  accepted_of_selected 13 431229 ⟨822929, by decide⟩ ⟨13, 2, 0, 822929, 431229, 3377, 16384⟩
    (by decide) selected_cut_32025

theorem selected_cut_32026 : selected 8 ⟨822962, by decide⟩
    (prefixPartial 13 431230) = some ⟨13, 2, 0, 822962, 431230, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_431230_822962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431230 ⟨822962, by decide⟩ :=
  accepted_of_selected 13 431230 ⟨822962, by decide⟩ ⟨13, 2, 0, 822962, 431230, 1529, 16384⟩
    (by decide) selected_cut_32026

theorem selected_cut_32027 : selected 8 ⟨822970, by decide⟩
    (prefixPartial 13 431231) = some ⟨13, 2, 0, 822970, 431231, 925, 16384⟩ := by
  decide +kernel

theorem context_13_431231_822970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431231 ⟨822970, by decide⟩ :=
  accepted_of_selected 13 431231 ⟨822970, by decide⟩ ⟨13, 2, 0, 822970, 431231, 925, 16384⟩
    (by decide) selected_cut_32027

theorem unmarked_context_12_107807_822971 : frontier 9 ⟨822971, by decide⟩
    (prefixCache 12 107807) (prefixPartial 12 107807) = false := by
  decide +kernel

theorem node_context_12_107807_822971 : EJMOriginalGlobalDAGData.nodes 9 ⟨822971, by decide⟩ =
    .split (coordinate 12) (![⟨822869, by decide⟩,⟨822929, by decide⟩,⟨822962, by decide⟩,⟨822970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107807_822971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107807 ⟨822971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107807
    ⟨822971, by decide⟩ (by decide) (![⟨822869, by decide⟩,⟨822929, by decide⟩,⟨822962, by decide⟩,⟨822970, by decide⟩]) unmarked_context_12_107807_822971 node_context_12_107807_822971
  intro a
  fin_cases a
  · exact context_13_431228_822869
  · exact context_13_431229_822929
  · exact context_13_431230_822962
  · exact context_13_431231_822970

theorem unmarked_context_11_26951_822972 : frontier 10 ⟨822972, by decide⟩
    (prefixCache 11 26951) (prefixPartial 11 26951) = false := by
  decide +kernel

theorem node_context_11_26951_822972 : EJMOriginalGlobalDAGData.nodes 10 ⟨822972, by decide⟩ =
    .split (coordinate 11) (![⟨822648, by decide⟩,⟨822737, by decide⟩,⟨822831, by decide⟩,⟨822971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26951_822972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26951 ⟨822972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26951
    ⟨822972, by decide⟩ (by decide) (![⟨822648, by decide⟩,⟨822737, by decide⟩,⟨822831, by decide⟩,⟨822971, by decide⟩]) unmarked_context_11_26951_822972 node_context_11_26951_822972
  intro a
  fin_cases a
  · exact context_12_107804_822648
  · exact context_12_107805_822737
  · exact context_12_107806_822831
  · exact context_12_107807_822971

theorem unmarked_context_10_6737_822973 : frontier 11 ⟨822973, by decide⟩
    (prefixCache 10 6737) (prefixPartial 10 6737) = false := by
  decide +kernel

theorem node_context_10_6737_822973 : EJMOriginalGlobalDAGData.nodes 11 ⟨822973, by decide⟩ =
    .split (coordinate 10) (![⟨822146, by decide⟩,⟨815620, by decide⟩,⟨822528, by decide⟩,⟨822972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6737_822973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6737 ⟨822973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6737
    ⟨822973, by decide⟩ (by decide) (![⟨822146, by decide⟩,⟨815620, by decide⟩,⟨822528, by decide⟩,⟨822972, by decide⟩]) unmarked_context_10_6737_822973 node_context_10_6737_822973
  intro a
  fin_cases a
  · exact context_11_26948_822146
  · exact context_11_26949_815620
  · exact context_11_26950_822528
  · exact context_11_26951_822972

theorem selected_cut_32028 : selected 8 ⟨822998, by decide⟩
    (prefixPartial 13 431232) = some ⟨13, 2, 0, 822998, 431232, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_431232_822998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431232 ⟨822998, by decide⟩ :=
  accepted_of_selected 13 431232 ⟨822998, by decide⟩ ⟨13, 2, 0, 822998, 431232, 1465, 16384⟩
    (by decide) selected_cut_32028

theorem selected_cut_32029 : selected 8 ⟨823033, by decide⟩
    (prefixPartial 13 431233) = some ⟨13, 2, 0, 823033, 431233, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_431233_823033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431233 ⟨823033, by decide⟩ :=
  accepted_of_selected 13 431233 ⟨823033, by decide⟩ ⟨13, 2, 0, 823033, 431233, 2537, 16384⟩
    (by decide) selected_cut_32029

theorem selected_cut_32030 : selected 8 ⟨823064, by decide⟩
    (prefixPartial 13 431234) = some ⟨13, 2, 0, 823064, 431234, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_431234_823064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431234 ⟨823064, by decide⟩ :=
  accepted_of_selected 13 431234 ⟨823064, by decide⟩ ⟨13, 2, 0, 823064, 431234, 1429, 16384⟩
    (by decide) selected_cut_32030

theorem selected_cut_32031 : selected 8 ⟨823073, by decide⟩
    (prefixPartial 13 431235) = some ⟨13, 2, 0, 823073, 431235, 913, 16384⟩ := by
  decide +kernel

theorem context_13_431235_823073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431235 ⟨823073, by decide⟩ :=
  accepted_of_selected 13 431235 ⟨823073, by decide⟩ ⟨13, 2, 0, 823073, 431235, 913, 16384⟩
    (by decide) selected_cut_32031

theorem unmarked_context_12_107808_823074 : frontier 9 ⟨823074, by decide⟩
    (prefixCache 12 107808) (prefixPartial 12 107808) = false := by
  decide +kernel

theorem node_context_12_107808_823074 : EJMOriginalGlobalDAGData.nodes 9 ⟨823074, by decide⟩ =
    .split (coordinate 12) (![⟨822998, by decide⟩,⟨823033, by decide⟩,⟨823064, by decide⟩,⟨823073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107808_823074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107808 ⟨823074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107808
    ⟨823074, by decide⟩ (by decide) (![⟨822998, by decide⟩,⟨823033, by decide⟩,⟨823064, by decide⟩,⟨823073, by decide⟩]) unmarked_context_12_107808_823074 node_context_12_107808_823074
  intro a
  fin_cases a
  · exact context_13_431232_822998
  · exact context_13_431233_823033
  · exact context_13_431234_823064
  · exact context_13_431235_823073

theorem selected_cut_32032 : selected 8 ⟨823094, by decide⟩
    (prefixPartial 13 431236) = some ⟨13, 2, 0, 823094, 431236, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_431236_823094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431236 ⟨823094, by decide⟩ :=
  accepted_of_selected 13 431236 ⟨823094, by decide⟩ ⟨13, 2, 0, 823094, 431236, 1545, 16384⟩
    (by decide) selected_cut_32032

theorem selected_cut_32033 : selected 8 ⟨823121, by decide⟩
    (prefixPartial 13 431237) = some ⟨13, 2, 0, 823121, 431237, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_431237_823121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431237 ⟨823121, by decide⟩ :=
  accepted_of_selected 13 431237 ⟨823121, by decide⟩ ⟨13, 2, 0, 823121, 431237, 2313, 16384⟩
    (by decide) selected_cut_32033

theorem selected_cut_32034 : selected 8 ⟨823146, by decide⟩
    (prefixPartial 13 431238) = some ⟨13, 2, 0, 823146, 431238, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_431238_823146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431238 ⟨823146, by decide⟩ :=
  accepted_of_selected 13 431238 ⟨823146, by decide⟩ ⟨13, 2, 0, 823146, 431238, 1285, 16384⟩
    (by decide) selected_cut_32034

theorem selected_cut_32035 : selected 8 ⟨823154, by decide⟩
    (prefixPartial 13 431239) = some ⟨13, 2, 0, 823154, 431239, 757, 16384⟩ := by
  decide +kernel

theorem context_13_431239_823154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431239 ⟨823154, by decide⟩ :=
  accepted_of_selected 13 431239 ⟨823154, by decide⟩ ⟨13, 2, 0, 823154, 431239, 757, 16384⟩
    (by decide) selected_cut_32035

theorem unmarked_context_12_107809_823155 : frontier 9 ⟨823155, by decide⟩
    (prefixCache 12 107809) (prefixPartial 12 107809) = false := by
  decide +kernel

theorem node_context_12_107809_823155 : EJMOriginalGlobalDAGData.nodes 9 ⟨823155, by decide⟩ =
    .split (coordinate 12) (![⟨823094, by decide⟩,⟨823121, by decide⟩,⟨823146, by decide⟩,⟨823154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107809_823155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107809 ⟨823155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107809
    ⟨823155, by decide⟩ (by decide) (![⟨823094, by decide⟩,⟨823121, by decide⟩,⟨823146, by decide⟩,⟨823154, by decide⟩]) unmarked_context_12_107809_823155 node_context_12_107809_823155
  intro a
  fin_cases a
  · exact context_13_431236_823094
  · exact context_13_431237_823121
  · exact context_13_431238_823146
  · exact context_13_431239_823154

theorem selected_cut_32036 : selected 8 ⟨823179, by decide⟩
    (prefixPartial 13 431240) = some ⟨13, 2, 0, 823179, 431240, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_431240_823179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431240 ⟨823179, by decide⟩ :=
  accepted_of_selected 13 431240 ⟨823179, by decide⟩ ⟨13, 2, 0, 823179, 431240, 1377, 16384⟩
    (by decide) selected_cut_32036

theorem selected_cut_32037 : selected 8 ⟨823206, by decide⟩
    (prefixPartial 13 431241) = some ⟨13, 2, 0, 823206, 431241, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_431241_823206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431241 ⟨823206, by decide⟩ :=
  accepted_of_selected 13 431241 ⟨823206, by decide⟩ ⟨13, 2, 0, 823206, 431241, 2301, 16384⟩
    (by decide) selected_cut_32037

theorem selected_cut_32038 : selected 8 ⟨823225, by decide⟩
    (prefixPartial 13 431242) = some ⟨13, 2, 0, 823225, 431242, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_431242_823225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431242 ⟨823225, by decide⟩ :=
  accepted_of_selected 13 431242 ⟨823225, by decide⟩ ⟨13, 2, 0, 823225, 431242, 1205, 16384⟩
    (by decide) selected_cut_32038

theorem selected_cut_32039 : selected 8 ⟨823232, by decide⟩
    (prefixPartial 13 431243) = some ⟨13, 2, 0, 823232, 431243, 825, 16384⟩ := by
  decide +kernel

theorem context_13_431243_823232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431243 ⟨823232, by decide⟩ :=
  accepted_of_selected 13 431243 ⟨823232, by decide⟩ ⟨13, 2, 0, 823232, 431243, 825, 16384⟩
    (by decide) selected_cut_32039

theorem unmarked_context_12_107810_823233 : frontier 9 ⟨823233, by decide⟩
    (prefixCache 12 107810) (prefixPartial 12 107810) = false := by
  decide +kernel

theorem node_context_12_107810_823233 : EJMOriginalGlobalDAGData.nodes 9 ⟨823233, by decide⟩ =
    .split (coordinate 12) (![⟨823179, by decide⟩,⟨823206, by decide⟩,⟨823225, by decide⟩,⟨823232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107810_823233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107810 ⟨823233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107810
    ⟨823233, by decide⟩ (by decide) (![⟨823179, by decide⟩,⟨823206, by decide⟩,⟨823225, by decide⟩,⟨823232, by decide⟩]) unmarked_context_12_107810_823233 node_context_12_107810_823233
  intro a
  fin_cases a
  · exact context_13_431240_823179
  · exact context_13_431241_823206
  · exact context_13_431242_823225
  · exact context_13_431243_823232

theorem selected_cut_32040 : selected 8 ⟨823266, by decide⟩
    (prefixPartial 13 431244) = some ⟨13, 2, 0, 823266, 431244, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_431244_823266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431244 ⟨823266, by decide⟩ :=
  accepted_of_selected 13 431244 ⟨823266, by decide⟩ ⟨13, 2, 0, 823266, 431244, 1825, 16384⟩
    (by decide) selected_cut_32040

theorem selected_cut_32041 : selected 8 ⟨823299, by decide⟩
    (prefixPartial 13 431245) = some ⟨13, 2, 0, 823299, 431245, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_431245_823299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431245 ⟨823299, by decide⟩ :=
  accepted_of_selected 13 431245 ⟨823299, by decide⟩ ⟨13, 2, 0, 823299, 431245, 2893, 16384⟩
    (by decide) selected_cut_32041

theorem selected_cut_32042 : selected 8 ⟨823334, by decide⟩
    (prefixPartial 13 431246) = some ⟨13, 2, 0, 823334, 431246, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_431246_823334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431246 ⟨823334, by decide⟩ :=
  accepted_of_selected 13 431246 ⟨823334, by decide⟩ ⟨13, 2, 0, 823334, 431246, 1525, 16384⟩
    (by decide) selected_cut_32042

theorem selected_cut_32043 : selected 8 ⟨823344, by decide⟩
    (prefixPartial 13 431247) = some ⟨13, 2, 0, 823344, 431247, 873, 16384⟩ := by
  decide +kernel

theorem context_13_431247_823344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431247 ⟨823344, by decide⟩ :=
  accepted_of_selected 13 431247 ⟨823344, by decide⟩ ⟨13, 2, 0, 823344, 431247, 873, 16384⟩
    (by decide) selected_cut_32043

theorem unmarked_context_12_107811_823345 : frontier 9 ⟨823345, by decide⟩
    (prefixCache 12 107811) (prefixPartial 12 107811) = false := by
  decide +kernel

theorem node_context_12_107811_823345 : EJMOriginalGlobalDAGData.nodes 9 ⟨823345, by decide⟩ =
    .split (coordinate 12) (![⟨823266, by decide⟩,⟨823299, by decide⟩,⟨823334, by decide⟩,⟨823344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107811_823345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107811 ⟨823345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107811
    ⟨823345, by decide⟩ (by decide) (![⟨823266, by decide⟩,⟨823299, by decide⟩,⟨823334, by decide⟩,⟨823344, by decide⟩]) unmarked_context_12_107811_823345 node_context_12_107811_823345
  intro a
  fin_cases a
  · exact context_13_431244_823266
  · exact context_13_431245_823299
  · exact context_13_431246_823334
  · exact context_13_431247_823344

theorem unmarked_context_11_26952_823346 : frontier 10 ⟨823346, by decide⟩
    (prefixCache 11 26952) (prefixPartial 11 26952) = false := by
  decide +kernel

theorem node_context_11_26952_823346 : EJMOriginalGlobalDAGData.nodes 10 ⟨823346, by decide⟩ =
    .split (coordinate 11) (![⟨823074, by decide⟩,⟨823155, by decide⟩,⟨823233, by decide⟩,⟨823345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26952_823346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26952 ⟨823346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26952
    ⟨823346, by decide⟩ (by decide) (![⟨823074, by decide⟩,⟨823155, by decide⟩,⟨823233, by decide⟩,⟨823345, by decide⟩]) unmarked_context_11_26952_823346 node_context_11_26952_823346
  intro a
  fin_cases a
  · exact context_12_107808_823074
  · exact context_12_107809_823155
  · exact context_12_107810_823233
  · exact context_12_107811_823345

theorem selected_cut_32044 : selected 8 ⟨823362, by decide⟩
    (prefixPartial 13 431248) = some ⟨13, 2, 0, 823362, 431248, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_431248_823362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431248 ⟨823362, by decide⟩ :=
  accepted_of_selected 13 431248 ⟨823362, by decide⟩ ⟨13, 2, 0, 823362, 431248, 1245, 16384⟩
    (by decide) selected_cut_32044

theorem selected_cut_32045 : selected 8 ⟨823394, by decide⟩
    (prefixPartial 13 431249) = some ⟨13, 2, 0, 823394, 431249, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_431249_823394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431249 ⟨823394, by decide⟩ :=
  accepted_of_selected 13 431249 ⟨823394, by decide⟩ ⟨13, 2, 0, 823394, 431249, 2533, 16384⟩
    (by decide) selected_cut_32045

theorem selected_cut_32046 : selected 8 ⟨823416, by decide⟩
    (prefixPartial 13 431250) = some ⟨13, 2, 0, 823416, 431250, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_431250_823416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431250 ⟨823416, by decide⟩ :=
  accepted_of_selected 13 431250 ⟨823416, by decide⟩ ⟨13, 2, 0, 823416, 431250, 1361, 16384⟩
    (by decide) selected_cut_32046

theorem selected_cut_32047 : selected 8 ⟨823430, by decide⟩
    (prefixPartial 13 431251) = some ⟨13, 2, 0, 823430, 431251, 989, 16384⟩ := by
  decide +kernel

theorem context_13_431251_823430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431251 ⟨823430, by decide⟩ :=
  accepted_of_selected 13 431251 ⟨823430, by decide⟩ ⟨13, 2, 0, 823430, 431251, 989, 16384⟩
    (by decide) selected_cut_32047

theorem unmarked_context_12_107812_823431 : frontier 9 ⟨823431, by decide⟩
    (prefixCache 12 107812) (prefixPartial 12 107812) = false := by
  decide +kernel

theorem node_context_12_107812_823431 : EJMOriginalGlobalDAGData.nodes 9 ⟨823431, by decide⟩ =
    .split (coordinate 12) (![⟨823362, by decide⟩,⟨823394, by decide⟩,⟨823416, by decide⟩,⟨823430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107812_823431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107812 ⟨823431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107812
    ⟨823431, by decide⟩ (by decide) (![⟨823362, by decide⟩,⟨823394, by decide⟩,⟨823416, by decide⟩,⟨823430, by decide⟩]) unmarked_context_12_107812_823431 node_context_12_107812_823431
  intro a
  fin_cases a
  · exact context_13_431248_823362
  · exact context_13_431249_823394
  · exact context_13_431250_823416
  · exact context_13_431251_823430

theorem selected_cut_32048 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 107813) = some ⟨12, 1, 0, 688903, 107813, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107813_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107813 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 107813 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 107813, 1, 65536⟩
    (by decide) selected_cut_32048

theorem selected_cut_32049 : selected 8 ⟨823449, by decide⟩
    (prefixPartial 13 431256) = some ⟨13, 2, 0, 823449, 431256, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_431256_823449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431256 ⟨823449, by decide⟩ :=
  accepted_of_selected 13 431256 ⟨823449, by decide⟩ ⟨13, 2, 0, 823449, 431256, 1249, 16384⟩
    (by decide) selected_cut_32049

theorem selected_cut_32050 : selected 8 ⟨823478, by decide⟩
    (prefixPartial 13 431257) = some ⟨13, 2, 0, 823478, 431257, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_431257_823478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431257 ⟨823478, by decide⟩ :=
  accepted_of_selected 13 431257 ⟨823478, by decide⟩ ⟨13, 2, 0, 823478, 431257, 2137, 16384⟩
    (by decide) selected_cut_32050

theorem selected_cut_32051 : selected 8 ⟨823495, by decide⟩
    (prefixPartial 13 431258) = some ⟨13, 2, 0, 823495, 431258, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_431258_823495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431258 ⟨823495, by decide⟩ :=
  accepted_of_selected 13 431258 ⟨823495, by decide⟩ ⟨13, 2, 0, 823495, 431258, 1021, 16384⟩
    (by decide) selected_cut_32051

theorem selected_cut_32052 : selected 8 ⟨823504, by decide⟩
    (prefixPartial 13 431259) = some ⟨13, 2, 0, 823504, 431259, 853, 16384⟩ := by
  decide +kernel

theorem context_13_431259_823504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431259 ⟨823504, by decide⟩ :=
  accepted_of_selected 13 431259 ⟨823504, by decide⟩ ⟨13, 2, 0, 823504, 431259, 853, 16384⟩
    (by decide) selected_cut_32052

theorem unmarked_context_12_107814_823505 : frontier 9 ⟨823505, by decide⟩
    (prefixCache 12 107814) (prefixPartial 12 107814) = false := by
  decide +kernel

theorem node_context_12_107814_823505 : EJMOriginalGlobalDAGData.nodes 9 ⟨823505, by decide⟩ =
    .split (coordinate 12) (![⟨823449, by decide⟩,⟨823478, by decide⟩,⟨823495, by decide⟩,⟨823504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107814_823505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107814 ⟨823505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107814
    ⟨823505, by decide⟩ (by decide) (![⟨823449, by decide⟩,⟨823478, by decide⟩,⟨823495, by decide⟩,⟨823504, by decide⟩]) unmarked_context_12_107814_823505 node_context_12_107814_823505
  intro a
  fin_cases a
  · exact context_13_431256_823449
  · exact context_13_431257_823478
  · exact context_13_431258_823495
  · exact context_13_431259_823504

theorem selected_cut_32053 : selected 8 ⟨823532, by decide⟩
    (prefixPartial 13 431260) = some ⟨13, 2, 0, 823532, 431260, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_431260_823532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431260 ⟨823532, by decide⟩ :=
  accepted_of_selected 13 431260 ⟨823532, by decide⟩ ⟨13, 2, 0, 823532, 431260, 1621, 16384⟩
    (by decide) selected_cut_32053

theorem selected_cut_32054 : selected 8 ⟨823571, by decide⟩
    (prefixPartial 13 431261) = some ⟨13, 2, 0, 823571, 431261, 2937, 16384⟩ := by
  decide +kernel

theorem context_13_431261_823571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431261 ⟨823571, by decide⟩ :=
  accepted_of_selected 13 431261 ⟨823571, by decide⟩ ⟨13, 2, 0, 823571, 431261, 2937, 16384⟩
    (by decide) selected_cut_32054

theorem selected_cut_32055 : selected 8 ⟨823609, by decide⟩
    (prefixPartial 13 431262) = some ⟨13, 2, 0, 823609, 431262, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_431262_823609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431262 ⟨823609, by decide⟩ :=
  accepted_of_selected 13 431262 ⟨823609, by decide⟩ ⟨13, 2, 0, 823609, 431262, 1521, 16384⟩
    (by decide) selected_cut_32055

theorem selected_cut_32056 : selected 8 ⟨823617, by decide⟩
    (prefixPartial 13 431263) = some ⟨13, 2, 0, 823617, 431263, 849, 16384⟩ := by
  decide +kernel

theorem context_13_431263_823617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431263 ⟨823617, by decide⟩ :=
  accepted_of_selected 13 431263 ⟨823617, by decide⟩ ⟨13, 2, 0, 823617, 431263, 849, 16384⟩
    (by decide) selected_cut_32056

theorem unmarked_context_12_107815_823618 : frontier 9 ⟨823618, by decide⟩
    (prefixCache 12 107815) (prefixPartial 12 107815) = false := by
  decide +kernel

theorem node_context_12_107815_823618 : EJMOriginalGlobalDAGData.nodes 9 ⟨823618, by decide⟩ =
    .split (coordinate 12) (![⟨823532, by decide⟩,⟨823571, by decide⟩,⟨823609, by decide⟩,⟨823617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107815_823618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107815 ⟨823618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107815
    ⟨823618, by decide⟩ (by decide) (![⟨823532, by decide⟩,⟨823571, by decide⟩,⟨823609, by decide⟩,⟨823617, by decide⟩]) unmarked_context_12_107815_823618 node_context_12_107815_823618
  intro a
  fin_cases a
  · exact context_13_431260_823532
  · exact context_13_431261_823571
  · exact context_13_431262_823609
  · exact context_13_431263_823617

theorem unmarked_context_11_26953_823619 : frontier 10 ⟨823619, by decide⟩
    (prefixCache 11 26953) (prefixPartial 11 26953) = false := by
  decide +kernel

theorem node_context_11_26953_823619 : EJMOriginalGlobalDAGData.nodes 10 ⟨823619, by decide⟩ =
    .split (coordinate 11) (![⟨823431, by decide⟩,⟨688903, by decide⟩,⟨823505, by decide⟩,⟨823618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26953_823619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26953 ⟨823619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26953
    ⟨823619, by decide⟩ (by decide) (![⟨823431, by decide⟩,⟨688903, by decide⟩,⟨823505, by decide⟩,⟨823618, by decide⟩]) unmarked_context_11_26953_823619 node_context_11_26953_823619
  intro a
  fin_cases a
  · exact context_12_107812_823431
  · exact context_12_107813_688903
  · exact context_12_107814_823505
  · exact context_12_107815_823618

theorem selected_cut_32057 : selected 8 ⟨823639, by decide⟩
    (prefixPartial 13 431264) = some ⟨13, 2, 0, 823639, 431264, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_431264_823639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431264 ⟨823639, by decide⟩ :=
  accepted_of_selected 13 431264 ⟨823639, by decide⟩ ⟨13, 2, 0, 823639, 431264, 1121, 16384⟩
    (by decide) selected_cut_32057

theorem selected_cut_32058 : selected 8 ⟨823663, by decide⟩
    (prefixPartial 13 431265) = some ⟨13, 2, 0, 823663, 431265, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_431265_823663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431265 ⟨823663, by decide⟩ :=
  accepted_of_selected 13 431265 ⟨823663, by decide⟩ ⟨13, 2, 0, 823663, 431265, 2241, 16384⟩
    (by decide) selected_cut_32058

theorem selected_cut_32059 : selected 8 ⟨823692, by decide⟩
    (prefixPartial 13 431266) = some ⟨13, 2, 0, 823692, 431266, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_431266_823692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431266 ⟨823692, by decide⟩ :=
  accepted_of_selected 13 431266 ⟨823692, by decide⟩ ⟨13, 2, 0, 823692, 431266, 1649, 16384⟩
    (by decide) selected_cut_32059

theorem selected_cut_32060 : selected 8 ⟨823711, by decide⟩
    (prefixPartial 13 431267) = some ⟨13, 2, 0, 823711, 431267, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_431267_823711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431267 ⟨823711, by decide⟩ :=
  accepted_of_selected 13 431267 ⟨823711, by decide⟩ ⟨13, 2, 0, 823711, 431267, 1113, 16384⟩
    (by decide) selected_cut_32060

theorem unmarked_context_12_107816_823712 : frontier 9 ⟨823712, by decide⟩
    (prefixCache 12 107816) (prefixPartial 12 107816) = false := by
  decide +kernel

theorem node_context_12_107816_823712 : EJMOriginalGlobalDAGData.nodes 9 ⟨823712, by decide⟩ =
    .split (coordinate 12) (![⟨823639, by decide⟩,⟨823663, by decide⟩,⟨823692, by decide⟩,⟨823711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107816_823712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107816 ⟨823712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107816
    ⟨823712, by decide⟩ (by decide) (![⟨823639, by decide⟩,⟨823663, by decide⟩,⟨823692, by decide⟩,⟨823711, by decide⟩]) unmarked_context_12_107816_823712 node_context_12_107816_823712
  intro a
  fin_cases a
  · exact context_13_431264_823639
  · exact context_13_431265_823663
  · exact context_13_431266_823692
  · exact context_13_431267_823711

theorem selected_cut_32061 : selected 8 ⟨823725, by decide⟩
    (prefixPartial 13 431268) = some ⟨13, 2, 0, 823725, 431268, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_431268_823725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431268 ⟨823725, by decide⟩ :=
  accepted_of_selected 13 431268 ⟨823725, by decide⟩ ⟨13, 2, 0, 823725, 431268, 1293, 16384⟩
    (by decide) selected_cut_32061

theorem selected_cut_32062 : selected 8 ⟨823753, by decide⟩
    (prefixPartial 13 431269) = some ⟨13, 2, 0, 823753, 431269, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_431269_823753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431269 ⟨823753, by decide⟩ :=
  accepted_of_selected 13 431269 ⟨823753, by decide⟩ ⟨13, 2, 0, 823753, 431269, 1997, 16384⟩
    (by decide) selected_cut_32062

theorem selected_cut_32063 : selected 8 ⟨823776, by decide⟩
    (prefixPartial 13 431270) = some ⟨13, 2, 0, 823776, 431270, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_431270_823776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431270 ⟨823776, by decide⟩ :=
  accepted_of_selected 13 431270 ⟨823776, by decide⟩ ⟨13, 2, 0, 823776, 431270, 1517, 16384⟩
    (by decide) selected_cut_32063

theorem selected_cut_32064 : selected 8 ⟨823785, by decide⟩
    (prefixPartial 13 431271) = some ⟨13, 2, 0, 823785, 431271, 953, 16384⟩ := by
  decide +kernel

theorem context_13_431271_823785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431271 ⟨823785, by decide⟩ :=
  accepted_of_selected 13 431271 ⟨823785, by decide⟩ ⟨13, 2, 0, 823785, 431271, 953, 16384⟩
    (by decide) selected_cut_32064

theorem unmarked_context_12_107817_823786 : frontier 9 ⟨823786, by decide⟩
    (prefixCache 12 107817) (prefixPartial 12 107817) = false := by
  decide +kernel

theorem node_context_12_107817_823786 : EJMOriginalGlobalDAGData.nodes 9 ⟨823786, by decide⟩ =
    .split (coordinate 12) (![⟨823725, by decide⟩,⟨823753, by decide⟩,⟨823776, by decide⟩,⟨823785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107817_823786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107817 ⟨823786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107817
    ⟨823786, by decide⟩ (by decide) (![⟨823725, by decide⟩,⟨823753, by decide⟩,⟨823776, by decide⟩,⟨823785, by decide⟩]) unmarked_context_12_107817_823786 node_context_12_107817_823786
  intro a
  fin_cases a
  · exact context_13_431268_823725
  · exact context_13_431269_823753
  · exact context_13_431270_823776
  · exact context_13_431271_823785

theorem selected_cut_32065 : selected 8 ⟨823799, by decide⟩
    (prefixPartial 13 431272) = some ⟨13, 2, 0, 823799, 431272, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_431272_823799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431272 ⟨823799, by decide⟩ :=
  accepted_of_selected 13 431272 ⟨823799, by decide⟩ ⟨13, 2, 0, 823799, 431272, 1065, 16384⟩
    (by decide) selected_cut_32065

theorem selected_cut_32066 : selected 8 ⟨823819, by decide⟩
    (prefixPartial 13 431273) = some ⟨13, 2, 0, 823819, 431273, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_431273_823819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431273 ⟨823819, by decide⟩ :=
  accepted_of_selected 13 431273 ⟨823819, by decide⟩ ⟨13, 2, 0, 823819, 431273, 1869, 16384⟩
    (by decide) selected_cut_32066

theorem selected_cut_32067 : selected 8 ⟨823840, by decide⟩
    (prefixPartial 13 431274) = some ⟨13, 2, 0, 823840, 431274, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_431274_823840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431274 ⟨823840, by decide⟩ :=
  accepted_of_selected 13 431274 ⟨823840, by decide⟩ ⟨13, 2, 0, 823840, 431274, 1237, 16384⟩
    (by decide) selected_cut_32067

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
