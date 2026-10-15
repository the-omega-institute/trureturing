/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover093
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09027 : selected 8 ⟨250286, by decide⟩
    (prefixPartial 13 93195) = some ⟨13, 2, 0, 250286, 93195, 97, 16384⟩ := by
  decide +kernel

theorem context_13_93195_250286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93195 ⟨250286, by decide⟩ :=
  accepted_of_selected 13 93195 ⟨250286, by decide⟩ ⟨13, 2, 0, 250286, 93195, 97, 16384⟩
    (by decide) selected_cut_09027

theorem unmarked_context_12_23298_250287 : frontier 9 ⟨250287, by decide⟩
    (prefixCache 12 23298) (prefixPartial 12 23298) = false := by
  decide +kernel

theorem node_context_12_23298_250287 : EJMOriginalGlobalDAGData.nodes 9 ⟨250287, by decide⟩ =
    .split (coordinate 12) (![⟨250124, by decide⟩,⟨250231, by decide⟩,⟨250283, by decide⟩,⟨250286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23298_250287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23298 ⟨250287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23298
    ⟨250287, by decide⟩ (by decide) (![⟨250124, by decide⟩,⟨250231, by decide⟩,⟨250283, by decide⟩,⟨250286, by decide⟩]) unmarked_context_12_23298_250287 node_context_12_23298_250287
  intro a
  fin_cases a
  · exact context_13_93192_250124
  · exact context_13_93193_250231
  · exact context_13_93194_250283
  · exact context_13_93195_250286

theorem selected_cut_09028 : selected 7 ⟨250315, by decide⟩
    (prefixPartial 14 372784) = some ⟨14, 2, 0, 250315, 372784, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_372784_250315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372784 ⟨250315, by decide⟩ :=
  accepted_of_selected 14 372784 ⟨250315, by decide⟩ ⟨14, 2, 0, 250315, 372784, 1453, 4096⟩
    (by decide) selected_cut_09028

theorem selected_cut_09029 : selected 7 ⟨250326, by decide⟩
    (prefixPartial 14 372785) = some ⟨14, 2, 0, 250326, 372785, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_372785_250326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372785 ⟨250326, by decide⟩ :=
  accepted_of_selected 14 372785 ⟨250326, by decide⟩ ⟨14, 2, 0, 250326, 372785, 1117, 4096⟩
    (by decide) selected_cut_09029

theorem selected_cut_09030 : selected 7 ⟨250339, by decide⟩
    (prefixPartial 14 372786) = some ⟨14, 2, 0, 250339, 372786, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_372786_250339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372786 ⟨250339, by decide⟩ :=
  accepted_of_selected 14 372786 ⟨250339, by decide⟩ ⟨14, 2, 0, 250339, 372786, 1161, 4096⟩
    (by decide) selected_cut_09030

theorem selected_cut_09031 : selected 7 ⟨250351, by decide⟩
    (prefixPartial 14 372787) = some ⟨14, 2, 0, 250351, 372787, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_372787_250351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372787 ⟨250351, by decide⟩ :=
  accepted_of_selected 14 372787 ⟨250351, by decide⟩ ⟨14, 2, 0, 250351, 372787, 1017, 4096⟩
    (by decide) selected_cut_09031

theorem unmarked_context_13_93196_250352 : frontier 8 ⟨250352, by decide⟩
    (prefixCache 13 93196) (prefixPartial 13 93196) = false := by
  decide +kernel

theorem node_context_13_93196_250352 : EJMOriginalGlobalDAGData.nodes 8 ⟨250352, by decide⟩ =
    .split (coordinate 13) (![⟨250315, by decide⟩,⟨250326, by decide⟩,⟨250339, by decide⟩,⟨250351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93196_250352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93196 ⟨250352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93196
    ⟨250352, by decide⟩ (by decide) (![⟨250315, by decide⟩,⟨250326, by decide⟩,⟨250339, by decide⟩,⟨250351, by decide⟩]) unmarked_context_13_93196_250352 node_context_13_93196_250352
  intro a
  fin_cases a
  · exact context_14_372784_250315
  · exact context_14_372785_250326
  · exact context_14_372786_250339
  · exact context_14_372787_250351

theorem selected_cut_09032 : selected 7 ⟨250375, by decide⟩
    (prefixPartial 14 372788) = some ⟨14, 2, 0, 250375, 372788, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_372788_250375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372788 ⟨250375, by decide⟩ :=
  accepted_of_selected 14 372788 ⟨250375, by decide⟩ ⟨14, 2, 0, 250375, 372788, 1197, 4096⟩
    (by decide) selected_cut_09032

theorem selected_cut_09033 : selected 7 ⟨250405, by decide⟩
    (prefixPartial 14 372789) = some ⟨14, 2, 0, 250405, 372789, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_372789_250405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372789 ⟨250405, by decide⟩ :=
  accepted_of_selected 14 372789 ⟨250405, by decide⟩ ⟨14, 2, 0, 250405, 372789, 1313, 4096⟩
    (by decide) selected_cut_09033

theorem selected_cut_09034 : selected 7 ⟨250430, by decide⟩
    (prefixPartial 14 372790) = some ⟨14, 2, 0, 250430, 372790, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_372790_250430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372790 ⟨250430, by decide⟩ :=
  accepted_of_selected 14 372790 ⟨250430, by decide⟩ ⟨14, 2, 0, 250430, 372790, 1213, 4096⟩
    (by decide) selected_cut_09034

theorem selected_cut_09035 : selected 7 ⟨250444, by decide⟩
    (prefixPartial 14 372791) = some ⟨14, 2, 0, 250444, 372791, 977, 4096⟩ := by
  decide +kernel

theorem context_14_372791_250444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372791 ⟨250444, by decide⟩ :=
  accepted_of_selected 14 372791 ⟨250444, by decide⟩ ⟨14, 2, 0, 250444, 372791, 977, 4096⟩
    (by decide) selected_cut_09035

theorem unmarked_context_13_93197_250445 : frontier 8 ⟨250445, by decide⟩
    (prefixCache 13 93197) (prefixPartial 13 93197) = false := by
  decide +kernel

theorem node_context_13_93197_250445 : EJMOriginalGlobalDAGData.nodes 8 ⟨250445, by decide⟩ =
    .split (coordinate 13) (![⟨250375, by decide⟩,⟨250405, by decide⟩,⟨250430, by decide⟩,⟨250444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93197_250445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93197 ⟨250445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93197
    ⟨250445, by decide⟩ (by decide) (![⟨250375, by decide⟩,⟨250405, by decide⟩,⟨250430, by decide⟩,⟨250444, by decide⟩]) unmarked_context_13_93197_250445 node_context_13_93197_250445
  intro a
  fin_cases a
  · exact context_14_372788_250375
  · exact context_14_372789_250405
  · exact context_14_372790_250430
  · exact context_14_372791_250444

theorem selected_cut_09036 : selected 8 ⟨250473, by decide⟩
    (prefixPartial 13 93198) = some ⟨13, 2, 0, 250473, 93198, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_93198_250473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93198 ⟨250473, by decide⟩ :=
  accepted_of_selected 13 93198 ⟨250473, by decide⟩ ⟨13, 2, 0, 250473, 93198, 2293, 16384⟩
    (by decide) selected_cut_09036

theorem selected_cut_09037 : selected 8 ⟨250482, by decide⟩
    (prefixPartial 13 93199) = some ⟨13, 2, 0, 250482, 93199, 929, 16384⟩ := by
  decide +kernel

theorem context_13_93199_250482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93199 ⟨250482, by decide⟩ :=
  accepted_of_selected 13 93199 ⟨250482, by decide⟩ ⟨13, 2, 0, 250482, 93199, 929, 16384⟩
    (by decide) selected_cut_09037

theorem unmarked_context_12_23299_250483 : frontier 9 ⟨250483, by decide⟩
    (prefixCache 12 23299) (prefixPartial 12 23299) = false := by
  decide +kernel

theorem node_context_12_23299_250483 : EJMOriginalGlobalDAGData.nodes 9 ⟨250483, by decide⟩ =
    .split (coordinate 12) (![⟨250352, by decide⟩,⟨250445, by decide⟩,⟨250473, by decide⟩,⟨250482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23299_250483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23299 ⟨250483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23299
    ⟨250483, by decide⟩ (by decide) (![⟨250352, by decide⟩,⟨250445, by decide⟩,⟨250473, by decide⟩,⟨250482, by decide⟩]) unmarked_context_12_23299_250483 node_context_12_23299_250483
  intro a
  fin_cases a
  · exact context_13_93196_250352
  · exact context_13_93197_250445
  · exact context_13_93198_250473
  · exact context_13_93199_250482

theorem unmarked_context_11_5824_250484 : frontier 10 ⟨250484, by decide⟩
    (prefixCache 11 5824) (prefixPartial 11 5824) = false := by
  decide +kernel

theorem node_context_11_5824_250484 : EJMOriginalGlobalDAGData.nodes 10 ⟨250484, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨250019, by decide⟩,⟨250287, by decide⟩,⟨250483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5824_250484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5824 ⟨250484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5824
    ⟨250484, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨250019, by decide⟩,⟨250287, by decide⟩,⟨250483, by decide⟩]) unmarked_context_11_5824_250484 node_context_11_5824_250484
  intro a
  fin_cases a
  · exact context_12_23296_34034
  · exact context_12_23297_250019
  · exact context_12_23298_250287
  · exact context_12_23299_250483

theorem selected_cut_09038 : selected 8 ⟨250557, by decide⟩
    (prefixPartial 13 93200) = some ⟨13, 2, 0, 250557, 93200, 3857, 16384⟩ := by
  decide +kernel

theorem context_13_93200_250557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93200 ⟨250557, by decide⟩ :=
  accepted_of_selected 13 93200 ⟨250557, by decide⟩ ⟨13, 2, 0, 250557, 93200, 3857, 16384⟩
    (by decide) selected_cut_09038

theorem selected_cut_09039 : selected 7 ⟨250590, by decide⟩
    (prefixPartial 14 372804) = some ⟨14, 2, 0, 250590, 372804, 1505, 4096⟩ := by
  decide +kernel

theorem context_14_372804_250590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372804 ⟨250590, by decide⟩ :=
  accepted_of_selected 14 372804 ⟨250590, by decide⟩ ⟨14, 2, 0, 250590, 372804, 1505, 4096⟩
    (by decide) selected_cut_09039

theorem selected_cut_09040 : selected 7 ⟨250627, by decide⟩
    (prefixPartial 14 372805) = some ⟨14, 2, 0, 250627, 372805, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_372805_250627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372805 ⟨250627, by decide⟩ :=
  accepted_of_selected 14 372805 ⟨250627, by decide⟩ ⟨14, 2, 0, 250627, 372805, 1393, 4096⟩
    (by decide) selected_cut_09040

theorem selected_cut_09041 : selected 7 ⟨250653, by decide⟩
    (prefixPartial 14 372806) = some ⟨14, 2, 0, 250653, 372806, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_372806_250653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372806 ⟨250653, by decide⟩ :=
  accepted_of_selected 14 372806 ⟨250653, by decide⟩ ⟨14, 2, 0, 250653, 372806, 1237, 4096⟩
    (by decide) selected_cut_09041

theorem selected_cut_09042 : selected 7 ⟨250674, by decide⟩
    (prefixPartial 14 372807) = some ⟨14, 2, 0, 250674, 372807, 845, 4096⟩ := by
  decide +kernel

theorem context_14_372807_250674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372807 ⟨250674, by decide⟩ :=
  accepted_of_selected 14 372807 ⟨250674, by decide⟩ ⟨14, 2, 0, 250674, 372807, 845, 4096⟩
    (by decide) selected_cut_09042

theorem unmarked_context_13_93201_250675 : frontier 8 ⟨250675, by decide⟩
    (prefixCache 13 93201) (prefixPartial 13 93201) = false := by
  decide +kernel

theorem node_context_13_93201_250675 : EJMOriginalGlobalDAGData.nodes 8 ⟨250675, by decide⟩ =
    .split (coordinate 13) (![⟨250590, by decide⟩,⟨250627, by decide⟩,⟨250653, by decide⟩,⟨250674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93201_250675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93201 ⟨250675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93201
    ⟨250675, by decide⟩ (by decide) (![⟨250590, by decide⟩,⟨250627, by decide⟩,⟨250653, by decide⟩,⟨250674, by decide⟩]) unmarked_context_13_93201_250675 node_context_13_93201_250675
  intro a
  fin_cases a
  · exact context_14_372804_250590
  · exact context_14_372805_250627
  · exact context_14_372806_250653
  · exact context_14_372807_250674

theorem selected_cut_09043 : selected 8 ⟨250714, by decide⟩
    (prefixPartial 13 93202) = some ⟨13, 2, 0, 250714, 93202, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_93202_250714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93202 ⟨250714, by decide⟩ :=
  accepted_of_selected 13 93202 ⟨250714, by decide⟩ ⟨13, 2, 0, 250714, 93202, 2021, 16384⟩
    (by decide) selected_cut_09043

theorem selected_cut_09044 : selected 8 ⟨250738, by decide⟩
    (prefixPartial 13 93203) = some ⟨13, 2, 0, 250738, 93203, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_93203_250738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93203 ⟨250738, by decide⟩ :=
  accepted_of_selected 13 93203 ⟨250738, by decide⟩ ⟨13, 2, 0, 250738, 93203, 1165, 16384⟩
    (by decide) selected_cut_09044

theorem unmarked_context_12_23300_250739 : frontier 9 ⟨250739, by decide⟩
    (prefixCache 12 23300) (prefixPartial 12 23300) = false := by
  decide +kernel

theorem node_context_12_23300_250739 : EJMOriginalGlobalDAGData.nodes 9 ⟨250739, by decide⟩ =
    .split (coordinate 12) (![⟨250557, by decide⟩,⟨250675, by decide⟩,⟨250714, by decide⟩,⟨250738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23300_250739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23300 ⟨250739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23300
    ⟨250739, by decide⟩ (by decide) (![⟨250557, by decide⟩,⟨250675, by decide⟩,⟨250714, by decide⟩,⟨250738, by decide⟩]) unmarked_context_12_23300_250739 node_context_12_23300_250739
  intro a
  fin_cases a
  · exact context_13_93200_250557
  · exact context_13_93201_250675
  · exact context_13_93202_250714
  · exact context_13_93203_250738

theorem selected_cut_09045 : selected 8 ⟨250795, by decide⟩
    (prefixPartial 13 93204) = some ⟨13, 2, 0, 250795, 93204, 4017, 16384⟩ := by
  decide +kernel

theorem context_13_93204_250795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93204 ⟨250795, by decide⟩ :=
  accepted_of_selected 13 93204 ⟨250795, by decide⟩ ⟨13, 2, 0, 250795, 93204, 4017, 16384⟩
    (by decide) selected_cut_09045

theorem selected_cut_09046 : selected 7 ⟨250815, by decide⟩
    (prefixPartial 14 372820) = some ⟨14, 2, 0, 250815, 372820, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_372820_250815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372820 ⟨250815, by decide⟩ :=
  accepted_of_selected 14 372820 ⟨250815, by decide⟩ ⟨14, 2, 0, 250815, 372820, 1041, 4096⟩
    (by decide) selected_cut_09046

theorem selected_cut_09047 : selected 7 ⟨250840, by decide⟩
    (prefixPartial 14 372821) = some ⟨14, 2, 0, 250840, 372821, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_372821_250840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372821 ⟨250840, by decide⟩ :=
  accepted_of_selected 14 372821 ⟨250840, by decide⟩ ⟨14, 2, 0, 250840, 372821, 1177, 4096⟩
    (by decide) selected_cut_09047

theorem selected_cut_09048 : selected 7 ⟨250858, by decide⟩
    (prefixPartial 14 372822) = some ⟨14, 2, 0, 250858, 372822, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_372822_250858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372822 ⟨250858, by decide⟩ :=
  accepted_of_selected 14 372822 ⟨250858, by decide⟩ ⟨14, 2, 0, 250858, 372822, 1053, 4096⟩
    (by decide) selected_cut_09048

theorem selected_cut_09049 : selected 7 ⟨250870, by decide⟩
    (prefixPartial 14 372823) = some ⟨14, 2, 0, 250870, 372823, 829, 4096⟩ := by
  decide +kernel

theorem context_14_372823_250870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372823 ⟨250870, by decide⟩ :=
  accepted_of_selected 14 372823 ⟨250870, by decide⟩ ⟨14, 2, 0, 250870, 372823, 829, 4096⟩
    (by decide) selected_cut_09049

theorem unmarked_context_13_93205_250871 : frontier 8 ⟨250871, by decide⟩
    (prefixCache 13 93205) (prefixPartial 13 93205) = false := by
  decide +kernel

theorem node_context_13_93205_250871 : EJMOriginalGlobalDAGData.nodes 8 ⟨250871, by decide⟩ =
    .split (coordinate 13) (![⟨250815, by decide⟩,⟨250840, by decide⟩,⟨250858, by decide⟩,⟨250870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93205_250871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93205 ⟨250871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93205
    ⟨250871, by decide⟩ (by decide) (![⟨250815, by decide⟩,⟨250840, by decide⟩,⟨250858, by decide⟩,⟨250870, by decide⟩]) unmarked_context_13_93205_250871 node_context_13_93205_250871
  intro a
  fin_cases a
  · exact context_14_372820_250815
  · exact context_14_372821_250840
  · exact context_14_372822_250858
  · exact context_14_372823_250870

theorem selected_cut_09050 : selected 8 ⟨250905, by decide⟩
    (prefixPartial 13 93206) = some ⟨13, 2, 0, 250905, 93206, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_93206_250905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93206 ⟨250905, by decide⟩ :=
  accepted_of_selected 13 93206 ⟨250905, by decide⟩ ⟨13, 2, 0, 250905, 93206, 2073, 16384⟩
    (by decide) selected_cut_09050

theorem selected_cut_09051 : selected 8 ⟨250920, by decide⟩
    (prefixPartial 13 93207) = some ⟨13, 2, 0, 250920, 93207, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_93207_250920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93207 ⟨250920, by decide⟩ :=
  accepted_of_selected 13 93207 ⟨250920, by decide⟩ ⟨13, 2, 0, 250920, 93207, 1029, 16384⟩
    (by decide) selected_cut_09051

theorem unmarked_context_12_23301_250921 : frontier 9 ⟨250921, by decide⟩
    (prefixCache 12 23301) (prefixPartial 12 23301) = false := by
  decide +kernel

theorem node_context_12_23301_250921 : EJMOriginalGlobalDAGData.nodes 9 ⟨250921, by decide⟩ =
    .split (coordinate 12) (![⟨250795, by decide⟩,⟨250871, by decide⟩,⟨250905, by decide⟩,⟨250920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23301_250921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23301 ⟨250921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23301
    ⟨250921, by decide⟩ (by decide) (![⟨250795, by decide⟩,⟨250871, by decide⟩,⟨250905, by decide⟩,⟨250920, by decide⟩]) unmarked_context_12_23301_250921 node_context_12_23301_250921
  intro a
  fin_cases a
  · exact context_13_93204_250795
  · exact context_13_93205_250871
  · exact context_13_93206_250905
  · exact context_13_93207_250920

theorem selected_cut_09052 : selected 7 ⟨250946, by decide⟩
    (prefixPartial 14 372832) = some ⟨14, 2, 0, 250946, 372832, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_372832_250946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372832 ⟨250946, by decide⟩ :=
  accepted_of_selected 14 372832 ⟨250946, by decide⟩ ⟨14, 2, 0, 250946, 372832, 1361, 4096⟩
    (by decide) selected_cut_09052

theorem selected_cut_09053 : selected 7 ⟨250970, by decide⟩
    (prefixPartial 14 372833) = some ⟨14, 2, 0, 250970, 372833, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_372833_250970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372833 ⟨250970, by decide⟩ :=
  accepted_of_selected 14 372833 ⟨250970, by decide⟩ ⟨14, 2, 0, 250970, 372833, 1253, 4096⟩
    (by decide) selected_cut_09053

theorem selected_cut_09054 : selected 7 ⟨250994, by decide⟩
    (prefixPartial 14 372834) = some ⟨14, 2, 0, 250994, 372834, 1465, 4096⟩ := by
  decide +kernel

theorem context_14_372834_250994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372834 ⟨250994, by decide⟩ :=
  accepted_of_selected 14 372834 ⟨250994, by decide⟩ ⟨14, 2, 0, 250994, 372834, 1465, 4096⟩
    (by decide) selected_cut_09054

theorem selected_cut_09055 : selected 7 ⟨251012, by decide⟩
    (prefixPartial 14 372835) = some ⟨14, 2, 0, 251012, 372835, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_372835_251012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372835 ⟨251012, by decide⟩ :=
  accepted_of_selected 14 372835 ⟨251012, by decide⟩ ⟨14, 2, 0, 251012, 372835, 1009, 4096⟩
    (by decide) selected_cut_09055

theorem unmarked_context_13_93208_251013 : frontier 8 ⟨251013, by decide⟩
    (prefixCache 13 93208) (prefixPartial 13 93208) = false := by
  decide +kernel

theorem node_context_13_93208_251013 : EJMOriginalGlobalDAGData.nodes 8 ⟨251013, by decide⟩ =
    .split (coordinate 13) (![⟨250946, by decide⟩,⟨250970, by decide⟩,⟨250994, by decide⟩,⟨251012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93208_251013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93208 ⟨251013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93208
    ⟨251013, by decide⟩ (by decide) (![⟨250946, by decide⟩,⟨250970, by decide⟩,⟨250994, by decide⟩,⟨251012, by decide⟩]) unmarked_context_13_93208_251013 node_context_13_93208_251013
  intro a
  fin_cases a
  · exact context_14_372832_250946
  · exact context_14_372833_250970
  · exact context_14_372834_250994
  · exact context_14_372835_251012

theorem selected_cut_09056 : selected 7 ⟨251049, by decide⟩
    (prefixPartial 14 372836) = some ⟨14, 2, 0, 251049, 372836, 1481, 4096⟩ := by
  decide +kernel

theorem context_14_372836_251049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372836 ⟨251049, by decide⟩ :=
  accepted_of_selected 14 372836 ⟨251049, by decide⟩ ⟨14, 2, 0, 251049, 372836, 1481, 4096⟩
    (by decide) selected_cut_09056

theorem selected_cut_09057 : selected 7 ⟨251082, by decide⟩
    (prefixPartial 14 372837) = some ⟨14, 2, 0, 251082, 372837, 1373, 4096⟩ := by
  decide +kernel

theorem context_14_372837_251082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372837 ⟨251082, by decide⟩ :=
  accepted_of_selected 14 372837 ⟨251082, by decide⟩ ⟨14, 2, 0, 251082, 372837, 1373, 4096⟩
    (by decide) selected_cut_09057

theorem selected_cut_09058 : selected 7 ⟨251101, by decide⟩
    (prefixPartial 14 372838) = some ⟨14, 2, 0, 251101, 372838, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_372838_251101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372838 ⟨251101, by decide⟩ :=
  accepted_of_selected 14 372838 ⟨251101, by decide⟩ ⟨14, 2, 0, 251101, 372838, 1205, 4096⟩
    (by decide) selected_cut_09058

theorem selected_cut_09059 : selected 7 ⟨251120, by decide⟩
    (prefixPartial 14 372839) = some ⟨14, 2, 0, 251120, 372839, 909, 4096⟩ := by
  decide +kernel

theorem context_14_372839_251120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372839 ⟨251120, by decide⟩ :=
  accepted_of_selected 14 372839 ⟨251120, by decide⟩ ⟨14, 2, 0, 251120, 372839, 909, 4096⟩
    (by decide) selected_cut_09059

theorem unmarked_context_13_93209_251121 : frontier 8 ⟨251121, by decide⟩
    (prefixCache 13 93209) (prefixPartial 13 93209) = false := by
  decide +kernel

theorem node_context_13_93209_251121 : EJMOriginalGlobalDAGData.nodes 8 ⟨251121, by decide⟩ =
    .split (coordinate 13) (![⟨251049, by decide⟩,⟨251082, by decide⟩,⟨251101, by decide⟩,⟨251120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93209_251121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93209 ⟨251121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93209
    ⟨251121, by decide⟩ (by decide) (![⟨251049, by decide⟩,⟨251082, by decide⟩,⟨251101, by decide⟩,⟨251120, by decide⟩]) unmarked_context_13_93209_251121 node_context_13_93209_251121
  intro a
  fin_cases a
  · exact context_14_372836_251049
  · exact context_14_372837_251082
  · exact context_14_372838_251101
  · exact context_14_372839_251120

theorem selected_cut_09060 : selected 8 ⟨251162, by decide⟩
    (prefixPartial 13 93210) = some ⟨13, 2, 0, 251162, 93210, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_93210_251162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93210 ⟨251162, by decide⟩ :=
  accepted_of_selected 13 93210 ⟨251162, by decide⟩ ⟨13, 2, 0, 251162, 93210, 2377, 16384⟩
    (by decide) selected_cut_09060

theorem selected_cut_09061 : selected 8 ⟨251185, by decide⟩
    (prefixPartial 13 93211) = some ⟨13, 2, 0, 251185, 93211, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_93211_251185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93211 ⟨251185, by decide⟩ :=
  accepted_of_selected 13 93211 ⟨251185, by decide⟩ ⟨13, 2, 0, 251185, 93211, 1193, 16384⟩
    (by decide) selected_cut_09061

theorem unmarked_context_12_23302_251186 : frontier 9 ⟨251186, by decide⟩
    (prefixCache 12 23302) (prefixPartial 12 23302) = false := by
  decide +kernel

theorem node_context_12_23302_251186 : EJMOriginalGlobalDAGData.nodes 9 ⟨251186, by decide⟩ =
    .split (coordinate 12) (![⟨251013, by decide⟩,⟨251121, by decide⟩,⟨251162, by decide⟩,⟨251185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23302_251186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23302 ⟨251186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23302
    ⟨251186, by decide⟩ (by decide) (![⟨251013, by decide⟩,⟨251121, by decide⟩,⟨251162, by decide⟩,⟨251185, by decide⟩]) unmarked_context_12_23302_251186 node_context_12_23302_251186
  intro a
  fin_cases a
  · exact context_13_93208_251013
  · exact context_13_93209_251121
  · exact context_13_93210_251162
  · exact context_13_93211_251185

theorem selected_cut_09062 : selected 7 ⟨251202, by decide⟩
    (prefixPartial 14 372848) = some ⟨14, 2, 0, 251202, 372848, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_372848_251202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372848 ⟨251202, by decide⟩ :=
  accepted_of_selected 14 372848 ⟨251202, by decide⟩ ⟨14, 2, 0, 251202, 372848, 1009, 4096⟩
    (by decide) selected_cut_09062

theorem selected_cut_09063 : selected 7 ⟨251215, by decide⟩
    (prefixPartial 14 372849) = some ⟨14, 2, 0, 251215, 372849, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_372849_251215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372849 ⟨251215, by decide⟩ :=
  accepted_of_selected 14 372849 ⟨251215, by decide⟩ ⟨14, 2, 0, 251215, 372849, 1069, 4096⟩
    (by decide) selected_cut_09063

theorem selected_cut_09064 : selected 7 ⟨251232, by decide⟩
    (prefixPartial 14 372850) = some ⟨14, 2, 0, 251232, 372850, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_372850_251232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372850 ⟨251232, by decide⟩ :=
  accepted_of_selected 14 372850 ⟨251232, by decide⟩ ⟨14, 2, 0, 251232, 372850, 1217, 4096⟩
    (by decide) selected_cut_09064

theorem selected_cut_09065 : selected 7 ⟨251246, by decide⟩
    (prefixPartial 14 372851) = some ⟨14, 2, 0, 251246, 372851, 953, 4096⟩ := by
  decide +kernel

theorem context_14_372851_251246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372851 ⟨251246, by decide⟩ :=
  accepted_of_selected 14 372851 ⟨251246, by decide⟩ ⟨14, 2, 0, 251246, 372851, 953, 4096⟩
    (by decide) selected_cut_09065

theorem unmarked_context_13_93212_251247 : frontier 8 ⟨251247, by decide⟩
    (prefixCache 13 93212) (prefixPartial 13 93212) = false := by
  decide +kernel

theorem node_context_13_93212_251247 : EJMOriginalGlobalDAGData.nodes 8 ⟨251247, by decide⟩ =
    .split (coordinate 13) (![⟨251202, by decide⟩,⟨251215, by decide⟩,⟨251232, by decide⟩,⟨251246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93212_251247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93212 ⟨251247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93212
    ⟨251247, by decide⟩ (by decide) (![⟨251202, by decide⟩,⟨251215, by decide⟩,⟨251232, by decide⟩,⟨251246, by decide⟩]) unmarked_context_13_93212_251247 node_context_13_93212_251247
  intro a
  fin_cases a
  · exact context_14_372848_251202
  · exact context_14_372849_251215
  · exact context_14_372850_251232
  · exact context_14_372851_251246

theorem selected_cut_09066 : selected 7 ⟨251276, by decide⟩
    (prefixPartial 14 372852) = some ⟨14, 2, 0, 251276, 372852, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_372852_251276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372852 ⟨251276, by decide⟩ :=
  accepted_of_selected 14 372852 ⟨251276, by decide⟩ ⟨14, 2, 0, 251276, 372852, 1277, 4096⟩
    (by decide) selected_cut_09066

theorem selected_cut_09067 : selected 7 ⟨251310, by decide⟩
    (prefixPartial 14 372853) = some ⟨14, 2, 0, 251310, 372853, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_372853_251310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372853 ⟨251310, by decide⟩ :=
  accepted_of_selected 14 372853 ⟨251310, by decide⟩ ⟨14, 2, 0, 251310, 372853, 1357, 4096⟩
    (by decide) selected_cut_09067

theorem selected_cut_09068 : selected 7 ⟨251333, by decide⟩
    (prefixPartial 14 372854) = some ⟨14, 2, 0, 251333, 372854, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_372854_251333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372854 ⟨251333, by decide⟩ :=
  accepted_of_selected 14 372854 ⟨251333, by decide⟩ ⟨14, 2, 0, 251333, 372854, 1173, 4096⟩
    (by decide) selected_cut_09068

theorem selected_cut_09069 : selected 7 ⟨251344, by decide⟩
    (prefixPartial 14 372855) = some ⟨14, 2, 0, 251344, 372855, 849, 4096⟩ := by
  decide +kernel

theorem context_14_372855_251344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372855 ⟨251344, by decide⟩ :=
  accepted_of_selected 14 372855 ⟨251344, by decide⟩ ⟨14, 2, 0, 251344, 372855, 849, 4096⟩
    (by decide) selected_cut_09069

theorem unmarked_context_13_93213_251345 : frontier 8 ⟨251345, by decide⟩
    (prefixCache 13 93213) (prefixPartial 13 93213) = false := by
  decide +kernel

theorem node_context_13_93213_251345 : EJMOriginalGlobalDAGData.nodes 8 ⟨251345, by decide⟩ =
    .split (coordinate 13) (![⟨251276, by decide⟩,⟨251310, by decide⟩,⟨251333, by decide⟩,⟨251344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93213_251345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93213 ⟨251345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93213
    ⟨251345, by decide⟩ (by decide) (![⟨251276, by decide⟩,⟨251310, by decide⟩,⟨251333, by decide⟩,⟨251344, by decide⟩]) unmarked_context_13_93213_251345 node_context_13_93213_251345
  intro a
  fin_cases a
  · exact context_14_372852_251276
  · exact context_14_372853_251310
  · exact context_14_372854_251333
  · exact context_14_372855_251344

theorem selected_cut_09070 : selected 8 ⟨251376, by decide⟩
    (prefixPartial 13 93214) = some ⟨13, 2, 0, 251376, 93214, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_93214_251376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93214 ⟨251376, by decide⟩ :=
  accepted_of_selected 13 93214 ⟨251376, by decide⟩ ⟨13, 2, 0, 251376, 93214, 2173, 16384⟩
    (by decide) selected_cut_09070

theorem selected_cut_09071 : selected 8 ⟨251385, by decide⟩
    (prefixPartial 13 93215) = some ⟨13, 2, 0, 251385, 93215, 933, 16384⟩ := by
  decide +kernel

theorem context_13_93215_251385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93215 ⟨251385, by decide⟩ :=
  accepted_of_selected 13 93215 ⟨251385, by decide⟩ ⟨13, 2, 0, 251385, 93215, 933, 16384⟩
    (by decide) selected_cut_09071

theorem unmarked_context_12_23303_251386 : frontier 9 ⟨251386, by decide⟩
    (prefixCache 12 23303) (prefixPartial 12 23303) = false := by
  decide +kernel

theorem node_context_12_23303_251386 : EJMOriginalGlobalDAGData.nodes 9 ⟨251386, by decide⟩ =
    .split (coordinate 12) (![⟨251247, by decide⟩,⟨251345, by decide⟩,⟨251376, by decide⟩,⟨251385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23303_251386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23303 ⟨251386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23303
    ⟨251386, by decide⟩ (by decide) (![⟨251247, by decide⟩,⟨251345, by decide⟩,⟨251376, by decide⟩,⟨251385, by decide⟩]) unmarked_context_12_23303_251386 node_context_12_23303_251386
  intro a
  fin_cases a
  · exact context_13_93212_251247
  · exact context_13_93213_251345
  · exact context_13_93214_251376
  · exact context_13_93215_251385

theorem unmarked_context_11_5825_251387 : frontier 10 ⟨251387, by decide⟩
    (prefixCache 11 5825) (prefixPartial 11 5825) = false := by
  decide +kernel

theorem node_context_11_5825_251387 : EJMOriginalGlobalDAGData.nodes 10 ⟨251387, by decide⟩ =
    .split (coordinate 11) (![⟨250739, by decide⟩,⟨250921, by decide⟩,⟨251186, by decide⟩,⟨251386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5825_251387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5825 ⟨251387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5825
    ⟨251387, by decide⟩ (by decide) (![⟨250739, by decide⟩,⟨250921, by decide⟩,⟨251186, by decide⟩,⟨251386, by decide⟩]) unmarked_context_11_5825_251387 node_context_11_5825_251387
  intro a
  fin_cases a
  · exact context_12_23300_250739
  · exact context_12_23301_250921
  · exact context_12_23302_251186
  · exact context_12_23303_251386

theorem selected_cut_09072 : selected 8 ⟨251427, by decide⟩
    (prefixPartial 13 93216) = some ⟨13, 2, 0, 251427, 93216, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_93216_251427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93216 ⟨251427, by decide⟩ :=
  accepted_of_selected 13 93216 ⟨251427, by decide⟩ ⟨13, 2, 0, 251427, 93216, 3009, 16384⟩
    (by decide) selected_cut_09072

theorem selected_cut_09073 : selected 7 ⟨251458, by decide⟩
    (prefixPartial 14 372868) = some ⟨14, 2, 0, 251458, 372868, 1473, 4096⟩ := by
  decide +kernel

theorem context_14_372868_251458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372868 ⟨251458, by decide⟩ :=
  accepted_of_selected 14 372868 ⟨251458, by decide⟩ ⟨14, 2, 0, 251458, 372868, 1473, 4096⟩
    (by decide) selected_cut_09073

theorem selected_cut_09074 : selected 7 ⟨251481, by decide⟩
    (prefixPartial 14 372869) = some ⟨14, 2, 0, 251481, 372869, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_372869_251481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372869 ⟨251481, by decide⟩ :=
  accepted_of_selected 14 372869 ⟨251481, by decide⟩ ⟨14, 2, 0, 251481, 372869, 1153, 4096⟩
    (by decide) selected_cut_09074

theorem selected_cut_09075 : selected 7 ⟨251500, by decide⟩
    (prefixPartial 14 372870) = some ⟨14, 2, 0, 251500, 372870, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_372870_251500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372870 ⟨251500, by decide⟩ :=
  accepted_of_selected 14 372870 ⟨251500, by decide⟩ ⟨14, 2, 0, 251500, 372870, 1173, 4096⟩
    (by decide) selected_cut_09075

theorem selected_cut_09076 : selected 7 ⟨251513, by decide⟩
    (prefixPartial 14 372871) = some ⟨14, 2, 0, 251513, 372871, 797, 4096⟩ := by
  decide +kernel

theorem context_14_372871_251513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372871 ⟨251513, by decide⟩ :=
  accepted_of_selected 14 372871 ⟨251513, by decide⟩ ⟨14, 2, 0, 251513, 372871, 797, 4096⟩
    (by decide) selected_cut_09076

theorem unmarked_context_13_93217_251514 : frontier 8 ⟨251514, by decide⟩
    (prefixCache 13 93217) (prefixPartial 13 93217) = false := by
  decide +kernel

theorem node_context_13_93217_251514 : EJMOriginalGlobalDAGData.nodes 8 ⟨251514, by decide⟩ =
    .split (coordinate 13) (![⟨251458, by decide⟩,⟨251481, by decide⟩,⟨251500, by decide⟩,⟨251513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93217_251514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93217 ⟨251514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93217
    ⟨251514, by decide⟩ (by decide) (![⟨251458, by decide⟩,⟨251481, by decide⟩,⟨251500, by decide⟩,⟨251513, by decide⟩]) unmarked_context_13_93217_251514 node_context_13_93217_251514
  intro a
  fin_cases a
  · exact context_14_372868_251458
  · exact context_14_372869_251481
  · exact context_14_372870_251500
  · exact context_14_372871_251513

theorem selected_cut_09077 : selected 8 ⟨251563, by decide⟩
    (prefixPartial 13 93218) = some ⟨13, 2, 0, 251563, 93218, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_93218_251563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93218 ⟨251563, by decide⟩ :=
  accepted_of_selected 13 93218 ⟨251563, by decide⟩ ⟨13, 2, 0, 251563, 93218, 2509, 16384⟩
    (by decide) selected_cut_09077

theorem selected_cut_09078 : selected 8 ⟨251587, by decide⟩
    (prefixPartial 13 93219) = some ⟨13, 2, 0, 251587, 93219, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_93219_251587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93219 ⟨251587, by decide⟩ :=
  accepted_of_selected 13 93219 ⟨251587, by decide⟩ ⟨13, 2, 0, 251587, 93219, 1181, 16384⟩
    (by decide) selected_cut_09078

theorem unmarked_context_12_23304_251588 : frontier 9 ⟨251588, by decide⟩
    (prefixCache 12 23304) (prefixPartial 12 23304) = false := by
  decide +kernel

theorem node_context_12_23304_251588 : EJMOriginalGlobalDAGData.nodes 9 ⟨251588, by decide⟩ =
    .split (coordinate 12) (![⟨251427, by decide⟩,⟨251514, by decide⟩,⟨251563, by decide⟩,⟨251587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23304_251588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23304 ⟨251588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23304
    ⟨251588, by decide⟩ (by decide) (![⟨251427, by decide⟩,⟨251514, by decide⟩,⟨251563, by decide⟩,⟨251587, by decide⟩]) unmarked_context_12_23304_251588 node_context_12_23304_251588
  intro a
  fin_cases a
  · exact context_13_93216_251427
  · exact context_13_93217_251514
  · exact context_13_93218_251563
  · exact context_13_93219_251587

theorem selected_cut_09079 : selected 8 ⟨251641, by decide⟩
    (prefixPartial 13 93220) = some ⟨13, 2, 0, 251641, 93220, 3573, 16384⟩ := by
  decide +kernel

theorem context_13_93220_251641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93220 ⟨251641, by decide⟩ :=
  accepted_of_selected 13 93220 ⟨251641, by decide⟩ ⟨13, 2, 0, 251641, 93220, 3573, 16384⟩
    (by decide) selected_cut_09079

theorem selected_cut_09080 : selected 7 ⟨251664, by decide⟩
    (prefixPartial 14 372884) = some ⟨14, 2, 0, 251664, 372884, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_372884_251664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372884 ⟨251664, by decide⟩ :=
  accepted_of_selected 14 372884 ⟨251664, by decide⟩ ⟨14, 2, 0, 251664, 372884, 1125, 4096⟩
    (by decide) selected_cut_09080

theorem selected_cut_09081 : selected 7 ⟨251692, by decide⟩
    (prefixPartial 14 372885) = some ⟨14, 2, 0, 251692, 372885, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_372885_251692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372885 ⟨251692, by decide⟩ :=
  accepted_of_selected 14 372885 ⟨251692, by decide⟩ ⟨14, 2, 0, 251692, 372885, 1201, 4096⟩
    (by decide) selected_cut_09081

theorem selected_cut_09082 : selected 7 ⟨251704, by decide⟩
    (prefixPartial 14 372886) = some ⟨14, 2, 0, 251704, 372886, 961, 4096⟩ := by
  decide +kernel

theorem context_14_372886_251704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372886 ⟨251704, by decide⟩ :=
  accepted_of_selected 14 372886 ⟨251704, by decide⟩ ⟨14, 2, 0, 251704, 372886, 961, 4096⟩
    (by decide) selected_cut_09082

theorem selected_cut_09083 : selected 7 ⟨251715, by decide⟩
    (prefixPartial 14 372887) = some ⟨14, 2, 0, 251715, 372887, 829, 4096⟩ := by
  decide +kernel

theorem context_14_372887_251715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372887 ⟨251715, by decide⟩ :=
  accepted_of_selected 14 372887 ⟨251715, by decide⟩ ⟨14, 2, 0, 251715, 372887, 829, 4096⟩
    (by decide) selected_cut_09083

theorem unmarked_context_13_93221_251716 : frontier 8 ⟨251716, by decide⟩
    (prefixCache 13 93221) (prefixPartial 13 93221) = false := by
  decide +kernel

theorem node_context_13_93221_251716 : EJMOriginalGlobalDAGData.nodes 8 ⟨251716, by decide⟩ =
    .split (coordinate 13) (![⟨251664, by decide⟩,⟨251692, by decide⟩,⟨251704, by decide⟩,⟨251715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93221_251716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93221 ⟨251716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93221
    ⟨251716, by decide⟩ (by decide) (![⟨251664, by decide⟩,⟨251692, by decide⟩,⟨251704, by decide⟩,⟨251715, by decide⟩]) unmarked_context_13_93221_251716 node_context_13_93221_251716
  intro a
  fin_cases a
  · exact context_14_372884_251664
  · exact context_14_372885_251692
  · exact context_14_372886_251704
  · exact context_14_372887_251715

theorem selected_cut_09084 : selected 8 ⟨251756, by decide⟩
    (prefixPartial 13 93222) = some ⟨13, 2, 0, 251756, 93222, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_93222_251756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93222 ⟨251756, by decide⟩ :=
  accepted_of_selected 13 93222 ⟨251756, by decide⟩ ⟨13, 2, 0, 251756, 93222, 2589, 16384⟩
    (by decide) selected_cut_09084

theorem selected_cut_09085 : selected 8 ⟨251771, by decide⟩
    (prefixPartial 13 93223) = some ⟨13, 2, 0, 251771, 93223, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_93223_251771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93223 ⟨251771, by decide⟩ :=
  accepted_of_selected 13 93223 ⟨251771, by decide⟩ ⟨13, 2, 0, 251771, 93223, 1137, 16384⟩
    (by decide) selected_cut_09085

theorem unmarked_context_12_23305_251772 : frontier 9 ⟨251772, by decide⟩
    (prefixCache 12 23305) (prefixPartial 12 23305) = false := by
  decide +kernel

theorem node_context_12_23305_251772 : EJMOriginalGlobalDAGData.nodes 9 ⟨251772, by decide⟩ =
    .split (coordinate 12) (![⟨251641, by decide⟩,⟨251716, by decide⟩,⟨251756, by decide⟩,⟨251771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23305_251772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23305 ⟨251772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23305
    ⟨251772, by decide⟩ (by decide) (![⟨251641, by decide⟩,⟨251716, by decide⟩,⟨251756, by decide⟩,⟨251771, by decide⟩]) unmarked_context_12_23305_251772 node_context_12_23305_251772
  intro a
  fin_cases a
  · exact context_13_93220_251641
  · exact context_13_93221_251716
  · exact context_13_93222_251756
  · exact context_13_93223_251771

theorem selected_cut_09086 : selected 7 ⟨251786, by decide⟩
    (prefixPartial 14 372896) = some ⟨14, 2, 0, 251786, 372896, 881, 4096⟩ := by
  decide +kernel

theorem context_14_372896_251786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372896 ⟨251786, by decide⟩ :=
  accepted_of_selected 14 372896 ⟨251786, by decide⟩ ⟨14, 2, 0, 251786, 372896, 881, 4096⟩
    (by decide) selected_cut_09086

theorem selected_cut_09087 : selected 7 ⟨251806, by decide⟩
    (prefixPartial 14 372897) = some ⟨14, 2, 0, 251806, 372897, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_372897_251806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372897 ⟨251806, by decide⟩ :=
  accepted_of_selected 14 372897 ⟨251806, by decide⟩ ⟨14, 2, 0, 251806, 372897, 1313, 4096⟩
    (by decide) selected_cut_09087

theorem selected_cut_09088 : selected 7 ⟨251820, by decide⟩
    (prefixPartial 14 372898) = some ⟨14, 2, 0, 251820, 372898, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_372898_251820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372898 ⟨251820, by decide⟩ :=
  accepted_of_selected 14 372898 ⟨251820, by decide⟩ ⟨14, 2, 0, 251820, 372898, 1073, 4096⟩
    (by decide) selected_cut_09088

theorem selected_cut_09089 : selected 7 ⟨251834, by decide⟩
    (prefixPartial 14 372899) = some ⟨14, 2, 0, 251834, 372899, 941, 4096⟩ := by
  decide +kernel

theorem context_14_372899_251834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372899 ⟨251834, by decide⟩ :=
  accepted_of_selected 14 372899 ⟨251834, by decide⟩ ⟨14, 2, 0, 251834, 372899, 941, 4096⟩
    (by decide) selected_cut_09089

theorem unmarked_context_13_93224_251835 : frontier 8 ⟨251835, by decide⟩
    (prefixCache 13 93224) (prefixPartial 13 93224) = false := by
  decide +kernel

theorem node_context_13_93224_251835 : EJMOriginalGlobalDAGData.nodes 8 ⟨251835, by decide⟩ =
    .split (coordinate 13) (![⟨251786, by decide⟩,⟨251806, by decide⟩,⟨251820, by decide⟩,⟨251834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93224_251835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93224 ⟨251835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93224
    ⟨251835, by decide⟩ (by decide) (![⟨251786, by decide⟩,⟨251806, by decide⟩,⟨251820, by decide⟩,⟨251834, by decide⟩]) unmarked_context_13_93224_251835 node_context_13_93224_251835
  intro a
  fin_cases a
  · exact context_14_372896_251786
  · exact context_14_372897_251806
  · exact context_14_372898_251820
  · exact context_14_372899_251834

theorem selected_cut_09090 : selected 7 ⟨251873, by decide⟩
    (prefixPartial 14 372900) = some ⟨14, 2, 0, 251873, 372900, 1689, 4096⟩ := by
  decide +kernel

theorem context_14_372900_251873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372900 ⟨251873, by decide⟩ :=
  accepted_of_selected 14 372900 ⟨251873, by decide⟩ ⟨14, 2, 0, 251873, 372900, 1689, 4096⟩
    (by decide) selected_cut_09090

theorem selected_cut_09091 : selected 7 ⟨251900, by decide⟩
    (prefixPartial 14 372901) = some ⟨14, 2, 0, 251900, 372901, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_372901_251900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372901 ⟨251900, by decide⟩ :=
  accepted_of_selected 14 372901 ⟨251900, by decide⟩ ⟨14, 2, 0, 251900, 372901, 1273, 4096⟩
    (by decide) selected_cut_09091

theorem selected_cut_09092 : selected 7 ⟨251912, by decide⟩
    (prefixPartial 14 372902) = some ⟨14, 2, 0, 251912, 372902, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_372902_251912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372902 ⟨251912, by decide⟩ :=
  accepted_of_selected 14 372902 ⟨251912, by decide⟩ ⟨14, 2, 0, 251912, 372902, 1053, 4096⟩
    (by decide) selected_cut_09092

theorem selected_cut_09093 : selected 7 ⟨251926, by decide⟩
    (prefixPartial 14 372903) = some ⟨14, 2, 0, 251926, 372903, 869, 4096⟩ := by
  decide +kernel

theorem context_14_372903_251926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372903 ⟨251926, by decide⟩ :=
  accepted_of_selected 14 372903 ⟨251926, by decide⟩ ⟨14, 2, 0, 251926, 372903, 869, 4096⟩
    (by decide) selected_cut_09093

theorem unmarked_context_13_93225_251927 : frontier 8 ⟨251927, by decide⟩
    (prefixCache 13 93225) (prefixPartial 13 93225) = false := by
  decide +kernel

theorem node_context_13_93225_251927 : EJMOriginalGlobalDAGData.nodes 8 ⟨251927, by decide⟩ =
    .split (coordinate 13) (![⟨251873, by decide⟩,⟨251900, by decide⟩,⟨251912, by decide⟩,⟨251926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93225_251927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93225 ⟨251927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93225
    ⟨251927, by decide⟩ (by decide) (![⟨251873, by decide⟩,⟨251900, by decide⟩,⟨251912, by decide⟩,⟨251926, by decide⟩]) unmarked_context_13_93225_251927 node_context_13_93225_251927
  intro a
  fin_cases a
  · exact context_14_372900_251873
  · exact context_14_372901_251900
  · exact context_14_372902_251912
  · exact context_14_372903_251926

theorem selected_cut_09094 : selected 8 ⟨251967, by decide⟩
    (prefixPartial 13 93226) = some ⟨13, 2, 0, 251967, 93226, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_93226_251967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93226 ⟨251967, by decide⟩ :=
  accepted_of_selected 13 93226 ⟨251967, by decide⟩ ⟨13, 2, 0, 251967, 93226, 2777, 16384⟩
    (by decide) selected_cut_09094

theorem selected_cut_09095 : selected 8 ⟨251977, by decide⟩
    (prefixPartial 13 93227) = some ⟨13, 2, 0, 251977, 93227, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_93227_251977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93227 ⟨251977, by decide⟩ :=
  accepted_of_selected 13 93227 ⟨251977, by decide⟩ ⟨13, 2, 0, 251977, 93227, 1065, 16384⟩
    (by decide) selected_cut_09095

theorem unmarked_context_12_23306_251978 : frontier 9 ⟨251978, by decide⟩
    (prefixCache 12 23306) (prefixPartial 12 23306) = false := by
  decide +kernel

theorem node_context_12_23306_251978 : EJMOriginalGlobalDAGData.nodes 9 ⟨251978, by decide⟩ =
    .split (coordinate 12) (![⟨251835, by decide⟩,⟨251927, by decide⟩,⟨251967, by decide⟩,⟨251977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23306_251978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23306 ⟨251978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23306
    ⟨251978, by decide⟩ (by decide) (![⟨251835, by decide⟩,⟨251927, by decide⟩,⟨251967, by decide⟩,⟨251977, by decide⟩]) unmarked_context_12_23306_251978 node_context_12_23306_251978
  intro a
  fin_cases a
  · exact context_13_93224_251835
  · exact context_13_93225_251927
  · exact context_13_93226_251967
  · exact context_13_93227_251977

theorem selected_cut_09096 : selected 8 ⟨252031, by decide⟩
    (prefixPartial 13 93228) = some ⟨13, 2, 0, 252031, 93228, 3713, 16384⟩ := by
  decide +kernel

theorem context_13_93228_252031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93228 ⟨252031, by decide⟩ :=
  accepted_of_selected 13 93228 ⟨252031, by decide⟩ ⟨13, 2, 0, 252031, 93228, 3713, 16384⟩
    (by decide) selected_cut_09096

theorem selected_cut_09097 : selected 7 ⟨252057, by decide⟩
    (prefixPartial 14 372916) = some ⟨14, 2, 0, 252057, 372916, 1445, 4096⟩ := by
  decide +kernel

theorem context_14_372916_252057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372916 ⟨252057, by decide⟩ :=
  accepted_of_selected 14 372916 ⟨252057, by decide⟩ ⟨14, 2, 0, 252057, 372916, 1445, 4096⟩
    (by decide) selected_cut_09097

theorem selected_cut_09098 : selected 7 ⟨252092, by decide⟩
    (prefixPartial 14 372917) = some ⟨14, 2, 0, 252092, 372917, 1505, 4096⟩ := by
  decide +kernel

theorem context_14_372917_252092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372917 ⟨252092, by decide⟩ :=
  accepted_of_selected 14 372917 ⟨252092, by decide⟩ ⟨14, 2, 0, 252092, 372917, 1505, 4096⟩
    (by decide) selected_cut_09098

theorem selected_cut_09099 : selected 7 ⟨252107, by decide⟩
    (prefixPartial 14 372918) = some ⟨14, 2, 0, 252107, 372918, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_372918_252107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372918 ⟨252107, by decide⟩ :=
  accepted_of_selected 14 372918 ⟨252107, by decide⟩ ⟨14, 2, 0, 252107, 372918, 1049, 4096⟩
    (by decide) selected_cut_09099

theorem selected_cut_09100 : selected 7 ⟨252120, by decide⟩
    (prefixPartial 14 372919) = some ⟨14, 2, 0, 252120, 372919, 893, 4096⟩ := by
  decide +kernel

theorem context_14_372919_252120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372919 ⟨252120, by decide⟩ :=
  accepted_of_selected 14 372919 ⟨252120, by decide⟩ ⟨14, 2, 0, 252120, 372919, 893, 4096⟩
    (by decide) selected_cut_09100

theorem unmarked_context_13_93229_252121 : frontier 8 ⟨252121, by decide⟩
    (prefixCache 13 93229) (prefixPartial 13 93229) = false := by
  decide +kernel

theorem node_context_13_93229_252121 : EJMOriginalGlobalDAGData.nodes 8 ⟨252121, by decide⟩ =
    .split (coordinate 13) (![⟨252057, by decide⟩,⟨252092, by decide⟩,⟨252107, by decide⟩,⟨252120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93229_252121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93229 ⟨252121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93229
    ⟨252121, by decide⟩ (by decide) (![⟨252057, by decide⟩,⟨252092, by decide⟩,⟨252107, by decide⟩,⟨252120, by decide⟩]) unmarked_context_13_93229_252121 node_context_13_93229_252121
  intro a
  fin_cases a
  · exact context_14_372916_252057
  · exact context_14_372917_252092
  · exact context_14_372918_252107
  · exact context_14_372919_252120

theorem selected_cut_09101 : selected 8 ⟨252156, by decide⟩
    (prefixPartial 13 93230) = some ⟨13, 2, 0, 252156, 93230, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_93230_252156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93230 ⟨252156, by decide⟩ :=
  accepted_of_selected 13 93230 ⟨252156, by decide⟩ ⟨13, 2, 0, 252156, 93230, 2537, 16384⟩
    (by decide) selected_cut_09101

theorem selected_cut_09102 : selected 8 ⟨252165, by decide⟩
    (prefixPartial 13 93231) = some ⟨13, 2, 0, 252165, 93231, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_93231_252165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93231 ⟨252165, by decide⟩ :=
  accepted_of_selected 13 93231 ⟨252165, by decide⟩ ⟨13, 2, 0, 252165, 93231, 1017, 16384⟩
    (by decide) selected_cut_09102

theorem unmarked_context_12_23307_252166 : frontier 9 ⟨252166, by decide⟩
    (prefixCache 12 23307) (prefixPartial 12 23307) = false := by
  decide +kernel

theorem node_context_12_23307_252166 : EJMOriginalGlobalDAGData.nodes 9 ⟨252166, by decide⟩ =
    .split (coordinate 12) (![⟨252031, by decide⟩,⟨252121, by decide⟩,⟨252156, by decide⟩,⟨252165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23307_252166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23307 ⟨252166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23307
    ⟨252166, by decide⟩ (by decide) (![⟨252031, by decide⟩,⟨252121, by decide⟩,⟨252156, by decide⟩,⟨252165, by decide⟩]) unmarked_context_12_23307_252166 node_context_12_23307_252166
  intro a
  fin_cases a
  · exact context_13_93228_252031
  · exact context_13_93229_252121
  · exact context_13_93230_252156
  · exact context_13_93231_252165

theorem unmarked_context_11_5826_252167 : frontier 10 ⟨252167, by decide⟩
    (prefixCache 11 5826) (prefixPartial 11 5826) = false := by
  decide +kernel

theorem node_context_11_5826_252167 : EJMOriginalGlobalDAGData.nodes 10 ⟨252167, by decide⟩ =
    .split (coordinate 11) (![⟨251588, by decide⟩,⟨251772, by decide⟩,⟨251978, by decide⟩,⟨252166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5826_252167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5826 ⟨252167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5826
    ⟨252167, by decide⟩ (by decide) (![⟨251588, by decide⟩,⟨251772, by decide⟩,⟨251978, by decide⟩,⟨252166, by decide⟩]) unmarked_context_11_5826_252167 node_context_11_5826_252167
  intro a
  fin_cases a
  · exact context_12_23304_251588
  · exact context_12_23305_251772
  · exact context_12_23306_251978
  · exact context_12_23307_252166

theorem selected_cut_09103 : selected 8 ⟨252204, by decide⟩
    (prefixPartial 13 93232) = some ⟨13, 2, 0, 252204, 93232, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_93232_252204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93232 ⟨252204, by decide⟩ :=
  accepted_of_selected 13 93232 ⟨252204, by decide⟩ ⟨13, 2, 0, 252204, 93232, 2701, 16384⟩
    (by decide) selected_cut_09103

theorem selected_cut_09104 : selected 7 ⟨252228, by decide⟩
    (prefixPartial 14 372932) = some ⟨14, 2, 0, 252228, 372932, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_372932_252228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372932 ⟨252228, by decide⟩ :=
  accepted_of_selected 14 372932 ⟨252228, by decide⟩ ⟨14, 2, 0, 252228, 372932, 1321, 4096⟩
    (by decide) selected_cut_09104

theorem selected_cut_09105 : selected 7 ⟨252249, by decide⟩
    (prefixPartial 14 372933) = some ⟨14, 2, 0, 252249, 372933, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_372933_252249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372933 ⟨252249, by decide⟩ :=
  accepted_of_selected 14 372933 ⟨252249, by decide⟩ ⟨14, 2, 0, 252249, 372933, 1101, 4096⟩
    (by decide) selected_cut_09105

theorem selected_cut_09106 : selected 7 ⟨252265, by decide⟩
    (prefixPartial 14 372934) = some ⟨14, 2, 0, 252265, 372934, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_372934_252265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372934 ⟨252265, by decide⟩ :=
  accepted_of_selected 14 372934 ⟨252265, by decide⟩ ⟨14, 2, 0, 252265, 372934, 1041, 4096⟩
    (by decide) selected_cut_09106

theorem selected_cut_09107 : selected 7 ⟨252278, by decide⟩
    (prefixPartial 14 372935) = some ⟨14, 2, 0, 252278, 372935, 737, 4096⟩ := by
  decide +kernel

theorem context_14_372935_252278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372935 ⟨252278, by decide⟩ :=
  accepted_of_selected 14 372935 ⟨252278, by decide⟩ ⟨14, 2, 0, 252278, 372935, 737, 4096⟩
    (by decide) selected_cut_09107

theorem unmarked_context_13_93233_252279 : frontier 8 ⟨252279, by decide⟩
    (prefixCache 13 93233) (prefixPartial 13 93233) = false := by
  decide +kernel

theorem node_context_13_93233_252279 : EJMOriginalGlobalDAGData.nodes 8 ⟨252279, by decide⟩ =
    .split (coordinate 13) (![⟨252228, by decide⟩,⟨252249, by decide⟩,⟨252265, by decide⟩,⟨252278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93233_252279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93233 ⟨252279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93233
    ⟨252279, by decide⟩ (by decide) (![⟨252228, by decide⟩,⟨252249, by decide⟩,⟨252265, by decide⟩,⟨252278, by decide⟩]) unmarked_context_13_93233_252279 node_context_13_93233_252279
  intro a
  fin_cases a
  · exact context_14_372932_252228
  · exact context_14_372933_252249
  · exact context_14_372934_252265
  · exact context_14_372935_252278

theorem selected_cut_09108 : selected 8 ⟨252305, by decide⟩
    (prefixPartial 13 93234) = some ⟨13, 2, 0, 252305, 93234, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_93234_252305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93234 ⟨252305, by decide⟩ :=
  accepted_of_selected 13 93234 ⟨252305, by decide⟩ ⟨13, 2, 0, 252305, 93234, 2013, 16384⟩
    (by decide) selected_cut_09108

theorem selected_cut_09109 : selected 8 ⟨252318, by decide⟩
    (prefixPartial 13 93235) = some ⟨13, 2, 0, 252318, 93235, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_93235_252318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93235 ⟨252318, by decide⟩ :=
  accepted_of_selected 13 93235 ⟨252318, by decide⟩ ⟨13, 2, 0, 252318, 93235, 1097, 16384⟩
    (by decide) selected_cut_09109

theorem unmarked_context_12_23308_252319 : frontier 9 ⟨252319, by decide⟩
    (prefixCache 12 23308) (prefixPartial 12 23308) = false := by
  decide +kernel

theorem node_context_12_23308_252319 : EJMOriginalGlobalDAGData.nodes 9 ⟨252319, by decide⟩ =
    .split (coordinate 12) (![⟨252204, by decide⟩,⟨252279, by decide⟩,⟨252305, by decide⟩,⟨252318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23308_252319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23308 ⟨252319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23308
    ⟨252319, by decide⟩ (by decide) (![⟨252204, by decide⟩,⟨252279, by decide⟩,⟨252305, by decide⟩,⟨252318, by decide⟩]) unmarked_context_12_23308_252319 node_context_12_23308_252319
  intro a
  fin_cases a
  · exact context_13_93232_252204
  · exact context_13_93233_252279
  · exact context_13_93234_252305
  · exact context_13_93235_252318

theorem selected_cut_09110 : selected 8 ⟨252367, by decide⟩
    (prefixPartial 13 93236) = some ⟨13, 2, 0, 252367, 93236, 3345, 16384⟩ := by
  decide +kernel

theorem context_13_93236_252367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93236 ⟨252367, by decide⟩ :=
  accepted_of_selected 13 93236 ⟨252367, by decide⟩ ⟨13, 2, 0, 252367, 93236, 3345, 16384⟩
    (by decide) selected_cut_09110

theorem selected_cut_09111 : selected 8 ⟨252439, by decide⟩
    (prefixPartial 13 93237) = some ⟨13, 2, 0, 252439, 93237, 3813, 16384⟩ := by
  decide +kernel

theorem context_13_93237_252439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93237 ⟨252439, by decide⟩ :=
  accepted_of_selected 13 93237 ⟨252439, by decide⟩ ⟨13, 2, 0, 252439, 93237, 3813, 16384⟩
    (by decide) selected_cut_09111

theorem selected_cut_09112 : selected 8 ⟨252471, by decide⟩
    (prefixPartial 13 93238) = some ⟨13, 2, 0, 252471, 93238, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_93238_252471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93238 ⟨252471, by decide⟩ :=
  accepted_of_selected 13 93238 ⟨252471, by decide⟩ ⟨13, 2, 0, 252471, 93238, 2257, 16384⟩
    (by decide) selected_cut_09112

theorem selected_cut_09113 : selected 8 ⟨252487, by decide⟩
    (prefixPartial 13 93239) = some ⟨13, 2, 0, 252487, 93239, 989, 16384⟩ := by
  decide +kernel

theorem context_13_93239_252487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93239 ⟨252487, by decide⟩ :=
  accepted_of_selected 13 93239 ⟨252487, by decide⟩ ⟨13, 2, 0, 252487, 93239, 989, 16384⟩
    (by decide) selected_cut_09113

theorem unmarked_context_12_23309_252488 : frontier 9 ⟨252488, by decide⟩
    (prefixCache 12 23309) (prefixPartial 12 23309) = false := by
  decide +kernel

theorem node_context_12_23309_252488 : EJMOriginalGlobalDAGData.nodes 9 ⟨252488, by decide⟩ =
    .split (coordinate 12) (![⟨252367, by decide⟩,⟨252439, by decide⟩,⟨252471, by decide⟩,⟨252487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23309_252488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23309 ⟨252488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23309
    ⟨252488, by decide⟩ (by decide) (![⟨252367, by decide⟩,⟨252439, by decide⟩,⟨252471, by decide⟩,⟨252487, by decide⟩]) unmarked_context_12_23309_252488 node_context_12_23309_252488
  intro a
  fin_cases a
  · exact context_13_93236_252367
  · exact context_13_93237_252439
  · exact context_13_93238_252471
  · exact context_13_93239_252487

theorem selected_cut_09114 : selected 8 ⟨252547, by decide⟩
    (prefixPartial 13 93240) = some ⟨13, 2, 0, 252547, 93240, 3921, 16384⟩ := by
  decide +kernel

theorem context_13_93240_252547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93240 ⟨252547, by decide⟩ :=
  accepted_of_selected 13 93240 ⟨252547, by decide⟩ ⟨13, 2, 0, 252547, 93240, 3921, 16384⟩
    (by decide) selected_cut_09114

theorem selected_cut_09115 : selected 7 ⟨252576, by decide⟩
    (prefixPartial 14 372964) = some ⟨14, 2, 0, 252576, 372964, 1401, 4096⟩ := by
  decide +kernel

theorem context_14_372964_252576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372964 ⟨252576, by decide⟩ :=
  accepted_of_selected 14 372964 ⟨252576, by decide⟩ ⟨14, 2, 0, 252576, 372964, 1401, 4096⟩
    (by decide) selected_cut_09115

theorem selected_cut_09116 : selected 7 ⟨252603, by decide⟩
    (prefixPartial 14 372965) = some ⟨14, 2, 0, 252603, 372965, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_372965_252603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372965 ⟨252603, by decide⟩ :=
  accepted_of_selected 14 372965 ⟨252603, by decide⟩ ⟨14, 2, 0, 252603, 372965, 1353, 4096⟩
    (by decide) selected_cut_09116

theorem selected_cut_09117 : selected 7 ⟨252622, by decide⟩
    (prefixPartial 14 372966) = some ⟨14, 2, 0, 252622, 372966, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_372966_252622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372966 ⟨252622, by decide⟩ :=
  accepted_of_selected 14 372966 ⟨252622, by decide⟩ ⟨14, 2, 0, 252622, 372966, 1157, 4096⟩
    (by decide) selected_cut_09117

theorem selected_cut_09118 : selected 7 ⟨252637, by decide⟩
    (prefixPartial 14 372967) = some ⟨14, 2, 0, 252637, 372967, 917, 4096⟩ := by
  decide +kernel

theorem context_14_372967_252637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372967 ⟨252637, by decide⟩ :=
  accepted_of_selected 14 372967 ⟨252637, by decide⟩ ⟨14, 2, 0, 252637, 372967, 917, 4096⟩
    (by decide) selected_cut_09118

theorem unmarked_context_13_93241_252638 : frontier 8 ⟨252638, by decide⟩
    (prefixCache 13 93241) (prefixPartial 13 93241) = false := by
  decide +kernel

theorem node_context_13_93241_252638 : EJMOriginalGlobalDAGData.nodes 8 ⟨252638, by decide⟩ =
    .split (coordinate 13) (![⟨252576, by decide⟩,⟨252603, by decide⟩,⟨252622, by decide⟩,⟨252637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93241_252638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93241 ⟨252638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93241
    ⟨252638, by decide⟩ (by decide) (![⟨252576, by decide⟩,⟨252603, by decide⟩,⟨252622, by decide⟩,⟨252637, by decide⟩]) unmarked_context_13_93241_252638 node_context_13_93241_252638
  intro a
  fin_cases a
  · exact context_14_372964_252576
  · exact context_14_372965_252603
  · exact context_14_372966_252622
  · exact context_14_372967_252637

theorem selected_cut_09119 : selected 8 ⟨252674, by decide⟩
    (prefixPartial 13 93242) = some ⟨13, 2, 0, 252674, 93242, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_93242_252674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93242 ⟨252674, by decide⟩ :=
  accepted_of_selected 13 93242 ⟨252674, by decide⟩ ⟨13, 2, 0, 252674, 93242, 2437, 16384⟩
    (by decide) selected_cut_09119

theorem selected_cut_09120 : selected 8 ⟨252687, by decide⟩
    (prefixPartial 13 93243) = some ⟨13, 2, 0, 252687, 93243, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_93243_252687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93243 ⟨252687, by decide⟩ :=
  accepted_of_selected 13 93243 ⟨252687, by decide⟩ ⟨13, 2, 0, 252687, 93243, 1049, 16384⟩
    (by decide) selected_cut_09120

theorem unmarked_context_12_23310_252688 : frontier 9 ⟨252688, by decide⟩
    (prefixCache 12 23310) (prefixPartial 12 23310) = false := by
  decide +kernel

theorem node_context_12_23310_252688 : EJMOriginalGlobalDAGData.nodes 9 ⟨252688, by decide⟩ =
    .split (coordinate 12) (![⟨252547, by decide⟩,⟨252638, by decide⟩,⟨252674, by decide⟩,⟨252687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23310_252688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23310 ⟨252688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23310
    ⟨252688, by decide⟩ (by decide) (![⟨252547, by decide⟩,⟨252638, by decide⟩,⟨252674, by decide⟩,⟨252687, by decide⟩]) unmarked_context_12_23310_252688 node_context_12_23310_252688
  intro a
  fin_cases a
  · exact context_13_93240_252547
  · exact context_13_93241_252638
  · exact context_13_93242_252674
  · exact context_13_93243_252687

theorem selected_cut_09121 : selected 7 ⟨252694, by decide⟩
    (prefixPartial 14 372976) = some ⟨14, 2, 0, 252694, 372976, 305, 4096⟩ := by
  decide +kernel

theorem context_14_372976_252694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372976 ⟨252694, by decide⟩ :=
  accepted_of_selected 14 372976 ⟨252694, by decide⟩ ⟨14, 2, 0, 252694, 372976, 305, 4096⟩
    (by decide) selected_cut_09121

theorem selected_cut_09122 : selected 7 ⟨252725, by decide⟩
    (prefixPartial 14 372977) = some ⟨14, 2, 0, 252725, 372977, 1885, 4096⟩ := by
  decide +kernel

theorem context_14_372977_252725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372977 ⟨252725, by decide⟩ :=
  accepted_of_selected 14 372977 ⟨252725, by decide⟩ ⟨14, 2, 0, 252725, 372977, 1885, 4096⟩
    (by decide) selected_cut_09122

theorem selected_cut_09123 : selected 7 ⟨252758, by decide⟩
    (prefixPartial 14 372978) = some ⟨14, 2, 0, 252758, 372978, 1825, 4096⟩ := by
  decide +kernel

theorem context_14_372978_252758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372978 ⟨252758, by decide⟩ :=
  accepted_of_selected 14 372978 ⟨252758, by decide⟩ ⟨14, 2, 0, 252758, 372978, 1825, 4096⟩
    (by decide) selected_cut_09123

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
