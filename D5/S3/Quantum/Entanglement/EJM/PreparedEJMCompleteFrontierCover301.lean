/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover300
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28899 : selected 8 ⟨730209, by decide⟩
    (prefixPartial 13 372792) = some ⟨13, 2, 0, 730209, 372792, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_372792_730209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372792 ⟨730209, by decide⟩ :=
  accepted_of_selected 13 372792 ⟨730209, by decide⟩ ⟨13, 2, 0, 730209, 372792, 2865, 16384⟩
    (by decide) selected_cut_28899

theorem selected_cut_28900 : selected 8 ⟨730279, by decide⟩
    (prefixPartial 13 372793) = some ⟨13, 2, 0, 730279, 372793, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_372793_730279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372793 ⟨730279, by decide⟩ :=
  accepted_of_selected 13 372793 ⟨730279, by decide⟩ ⟨13, 2, 0, 730279, 372793, 1693, 16384⟩
    (by decide) selected_cut_28900

theorem selected_cut_28901 : selected 8 ⟨730310, by decide⟩
    (prefixPartial 13 372794) = some ⟨13, 2, 0, 730310, 372794, 717, 16384⟩ := by
  decide +kernel

theorem context_13_372794_730310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372794 ⟨730310, by decide⟩ :=
  accepted_of_selected 13 372794 ⟨730310, by decide⟩ ⟨13, 2, 0, 730310, 372794, 717, 16384⟩
    (by decide) selected_cut_28901

theorem selected_cut_28902 : selected 8 ⟨730315, by decide⟩
    (prefixPartial 13 372795) = some ⟨13, 2, 0, 730315, 372795, 149, 16384⟩ := by
  decide +kernel

theorem context_13_372795_730315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372795 ⟨730315, by decide⟩ :=
  accepted_of_selected 13 372795 ⟨730315, by decide⟩ ⟨13, 2, 0, 730315, 372795, 149, 16384⟩
    (by decide) selected_cut_28902

theorem unmarked_context_12_93198_730316 : frontier 9 ⟨730316, by decide⟩
    (prefixCache 12 93198) (prefixPartial 12 93198) = false := by
  decide +kernel

theorem node_context_12_93198_730316 : EJMOriginalGlobalDAGData.nodes 9 ⟨730316, by decide⟩ =
    .split (coordinate 12) (![⟨730209, by decide⟩,⟨730279, by decide⟩,⟨730310, by decide⟩,⟨730315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93198_730316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93198 ⟨730316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93198
    ⟨730316, by decide⟩ (by decide) (![⟨730209, by decide⟩,⟨730279, by decide⟩,⟨730310, by decide⟩,⟨730315, by decide⟩]) unmarked_context_12_93198_730316 node_context_12_93198_730316
  intro a
  fin_cases a
  · exact context_13_372792_730209
  · exact context_13_372793_730279
  · exact context_13_372794_730310
  · exact context_13_372795_730315

theorem selected_cut_28903 : selected 9 ⟨389061, by decide⟩
    (prefixPartial 12 93199) = some ⟨12, 1, 0, 389061, 93199, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93199_389061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93199 ⟨389061, by decide⟩ :=
  accepted_of_selected 12 93199 ⟨389061, by decide⟩ ⟨12, 1, 0, 389061, 93199, 1, 65536⟩
    (by decide) selected_cut_28903

theorem unmarked_context_11_23299_730317 : frontier 10 ⟨730317, by decide⟩
    (prefixCache 11 23299) (prefixPartial 11 23299) = false := by
  decide +kernel

theorem node_context_11_23299_730317 : EJMOriginalGlobalDAGData.nodes 10 ⟨730317, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨730316, by decide⟩,⟨389061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23299_730317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23299 ⟨730317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23299
    ⟨730317, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨730316, by decide⟩,⟨389061, by decide⟩]) unmarked_context_11_23299_730317 node_context_11_23299_730317
  intro a
  fin_cases a
  · exact context_12_93196_448748
  · exact context_12_93197_390434
  · exact context_12_93198_730316
  · exact context_12_93199_389061

theorem unmarked_context_10_5824_730318 : frontier 11 ⟨730318, by decide⟩
    (prefixCache 10 5824) (prefixPartial 10 5824) = false := by
  decide +kernel

theorem node_context_10_5824_730318 : EJMOriginalGlobalDAGData.nodes 11 ⟨730318, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨729391, by decide⟩,⟨730136, by decide⟩,⟨730317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5824_730318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5824 ⟨730318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5824
    ⟨730318, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨729391, by decide⟩,⟨730136, by decide⟩,⟨730317, by decide⟩]) unmarked_context_10_5824_730318 node_context_10_5824_730318
  intro a
  fin_cases a
  · exact context_11_23296_434745
  · exact context_11_23297_729391
  · exact context_11_23298_730136
  · exact context_11_23299_730317

theorem selected_cut_28904 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 93200) = some ⟨12, 1, 0, 641337, 93200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93200_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93200 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 93200 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 93200, 1, 65536⟩
    (by decide) selected_cut_28904

theorem selected_cut_28905 : selected 8 ⟨730360, by decide⟩
    (prefixPartial 13 372804) = some ⟨13, 2, 0, 730360, 372804, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_372804_730360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372804 ⟨730360, by decide⟩ :=
  accepted_of_selected 13 372804 ⟨730360, by decide⟩ ⟨13, 2, 0, 730360, 372804, 1833, 16384⟩
    (by decide) selected_cut_28905

theorem selected_cut_28906 : selected 8 ⟨730385, by decide⟩
    (prefixPartial 13 372805) = some ⟨13, 2, 0, 730385, 372805, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_372805_730385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372805 ⟨730385, by decide⟩ :=
  accepted_of_selected 13 372805 ⟨730385, by decide⟩ ⟨13, 2, 0, 730385, 372805, 1425, 16384⟩
    (by decide) selected_cut_28906

theorem selected_cut_28907 : selected 8 ⟨730413, by decide⟩
    (prefixPartial 13 372806) = some ⟨13, 2, 0, 730413, 372806, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_372806_730413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372806 ⟨730413, by decide⟩ :=
  accepted_of_selected 13 372806 ⟨730413, by decide⟩ ⟨13, 2, 0, 730413, 372806, 1725, 16384⟩
    (by decide) selected_cut_28907

theorem selected_cut_28908 : selected 8 ⟨730422, by decide⟩
    (prefixPartial 13 372807) = some ⟨13, 2, 0, 730422, 372807, 869, 16384⟩ := by
  decide +kernel

theorem context_13_372807_730422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372807 ⟨730422, by decide⟩ :=
  accepted_of_selected 13 372807 ⟨730422, by decide⟩ ⟨13, 2, 0, 730422, 372807, 869, 16384⟩
    (by decide) selected_cut_28908

theorem unmarked_context_12_93201_730423 : frontier 9 ⟨730423, by decide⟩
    (prefixCache 12 93201) (prefixPartial 12 93201) = false := by
  decide +kernel

theorem node_context_12_93201_730423 : EJMOriginalGlobalDAGData.nodes 9 ⟨730423, by decide⟩ =
    .split (coordinate 12) (![⟨730360, by decide⟩,⟨730385, by decide⟩,⟨730413, by decide⟩,⟨730422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93201_730423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93201 ⟨730423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93201
    ⟨730423, by decide⟩ (by decide) (![⟨730360, by decide⟩,⟨730385, by decide⟩,⟨730413, by decide⟩,⟨730422, by decide⟩]) unmarked_context_12_93201_730423 node_context_12_93201_730423
  intro a
  fin_cases a
  · exact context_13_372804_730360
  · exact context_13_372805_730385
  · exact context_13_372806_730413
  · exact context_13_372807_730422

theorem selected_cut_28909 : selected 8 ⟨730465, by decide⟩
    (prefixPartial 13 372808) = some ⟨13, 2, 0, 730465, 372808, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_372808_730465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372808 ⟨730465, by decide⟩ :=
  accepted_of_selected 13 372808 ⟨730465, by decide⟩ ⟨13, 2, 0, 730465, 372808, 1821, 16384⟩
    (by decide) selected_cut_28909

theorem selected_cut_28910 : selected 8 ⟨730491, by decide⟩
    (prefixPartial 13 372809) = some ⟨13, 2, 0, 730491, 372809, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_372809_730491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372809 ⟨730491, by decide⟩ :=
  accepted_of_selected 13 372809 ⟨730491, by decide⟩ ⟨13, 2, 0, 730491, 372809, 1553, 16384⟩
    (by decide) selected_cut_28910

theorem selected_cut_28911 : selected 8 ⟨730510, by decide⟩
    (prefixPartial 13 372810) = some ⟨13, 2, 0, 730510, 372810, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_372810_730510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372810 ⟨730510, by decide⟩ :=
  accepted_of_selected 13 372810 ⟨730510, by decide⟩ ⟨13, 2, 0, 730510, 372810, 1325, 16384⟩
    (by decide) selected_cut_28911

theorem selected_cut_28912 : selected 8 ⟨730522, by decide⟩
    (prefixPartial 13 372811) = some ⟨13, 2, 0, 730522, 372811, 933, 16384⟩ := by
  decide +kernel

theorem context_13_372811_730522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372811 ⟨730522, by decide⟩ :=
  accepted_of_selected 13 372811 ⟨730522, by decide⟩ ⟨13, 2, 0, 730522, 372811, 933, 16384⟩
    (by decide) selected_cut_28912

theorem unmarked_context_12_93202_730523 : frontier 9 ⟨730523, by decide⟩
    (prefixCache 12 93202) (prefixPartial 12 93202) = false := by
  decide +kernel

theorem node_context_12_93202_730523 : EJMOriginalGlobalDAGData.nodes 9 ⟨730523, by decide⟩ =
    .split (coordinate 12) (![⟨730465, by decide⟩,⟨730491, by decide⟩,⟨730510, by decide⟩,⟨730522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93202_730523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93202 ⟨730523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93202
    ⟨730523, by decide⟩ (by decide) (![⟨730465, by decide⟩,⟨730491, by decide⟩,⟨730510, by decide⟩,⟨730522, by decide⟩]) unmarked_context_12_93202_730523 node_context_12_93202_730523
  intro a
  fin_cases a
  · exact context_13_372808_730465
  · exact context_13_372809_730491
  · exact context_13_372810_730510
  · exact context_13_372811_730522

theorem selected_cut_28913 : selected 8 ⟨730565, by decide⟩
    (prefixPartial 13 372812) = some ⟨13, 2, 0, 730565, 372812, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_372812_730565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372812 ⟨730565, by decide⟩ :=
  accepted_of_selected 13 372812 ⟨730565, by decide⟩ ⟨13, 2, 0, 730565, 372812, 1973, 16384⟩
    (by decide) selected_cut_28913

theorem selected_cut_28914 : selected 8 ⟨730589, by decide⟩
    (prefixPartial 13 372813) = some ⟨13, 2, 0, 730589, 372813, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_372813_730589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372813 ⟨730589, by decide⟩ :=
  accepted_of_selected 13 372813 ⟨730589, by decide⟩ ⟨13, 2, 0, 730589, 372813, 1493, 16384⟩
    (by decide) selected_cut_28914

theorem selected_cut_28915 : selected 8 ⟨730613, by decide⟩
    (prefixPartial 13 372814) = some ⟨13, 2, 0, 730613, 372814, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_372814_730613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372814 ⟨730613, by decide⟩ :=
  accepted_of_selected 13 372814 ⟨730613, by decide⟩ ⟨13, 2, 0, 730613, 372814, 1657, 16384⟩
    (by decide) selected_cut_28915

theorem selected_cut_28916 : selected 8 ⟨730622, by decide⟩
    (prefixPartial 13 372815) = some ⟨13, 2, 0, 730622, 372815, 833, 16384⟩ := by
  decide +kernel

theorem context_13_372815_730622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372815 ⟨730622, by decide⟩ :=
  accepted_of_selected 13 372815 ⟨730622, by decide⟩ ⟨13, 2, 0, 730622, 372815, 833, 16384⟩
    (by decide) selected_cut_28916

theorem unmarked_context_12_93203_730623 : frontier 9 ⟨730623, by decide⟩
    (prefixCache 12 93203) (prefixPartial 12 93203) = false := by
  decide +kernel

theorem node_context_12_93203_730623 : EJMOriginalGlobalDAGData.nodes 9 ⟨730623, by decide⟩ =
    .split (coordinate 12) (![⟨730565, by decide⟩,⟨730589, by decide⟩,⟨730613, by decide⟩,⟨730622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93203_730623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93203 ⟨730623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93203
    ⟨730623, by decide⟩ (by decide) (![⟨730565, by decide⟩,⟨730589, by decide⟩,⟨730613, by decide⟩,⟨730622, by decide⟩]) unmarked_context_12_93203_730623 node_context_12_93203_730623
  intro a
  fin_cases a
  · exact context_13_372812_730565
  · exact context_13_372813_730589
  · exact context_13_372814_730613
  · exact context_13_372815_730622

theorem unmarked_context_11_23300_730624 : frontier 10 ⟨730624, by decide⟩
    (prefixCache 11 23300) (prefixPartial 11 23300) = false := by
  decide +kernel

theorem node_context_11_23300_730624 : EJMOriginalGlobalDAGData.nodes 10 ⟨730624, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨730423, by decide⟩,⟨730523, by decide⟩,⟨730623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23300_730624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23300 ⟨730624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23300
    ⟨730624, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨730423, by decide⟩,⟨730523, by decide⟩,⟨730623, by decide⟩]) unmarked_context_11_23300_730624 node_context_11_23300_730624
  intro a
  fin_cases a
  · exact context_12_93200_641337
  · exact context_12_93201_730423
  · exact context_12_93202_730523
  · exact context_12_93203_730623

theorem selected_cut_28917 : selected 8 ⟨730650, by decide⟩
    (prefixPartial 13 372816) = some ⟨13, 2, 0, 730650, 372816, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_372816_730650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372816 ⟨730650, by decide⟩ :=
  accepted_of_selected 13 372816 ⟨730650, by decide⟩ ⟨13, 2, 0, 730650, 372816, 1293, 16384⟩
    (by decide) selected_cut_28917

theorem selected_cut_28918 : selected 8 ⟨730677, by decide⟩
    (prefixPartial 13 372817) = some ⟨13, 2, 0, 730677, 372817, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_372817_730677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372817 ⟨730677, by decide⟩ :=
  accepted_of_selected 13 372817 ⟨730677, by decide⟩ ⟨13, 2, 0, 730677, 372817, 1829, 16384⟩
    (by decide) selected_cut_28918

theorem selected_cut_28919 : selected 8 ⟨730699, by decide⟩
    (prefixPartial 13 372818) = some ⟨13, 2, 0, 730699, 372818, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_372818_730699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372818 ⟨730699, by decide⟩ :=
  accepted_of_selected 13 372818 ⟨730699, by decide⟩ ⟨13, 2, 0, 730699, 372818, 1485, 16384⟩
    (by decide) selected_cut_28919

theorem selected_cut_28920 : selected 8 ⟨730708, by decide⟩
    (prefixPartial 13 372819) = some ⟨13, 2, 0, 730708, 372819, 757, 16384⟩ := by
  decide +kernel

theorem context_13_372819_730708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372819 ⟨730708, by decide⟩ :=
  accepted_of_selected 13 372819 ⟨730708, by decide⟩ ⟨13, 2, 0, 730708, 372819, 757, 16384⟩
    (by decide) selected_cut_28920

theorem unmarked_context_12_93204_730709 : frontier 9 ⟨730709, by decide⟩
    (prefixCache 12 93204) (prefixPartial 12 93204) = false := by
  decide +kernel

theorem node_context_12_93204_730709 : EJMOriginalGlobalDAGData.nodes 9 ⟨730709, by decide⟩ =
    .split (coordinate 12) (![⟨730650, by decide⟩,⟨730677, by decide⟩,⟨730699, by decide⟩,⟨730708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93204_730709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93204 ⟨730709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93204
    ⟨730709, by decide⟩ (by decide) (![⟨730650, by decide⟩,⟨730677, by decide⟩,⟨730699, by decide⟩,⟨730708, by decide⟩]) unmarked_context_12_93204_730709 node_context_12_93204_730709
  intro a
  fin_cases a
  · exact context_13_372816_730650
  · exact context_13_372817_730677
  · exact context_13_372818_730699
  · exact context_13_372819_730708

theorem selected_cut_28921 : selected 8 ⟨730754, by decide⟩
    (prefixPartial 13 372820) = some ⟨13, 2, 0, 730754, 372820, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_372820_730754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372820 ⟨730754, by decide⟩ :=
  accepted_of_selected 13 372820 ⟨730754, by decide⟩ ⟨13, 2, 0, 730754, 372820, 1733, 16384⟩
    (by decide) selected_cut_28921

theorem selected_cut_28922 : selected 8 ⟨730782, by decide⟩
    (prefixPartial 13 372821) = some ⟨13, 2, 0, 730782, 372821, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_372821_730782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372821 ⟨730782, by decide⟩ :=
  accepted_of_selected 13 372821 ⟨730782, by decide⟩ ⟨13, 2, 0, 730782, 372821, 1545, 16384⟩
    (by decide) selected_cut_28922

theorem selected_cut_28923 : selected 8 ⟨730810, by decide⟩
    (prefixPartial 13 372822) = some ⟨13, 2, 0, 730810, 372822, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_372822_730810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372822 ⟨730810, by decide⟩ :=
  accepted_of_selected 13 372822 ⟨730810, by decide⟩ ⟨13, 2, 0, 730810, 372822, 1909, 16384⟩
    (by decide) selected_cut_28923

theorem selected_cut_28924 : selected 8 ⟨730819, by decide⟩
    (prefixPartial 13 372823) = some ⟨13, 2, 0, 730819, 372823, 837, 16384⟩ := by
  decide +kernel

theorem context_13_372823_730819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372823 ⟨730819, by decide⟩ :=
  accepted_of_selected 13 372823 ⟨730819, by decide⟩ ⟨13, 2, 0, 730819, 372823, 837, 16384⟩
    (by decide) selected_cut_28924

theorem unmarked_context_12_93205_730820 : frontier 9 ⟨730820, by decide⟩
    (prefixCache 12 93205) (prefixPartial 12 93205) = false := by
  decide +kernel

theorem node_context_12_93205_730820 : EJMOriginalGlobalDAGData.nodes 9 ⟨730820, by decide⟩ =
    .split (coordinate 12) (![⟨730754, by decide⟩,⟨730782, by decide⟩,⟨730810, by decide⟩,⟨730819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93205_730820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93205 ⟨730820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93205
    ⟨730820, by decide⟩ (by decide) (![⟨730754, by decide⟩,⟨730782, by decide⟩,⟨730810, by decide⟩,⟨730819, by decide⟩]) unmarked_context_12_93205_730820 node_context_12_93205_730820
  intro a
  fin_cases a
  · exact context_13_372820_730754
  · exact context_13_372821_730782
  · exact context_13_372822_730810
  · exact context_13_372823_730819

theorem selected_cut_28925 : selected 8 ⟨730863, by decide⟩
    (prefixPartial 13 372824) = some ⟨13, 2, 0, 730863, 372824, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_372824_730863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372824 ⟨730863, by decide⟩ :=
  accepted_of_selected 13 372824 ⟨730863, by decide⟩ ⟨13, 2, 0, 730863, 372824, 1865, 16384⟩
    (by decide) selected_cut_28925

theorem selected_cut_28926 : selected 8 ⟨730901, by decide⟩
    (prefixPartial 13 372825) = some ⟨13, 2, 0, 730901, 372825, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_372825_730901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372825 ⟨730901, by decide⟩ :=
  accepted_of_selected 13 372825 ⟨730901, by decide⟩ ⟨13, 2, 0, 730901, 372825, 1957, 16384⟩
    (by decide) selected_cut_28926

theorem selected_cut_28927 : selected 8 ⟨730926, by decide⟩
    (prefixPartial 13 372826) = some ⟨13, 2, 0, 730926, 372826, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_372826_730926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372826 ⟨730926, by decide⟩ :=
  accepted_of_selected 13 372826 ⟨730926, by decide⟩ ⟨13, 2, 0, 730926, 372826, 1581, 16384⟩
    (by decide) selected_cut_28927

theorem selected_cut_28928 : selected 8 ⟨730937, by decide⟩
    (prefixPartial 13 372827) = some ⟨13, 2, 0, 730937, 372827, 925, 16384⟩ := by
  decide +kernel

theorem context_13_372827_730937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372827 ⟨730937, by decide⟩ :=
  accepted_of_selected 13 372827 ⟨730937, by decide⟩ ⟨13, 2, 0, 730937, 372827, 925, 16384⟩
    (by decide) selected_cut_28928

theorem unmarked_context_12_93206_730938 : frontier 9 ⟨730938, by decide⟩
    (prefixCache 12 93206) (prefixPartial 12 93206) = false := by
  decide +kernel

theorem node_context_12_93206_730938 : EJMOriginalGlobalDAGData.nodes 9 ⟨730938, by decide⟩ =
    .split (coordinate 12) (![⟨730863, by decide⟩,⟨730901, by decide⟩,⟨730926, by decide⟩,⟨730937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93206_730938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93206 ⟨730938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93206
    ⟨730938, by decide⟩ (by decide) (![⟨730863, by decide⟩,⟨730901, by decide⟩,⟨730926, by decide⟩,⟨730937, by decide⟩]) unmarked_context_12_93206_730938 node_context_12_93206_730938
  intro a
  fin_cases a
  · exact context_13_372824_730863
  · exact context_13_372825_730901
  · exact context_13_372826_730926
  · exact context_13_372827_730937

theorem selected_cut_28929 : selected 8 ⟨730973, by decide⟩
    (prefixPartial 13 372828) = some ⟨13, 2, 0, 730973, 372828, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_372828_730973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372828 ⟨730973, by decide⟩ :=
  accepted_of_selected 13 372828 ⟨730973, by decide⟩ ⟨13, 2, 0, 730973, 372828, 1845, 16384⟩
    (by decide) selected_cut_28929

theorem selected_cut_28930 : selected 8 ⟨731002, by decide⟩
    (prefixPartial 13 372829) = some ⟨13, 2, 0, 731002, 372829, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_372829_731002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372829 ⟨731002, by decide⟩ :=
  accepted_of_selected 13 372829 ⟨731002, by decide⟩ ⟨13, 2, 0, 731002, 372829, 1917, 16384⟩
    (by decide) selected_cut_28930

theorem selected_cut_28931 : selected 8 ⟨731033, by decide⟩
    (prefixPartial 13 372830) = some ⟨13, 2, 0, 731033, 372830, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_372830_731033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372830 ⟨731033, by decide⟩ :=
  accepted_of_selected 13 372830 ⟨731033, by decide⟩ ⟨13, 2, 0, 731033, 372830, 1961, 16384⟩
    (by decide) selected_cut_28931

theorem selected_cut_28932 : selected 8 ⟨731040, by decide⟩
    (prefixPartial 13 372831) = some ⟨13, 2, 0, 731040, 372831, 857, 16384⟩ := by
  decide +kernel

theorem context_13_372831_731040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372831 ⟨731040, by decide⟩ :=
  accepted_of_selected 13 372831 ⟨731040, by decide⟩ ⟨13, 2, 0, 731040, 372831, 857, 16384⟩
    (by decide) selected_cut_28932

theorem unmarked_context_12_93207_731041 : frontier 9 ⟨731041, by decide⟩
    (prefixCache 12 93207) (prefixPartial 12 93207) = false := by
  decide +kernel

theorem node_context_12_93207_731041 : EJMOriginalGlobalDAGData.nodes 9 ⟨731041, by decide⟩ =
    .split (coordinate 12) (![⟨730973, by decide⟩,⟨731002, by decide⟩,⟨731033, by decide⟩,⟨731040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93207_731041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93207 ⟨731041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93207
    ⟨731041, by decide⟩ (by decide) (![⟨730973, by decide⟩,⟨731002, by decide⟩,⟨731033, by decide⟩,⟨731040, by decide⟩]) unmarked_context_12_93207_731041 node_context_12_93207_731041
  intro a
  fin_cases a
  · exact context_13_372828_730973
  · exact context_13_372829_731002
  · exact context_13_372830_731033
  · exact context_13_372831_731040

theorem unmarked_context_11_23301_731042 : frontier 10 ⟨731042, by decide⟩
    (prefixCache 11 23301) (prefixPartial 11 23301) = false := by
  decide +kernel

theorem node_context_11_23301_731042 : EJMOriginalGlobalDAGData.nodes 10 ⟨731042, by decide⟩ =
    .split (coordinate 11) (![⟨730709, by decide⟩,⟨730820, by decide⟩,⟨730938, by decide⟩,⟨731041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23301_731042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23301 ⟨731042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23301
    ⟨731042, by decide⟩ (by decide) (![⟨730709, by decide⟩,⟨730820, by decide⟩,⟨730938, by decide⟩,⟨731041, by decide⟩]) unmarked_context_11_23301_731042 node_context_11_23301_731042
  intro a
  fin_cases a
  · exact context_12_93204_730709
  · exact context_12_93205_730820
  · exact context_12_93206_730938
  · exact context_12_93207_731041

theorem selected_cut_28933 : selected 8 ⟨731060, by decide⟩
    (prefixPartial 13 372832) = some ⟨13, 2, 0, 731060, 372832, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_372832_731060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372832 ⟨731060, by decide⟩ :=
  accepted_of_selected 13 372832 ⟨731060, by decide⟩ ⟨13, 2, 0, 731060, 372832, 1141, 16384⟩
    (by decide) selected_cut_28933

theorem selected_cut_28934 : selected 8 ⟨731090, by decide⟩
    (prefixPartial 13 372833) = some ⟨13, 2, 0, 731090, 372833, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_372833_731090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372833 ⟨731090, by decide⟩ :=
  accepted_of_selected 13 372833 ⟨731090, by decide⟩ ⟨13, 2, 0, 731090, 372833, 1777, 16384⟩
    (by decide) selected_cut_28934

theorem selected_cut_28935 : selected 8 ⟨731109, by decide⟩
    (prefixPartial 13 372834) = some ⟨13, 2, 0, 731109, 372834, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_372834_731109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372834 ⟨731109, by decide⟩ :=
  accepted_of_selected 13 372834 ⟨731109, by decide⟩ ⟨13, 2, 0, 731109, 372834, 1421, 16384⟩
    (by decide) selected_cut_28935

theorem selected_cut_28936 : selected 8 ⟨731120, by decide⟩
    (prefixPartial 13 372835) = some ⟨13, 2, 0, 731120, 372835, 797, 16384⟩ := by
  decide +kernel

theorem context_13_372835_731120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372835 ⟨731120, by decide⟩ :=
  accepted_of_selected 13 372835 ⟨731120, by decide⟩ ⟨13, 2, 0, 731120, 372835, 797, 16384⟩
    (by decide) selected_cut_28936

theorem unmarked_context_12_93208_731121 : frontier 9 ⟨731121, by decide⟩
    (prefixCache 12 93208) (prefixPartial 12 93208) = false := by
  decide +kernel

theorem node_context_12_93208_731121 : EJMOriginalGlobalDAGData.nodes 9 ⟨731121, by decide⟩ =
    .split (coordinate 12) (![⟨731060, by decide⟩,⟨731090, by decide⟩,⟨731109, by decide⟩,⟨731120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93208_731121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93208 ⟨731121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93208
    ⟨731121, by decide⟩ (by decide) (![⟨731060, by decide⟩,⟨731090, by decide⟩,⟨731109, by decide⟩,⟨731120, by decide⟩]) unmarked_context_12_93208_731121 node_context_12_93208_731121
  intro a
  fin_cases a
  · exact context_13_372832_731060
  · exact context_13_372833_731090
  · exact context_13_372834_731109
  · exact context_13_372835_731120

theorem selected_cut_28937 : selected 8 ⟨731156, by decide⟩
    (prefixPartial 13 372836) = some ⟨13, 2, 0, 731156, 372836, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_372836_731156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372836 ⟨731156, by decide⟩ :=
  accepted_of_selected 13 372836 ⟨731156, by decide⟩ ⟨13, 2, 0, 731156, 372836, 1637, 16384⟩
    (by decide) selected_cut_28937

theorem selected_cut_28938 : selected 8 ⟨731191, by decide⟩
    (prefixPartial 13 372837) = some ⟨13, 2, 0, 731191, 372837, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_372837_731191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372837 ⟨731191, by decide⟩ :=
  accepted_of_selected 13 372837 ⟨731191, by decide⟩ ⟨13, 2, 0, 731191, 372837, 1733, 16384⟩
    (by decide) selected_cut_28938

theorem selected_cut_28939 : selected 8 ⟨731224, by decide⟩
    (prefixPartial 13 372838) = some ⟨13, 2, 0, 731224, 372838, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_372838_731224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372838 ⟨731224, by decide⟩ :=
  accepted_of_selected 13 372838 ⟨731224, by decide⟩ ⟨13, 2, 0, 731224, 372838, 1989, 16384⟩
    (by decide) selected_cut_28939

theorem selected_cut_28940 : selected 8 ⟨731232, by decide⟩
    (prefixPartial 13 372839) = some ⟨13, 2, 0, 731232, 372839, 989, 16384⟩ := by
  decide +kernel

theorem context_13_372839_731232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372839 ⟨731232, by decide⟩ :=
  accepted_of_selected 13 372839 ⟨731232, by decide⟩ ⟨13, 2, 0, 731232, 372839, 989, 16384⟩
    (by decide) selected_cut_28940

theorem unmarked_context_12_93209_731233 : frontier 9 ⟨731233, by decide⟩
    (prefixCache 12 93209) (prefixPartial 12 93209) = false := by
  decide +kernel

theorem node_context_12_93209_731233 : EJMOriginalGlobalDAGData.nodes 9 ⟨731233, by decide⟩ =
    .split (coordinate 12) (![⟨731156, by decide⟩,⟨731191, by decide⟩,⟨731224, by decide⟩,⟨731232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93209_731233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93209 ⟨731233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93209
    ⟨731233, by decide⟩ (by decide) (![⟨731156, by decide⟩,⟨731191, by decide⟩,⟨731224, by decide⟩,⟨731232, by decide⟩]) unmarked_context_12_93209_731233 node_context_12_93209_731233
  intro a
  fin_cases a
  · exact context_13_372836_731156
  · exact context_13_372837_731191
  · exact context_13_372838_731224
  · exact context_13_372839_731232

theorem selected_cut_28941 : selected 8 ⟨731266, by decide⟩
    (prefixPartial 13 372840) = some ⟨13, 2, 0, 731266, 372840, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_372840_731266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372840 ⟨731266, by decide⟩ :=
  accepted_of_selected 13 372840 ⟨731266, by decide⟩ ⟨13, 2, 0, 731266, 372840, 1425, 16384⟩
    (by decide) selected_cut_28941

theorem selected_cut_28942 : selected 8 ⟨731300, by decide⟩
    (prefixPartial 13 372841) = some ⟨13, 2, 0, 731300, 372841, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_372841_731300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372841 ⟨731300, by decide⟩ :=
  accepted_of_selected 13 372841 ⟨731300, by decide⟩ ⟨13, 2, 0, 731300, 372841, 1681, 16384⟩
    (by decide) selected_cut_28942

theorem selected_cut_28943 : selected 8 ⟨731328, by decide⟩
    (prefixPartial 13 372842) = some ⟨13, 2, 0, 731328, 372842, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_372842_731328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372842 ⟨731328, by decide⟩ :=
  accepted_of_selected 13 372842 ⟨731328, by decide⟩ ⟨13, 2, 0, 731328, 372842, 1433, 16384⟩
    (by decide) selected_cut_28943

theorem selected_cut_28944 : selected 8 ⟨731337, by decide⟩
    (prefixPartial 13 372843) = some ⟨13, 2, 0, 731337, 372843, 957, 16384⟩ := by
  decide +kernel

theorem context_13_372843_731337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372843 ⟨731337, by decide⟩ :=
  accepted_of_selected 13 372843 ⟨731337, by decide⟩ ⟨13, 2, 0, 731337, 372843, 957, 16384⟩
    (by decide) selected_cut_28944

theorem unmarked_context_12_93210_731338 : frontier 9 ⟨731338, by decide⟩
    (prefixCache 12 93210) (prefixPartial 12 93210) = false := by
  decide +kernel

theorem node_context_12_93210_731338 : EJMOriginalGlobalDAGData.nodes 9 ⟨731338, by decide⟩ =
    .split (coordinate 12) (![⟨731266, by decide⟩,⟨731300, by decide⟩,⟨731328, by decide⟩,⟨731337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93210_731338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93210 ⟨731338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93210
    ⟨731338, by decide⟩ (by decide) (![⟨731266, by decide⟩,⟨731300, by decide⟩,⟨731328, by decide⟩,⟨731337, by decide⟩]) unmarked_context_12_93210_731338 node_context_12_93210_731338
  intro a
  fin_cases a
  · exact context_13_372840_731266
  · exact context_13_372841_731300
  · exact context_13_372842_731328
  · exact context_13_372843_731337

theorem selected_cut_28945 : selected 8 ⟨731368, by decide⟩
    (prefixPartial 13 372844) = some ⟨13, 2, 0, 731368, 372844, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_372844_731368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372844 ⟨731368, by decide⟩ :=
  accepted_of_selected 13 372844 ⟨731368, by decide⟩ ⟨13, 2, 0, 731368, 372844, 1593, 16384⟩
    (by decide) selected_cut_28945

theorem selected_cut_28946 : selected 8 ⟨731400, by decide⟩
    (prefixPartial 13 372845) = some ⟨13, 2, 0, 731400, 372845, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_372845_731400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372845 ⟨731400, by decide⟩ :=
  accepted_of_selected 13 372845 ⟨731400, by decide⟩ ⟨13, 2, 0, 731400, 372845, 1901, 16384⟩
    (by decide) selected_cut_28946

theorem selected_cut_28947 : selected 8 ⟨731427, by decide⟩
    (prefixPartial 13 372846) = some ⟨13, 2, 0, 731427, 372846, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_372846_731427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372846 ⟨731427, by decide⟩ :=
  accepted_of_selected 13 372846 ⟨731427, by decide⟩ ⟨13, 2, 0, 731427, 372846, 1881, 16384⟩
    (by decide) selected_cut_28947

theorem selected_cut_28948 : selected 8 ⟨731438, by decide⟩
    (prefixPartial 13 372847) = some ⟨13, 2, 0, 731438, 372847, 945, 16384⟩ := by
  decide +kernel

theorem context_13_372847_731438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372847 ⟨731438, by decide⟩ :=
  accepted_of_selected 13 372847 ⟨731438, by decide⟩ ⟨13, 2, 0, 731438, 372847, 945, 16384⟩
    (by decide) selected_cut_28948

theorem unmarked_context_12_93211_731439 : frontier 9 ⟨731439, by decide⟩
    (prefixCache 12 93211) (prefixPartial 12 93211) = false := by
  decide +kernel

theorem node_context_12_93211_731439 : EJMOriginalGlobalDAGData.nodes 9 ⟨731439, by decide⟩ =
    .split (coordinate 12) (![⟨731368, by decide⟩,⟨731400, by decide⟩,⟨731427, by decide⟩,⟨731438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93211_731439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93211 ⟨731439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93211
    ⟨731439, by decide⟩ (by decide) (![⟨731368, by decide⟩,⟨731400, by decide⟩,⟨731427, by decide⟩,⟨731438, by decide⟩]) unmarked_context_12_93211_731439 node_context_12_93211_731439
  intro a
  fin_cases a
  · exact context_13_372844_731368
  · exact context_13_372845_731400
  · exact context_13_372846_731427
  · exact context_13_372847_731438

theorem unmarked_context_11_23302_731440 : frontier 10 ⟨731440, by decide⟩
    (prefixCache 11 23302) (prefixPartial 11 23302) = false := by
  decide +kernel

theorem node_context_11_23302_731440 : EJMOriginalGlobalDAGData.nodes 10 ⟨731440, by decide⟩ =
    .split (coordinate 11) (![⟨731121, by decide⟩,⟨731233, by decide⟩,⟨731338, by decide⟩,⟨731439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23302_731440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23302 ⟨731440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23302
    ⟨731440, by decide⟩ (by decide) (![⟨731121, by decide⟩,⟨731233, by decide⟩,⟨731338, by decide⟩,⟨731439, by decide⟩]) unmarked_context_11_23302_731440 node_context_11_23302_731440
  intro a
  fin_cases a
  · exact context_12_93208_731121
  · exact context_12_93209_731233
  · exact context_12_93210_731338
  · exact context_12_93211_731439

theorem selected_cut_28949 : selected 8 ⟨731458, by decide⟩
    (prefixPartial 13 372848) = some ⟨13, 2, 0, 731458, 372848, 949, 16384⟩ := by
  decide +kernel

theorem context_13_372848_731458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372848 ⟨731458, by decide⟩ :=
  accepted_of_selected 13 372848 ⟨731458, by decide⟩ ⟨13, 2, 0, 731458, 372848, 949, 16384⟩
    (by decide) selected_cut_28949

theorem selected_cut_28950 : selected 8 ⟨731483, by decide⟩
    (prefixPartial 13 372849) = some ⟨13, 2, 0, 731483, 372849, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_372849_731483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372849 ⟨731483, by decide⟩ :=
  accepted_of_selected 13 372849 ⟨731483, by decide⟩ ⟨13, 2, 0, 731483, 372849, 1593, 16384⟩
    (by decide) selected_cut_28950

theorem selected_cut_28951 : selected 8 ⟨731500, by decide⟩
    (prefixPartial 13 372850) = some ⟨13, 2, 0, 731500, 372850, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_372850_731500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372850 ⟨731500, by decide⟩ :=
  accepted_of_selected 13 372850 ⟨731500, by decide⟩ ⟨13, 2, 0, 731500, 372850, 1245, 16384⟩
    (by decide) selected_cut_28951

theorem selected_cut_28952 : selected 8 ⟨731508, by decide⟩
    (prefixPartial 13 372851) = some ⟨13, 2, 0, 731508, 372851, 685, 16384⟩ := by
  decide +kernel

theorem context_13_372851_731508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372851 ⟨731508, by decide⟩ :=
  accepted_of_selected 13 372851 ⟨731508, by decide⟩ ⟨13, 2, 0, 731508, 372851, 685, 16384⟩
    (by decide) selected_cut_28952

theorem unmarked_context_12_93212_731509 : frontier 9 ⟨731509, by decide⟩
    (prefixCache 12 93212) (prefixPartial 12 93212) = false := by
  decide +kernel

theorem node_context_12_93212_731509 : EJMOriginalGlobalDAGData.nodes 9 ⟨731509, by decide⟩ =
    .split (coordinate 12) (![⟨731458, by decide⟩,⟨731483, by decide⟩,⟨731500, by decide⟩,⟨731508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93212_731509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93212 ⟨731509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93212
    ⟨731509, by decide⟩ (by decide) (![⟨731458, by decide⟩,⟨731483, by decide⟩,⟨731500, by decide⟩,⟨731508, by decide⟩]) unmarked_context_12_93212_731509 node_context_12_93212_731509
  intro a
  fin_cases a
  · exact context_13_372848_731458
  · exact context_13_372849_731483
  · exact context_13_372850_731500
  · exact context_13_372851_731508

theorem selected_cut_28953 : selected 8 ⟨731533, by decide⟩
    (prefixPartial 13 372852) = some ⟨13, 2, 0, 731533, 372852, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_372852_731533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372852 ⟨731533, by decide⟩ :=
  accepted_of_selected 13 372852 ⟨731533, by decide⟩ ⟨13, 2, 0, 731533, 372852, 1373, 16384⟩
    (by decide) selected_cut_28953

theorem selected_cut_28954 : selected 8 ⟨731561, by decide⟩
    (prefixPartial 13 372853) = some ⟨13, 2, 0, 731561, 372853, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_372853_731561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372853 ⟨731561, by decide⟩ :=
  accepted_of_selected 13 372853 ⟨731561, by decide⟩ ⟨13, 2, 0, 731561, 372853, 1649, 16384⟩
    (by decide) selected_cut_28954

theorem selected_cut_28955 : selected 8 ⟨731582, by decide⟩
    (prefixPartial 13 372854) = some ⟨13, 2, 0, 731582, 372854, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_372854_731582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372854 ⟨731582, by decide⟩ :=
  accepted_of_selected 13 372854 ⟨731582, by decide⟩ ⟨13, 2, 0, 731582, 372854, 1713, 16384⟩
    (by decide) selected_cut_28955

theorem selected_cut_28956 : selected 8 ⟨731591, by decide⟩
    (prefixPartial 13 372855) = some ⟨13, 2, 0, 731591, 372855, 753, 16384⟩ := by
  decide +kernel

theorem context_13_372855_731591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372855 ⟨731591, by decide⟩ :=
  accepted_of_selected 13 372855 ⟨731591, by decide⟩ ⟨13, 2, 0, 731591, 372855, 753, 16384⟩
    (by decide) selected_cut_28956

theorem unmarked_context_12_93213_731592 : frontier 9 ⟨731592, by decide⟩
    (prefixCache 12 93213) (prefixPartial 12 93213) = false := by
  decide +kernel

theorem node_context_12_93213_731592 : EJMOriginalGlobalDAGData.nodes 9 ⟨731592, by decide⟩ =
    .split (coordinate 12) (![⟨731533, by decide⟩,⟨731561, by decide⟩,⟨731582, by decide⟩,⟨731591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93213_731592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93213 ⟨731592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93213
    ⟨731592, by decide⟩ (by decide) (![⟨731533, by decide⟩,⟨731561, by decide⟩,⟨731582, by decide⟩,⟨731591, by decide⟩]) unmarked_context_12_93213_731592 node_context_12_93213_731592
  intro a
  fin_cases a
  · exact context_13_372852_731533
  · exact context_13_372853_731561
  · exact context_13_372854_731582
  · exact context_13_372855_731591

theorem selected_cut_28957 : selected 8 ⟨731619, by decide⟩
    (prefixPartial 13 372856) = some ⟨13, 2, 0, 731619, 372856, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_372856_731619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372856 ⟨731619, by decide⟩ :=
  accepted_of_selected 13 372856 ⟨731619, by decide⟩ ⟨13, 2, 0, 731619, 372856, 1257, 16384⟩
    (by decide) selected_cut_28957

theorem selected_cut_28958 : selected 8 ⟨731647, by decide⟩
    (prefixPartial 13 372857) = some ⟨13, 2, 0, 731647, 372857, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_372857_731647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372857 ⟨731647, by decide⟩ :=
  accepted_of_selected 13 372857 ⟨731647, by decide⟩ ⟨13, 2, 0, 731647, 372857, 1785, 16384⟩
    (by decide) selected_cut_28958

theorem selected_cut_28959 : selected 8 ⟨731668, by decide⟩
    (prefixPartial 13 372858) = some ⟨13, 2, 0, 731668, 372858, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_372858_731668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372858 ⟨731668, by decide⟩ :=
  accepted_of_selected 13 372858 ⟨731668, by decide⟩ ⟨13, 2, 0, 731668, 372858, 1361, 16384⟩
    (by decide) selected_cut_28959

theorem selected_cut_28960 : selected 8 ⟨731675, by decide⟩
    (prefixPartial 13 372859) = some ⟨13, 2, 0, 731675, 372859, 881, 16384⟩ := by
  decide +kernel

theorem context_13_372859_731675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372859 ⟨731675, by decide⟩ :=
  accepted_of_selected 13 372859 ⟨731675, by decide⟩ ⟨13, 2, 0, 731675, 372859, 881, 16384⟩
    (by decide) selected_cut_28960

theorem unmarked_context_12_93214_731676 : frontier 9 ⟨731676, by decide⟩
    (prefixCache 12 93214) (prefixPartial 12 93214) = false := by
  decide +kernel

theorem node_context_12_93214_731676 : EJMOriginalGlobalDAGData.nodes 9 ⟨731676, by decide⟩ =
    .split (coordinate 12) (![⟨731619, by decide⟩,⟨731647, by decide⟩,⟨731668, by decide⟩,⟨731675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93214_731676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93214 ⟨731676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93214
    ⟨731676, by decide⟩ (by decide) (![⟨731619, by decide⟩,⟨731647, by decide⟩,⟨731668, by decide⟩,⟨731675, by decide⟩]) unmarked_context_12_93214_731676 node_context_12_93214_731676
  intro a
  fin_cases a
  · exact context_13_372856_731619
  · exact context_13_372857_731647
  · exact context_13_372858_731668
  · exact context_13_372859_731675

theorem selected_cut_28961 : selected 8 ⟨731705, by decide⟩
    (prefixPartial 13 372860) = some ⟨13, 2, 0, 731705, 372860, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_372860_731705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372860 ⟨731705, by decide⟩ :=
  accepted_of_selected 13 372860 ⟨731705, by decide⟩ ⟨13, 2, 0, 731705, 372860, 1189, 16384⟩
    (by decide) selected_cut_28961

theorem selected_cut_28962 : selected 8 ⟨731730, by decide⟩
    (prefixPartial 13 372861) = some ⟨13, 2, 0, 731730, 372861, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_372861_731730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372861 ⟨731730, by decide⟩ :=
  accepted_of_selected 13 372861 ⟨731730, by decide⟩ ⟨13, 2, 0, 731730, 372861, 1649, 16384⟩
    (by decide) selected_cut_28962

theorem selected_cut_28963 : selected 8 ⟨731750, by decide⟩
    (prefixPartial 13 372862) = some ⟨13, 2, 0, 731750, 372862, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_372862_731750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372862 ⟨731750, by decide⟩ :=
  accepted_of_selected 13 372862 ⟨731750, by decide⟩ ⟨13, 2, 0, 731750, 372862, 1621, 16384⟩
    (by decide) selected_cut_28963

theorem selected_cut_28964 : selected 8 ⟨731760, by decide⟩
    (prefixPartial 13 372863) = some ⟨13, 2, 0, 731760, 372863, 773, 16384⟩ := by
  decide +kernel

theorem context_13_372863_731760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372863 ⟨731760, by decide⟩ :=
  accepted_of_selected 13 372863 ⟨731760, by decide⟩ ⟨13, 2, 0, 731760, 372863, 773, 16384⟩
    (by decide) selected_cut_28964

theorem unmarked_context_12_93215_731761 : frontier 9 ⟨731761, by decide⟩
    (prefixCache 12 93215) (prefixPartial 12 93215) = false := by
  decide +kernel

theorem node_context_12_93215_731761 : EJMOriginalGlobalDAGData.nodes 9 ⟨731761, by decide⟩ =
    .split (coordinate 12) (![⟨731705, by decide⟩,⟨731730, by decide⟩,⟨731750, by decide⟩,⟨731760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93215_731761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93215 ⟨731761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93215
    ⟨731761, by decide⟩ (by decide) (![⟨731705, by decide⟩,⟨731730, by decide⟩,⟨731750, by decide⟩,⟨731760, by decide⟩]) unmarked_context_12_93215_731761 node_context_12_93215_731761
  intro a
  fin_cases a
  · exact context_13_372860_731705
  · exact context_13_372861_731730
  · exact context_13_372862_731750
  · exact context_13_372863_731760

theorem unmarked_context_11_23303_731762 : frontier 10 ⟨731762, by decide⟩
    (prefixCache 11 23303) (prefixPartial 11 23303) = false := by
  decide +kernel

theorem node_context_11_23303_731762 : EJMOriginalGlobalDAGData.nodes 10 ⟨731762, by decide⟩ =
    .split (coordinate 11) (![⟨731509, by decide⟩,⟨731592, by decide⟩,⟨731676, by decide⟩,⟨731761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23303_731762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23303 ⟨731762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23303
    ⟨731762, by decide⟩ (by decide) (![⟨731509, by decide⟩,⟨731592, by decide⟩,⟨731676, by decide⟩,⟨731761, by decide⟩]) unmarked_context_11_23303_731762 node_context_11_23303_731762
  intro a
  fin_cases a
  · exact context_12_93212_731509
  · exact context_12_93213_731592
  · exact context_12_93214_731676
  · exact context_12_93215_731761

theorem unmarked_context_10_5825_731763 : frontier 11 ⟨731763, by decide⟩
    (prefixCache 10 5825) (prefixPartial 10 5825) = false := by
  decide +kernel

theorem node_context_10_5825_731763 : EJMOriginalGlobalDAGData.nodes 11 ⟨731763, by decide⟩ =
    .split (coordinate 10) (![⟨730624, by decide⟩,⟨731042, by decide⟩,⟨731440, by decide⟩,⟨731762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5825_731763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5825 ⟨731763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5825
    ⟨731763, by decide⟩ (by decide) (![⟨730624, by decide⟩,⟨731042, by decide⟩,⟨731440, by decide⟩,⟨731762, by decide⟩]) unmarked_context_10_5825_731763 node_context_10_5825_731763
  intro a
  fin_cases a
  · exact context_11_23300_730624
  · exact context_11_23301_731042
  · exact context_11_23302_731440
  · exact context_11_23303_731762

theorem selected_cut_28965 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 93216) = some ⟨12, 1, 0, 641337, 93216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93216_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93216 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 93216 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 93216, 1, 65536⟩
    (by decide) selected_cut_28965

theorem selected_cut_28966 : selected 8 ⟨731791, by decide⟩
    (prefixPartial 13 372868) = some ⟨13, 2, 0, 731791, 372868, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_372868_731791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372868 ⟨731791, by decide⟩ :=
  accepted_of_selected 13 372868 ⟨731791, by decide⟩ ⟨13, 2, 0, 731791, 372868, 1325, 16384⟩
    (by decide) selected_cut_28966

theorem selected_cut_28967 : selected 8 ⟨731825, by decide⟩
    (prefixPartial 13 372869) = some ⟨13, 2, 0, 731825, 372869, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_372869_731825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372869 ⟨731825, by decide⟩ :=
  accepted_of_selected 13 372869 ⟨731825, by decide⟩ ⟨13, 2, 0, 731825, 372869, 1621, 16384⟩
    (by decide) selected_cut_28967

theorem selected_cut_28968 : selected 8 ⟨731847, by decide⟩
    (prefixPartial 13 372870) = some ⟨13, 2, 0, 731847, 372870, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_372870_731847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372870 ⟨731847, by decide⟩ :=
  accepted_of_selected 13 372870 ⟨731847, by decide⟩ ⟨13, 2, 0, 731847, 372870, 1537, 16384⟩
    (by decide) selected_cut_28968

theorem selected_cut_28969 : selected 8 ⟨731858, by decide⟩
    (prefixPartial 13 372871) = some ⟨13, 2, 0, 731858, 372871, 777, 16384⟩ := by
  decide +kernel

theorem context_13_372871_731858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372871 ⟨731858, by decide⟩ :=
  accepted_of_selected 13 372871 ⟨731858, by decide⟩ ⟨13, 2, 0, 731858, 372871, 777, 16384⟩
    (by decide) selected_cut_28969

theorem unmarked_context_12_93217_731859 : frontier 9 ⟨731859, by decide⟩
    (prefixCache 12 93217) (prefixPartial 12 93217) = false := by
  decide +kernel

theorem node_context_12_93217_731859 : EJMOriginalGlobalDAGData.nodes 9 ⟨731859, by decide⟩ =
    .split (coordinate 12) (![⟨731791, by decide⟩,⟨731825, by decide⟩,⟨731847, by decide⟩,⟨731858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93217_731859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93217 ⟨731859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93217
    ⟨731859, by decide⟩ (by decide) (![⟨731791, by decide⟩,⟨731825, by decide⟩,⟨731847, by decide⟩,⟨731858, by decide⟩]) unmarked_context_12_93217_731859 node_context_12_93217_731859
  intro a
  fin_cases a
  · exact context_13_372868_731791
  · exact context_13_372869_731825
  · exact context_13_372870_731847
  · exact context_13_372871_731858

theorem selected_cut_28970 : selected 8 ⟨731885, by decide⟩
    (prefixPartial 13 372872) = some ⟨13, 2, 0, 731885, 372872, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_372872_731885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372872 ⟨731885, by decide⟩ :=
  accepted_of_selected 13 372872 ⟨731885, by decide⟩ ⟨13, 2, 0, 731885, 372872, 1197, 16384⟩
    (by decide) selected_cut_28970

theorem selected_cut_28971 : selected 8 ⟨731917, by decide⟩
    (prefixPartial 13 372873) = some ⟨13, 2, 0, 731917, 372873, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_372873_731917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372873 ⟨731917, by decide⟩ :=
  accepted_of_selected 13 372873 ⟨731917, by decide⟩ ⟨13, 2, 0, 731917, 372873, 1801, 16384⟩
    (by decide) selected_cut_28971

theorem selected_cut_28972 : selected 8 ⟨731933, by decide⟩
    (prefixPartial 13 372874) = some ⟨13, 2, 0, 731933, 372874, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_372874_731933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372874 ⟨731933, by decide⟩ :=
  accepted_of_selected 13 372874 ⟨731933, by decide⟩ ⟨13, 2, 0, 731933, 372874, 1309, 16384⟩
    (by decide) selected_cut_28972

theorem selected_cut_28973 : selected 8 ⟨731945, by decide⟩
    (prefixPartial 13 372875) = some ⟨13, 2, 0, 731945, 372875, 861, 16384⟩ := by
  decide +kernel

theorem context_13_372875_731945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372875 ⟨731945, by decide⟩ :=
  accepted_of_selected 13 372875 ⟨731945, by decide⟩ ⟨13, 2, 0, 731945, 372875, 861, 16384⟩
    (by decide) selected_cut_28973

theorem unmarked_context_12_93218_731946 : frontier 9 ⟨731946, by decide⟩
    (prefixCache 12 93218) (prefixPartial 12 93218) = false := by
  decide +kernel

theorem node_context_12_93218_731946 : EJMOriginalGlobalDAGData.nodes 9 ⟨731946, by decide⟩ =
    .split (coordinate 12) (![⟨731885, by decide⟩,⟨731917, by decide⟩,⟨731933, by decide⟩,⟨731945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93218_731946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93218 ⟨731946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93218
    ⟨731946, by decide⟩ (by decide) (![⟨731885, by decide⟩,⟨731917, by decide⟩,⟨731933, by decide⟩,⟨731945, by decide⟩]) unmarked_context_12_93218_731946 node_context_12_93218_731946
  intro a
  fin_cases a
  · exact context_13_372872_731885
  · exact context_13_372873_731917
  · exact context_13_372874_731933
  · exact context_13_372875_731945

theorem selected_cut_28974 : selected 8 ⟨731965, by decide⟩
    (prefixPartial 13 372876) = some ⟨13, 2, 0, 731965, 372876, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_372876_731965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372876 ⟨731965, by decide⟩ :=
  accepted_of_selected 13 372876 ⟨731965, by decide⟩ ⟨13, 2, 0, 731965, 372876, 1193, 16384⟩
    (by decide) selected_cut_28974

theorem selected_cut_28975 : selected 8 ⟨731993, by decide⟩
    (prefixPartial 13 372877) = some ⟨13, 2, 0, 731993, 372877, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_372877_731993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372877 ⟨731993, by decide⟩ :=
  accepted_of_selected 13 372877 ⟨731993, by decide⟩ ⟨13, 2, 0, 731993, 372877, 1737, 16384⟩
    (by decide) selected_cut_28975

theorem selected_cut_28976 : selected 8 ⟨732011, by decide⟩
    (prefixPartial 13 372878) = some ⟨13, 2, 0, 732011, 372878, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_372878_732011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372878 ⟨732011, by decide⟩ :=
  accepted_of_selected 13 372878 ⟨732011, by decide⟩ ⟨13, 2, 0, 732011, 372878, 1425, 16384⟩
    (by decide) selected_cut_28976

theorem selected_cut_28977 : selected 8 ⟨732021, by decide⟩
    (prefixPartial 13 372879) = some ⟨13, 2, 0, 732021, 372879, 793, 16384⟩ := by
  decide +kernel

theorem context_13_372879_732021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372879 ⟨732021, by decide⟩ :=
  accepted_of_selected 13 372879 ⟨732021, by decide⟩ ⟨13, 2, 0, 732021, 372879, 793, 16384⟩
    (by decide) selected_cut_28977

theorem unmarked_context_12_93219_732022 : frontier 9 ⟨732022, by decide⟩
    (prefixCache 12 93219) (prefixPartial 12 93219) = false := by
  decide +kernel

theorem node_context_12_93219_732022 : EJMOriginalGlobalDAGData.nodes 9 ⟨732022, by decide⟩ =
    .split (coordinate 12) (![⟨731965, by decide⟩,⟨731993, by decide⟩,⟨732011, by decide⟩,⟨732021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93219_732022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93219 ⟨732022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93219
    ⟨732022, by decide⟩ (by decide) (![⟨731965, by decide⟩,⟨731993, by decide⟩,⟨732011, by decide⟩,⟨732021, by decide⟩]) unmarked_context_12_93219_732022 node_context_12_93219_732022
  intro a
  fin_cases a
  · exact context_13_372876_731965
  · exact context_13_372877_731993
  · exact context_13_372878_732011
  · exact context_13_372879_732021

theorem unmarked_context_11_23304_732023 : frontier 10 ⟨732023, by decide⟩
    (prefixCache 11 23304) (prefixPartial 11 23304) = false := by
  decide +kernel

theorem node_context_11_23304_732023 : EJMOriginalGlobalDAGData.nodes 10 ⟨732023, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨731859, by decide⟩,⟨731946, by decide⟩,⟨732022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23304_732023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23304 ⟨732023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23304
    ⟨732023, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨731859, by decide⟩,⟨731946, by decide⟩,⟨732022, by decide⟩]) unmarked_context_11_23304_732023 node_context_11_23304_732023
  intro a
  fin_cases a
  · exact context_12_93216_641337
  · exact context_12_93217_731859
  · exact context_12_93218_731946
  · exact context_12_93219_732022

theorem selected_cut_28978 : selected 8 ⟨732035, by decide⟩
    (prefixPartial 13 372880) = some ⟨13, 2, 0, 732035, 372880, 837, 16384⟩ := by
  decide +kernel

theorem context_13_372880_732035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372880 ⟨732035, by decide⟩ :=
  accepted_of_selected 13 372880 ⟨732035, by decide⟩ ⟨13, 2, 0, 732035, 372880, 837, 16384⟩
    (by decide) selected_cut_28978

theorem selected_cut_28979 : selected 8 ⟨732064, by decide⟩
    (prefixPartial 13 372881) = some ⟨13, 2, 0, 732064, 372881, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_372881_732064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372881 ⟨732064, by decide⟩ :=
  accepted_of_selected 13 372881 ⟨732064, by decide⟩ ⟨13, 2, 0, 732064, 372881, 1597, 16384⟩
    (by decide) selected_cut_28979

theorem selected_cut_28980 : selected 8 ⟨732086, by decide⟩
    (prefixPartial 13 372882) = some ⟨13, 2, 0, 732086, 372882, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_372882_732086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372882 ⟨732086, by decide⟩ :=
  accepted_of_selected 13 372882 ⟨732086, by decide⟩ ⟨13, 2, 0, 732086, 372882, 1485, 16384⟩
    (by decide) selected_cut_28980

theorem selected_cut_28981 : selected 8 ⟨732092, by decide⟩
    (prefixPartial 13 372883) = some ⟨13, 2, 0, 732092, 372883, 753, 16384⟩ := by
  decide +kernel

theorem context_13_372883_732092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372883 ⟨732092, by decide⟩ :=
  accepted_of_selected 13 372883 ⟨732092, by decide⟩ ⟨13, 2, 0, 732092, 372883, 753, 16384⟩
    (by decide) selected_cut_28981

theorem unmarked_context_12_93220_732093 : frontier 9 ⟨732093, by decide⟩
    (prefixCache 12 93220) (prefixPartial 12 93220) = false := by
  decide +kernel

theorem node_context_12_93220_732093 : EJMOriginalGlobalDAGData.nodes 9 ⟨732093, by decide⟩ =
    .split (coordinate 12) (![⟨732035, by decide⟩,⟨732064, by decide⟩,⟨732086, by decide⟩,⟨732092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93220_732093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93220 ⟨732093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93220
    ⟨732093, by decide⟩ (by decide) (![⟨732035, by decide⟩,⟨732064, by decide⟩,⟨732086, by decide⟩,⟨732092, by decide⟩]) unmarked_context_12_93220_732093 node_context_12_93220_732093
  intro a
  fin_cases a
  · exact context_13_372880_732035
  · exact context_13_372881_732064
  · exact context_13_372882_732086
  · exact context_13_372883_732092

theorem selected_cut_28982 : selected 8 ⟨732112, by decide⟩
    (prefixPartial 13 372884) = some ⟨13, 2, 0, 732112, 372884, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_372884_732112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372884 ⟨732112, by decide⟩ :=
  accepted_of_selected 13 372884 ⟨732112, by decide⟩ ⟨13, 2, 0, 732112, 372884, 1077, 16384⟩
    (by decide) selected_cut_28982

theorem selected_cut_28983 : selected 8 ⟨732140, by decide⟩
    (prefixPartial 13 372885) = some ⟨13, 2, 0, 732140, 372885, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_372885_732140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372885 ⟨732140, by decide⟩ :=
  accepted_of_selected 13 372885 ⟨732140, by decide⟩ ⟨13, 2, 0, 732140, 372885, 1597, 16384⟩
    (by decide) selected_cut_28983

theorem selected_cut_28984 : selected 8 ⟨732162, by decide⟩
    (prefixPartial 13 372886) = some ⟨13, 2, 0, 732162, 372886, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_372886_732162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372886 ⟨732162, by decide⟩ :=
  accepted_of_selected 13 372886 ⟨732162, by decide⟩ ⟨13, 2, 0, 732162, 372886, 1733, 16384⟩
    (by decide) selected_cut_28984

theorem selected_cut_28985 : selected 8 ⟨732169, by decide⟩
    (prefixPartial 13 372887) = some ⟨13, 2, 0, 732169, 372887, 717, 16384⟩ := by
  decide +kernel

theorem context_13_372887_732169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372887 ⟨732169, by decide⟩ :=
  accepted_of_selected 13 372887 ⟨732169, by decide⟩ ⟨13, 2, 0, 732169, 372887, 717, 16384⟩
    (by decide) selected_cut_28985

theorem unmarked_context_12_93221_732170 : frontier 9 ⟨732170, by decide⟩
    (prefixCache 12 93221) (prefixPartial 12 93221) = false := by
  decide +kernel

theorem node_context_12_93221_732170 : EJMOriginalGlobalDAGData.nodes 9 ⟨732170, by decide⟩ =
    .split (coordinate 12) (![⟨732112, by decide⟩,⟨732140, by decide⟩,⟨732162, by decide⟩,⟨732169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93221_732170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93221 ⟨732170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93221
    ⟨732170, by decide⟩ (by decide) (![⟨732112, by decide⟩,⟨732140, by decide⟩,⟨732162, by decide⟩,⟨732169, by decide⟩]) unmarked_context_12_93221_732170 node_context_12_93221_732170
  intro a
  fin_cases a
  · exact context_13_372884_732112
  · exact context_13_372885_732140
  · exact context_13_372886_732162
  · exact context_13_372887_732169

theorem selected_cut_28986 : selected 8 ⟨732189, by decide⟩
    (prefixPartial 13 372888) = some ⟨13, 2, 0, 732189, 372888, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_372888_732189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372888 ⟨732189, by decide⟩ :=
  accepted_of_selected 13 372888 ⟨732189, by decide⟩ ⟨13, 2, 0, 732189, 372888, 1029, 16384⟩
    (by decide) selected_cut_28986

theorem selected_cut_28987 : selected 8 ⟨732226, by decide⟩
    (prefixPartial 13 372889) = some ⟨13, 2, 0, 732226, 372889, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_372889_732226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372889 ⟨732226, by decide⟩ :=
  accepted_of_selected 13 372889 ⟨732226, by decide⟩ ⟨13, 2, 0, 732226, 372889, 1953, 16384⟩
    (by decide) selected_cut_28987

theorem selected_cut_28988 : selected 8 ⟨732250, by decide⟩
    (prefixPartial 13 372890) = some ⟨13, 2, 0, 732250, 372890, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_372890_732250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372890 ⟨732250, by decide⟩ :=
  accepted_of_selected 13 372890 ⟨732250, by decide⟩ ⟨13, 2, 0, 732250, 372890, 1557, 16384⟩
    (by decide) selected_cut_28988

theorem selected_cut_28989 : selected 8 ⟨732257, by decide⟩
    (prefixPartial 13 372891) = some ⟨13, 2, 0, 732257, 372891, 873, 16384⟩ := by
  decide +kernel

theorem context_13_372891_732257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372891 ⟨732257, by decide⟩ :=
  accepted_of_selected 13 372891 ⟨732257, by decide⟩ ⟨13, 2, 0, 732257, 372891, 873, 16384⟩
    (by decide) selected_cut_28989

theorem unmarked_context_12_93222_732258 : frontier 9 ⟨732258, by decide⟩
    (prefixCache 12 93222) (prefixPartial 12 93222) = false := by
  decide +kernel

theorem node_context_12_93222_732258 : EJMOriginalGlobalDAGData.nodes 9 ⟨732258, by decide⟩ =
    .split (coordinate 12) (![⟨732189, by decide⟩,⟨732226, by decide⟩,⟨732250, by decide⟩,⟨732257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93222_732258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93222 ⟨732258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93222
    ⟨732258, by decide⟩ (by decide) (![⟨732189, by decide⟩,⟨732226, by decide⟩,⟨732250, by decide⟩,⟨732257, by decide⟩]) unmarked_context_12_93222_732258 node_context_12_93222_732258
  intro a
  fin_cases a
  · exact context_13_372888_732189
  · exact context_13_372889_732226
  · exact context_13_372890_732250
  · exact context_13_372891_732257

theorem selected_cut_28990 : selected 8 ⟨732276, by decide⟩
    (prefixPartial 13 372892) = some ⟨13, 2, 0, 732276, 372892, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_372892_732276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372892 ⟨732276, by decide⟩ :=
  accepted_of_selected 13 372892 ⟨732276, by decide⟩ ⟨13, 2, 0, 732276, 372892, 1109, 16384⟩
    (by decide) selected_cut_28990

theorem selected_cut_28991 : selected 8 ⟨732306, by decide⟩
    (prefixPartial 13 372893) = some ⟨13, 2, 0, 732306, 372893, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_372893_732306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372893 ⟨732306, by decide⟩ :=
  accepted_of_selected 13 372893 ⟨732306, by decide⟩ ⟨13, 2, 0, 732306, 372893, 1841, 16384⟩
    (by decide) selected_cut_28991

theorem selected_cut_28992 : selected 8 ⟨732331, by decide⟩
    (prefixPartial 13 372894) = some ⟨13, 2, 0, 732331, 372894, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_372894_732331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372894 ⟨732331, by decide⟩ :=
  accepted_of_selected 13 372894 ⟨732331, by decide⟩ ⟨13, 2, 0, 732331, 372894, 1817, 16384⟩
    (by decide) selected_cut_28992

theorem selected_cut_28993 : selected 8 ⟨732344, by decide⟩
    (prefixPartial 13 372895) = some ⟨13, 2, 0, 732344, 372895, 849, 16384⟩ := by
  decide +kernel

theorem context_13_372895_732344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372895 ⟨732344, by decide⟩ :=
  accepted_of_selected 13 372895 ⟨732344, by decide⟩ ⟨13, 2, 0, 732344, 372895, 849, 16384⟩
    (by decide) selected_cut_28993

theorem unmarked_context_12_93223_732345 : frontier 9 ⟨732345, by decide⟩
    (prefixCache 12 93223) (prefixPartial 12 93223) = false := by
  decide +kernel

theorem node_context_12_93223_732345 : EJMOriginalGlobalDAGData.nodes 9 ⟨732345, by decide⟩ =
    .split (coordinate 12) (![⟨732276, by decide⟩,⟨732306, by decide⟩,⟨732331, by decide⟩,⟨732344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93223_732345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93223 ⟨732345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93223
    ⟨732345, by decide⟩ (by decide) (![⟨732276, by decide⟩,⟨732306, by decide⟩,⟨732331, by decide⟩,⟨732344, by decide⟩]) unmarked_context_12_93223_732345 node_context_12_93223_732345
  intro a
  fin_cases a
  · exact context_13_372892_732276
  · exact context_13_372893_732306
  · exact context_13_372894_732331
  · exact context_13_372895_732344

theorem unmarked_context_11_23305_732346 : frontier 10 ⟨732346, by decide⟩
    (prefixCache 11 23305) (prefixPartial 11 23305) = false := by
  decide +kernel

theorem node_context_11_23305_732346 : EJMOriginalGlobalDAGData.nodes 10 ⟨732346, by decide⟩ =
    .split (coordinate 11) (![⟨732093, by decide⟩,⟨732170, by decide⟩,⟨732258, by decide⟩,⟨732345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23305_732346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23305 ⟨732346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23305
    ⟨732346, by decide⟩ (by decide) (![⟨732093, by decide⟩,⟨732170, by decide⟩,⟨732258, by decide⟩,⟨732345, by decide⟩]) unmarked_context_11_23305_732346 node_context_11_23305_732346
  intro a
  fin_cases a
  · exact context_12_93220_732093
  · exact context_12_93221_732170
  · exact context_12_93222_732258
  · exact context_12_93223_732345

theorem selected_cut_28994 : selected 8 ⟨732356, by decide⟩
    (prefixPartial 13 372896) = some ⟨13, 2, 0, 732356, 372896, 621, 16384⟩ := by
  decide +kernel

theorem context_13_372896_732356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372896 ⟨732356, by decide⟩ :=
  accepted_of_selected 13 372896 ⟨732356, by decide⟩ ⟨13, 2, 0, 732356, 372896, 621, 16384⟩
    (by decide) selected_cut_28994

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
