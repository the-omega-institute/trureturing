/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover157
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15171 : selected 8 ⟨390674, by decide⟩
    (prefixPartial 13 110649) = some ⟨13, 2, 0, 390674, 110649, 3693, 16384⟩ := by
  decide +kernel

theorem context_13_110649_390674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110649 ⟨390674, by decide⟩ :=
  accepted_of_selected 13 110649 ⟨390674, by decide⟩ ⟨13, 2, 0, 390674, 110649, 3693, 16384⟩
    (by decide) selected_cut_15171

theorem selected_cut_15172 : selected 8 ⟨390699, by decide⟩
    (prefixPartial 13 110650) = some ⟨13, 2, 0, 390699, 110650, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_110650_390699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110650 ⟨390699, by decide⟩ :=
  accepted_of_selected 13 110650 ⟨390699, by decide⟩ ⟨13, 2, 0, 390699, 110650, 2217, 16384⟩
    (by decide) selected_cut_15172

theorem selected_cut_15173 : selected 8 ⟨390709, by decide⟩
    (prefixPartial 13 110651) = some ⟨13, 2, 0, 390709, 110651, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_110651_390709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110651 ⟨390709, by decide⟩ :=
  accepted_of_selected 13 110651 ⟨390709, by decide⟩ ⟨13, 2, 0, 390709, 110651, 1069, 16384⟩
    (by decide) selected_cut_15173

theorem unmarked_context_12_27662_390710 : frontier 9 ⟨390710, by decide⟩
    (prefixCache 12 27662) (prefixPartial 12 27662) = false := by
  decide +kernel

theorem node_context_12_27662_390710 : EJMOriginalGlobalDAGData.nodes 9 ⟨390710, by decide⟩ =
    .split (coordinate 12) (![⟨390617, by decide⟩,⟨390674, by decide⟩,⟨390699, by decide⟩,⟨390709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27662_390710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27662 ⟨390710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27662
    ⟨390710, by decide⟩ (by decide) (![⟨390617, by decide⟩,⟨390674, by decide⟩,⟨390699, by decide⟩,⟨390709, by decide⟩]) unmarked_context_12_27662_390710 node_context_12_27662_390710
  intro a
  fin_cases a
  · exact context_13_110648_390617
  · exact context_13_110649_390674
  · exact context_13_110650_390699
  · exact context_13_110651_390709

theorem selected_cut_15174 : selected 8 ⟨390757, by decide⟩
    (prefixPartial 13 110652) = some ⟨13, 2, 0, 390757, 110652, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_110652_390757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110652 ⟨390757, by decide⟩ :=
  accepted_of_selected 13 110652 ⟨390757, by decide⟩ ⟨13, 2, 0, 390757, 110652, 2785, 16384⟩
    (by decide) selected_cut_15174

theorem selected_cut_15175 : selected 8 ⟨390826, by decide⟩
    (prefixPartial 13 110653) = some ⟨13, 2, 0, 390826, 110653, 3861, 16384⟩ := by
  decide +kernel

theorem context_13_110653_390826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110653 ⟨390826, by decide⟩ :=
  accepted_of_selected 13 110653 ⟨390826, by decide⟩ ⟨13, 2, 0, 390826, 110653, 3861, 16384⟩
    (by decide) selected_cut_15175

theorem selected_cut_15176 : selected 8 ⟨390854, by decide⟩
    (prefixPartial 13 110654) = some ⟨13, 2, 0, 390854, 110654, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_110654_390854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110654 ⟨390854, by decide⟩ :=
  accepted_of_selected 13 110654 ⟨390854, by decide⟩ ⟨13, 2, 0, 390854, 110654, 2345, 16384⟩
    (by decide) selected_cut_15176

theorem selected_cut_15177 : selected 8 ⟨390866, by decide⟩
    (prefixPartial 13 110655) = some ⟨13, 2, 0, 390866, 110655, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_110655_390866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110655 ⟨390866, by decide⟩ :=
  accepted_of_selected 13 110655 ⟨390866, by decide⟩ ⟨13, 2, 0, 390866, 110655, 1217, 16384⟩
    (by decide) selected_cut_15177

theorem unmarked_context_12_27663_390867 : frontier 9 ⟨390867, by decide⟩
    (prefixCache 12 27663) (prefixPartial 12 27663) = false := by
  decide +kernel

theorem node_context_12_27663_390867 : EJMOriginalGlobalDAGData.nodes 9 ⟨390867, by decide⟩ =
    .split (coordinate 12) (![⟨390757, by decide⟩,⟨390826, by decide⟩,⟨390854, by decide⟩,⟨390866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27663_390867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27663 ⟨390867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27663
    ⟨390867, by decide⟩ (by decide) (![⟨390757, by decide⟩,⟨390826, by decide⟩,⟨390854, by decide⟩,⟨390866, by decide⟩]) unmarked_context_12_27663_390867 node_context_12_27663_390867
  intro a
  fin_cases a
  · exact context_13_110652_390757
  · exact context_13_110653_390826
  · exact context_13_110654_390854
  · exact context_13_110655_390866

theorem unmarked_context_11_6915_390868 : frontier 10 ⟨390868, by decide⟩
    (prefixCache 11 6915) (prefixPartial 11 6915) = false := by
  decide +kernel

theorem node_context_11_6915_390868 : EJMOriginalGlobalDAGData.nodes 10 ⟨390868, by decide⟩ =
    .split (coordinate 11) (![⟨390434, by decide⟩,⟨390565, by decide⟩,⟨390710, by decide⟩,⟨390867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6915_390868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6915 ⟨390868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6915
    ⟨390868, by decide⟩ (by decide) (![⟨390434, by decide⟩,⟨390565, by decide⟩,⟨390710, by decide⟩,⟨390867, by decide⟩]) unmarked_context_11_6915_390868 node_context_11_6915_390868
  intro a
  fin_cases a
  · exact context_12_27660_390434
  · exact context_12_27661_390565
  · exact context_12_27662_390710
  · exact context_12_27663_390867

theorem unmarked_context_10_1728_390869 : frontier 11 ⟨390869, by decide⟩
    (prefixCache 10 1728) (prefixPartial 10 1728) = false := by
  decide +kernel

theorem node_context_10_1728_390869 : EJMOriginalGlobalDAGData.nodes 11 ⟨390869, by decide⟩ =
    .split (coordinate 10) (![⟨389062, by decide⟩,⟨389676, by decide⟩,⟨390433, by decide⟩,⟨390868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1728_390869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1728 ⟨390869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1728
    ⟨390869, by decide⟩ (by decide) (![⟨389062, by decide⟩,⟨389676, by decide⟩,⟨390433, by decide⟩,⟨390868, by decide⟩]) unmarked_context_10_1728_390869 node_context_10_1728_390869
  intro a
  fin_cases a
  · exact context_11_6912_389062
  · exact context_11_6913_389676
  · exact context_11_6914_390433
  · exact context_11_6915_390868

theorem selected_cut_15178 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 27664) = some ⟨12, 1, 0, 266170, 27664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27664_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27664 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 27664 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 27664, 1, 65536⟩
    (by decide) selected_cut_15178

theorem selected_cut_15179 : selected 8 ⟨390888, by decide⟩
    (prefixPartial 13 110660) = some ⟨13, 2, 0, 390888, 110660, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_110660_390888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110660 ⟨390888, by decide⟩ :=
  accepted_of_selected 13 110660 ⟨390888, by decide⟩ ⟨13, 2, 0, 390888, 110660, 1461, 16384⟩
    (by decide) selected_cut_15179

theorem selected_cut_15180 : selected 8 ⟨390910, by decide⟩
    (prefixPartial 13 110661) = some ⟨13, 2, 0, 390910, 110661, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_110661_390910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110661 ⟨390910, by decide⟩ :=
  accepted_of_selected 13 110661 ⟨390910, by decide⟩ ⟨13, 2, 0, 390910, 110661, 1553, 16384⟩
    (by decide) selected_cut_15180

theorem selected_cut_15181 : selected 8 ⟨390934, by decide⟩
    (prefixPartial 13 110662) = some ⟨13, 2, 0, 390934, 110662, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_110662_390934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110662 ⟨390934, by decide⟩ :=
  accepted_of_selected 13 110662 ⟨390934, by decide⟩ ⟨13, 2, 0, 390934, 110662, 1629, 16384⟩
    (by decide) selected_cut_15181

theorem selected_cut_15182 : selected 8 ⟨390946, by decide⟩
    (prefixPartial 13 110663) = some ⟨13, 2, 0, 390946, 110663, 993, 16384⟩ := by
  decide +kernel

theorem context_13_110663_390946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110663 ⟨390946, by decide⟩ :=
  accepted_of_selected 13 110663 ⟨390946, by decide⟩ ⟨13, 2, 0, 390946, 110663, 993, 16384⟩
    (by decide) selected_cut_15182

theorem unmarked_context_12_27665_390947 : frontier 9 ⟨390947, by decide⟩
    (prefixCache 12 27665) (prefixPartial 12 27665) = false := by
  decide +kernel

theorem node_context_12_27665_390947 : EJMOriginalGlobalDAGData.nodes 9 ⟨390947, by decide⟩ =
    .split (coordinate 12) (![⟨390888, by decide⟩,⟨390910, by decide⟩,⟨390934, by decide⟩,⟨390946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27665_390947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27665 ⟨390947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27665
    ⟨390947, by decide⟩ (by decide) (![⟨390888, by decide⟩,⟨390910, by decide⟩,⟨390934, by decide⟩,⟨390946, by decide⟩]) unmarked_context_12_27665_390947 node_context_12_27665_390947
  intro a
  fin_cases a
  · exact context_13_110660_390888
  · exact context_13_110661_390910
  · exact context_13_110662_390934
  · exact context_13_110663_390946

theorem selected_cut_15183 : selected 8 ⟨390971, by decide⟩
    (prefixPartial 13 110664) = some ⟨13, 2, 0, 390971, 110664, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_110664_390971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110664 ⟨390971, by decide⟩ :=
  accepted_of_selected 13 110664 ⟨390971, by decide⟩ ⟨13, 2, 0, 390971, 110664, 1737, 16384⟩
    (by decide) selected_cut_15183

theorem selected_cut_15184 : selected 8 ⟨390996, by decide⟩
    (prefixPartial 13 110665) = some ⟨13, 2, 0, 390996, 110665, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_110665_390996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110665 ⟨390996, by decide⟩ :=
  accepted_of_selected 13 110665 ⟨390996, by decide⟩ ⟨13, 2, 0, 390996, 110665, 1913, 16384⟩
    (by decide) selected_cut_15184

theorem selected_cut_15185 : selected 8 ⟨391014, by decide⟩
    (prefixPartial 13 110666) = some ⟨13, 2, 0, 391014, 110666, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_110666_391014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110666 ⟨391014, by decide⟩ :=
  accepted_of_selected 13 110666 ⟨391014, by decide⟩ ⟨13, 2, 0, 391014, 110666, 1421, 16384⟩
    (by decide) selected_cut_15185

theorem selected_cut_15186 : selected 8 ⟨391023, by decide⟩
    (prefixPartial 13 110667) = some ⟨13, 2, 0, 391023, 110667, 977, 16384⟩ := by
  decide +kernel

theorem context_13_110667_391023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110667 ⟨391023, by decide⟩ :=
  accepted_of_selected 13 110667 ⟨391023, by decide⟩ ⟨13, 2, 0, 391023, 110667, 977, 16384⟩
    (by decide) selected_cut_15186

theorem unmarked_context_12_27666_391024 : frontier 9 ⟨391024, by decide⟩
    (prefixCache 12 27666) (prefixPartial 12 27666) = false := by
  decide +kernel

theorem node_context_12_27666_391024 : EJMOriginalGlobalDAGData.nodes 9 ⟨391024, by decide⟩ =
    .split (coordinate 12) (![⟨390971, by decide⟩,⟨390996, by decide⟩,⟨391014, by decide⟩,⟨391023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27666_391024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27666 ⟨391024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27666
    ⟨391024, by decide⟩ (by decide) (![⟨390971, by decide⟩,⟨390996, by decide⟩,⟨391014, by decide⟩,⟨391023, by decide⟩]) unmarked_context_12_27666_391024 node_context_12_27666_391024
  intro a
  fin_cases a
  · exact context_13_110664_390971
  · exact context_13_110665_390996
  · exact context_13_110666_391014
  · exact context_13_110667_391023

theorem selected_cut_15187 : selected 8 ⟨391047, by decide⟩
    (prefixPartial 13 110668) = some ⟨13, 2, 0, 391047, 110668, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_110668_391047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110668 ⟨391047, by decide⟩ :=
  accepted_of_selected 13 110668 ⟨391047, by decide⟩ ⟨13, 2, 0, 391047, 110668, 1669, 16384⟩
    (by decide) selected_cut_15187

theorem selected_cut_15188 : selected 8 ⟨391073, by decide⟩
    (prefixPartial 13 110669) = some ⟨13, 2, 0, 391073, 110669, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_110669_391073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110669 ⟨391073, by decide⟩ :=
  accepted_of_selected 13 110669 ⟨391073, by decide⟩ ⟨13, 2, 0, 391073, 110669, 1901, 16384⟩
    (by decide) selected_cut_15188

theorem selected_cut_15189 : selected 8 ⟨391099, by decide⟩
    (prefixPartial 13 110670) = some ⟨13, 2, 0, 391099, 110670, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_110670_391099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110670 ⟨391099, by decide⟩ :=
  accepted_of_selected 13 110670 ⟨391099, by decide⟩ ⟨13, 2, 0, 391099, 110670, 1721, 16384⟩
    (by decide) selected_cut_15189

theorem selected_cut_15190 : selected 8 ⟨391109, by decide⟩
    (prefixPartial 13 110671) = some ⟨13, 2, 0, 391109, 110671, 969, 16384⟩ := by
  decide +kernel

theorem context_13_110671_391109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110671 ⟨391109, by decide⟩ :=
  accepted_of_selected 13 110671 ⟨391109, by decide⟩ ⟨13, 2, 0, 391109, 110671, 969, 16384⟩
    (by decide) selected_cut_15190

theorem unmarked_context_12_27667_391110 : frontier 9 ⟨391110, by decide⟩
    (prefixCache 12 27667) (prefixPartial 12 27667) = false := by
  decide +kernel

theorem node_context_12_27667_391110 : EJMOriginalGlobalDAGData.nodes 9 ⟨391110, by decide⟩ =
    .split (coordinate 12) (![⟨391047, by decide⟩,⟨391073, by decide⟩,⟨391099, by decide⟩,⟨391109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27667_391110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27667 ⟨391110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27667
    ⟨391110, by decide⟩ (by decide) (![⟨391047, by decide⟩,⟨391073, by decide⟩,⟨391099, by decide⟩,⟨391109, by decide⟩]) unmarked_context_12_27667_391110 node_context_12_27667_391110
  intro a
  fin_cases a
  · exact context_13_110668_391047
  · exact context_13_110669_391073
  · exact context_13_110670_391099
  · exact context_13_110671_391109

theorem unmarked_context_11_6916_391111 : frontier 10 ⟨391111, by decide⟩
    (prefixCache 11 6916) (prefixPartial 11 6916) = false := by
  decide +kernel

theorem node_context_11_6916_391111 : EJMOriginalGlobalDAGData.nodes 10 ⟨391111, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨390947, by decide⟩,⟨391024, by decide⟩,⟨391110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6916_391111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6916 ⟨391111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6916
    ⟨391111, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨390947, by decide⟩,⟨391024, by decide⟩,⟨391110, by decide⟩]) unmarked_context_11_6916_391111 node_context_11_6916_391111
  intro a
  fin_cases a
  · exact context_12_27664_266170
  · exact context_12_27665_390947
  · exact context_12_27666_391024
  · exact context_12_27667_391110

theorem selected_cut_15191 : selected 8 ⟨391128, by decide⟩
    (prefixPartial 13 110672) = some ⟨13, 2, 0, 391128, 110672, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_110672_391128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110672 ⟨391128, by decide⟩ :=
  accepted_of_selected 13 110672 ⟨391128, by decide⟩ ⟨13, 2, 0, 391128, 110672, 1385, 16384⟩
    (by decide) selected_cut_15191

theorem selected_cut_15192 : selected 8 ⟨391155, by decide⟩
    (prefixPartial 13 110673) = some ⟨13, 2, 0, 391155, 110673, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_110673_391155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110673 ⟨391155, by decide⟩ :=
  accepted_of_selected 13 110673 ⟨391155, by decide⟩ ⟨13, 2, 0, 391155, 110673, 1897, 16384⟩
    (by decide) selected_cut_15192

theorem selected_cut_15193 : selected 8 ⟨391177, by decide⟩
    (prefixPartial 13 110674) = some ⟨13, 2, 0, 391177, 110674, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_110674_391177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110674 ⟨391177, by decide⟩ :=
  accepted_of_selected 13 110674 ⟨391177, by decide⟩ ⟨13, 2, 0, 391177, 110674, 1389, 16384⟩
    (by decide) selected_cut_15193

theorem selected_cut_15194 : selected 8 ⟨391186, by decide⟩
    (prefixPartial 13 110675) = some ⟨13, 2, 0, 391186, 110675, 689, 16384⟩ := by
  decide +kernel

theorem context_13_110675_391186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110675 ⟨391186, by decide⟩ :=
  accepted_of_selected 13 110675 ⟨391186, by decide⟩ ⟨13, 2, 0, 391186, 110675, 689, 16384⟩
    (by decide) selected_cut_15194

theorem unmarked_context_12_27668_391187 : frontier 9 ⟨391187, by decide⟩
    (prefixCache 12 27668) (prefixPartial 12 27668) = false := by
  decide +kernel

theorem node_context_12_27668_391187 : EJMOriginalGlobalDAGData.nodes 9 ⟨391187, by decide⟩ =
    .split (coordinate 12) (![⟨391128, by decide⟩,⟨391155, by decide⟩,⟨391177, by decide⟩,⟨391186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27668_391187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27668 ⟨391187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27668
    ⟨391187, by decide⟩ (by decide) (![⟨391128, by decide⟩,⟨391155, by decide⟩,⟨391177, by decide⟩,⟨391186, by decide⟩]) unmarked_context_12_27668_391187 node_context_12_27668_391187
  intro a
  fin_cases a
  · exact context_13_110672_391128
  · exact context_13_110673_391155
  · exact context_13_110674_391177
  · exact context_13_110675_391186

theorem selected_cut_15195 : selected 8 ⟨391211, by decide⟩
    (prefixPartial 13 110676) = some ⟨13, 2, 0, 391211, 110676, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_110676_391211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110676 ⟨391211, by decide⟩ :=
  accepted_of_selected 13 110676 ⟨391211, by decide⟩ ⟨13, 2, 0, 391211, 110676, 1545, 16384⟩
    (by decide) selected_cut_15195

theorem selected_cut_15196 : selected 8 ⟨391232, by decide⟩
    (prefixPartial 13 110677) = some ⟨13, 2, 0, 391232, 110677, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_110677_391232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110677 ⟨391232, by decide⟩ :=
  accepted_of_selected 13 110677 ⟨391232, by decide⟩ ⟨13, 2, 0, 391232, 110677, 1585, 16384⟩
    (by decide) selected_cut_15196

theorem selected_cut_15197 : selected 8 ⟨391254, by decide⟩
    (prefixPartial 13 110678) = some ⟨13, 2, 0, 391254, 110678, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_110678_391254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110678 ⟨391254, by decide⟩ :=
  accepted_of_selected 13 110678 ⟨391254, by decide⟩ ⟨13, 2, 0, 391254, 110678, 1817, 16384⟩
    (by decide) selected_cut_15197

theorem selected_cut_15198 : selected 8 ⟨391262, by decide⟩
    (prefixPartial 13 110679) = some ⟨13, 2, 0, 391262, 110679, 817, 16384⟩ := by
  decide +kernel

theorem context_13_110679_391262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110679 ⟨391262, by decide⟩ :=
  accepted_of_selected 13 110679 ⟨391262, by decide⟩ ⟨13, 2, 0, 391262, 110679, 817, 16384⟩
    (by decide) selected_cut_15198

theorem unmarked_context_12_27669_391263 : frontier 9 ⟨391263, by decide⟩
    (prefixCache 12 27669) (prefixPartial 12 27669) = false := by
  decide +kernel

theorem node_context_12_27669_391263 : EJMOriginalGlobalDAGData.nodes 9 ⟨391263, by decide⟩ =
    .split (coordinate 12) (![⟨391211, by decide⟩,⟨391232, by decide⟩,⟨391254, by decide⟩,⟨391262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27669_391263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27669 ⟨391263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27669
    ⟨391263, by decide⟩ (by decide) (![⟨391211, by decide⟩,⟨391232, by decide⟩,⟨391254, by decide⟩,⟨391262, by decide⟩]) unmarked_context_12_27669_391263 node_context_12_27669_391263
  intro a
  fin_cases a
  · exact context_13_110676_391211
  · exact context_13_110677_391232
  · exact context_13_110678_391254
  · exact context_13_110679_391262

theorem selected_cut_15199 : selected 8 ⟨391288, by decide⟩
    (prefixPartial 13 110680) = some ⟨13, 2, 0, 391288, 110680, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_110680_391288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110680 ⟨391288, by decide⟩ :=
  accepted_of_selected 13 110680 ⟨391288, by decide⟩ ⟨13, 2, 0, 391288, 110680, 1677, 16384⟩
    (by decide) selected_cut_15199

theorem selected_cut_15200 : selected 8 ⟨391316, by decide⟩
    (prefixPartial 13 110681) = some ⟨13, 2, 0, 391316, 110681, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_110681_391316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110681 ⟨391316, by decide⟩ :=
  accepted_of_selected 13 110681 ⟨391316, by decide⟩ ⟨13, 2, 0, 391316, 110681, 2029, 16384⟩
    (by decide) selected_cut_15200

theorem selected_cut_15201 : selected 8 ⟨391341, by decide⟩
    (prefixPartial 13 110682) = some ⟨13, 2, 0, 391341, 110682, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_110682_391341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110682 ⟨391341, by decide⟩ :=
  accepted_of_selected 13 110682 ⟨391341, by decide⟩ ⟨13, 2, 0, 391341, 110682, 1609, 16384⟩
    (by decide) selected_cut_15201

theorem selected_cut_15202 : selected 8 ⟨391351, by decide⟩
    (prefixPartial 13 110683) = some ⟨13, 2, 0, 391351, 110683, 913, 16384⟩ := by
  decide +kernel

theorem context_13_110683_391351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110683 ⟨391351, by decide⟩ :=
  accepted_of_selected 13 110683 ⟨391351, by decide⟩ ⟨13, 2, 0, 391351, 110683, 913, 16384⟩
    (by decide) selected_cut_15202

theorem unmarked_context_12_27670_391352 : frontier 9 ⟨391352, by decide⟩
    (prefixCache 12 27670) (prefixPartial 12 27670) = false := by
  decide +kernel

theorem node_context_12_27670_391352 : EJMOriginalGlobalDAGData.nodes 9 ⟨391352, by decide⟩ =
    .split (coordinate 12) (![⟨391288, by decide⟩,⟨391316, by decide⟩,⟨391341, by decide⟩,⟨391351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27670_391352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27670 ⟨391352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27670
    ⟨391352, by decide⟩ (by decide) (![⟨391288, by decide⟩,⟨391316, by decide⟩,⟨391341, by decide⟩,⟨391351, by decide⟩]) unmarked_context_12_27670_391352 node_context_12_27670_391352
  intro a
  fin_cases a
  · exact context_13_110680_391288
  · exact context_13_110681_391316
  · exact context_13_110682_391341
  · exact context_13_110683_391351

theorem selected_cut_15203 : selected 8 ⟨391378, by decide⟩
    (prefixPartial 13 110684) = some ⟨13, 2, 0, 391378, 110684, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_110684_391378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110684 ⟨391378, by decide⟩ :=
  accepted_of_selected 13 110684 ⟨391378, by decide⟩ ⟨13, 2, 0, 391378, 110684, 1825, 16384⟩
    (by decide) selected_cut_15203

theorem selected_cut_15204 : selected 8 ⟨391402, by decide⟩
    (prefixPartial 13 110685) = some ⟨13, 2, 0, 391402, 110685, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_110685_391402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110685 ⟨391402, by decide⟩ :=
  accepted_of_selected 13 110685 ⟨391402, by decide⟩ ⟨13, 2, 0, 391402, 110685, 2057, 16384⟩
    (by decide) selected_cut_15204

theorem selected_cut_15205 : selected 8 ⟨391423, by decide⟩
    (prefixPartial 13 110686) = some ⟨13, 2, 0, 391423, 110686, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_110686_391423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110686 ⟨391423, by decide⟩ :=
  accepted_of_selected 13 110686 ⟨391423, by decide⟩ ⟨13, 2, 0, 391423, 110686, 1957, 16384⟩
    (by decide) selected_cut_15205

theorem selected_cut_15206 : selected 8 ⟨391435, by decide⟩
    (prefixPartial 13 110687) = some ⟨13, 2, 0, 391435, 110687, 985, 16384⟩ := by
  decide +kernel

theorem context_13_110687_391435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110687 ⟨391435, by decide⟩ :=
  accepted_of_selected 13 110687 ⟨391435, by decide⟩ ⟨13, 2, 0, 391435, 110687, 985, 16384⟩
    (by decide) selected_cut_15206

theorem unmarked_context_12_27671_391436 : frontier 9 ⟨391436, by decide⟩
    (prefixCache 12 27671) (prefixPartial 12 27671) = false := by
  decide +kernel

theorem node_context_12_27671_391436 : EJMOriginalGlobalDAGData.nodes 9 ⟨391436, by decide⟩ =
    .split (coordinate 12) (![⟨391378, by decide⟩,⟨391402, by decide⟩,⟨391423, by decide⟩,⟨391435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27671_391436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27671 ⟨391436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27671
    ⟨391436, by decide⟩ (by decide) (![⟨391378, by decide⟩,⟨391402, by decide⟩,⟨391423, by decide⟩,⟨391435, by decide⟩]) unmarked_context_12_27671_391436 node_context_12_27671_391436
  intro a
  fin_cases a
  · exact context_13_110684_391378
  · exact context_13_110685_391402
  · exact context_13_110686_391423
  · exact context_13_110687_391435

theorem unmarked_context_11_6917_391437 : frontier 10 ⟨391437, by decide⟩
    (prefixCache 11 6917) (prefixPartial 11 6917) = false := by
  decide +kernel

theorem node_context_11_6917_391437 : EJMOriginalGlobalDAGData.nodes 10 ⟨391437, by decide⟩ =
    .split (coordinate 11) (![⟨391187, by decide⟩,⟨391263, by decide⟩,⟨391352, by decide⟩,⟨391436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6917_391437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6917 ⟨391437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6917
    ⟨391437, by decide⟩ (by decide) (![⟨391187, by decide⟩,⟨391263, by decide⟩,⟨391352, by decide⟩,⟨391436, by decide⟩]) unmarked_context_11_6917_391437 node_context_11_6917_391437
  intro a
  fin_cases a
  · exact context_12_27668_391187
  · exact context_12_27669_391263
  · exact context_12_27670_391352
  · exact context_12_27671_391436

theorem selected_cut_15207 : selected 8 ⟨391454, by decide⟩
    (prefixPartial 13 110688) = some ⟨13, 2, 0, 391454, 110688, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_110688_391454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110688 ⟨391454, by decide⟩ :=
  accepted_of_selected 13 110688 ⟨391454, by decide⟩ ⟨13, 2, 0, 391454, 110688, 1133, 16384⟩
    (by decide) selected_cut_15207

theorem selected_cut_15208 : selected 8 ⟨391492, by decide⟩
    (prefixPartial 13 110689) = some ⟨13, 2, 0, 391492, 110689, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_110689_391492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110689 ⟨391492, by decide⟩ :=
  accepted_of_selected 13 110689 ⟨391492, by decide⟩ ⟨13, 2, 0, 391492, 110689, 2161, 16384⟩
    (by decide) selected_cut_15208

theorem selected_cut_15209 : selected 8 ⟨391509, by decide⟩
    (prefixPartial 13 110690) = some ⟨13, 2, 0, 391509, 110690, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_110690_391509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110690 ⟨391509, by decide⟩ :=
  accepted_of_selected 13 110690 ⟨391509, by decide⟩ ⟨13, 2, 0, 391509, 110690, 1373, 16384⟩
    (by decide) selected_cut_15209

theorem selected_cut_15210 : selected 8 ⟨391517, by decide⟩
    (prefixPartial 13 110691) = some ⟨13, 2, 0, 391517, 110691, 785, 16384⟩ := by
  decide +kernel

theorem context_13_110691_391517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110691 ⟨391517, by decide⟩ :=
  accepted_of_selected 13 110691 ⟨391517, by decide⟩ ⟨13, 2, 0, 391517, 110691, 785, 16384⟩
    (by decide) selected_cut_15210

theorem unmarked_context_12_27672_391518 : frontier 9 ⟨391518, by decide⟩
    (prefixCache 12 27672) (prefixPartial 12 27672) = false := by
  decide +kernel

theorem node_context_12_27672_391518 : EJMOriginalGlobalDAGData.nodes 9 ⟨391518, by decide⟩ =
    .split (coordinate 12) (![⟨391454, by decide⟩,⟨391492, by decide⟩,⟨391509, by decide⟩,⟨391517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27672_391518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27672 ⟨391518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27672
    ⟨391518, by decide⟩ (by decide) (![⟨391454, by decide⟩,⟨391492, by decide⟩,⟨391509, by decide⟩,⟨391517, by decide⟩]) unmarked_context_12_27672_391518 node_context_12_27672_391518
  intro a
  fin_cases a
  · exact context_13_110688_391454
  · exact context_13_110689_391492
  · exact context_13_110690_391509
  · exact context_13_110691_391517

theorem selected_cut_15211 : selected 8 ⟨391535, by decide⟩
    (prefixPartial 13 110692) = some ⟨13, 2, 0, 391535, 110692, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_110692_391535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110692 ⟨391535, by decide⟩ :=
  accepted_of_selected 13 110692 ⟨391535, by decide⟩ ⟨13, 2, 0, 391535, 110692, 1341, 16384⟩
    (by decide) selected_cut_15211

theorem selected_cut_15212 : selected 8 ⟨391565, by decide⟩
    (prefixPartial 13 110693) = some ⟨13, 2, 0, 391565, 110693, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_110693_391565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110693 ⟨391565, by decide⟩ :=
  accepted_of_selected 13 110693 ⟨391565, by decide⟩ ⟨13, 2, 0, 391565, 110693, 1949, 16384⟩
    (by decide) selected_cut_15212

theorem selected_cut_15213 : selected 8 ⟨391586, by decide⟩
    (prefixPartial 13 110694) = some ⟨13, 2, 0, 391586, 110694, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_110694_391586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110694 ⟨391586, by decide⟩ :=
  accepted_of_selected 13 110694 ⟨391586, by decide⟩ ⟨13, 2, 0, 391586, 110694, 1541, 16384⟩
    (by decide) selected_cut_15213

theorem selected_cut_15214 : selected 8 ⟨391595, by decide⟩
    (prefixPartial 13 110695) = some ⟨13, 2, 0, 391595, 110695, 929, 16384⟩ := by
  decide +kernel

theorem context_13_110695_391595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110695 ⟨391595, by decide⟩ :=
  accepted_of_selected 13 110695 ⟨391595, by decide⟩ ⟨13, 2, 0, 391595, 110695, 929, 16384⟩
    (by decide) selected_cut_15214

theorem unmarked_context_12_27673_391596 : frontier 9 ⟨391596, by decide⟩
    (prefixCache 12 27673) (prefixPartial 12 27673) = false := by
  decide +kernel

theorem node_context_12_27673_391596 : EJMOriginalGlobalDAGData.nodes 9 ⟨391596, by decide⟩ =
    .split (coordinate 12) (![⟨391535, by decide⟩,⟨391565, by decide⟩,⟨391586, by decide⟩,⟨391595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27673_391596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27673 ⟨391596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27673
    ⟨391596, by decide⟩ (by decide) (![⟨391535, by decide⟩,⟨391565, by decide⟩,⟨391586, by decide⟩,⟨391595, by decide⟩]) unmarked_context_12_27673_391596 node_context_12_27673_391596
  intro a
  fin_cases a
  · exact context_13_110692_391535
  · exact context_13_110693_391565
  · exact context_13_110694_391586
  · exact context_13_110695_391595

theorem selected_cut_15215 : selected 8 ⟨391619, by decide⟩
    (prefixPartial 13 110696) = some ⟨13, 2, 0, 391619, 110696, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_110696_391619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110696 ⟨391619, by decide⟩ :=
  accepted_of_selected 13 110696 ⟨391619, by decide⟩ ⟨13, 2, 0, 391619, 110696, 1349, 16384⟩
    (by decide) selected_cut_15215

theorem selected_cut_15216 : selected 8 ⟨391655, by decide⟩
    (prefixPartial 13 110697) = some ⟨13, 2, 0, 391655, 110697, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_110697_391655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110697 ⟨391655, by decide⟩ :=
  accepted_of_selected 13 110697 ⟨391655, by decide⟩ ⟨13, 2, 0, 391655, 110697, 2097, 16384⟩
    (by decide) selected_cut_15216

theorem selected_cut_15217 : selected 8 ⟨391672, by decide⟩
    (prefixPartial 13 110698) = some ⟨13, 2, 0, 391672, 110698, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_110698_391672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110698 ⟨391672, by decide⟩ :=
  accepted_of_selected 13 110698 ⟨391672, by decide⟩ ⟨13, 2, 0, 391672, 110698, 1285, 16384⟩
    (by decide) selected_cut_15217

theorem selected_cut_15218 : selected 8 ⟨391679, by decide⟩
    (prefixPartial 13 110699) = some ⟨13, 2, 0, 391679, 110699, 921, 16384⟩ := by
  decide +kernel

theorem context_13_110699_391679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110699 ⟨391679, by decide⟩ :=
  accepted_of_selected 13 110699 ⟨391679, by decide⟩ ⟨13, 2, 0, 391679, 110699, 921, 16384⟩
    (by decide) selected_cut_15218

theorem unmarked_context_12_27674_391680 : frontier 9 ⟨391680, by decide⟩
    (prefixCache 12 27674) (prefixPartial 12 27674) = false := by
  decide +kernel

theorem node_context_12_27674_391680 : EJMOriginalGlobalDAGData.nodes 9 ⟨391680, by decide⟩ =
    .split (coordinate 12) (![⟨391619, by decide⟩,⟨391655, by decide⟩,⟨391672, by decide⟩,⟨391679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27674_391680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27674 ⟨391680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27674
    ⟨391680, by decide⟩ (by decide) (![⟨391619, by decide⟩,⟨391655, by decide⟩,⟨391672, by decide⟩,⟨391679, by decide⟩]) unmarked_context_12_27674_391680 node_context_12_27674_391680
  intro a
  fin_cases a
  · exact context_13_110696_391619
  · exact context_13_110697_391655
  · exact context_13_110698_391672
  · exact context_13_110699_391679

theorem selected_cut_15219 : selected 8 ⟨391704, by decide⟩
    (prefixPartial 13 110700) = some ⟨13, 2, 0, 391704, 110700, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_110700_391704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110700 ⟨391704, by decide⟩ :=
  accepted_of_selected 13 110700 ⟨391704, by decide⟩ ⟨13, 2, 0, 391704, 110700, 1477, 16384⟩
    (by decide) selected_cut_15219

theorem selected_cut_15220 : selected 8 ⟨391739, by decide⟩
    (prefixPartial 13 110701) = some ⟨13, 2, 0, 391739, 110701, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_110701_391739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110701 ⟨391739, by decide⟩ :=
  accepted_of_selected 13 110701 ⟨391739, by decide⟩ ⟨13, 2, 0, 391739, 110701, 2265, 16384⟩
    (by decide) selected_cut_15220

theorem selected_cut_15221 : selected 8 ⟨391760, by decide⟩
    (prefixPartial 13 110702) = some ⟨13, 2, 0, 391760, 110702, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_110702_391760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110702 ⟨391760, by decide⟩ :=
  accepted_of_selected 13 110702 ⟨391760, by decide⟩ ⟨13, 2, 0, 391760, 110702, 1721, 16384⟩
    (by decide) selected_cut_15221

theorem selected_cut_15222 : selected 8 ⟨391769, by decide⟩
    (prefixPartial 13 110703) = some ⟨13, 2, 0, 391769, 110703, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_110703_391769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110703 ⟨391769, by decide⟩ :=
  accepted_of_selected 13 110703 ⟨391769, by decide⟩ ⟨13, 2, 0, 391769, 110703, 1037, 16384⟩
    (by decide) selected_cut_15222

theorem unmarked_context_12_27675_391770 : frontier 9 ⟨391770, by decide⟩
    (prefixCache 12 27675) (prefixPartial 12 27675) = false := by
  decide +kernel

theorem node_context_12_27675_391770 : EJMOriginalGlobalDAGData.nodes 9 ⟨391770, by decide⟩ =
    .split (coordinate 12) (![⟨391704, by decide⟩,⟨391739, by decide⟩,⟨391760, by decide⟩,⟨391769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27675_391770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27675 ⟨391770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27675
    ⟨391770, by decide⟩ (by decide) (![⟨391704, by decide⟩,⟨391739, by decide⟩,⟨391760, by decide⟩,⟨391769, by decide⟩]) unmarked_context_12_27675_391770 node_context_12_27675_391770
  intro a
  fin_cases a
  · exact context_13_110700_391704
  · exact context_13_110701_391739
  · exact context_13_110702_391760
  · exact context_13_110703_391769

theorem unmarked_context_11_6918_391771 : frontier 10 ⟨391771, by decide⟩
    (prefixCache 11 6918) (prefixPartial 11 6918) = false := by
  decide +kernel

theorem node_context_11_6918_391771 : EJMOriginalGlobalDAGData.nodes 10 ⟨391771, by decide⟩ =
    .split (coordinate 11) (![⟨391518, by decide⟩,⟨391596, by decide⟩,⟨391680, by decide⟩,⟨391770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6918_391771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6918 ⟨391771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6918
    ⟨391771, by decide⟩ (by decide) (![⟨391518, by decide⟩,⟨391596, by decide⟩,⟨391680, by decide⟩,⟨391770, by decide⟩]) unmarked_context_11_6918_391771 node_context_11_6918_391771
  intro a
  fin_cases a
  · exact context_12_27672_391518
  · exact context_12_27673_391596
  · exact context_12_27674_391680
  · exact context_12_27675_391770

theorem selected_cut_15223 : selected 8 ⟨391784, by decide⟩
    (prefixPartial 13 110704) = some ⟨13, 2, 0, 391784, 110704, 957, 16384⟩ := by
  decide +kernel

theorem context_13_110704_391784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110704 ⟨391784, by decide⟩ :=
  accepted_of_selected 13 110704 ⟨391784, by decide⟩ ⟨13, 2, 0, 391784, 110704, 957, 16384⟩
    (by decide) selected_cut_15223

theorem selected_cut_15224 : selected 8 ⟨391811, by decide⟩
    (prefixPartial 13 110705) = some ⟨13, 2, 0, 391811, 110705, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_110705_391811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110705 ⟨391811, by decide⟩ :=
  accepted_of_selected 13 110705 ⟨391811, by decide⟩ ⟨13, 2, 0, 391811, 110705, 1837, 16384⟩
    (by decide) selected_cut_15224

theorem selected_cut_15225 : selected 8 ⟨391829, by decide⟩
    (prefixPartial 13 110706) = some ⟨13, 2, 0, 391829, 110706, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_110706_391829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110706 ⟨391829, by decide⟩ :=
  accepted_of_selected 13 110706 ⟨391829, by decide⟩ ⟨13, 2, 0, 391829, 110706, 1209, 16384⟩
    (by decide) selected_cut_15225

theorem selected_cut_15226 : selected 8 ⟨391837, by decide⟩
    (prefixPartial 13 110707) = some ⟨13, 2, 0, 391837, 110707, 713, 16384⟩ := by
  decide +kernel

theorem context_13_110707_391837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110707 ⟨391837, by decide⟩ :=
  accepted_of_selected 13 110707 ⟨391837, by decide⟩ ⟨13, 2, 0, 391837, 110707, 713, 16384⟩
    (by decide) selected_cut_15226

theorem unmarked_context_12_27676_391838 : frontier 9 ⟨391838, by decide⟩
    (prefixCache 12 27676) (prefixPartial 12 27676) = false := by
  decide +kernel

theorem node_context_12_27676_391838 : EJMOriginalGlobalDAGData.nodes 9 ⟨391838, by decide⟩ =
    .split (coordinate 12) (![⟨391784, by decide⟩,⟨391811, by decide⟩,⟨391829, by decide⟩,⟨391837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27676_391838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27676 ⟨391838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27676
    ⟨391838, by decide⟩ (by decide) (![⟨391784, by decide⟩,⟨391811, by decide⟩,⟨391829, by decide⟩,⟨391837, by decide⟩]) unmarked_context_12_27676_391838 node_context_12_27676_391838
  intro a
  fin_cases a
  · exact context_13_110704_391784
  · exact context_13_110705_391811
  · exact context_13_110706_391829
  · exact context_13_110707_391837

theorem selected_cut_15227 : selected 8 ⟨391854, by decide⟩
    (prefixPartial 13 110708) = some ⟨13, 2, 0, 391854, 110708, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_110708_391854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110708 ⟨391854, by decide⟩ :=
  accepted_of_selected 13 110708 ⟨391854, by decide⟩ ⟨13, 2, 0, 391854, 110708, 1121, 16384⟩
    (by decide) selected_cut_15227

theorem selected_cut_15228 : selected 8 ⟨391881, by decide⟩
    (prefixPartial 13 110709) = some ⟨13, 2, 0, 391881, 110709, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_110709_391881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110709 ⟨391881, by decide⟩ :=
  accepted_of_selected 13 110709 ⟨391881, by decide⟩ ⟨13, 2, 0, 391881, 110709, 1785, 16384⟩
    (by decide) selected_cut_15228

theorem selected_cut_15229 : selected 8 ⟨391901, by decide⟩
    (prefixPartial 13 110710) = some ⟨13, 2, 0, 391901, 110710, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_110710_391901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110710 ⟨391901, by decide⟩ :=
  accepted_of_selected 13 110710 ⟨391901, by decide⟩ ⟨13, 2, 0, 391901, 110710, 1589, 16384⟩
    (by decide) selected_cut_15229

theorem selected_cut_15230 : selected 8 ⟨391908, by decide⟩
    (prefixPartial 13 110711) = some ⟨13, 2, 0, 391908, 110711, 817, 16384⟩ := by
  decide +kernel

theorem context_13_110711_391908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110711 ⟨391908, by decide⟩ :=
  accepted_of_selected 13 110711 ⟨391908, by decide⟩ ⟨13, 2, 0, 391908, 110711, 817, 16384⟩
    (by decide) selected_cut_15230

theorem unmarked_context_12_27677_391909 : frontier 9 ⟨391909, by decide⟩
    (prefixCache 12 27677) (prefixPartial 12 27677) = false := by
  decide +kernel

theorem node_context_12_27677_391909 : EJMOriginalGlobalDAGData.nodes 9 ⟨391909, by decide⟩ =
    .split (coordinate 12) (![⟨391854, by decide⟩,⟨391881, by decide⟩,⟨391901, by decide⟩,⟨391908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27677_391909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27677 ⟨391909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27677
    ⟨391909, by decide⟩ (by decide) (![⟨391854, by decide⟩,⟨391881, by decide⟩,⟨391901, by decide⟩,⟨391908, by decide⟩]) unmarked_context_12_27677_391909 node_context_12_27677_391909
  intro a
  fin_cases a
  · exact context_13_110708_391854
  · exact context_13_110709_391881
  · exact context_13_110710_391901
  · exact context_13_110711_391908

theorem selected_cut_15231 : selected 8 ⟨391930, by decide⟩
    (prefixPartial 13 110712) = some ⟨13, 2, 0, 391930, 110712, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_110712_391930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110712 ⟨391930, by decide⟩ :=
  accepted_of_selected 13 110712 ⟨391930, by decide⟩ ⟨13, 2, 0, 391930, 110712, 1209, 16384⟩
    (by decide) selected_cut_15231

theorem selected_cut_15232 : selected 8 ⟨391954, by decide⟩
    (prefixPartial 13 110713) = some ⟨13, 2, 0, 391954, 110713, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_110713_391954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110713 ⟨391954, by decide⟩ :=
  accepted_of_selected 13 110713 ⟨391954, by decide⟩ ⟨13, 2, 0, 391954, 110713, 2085, 16384⟩
    (by decide) selected_cut_15232

theorem selected_cut_15233 : selected 8 ⟨391973, by decide⟩
    (prefixPartial 13 110714) = some ⟨13, 2, 0, 391973, 110714, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_110714_391973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110714 ⟨391973, by decide⟩ :=
  accepted_of_selected 13 110714 ⟨391973, by decide⟩ ⟨13, 2, 0, 391973, 110714, 1417, 16384⟩
    (by decide) selected_cut_15233

theorem selected_cut_15234 : selected 8 ⟨391982, by decide⟩
    (prefixPartial 13 110715) = some ⟨13, 2, 0, 391982, 110715, 861, 16384⟩ := by
  decide +kernel

theorem context_13_110715_391982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110715 ⟨391982, by decide⟩ :=
  accepted_of_selected 13 110715 ⟨391982, by decide⟩ ⟨13, 2, 0, 391982, 110715, 861, 16384⟩
    (by decide) selected_cut_15234

theorem unmarked_context_12_27678_391983 : frontier 9 ⟨391983, by decide⟩
    (prefixCache 12 27678) (prefixPartial 12 27678) = false := by
  decide +kernel

theorem node_context_12_27678_391983 : EJMOriginalGlobalDAGData.nodes 9 ⟨391983, by decide⟩ =
    .split (coordinate 12) (![⟨391930, by decide⟩,⟨391954, by decide⟩,⟨391973, by decide⟩,⟨391982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27678_391983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27678 ⟨391983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27678
    ⟨391983, by decide⟩ (by decide) (![⟨391930, by decide⟩,⟨391954, by decide⟩,⟨391973, by decide⟩,⟨391982, by decide⟩]) unmarked_context_12_27678_391983 node_context_12_27678_391983
  intro a
  fin_cases a
  · exact context_13_110712_391930
  · exact context_13_110713_391954
  · exact context_13_110714_391973
  · exact context_13_110715_391982

theorem selected_cut_15235 : selected 8 ⟨392002, by decide⟩
    (prefixPartial 13 110716) = some ⟨13, 2, 0, 392002, 110716, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_110716_392002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110716 ⟨392002, by decide⟩ :=
  accepted_of_selected 13 110716 ⟨392002, by decide⟩ ⟨13, 2, 0, 392002, 110716, 1133, 16384⟩
    (by decide) selected_cut_15235

theorem selected_cut_15236 : selected 8 ⟨392029, by decide⟩
    (prefixPartial 13 110717) = some ⟨13, 2, 0, 392029, 110717, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_110717_392029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110717 ⟨392029, by decide⟩ :=
  accepted_of_selected 13 110717 ⟨392029, by decide⟩ ⟨13, 2, 0, 392029, 110717, 2025, 16384⟩
    (by decide) selected_cut_15236

theorem selected_cut_15237 : selected 8 ⟨392047, by decide⟩
    (prefixPartial 13 110718) = some ⟨13, 2, 0, 392047, 110718, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_110718_392047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110718 ⟨392047, by decide⟩ :=
  accepted_of_selected 13 110718 ⟨392047, by decide⟩ ⟨13, 2, 0, 392047, 110718, 1773, 16384⟩
    (by decide) selected_cut_15237

theorem selected_cut_15238 : selected 8 ⟨392055, by decide⟩
    (prefixPartial 13 110719) = some ⟨13, 2, 0, 392055, 110719, 933, 16384⟩ := by
  decide +kernel

theorem context_13_110719_392055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110719 ⟨392055, by decide⟩ :=
  accepted_of_selected 13 110719 ⟨392055, by decide⟩ ⟨13, 2, 0, 392055, 110719, 933, 16384⟩
    (by decide) selected_cut_15238

theorem unmarked_context_12_27679_392056 : frontier 9 ⟨392056, by decide⟩
    (prefixCache 12 27679) (prefixPartial 12 27679) = false := by
  decide +kernel

theorem node_context_12_27679_392056 : EJMOriginalGlobalDAGData.nodes 9 ⟨392056, by decide⟩ =
    .split (coordinate 12) (![⟨392002, by decide⟩,⟨392029, by decide⟩,⟨392047, by decide⟩,⟨392055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27679_392056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27679 ⟨392056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27679
    ⟨392056, by decide⟩ (by decide) (![⟨392002, by decide⟩,⟨392029, by decide⟩,⟨392047, by decide⟩,⟨392055, by decide⟩]) unmarked_context_12_27679_392056 node_context_12_27679_392056
  intro a
  fin_cases a
  · exact context_13_110716_392002
  · exact context_13_110717_392029
  · exact context_13_110718_392047
  · exact context_13_110719_392055

theorem unmarked_context_11_6919_392057 : frontier 10 ⟨392057, by decide⟩
    (prefixCache 11 6919) (prefixPartial 11 6919) = false := by
  decide +kernel

theorem node_context_11_6919_392057 : EJMOriginalGlobalDAGData.nodes 10 ⟨392057, by decide⟩ =
    .split (coordinate 11) (![⟨391838, by decide⟩,⟨391909, by decide⟩,⟨391983, by decide⟩,⟨392056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6919_392057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6919 ⟨392057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6919
    ⟨392057, by decide⟩ (by decide) (![⟨391838, by decide⟩,⟨391909, by decide⟩,⟨391983, by decide⟩,⟨392056, by decide⟩]) unmarked_context_11_6919_392057 node_context_11_6919_392057
  intro a
  fin_cases a
  · exact context_12_27676_391838
  · exact context_12_27677_391909
  · exact context_12_27678_391983
  · exact context_12_27679_392056

theorem unmarked_context_10_1729_392058 : frontier 11 ⟨392058, by decide⟩
    (prefixCache 10 1729) (prefixPartial 10 1729) = false := by
  decide +kernel

theorem node_context_10_1729_392058 : EJMOriginalGlobalDAGData.nodes 11 ⟨392058, by decide⟩ =
    .split (coordinate 10) (![⟨391111, by decide⟩,⟨391437, by decide⟩,⟨391771, by decide⟩,⟨392057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1729_392058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1729 ⟨392058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1729
    ⟨392058, by decide⟩ (by decide) (![⟨391111, by decide⟩,⟨391437, by decide⟩,⟨391771, by decide⟩,⟨392057, by decide⟩]) unmarked_context_10_1729_392058 node_context_10_1729_392058
  intro a
  fin_cases a
  · exact context_11_6916_391111
  · exact context_11_6917_391437
  · exact context_11_6918_391771
  · exact context_11_6919_392057

theorem selected_cut_15239 : selected 8 ⟨392083, by decide⟩
    (prefixPartial 13 110720) = some ⟨13, 2, 0, 392083, 110720, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_110720_392083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110720 ⟨392083, by decide⟩ :=
  accepted_of_selected 13 110720 ⟨392083, by decide⟩ ⟨13, 2, 0, 392083, 110720, 1245, 16384⟩
    (by decide) selected_cut_15239

theorem selected_cut_15240 : selected 8 ⟨392161, by decide⟩
    (prefixPartial 13 110721) = some ⟨13, 2, 0, 392161, 110721, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_110721_392161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110721 ⟨392161, by decide⟩ :=
  accepted_of_selected 13 110721 ⟨392161, by decide⟩ ⟨13, 2, 0, 392161, 110721, 2365, 16384⟩
    (by decide) selected_cut_15240

theorem selected_cut_15241 : selected 8 ⟨392197, by decide⟩
    (prefixPartial 13 110722) = some ⟨13, 2, 0, 392197, 110722, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_110722_392197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110722 ⟨392197, by decide⟩ :=
  accepted_of_selected 13 110722 ⟨392197, by decide⟩ ⟨13, 2, 0, 392197, 110722, 1017, 16384⟩
    (by decide) selected_cut_15241

theorem selected_cut_15242 : selected 8 ⟨392206, by decide⟩
    (prefixPartial 13 110723) = some ⟨13, 2, 0, 392206, 110723, 269, 16384⟩ := by
  decide +kernel

theorem context_13_110723_392206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110723 ⟨392206, by decide⟩ :=
  accepted_of_selected 13 110723 ⟨392206, by decide⟩ ⟨13, 2, 0, 392206, 110723, 269, 16384⟩
    (by decide) selected_cut_15242

theorem unmarked_context_12_27680_392207 : frontier 9 ⟨392207, by decide⟩
    (prefixCache 12 27680) (prefixPartial 12 27680) = false := by
  decide +kernel

theorem node_context_12_27680_392207 : EJMOriginalGlobalDAGData.nodes 9 ⟨392207, by decide⟩ =
    .split (coordinate 12) (![⟨392083, by decide⟩,⟨392161, by decide⟩,⟨392197, by decide⟩,⟨392206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27680_392207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27680 ⟨392207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27680
    ⟨392207, by decide⟩ (by decide) (![⟨392083, by decide⟩,⟨392161, by decide⟩,⟨392197, by decide⟩,⟨392206, by decide⟩]) unmarked_context_12_27680_392207 node_context_12_27680_392207
  intro a
  fin_cases a
  · exact context_13_110720_392083
  · exact context_13_110721_392161
  · exact context_13_110722_392197
  · exact context_13_110723_392206

theorem selected_cut_15243 : selected 8 ⟨392220, by decide⟩
    (prefixPartial 13 110724) = some ⟨13, 2, 0, 392220, 110724, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_110724_392220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110724 ⟨392220, by decide⟩ :=
  accepted_of_selected 13 110724 ⟨392220, by decide⟩ ⟨13, 2, 0, 392220, 110724, 1033, 16384⟩
    (by decide) selected_cut_15243

theorem selected_cut_15244 : selected 8 ⟨392241, by decide⟩
    (prefixPartial 13 110725) = some ⟨13, 2, 0, 392241, 110725, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_110725_392241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110725 ⟨392241, by decide⟩ :=
  accepted_of_selected 13 110725 ⟨392241, by decide⟩ ⟨13, 2, 0, 392241, 110725, 1657, 16384⟩
    (by decide) selected_cut_15244

theorem selected_cut_15245 : selected 8 ⟨392259, by decide⟩
    (prefixPartial 13 110726) = some ⟨13, 2, 0, 392259, 110726, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_110726_392259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110726 ⟨392259, by decide⟩ :=
  accepted_of_selected 13 110726 ⟨392259, by decide⟩ ⟨13, 2, 0, 392259, 110726, 1337, 16384⟩
    (by decide) selected_cut_15245

theorem selected_cut_15246 : selected 8 ⟨392268, by decide⟩
    (prefixPartial 13 110727) = some ⟨13, 2, 0, 392268, 110727, 861, 16384⟩ := by
  decide +kernel

theorem context_13_110727_392268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110727 ⟨392268, by decide⟩ :=
  accepted_of_selected 13 110727 ⟨392268, by decide⟩ ⟨13, 2, 0, 392268, 110727, 861, 16384⟩
    (by decide) selected_cut_15246

theorem unmarked_context_12_27681_392269 : frontier 9 ⟨392269, by decide⟩
    (prefixCache 12 27681) (prefixPartial 12 27681) = false := by
  decide +kernel

theorem node_context_12_27681_392269 : EJMOriginalGlobalDAGData.nodes 9 ⟨392269, by decide⟩ =
    .split (coordinate 12) (![⟨392220, by decide⟩,⟨392241, by decide⟩,⟨392259, by decide⟩,⟨392268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27681_392269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27681 ⟨392269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27681
    ⟨392269, by decide⟩ (by decide) (![⟨392220, by decide⟩,⟨392241, by decide⟩,⟨392259, by decide⟩,⟨392268, by decide⟩]) unmarked_context_12_27681_392269 node_context_12_27681_392269
  intro a
  fin_cases a
  · exact context_13_110724_392220
  · exact context_13_110725_392241
  · exact context_13_110726_392259
  · exact context_13_110727_392268

theorem selected_cut_15247 : selected 8 ⟨392282, by decide⟩
    (prefixPartial 13 110728) = some ⟨13, 2, 0, 392282, 110728, 953, 16384⟩ := by
  decide +kernel

theorem context_13_110728_392282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110728 ⟨392282, by decide⟩ :=
  accepted_of_selected 13 110728 ⟨392282, by decide⟩ ⟨13, 2, 0, 392282, 110728, 953, 16384⟩
    (by decide) selected_cut_15247

theorem selected_cut_15248 : selected 8 ⟨392305, by decide⟩
    (prefixPartial 13 110729) = some ⟨13, 2, 0, 392305, 110729, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_110729_392305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110729 ⟨392305, by decide⟩ :=
  accepted_of_selected 13 110729 ⟨392305, by decide⟩ ⟨13, 2, 0, 392305, 110729, 2017, 16384⟩
    (by decide) selected_cut_15248

theorem selected_cut_15249 : selected 8 ⟨392322, by decide⟩
    (prefixPartial 13 110730) = some ⟨13, 2, 0, 392322, 110730, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_110730_392322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110730 ⟨392322, by decide⟩ :=
  accepted_of_selected 13 110730 ⟨392322, by decide⟩ ⟨13, 2, 0, 392322, 110730, 1177, 16384⟩
    (by decide) selected_cut_15249

theorem selected_cut_15250 : selected 8 ⟨392331, by decide⟩
    (prefixPartial 13 110731) = some ⟨13, 2, 0, 392331, 110731, 869, 16384⟩ := by
  decide +kernel

theorem context_13_110731_392331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110731 ⟨392331, by decide⟩ :=
  accepted_of_selected 13 110731 ⟨392331, by decide⟩ ⟨13, 2, 0, 392331, 110731, 869, 16384⟩
    (by decide) selected_cut_15250

theorem unmarked_context_12_27682_392332 : frontier 9 ⟨392332, by decide⟩
    (prefixCache 12 27682) (prefixPartial 12 27682) = false := by
  decide +kernel

theorem node_context_12_27682_392332 : EJMOriginalGlobalDAGData.nodes 9 ⟨392332, by decide⟩ =
    .split (coordinate 12) (![⟨392282, by decide⟩,⟨392305, by decide⟩,⟨392322, by decide⟩,⟨392331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27682_392332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27682 ⟨392332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27682
    ⟨392332, by decide⟩ (by decide) (![⟨392282, by decide⟩,⟨392305, by decide⟩,⟨392322, by decide⟩,⟨392331, by decide⟩]) unmarked_context_12_27682_392332 node_context_12_27682_392332
  intro a
  fin_cases a
  · exact context_13_110728_392282
  · exact context_13_110729_392305
  · exact context_13_110730_392322
  · exact context_13_110731_392331

theorem selected_cut_15251 : selected 8 ⟨392346, by decide⟩
    (prefixPartial 13 110732) = some ⟨13, 2, 0, 392346, 110732, 973, 16384⟩ := by
  decide +kernel

theorem context_13_110732_392346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110732 ⟨392346, by decide⟩ :=
  accepted_of_selected 13 110732 ⟨392346, by decide⟩ ⟨13, 2, 0, 392346, 110732, 973, 16384⟩
    (by decide) selected_cut_15251

theorem selected_cut_15252 : selected 8 ⟨392376, by decide⟩
    (prefixPartial 13 110733) = some ⟨13, 2, 0, 392376, 110733, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_110733_392376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110733 ⟨392376, by decide⟩ :=
  accepted_of_selected 13 110733 ⟨392376, by decide⟩ ⟨13, 2, 0, 392376, 110733, 2093, 16384⟩
    (by decide) selected_cut_15252

theorem selected_cut_15253 : selected 8 ⟨392393, by decide⟩
    (prefixPartial 13 110734) = some ⟨13, 2, 0, 392393, 110734, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_110734_392393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110734 ⟨392393, by decide⟩ :=
  accepted_of_selected 13 110734 ⟨392393, by decide⟩ ⟨13, 2, 0, 392393, 110734, 1285, 16384⟩
    (by decide) selected_cut_15253

theorem selected_cut_15254 : selected 8 ⟨392402, by decide⟩
    (prefixPartial 13 110735) = some ⟨13, 2, 0, 392402, 110735, 861, 16384⟩ := by
  decide +kernel

theorem context_13_110735_392402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110735 ⟨392402, by decide⟩ :=
  accepted_of_selected 13 110735 ⟨392402, by decide⟩ ⟨13, 2, 0, 392402, 110735, 861, 16384⟩
    (by decide) selected_cut_15254

theorem unmarked_context_12_27683_392403 : frontier 9 ⟨392403, by decide⟩
    (prefixCache 12 27683) (prefixPartial 12 27683) = false := by
  decide +kernel

theorem node_context_12_27683_392403 : EJMOriginalGlobalDAGData.nodes 9 ⟨392403, by decide⟩ =
    .split (coordinate 12) (![⟨392346, by decide⟩,⟨392376, by decide⟩,⟨392393, by decide⟩,⟨392402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27683_392403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27683 ⟨392403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27683
    ⟨392403, by decide⟩ (by decide) (![⟨392346, by decide⟩,⟨392376, by decide⟩,⟨392393, by decide⟩,⟨392402, by decide⟩]) unmarked_context_12_27683_392403 node_context_12_27683_392403
  intro a
  fin_cases a
  · exact context_13_110732_392346
  · exact context_13_110733_392376
  · exact context_13_110734_392393
  · exact context_13_110735_392402

theorem unmarked_context_11_6920_392404 : frontier 10 ⟨392404, by decide⟩
    (prefixCache 11 6920) (prefixPartial 11 6920) = false := by
  decide +kernel

theorem node_context_11_6920_392404 : EJMOriginalGlobalDAGData.nodes 10 ⟨392404, by decide⟩ =
    .split (coordinate 11) (![⟨392207, by decide⟩,⟨392269, by decide⟩,⟨392332, by decide⟩,⟨392403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6920_392404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6920 ⟨392404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6920
    ⟨392404, by decide⟩ (by decide) (![⟨392207, by decide⟩,⟨392269, by decide⟩,⟨392332, by decide⟩,⟨392403, by decide⟩]) unmarked_context_11_6920_392404 node_context_11_6920_392404
  intro a
  fin_cases a
  · exact context_12_27680_392207
  · exact context_12_27681_392269
  · exact context_12_27682_392332
  · exact context_12_27683_392403

theorem selected_cut_15255 : selected 8 ⟨392416, by decide⟩
    (prefixPartial 13 110736) = some ⟨13, 2, 0, 392416, 110736, 777, 16384⟩ := by
  decide +kernel

theorem context_13_110736_392416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110736 ⟨392416, by decide⟩ :=
  accepted_of_selected 13 110736 ⟨392416, by decide⟩ ⟨13, 2, 0, 392416, 110736, 777, 16384⟩
    (by decide) selected_cut_15255

theorem selected_cut_15256 : selected 8 ⟨392438, by decide⟩
    (prefixPartial 13 110737) = some ⟨13, 2, 0, 392438, 110737, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_110737_392438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110737 ⟨392438, by decide⟩ :=
  accepted_of_selected 13 110737 ⟨392438, by decide⟩ ⟨13, 2, 0, 392438, 110737, 1857, 16384⟩
    (by decide) selected_cut_15256

theorem selected_cut_15257 : selected 8 ⟨392456, by decide⟩
    (prefixPartial 13 110738) = some ⟨13, 2, 0, 392456, 110738, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_110738_392456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110738 ⟨392456, by decide⟩ :=
  accepted_of_selected 13 110738 ⟨392456, by decide⟩ ⟨13, 2, 0, 392456, 110738, 1245, 16384⟩
    (by decide) selected_cut_15257

theorem selected_cut_15258 : selected 8 ⟨392461, by decide⟩
    (prefixPartial 13 110739) = some ⟨13, 2, 0, 392461, 110739, 677, 16384⟩ := by
  decide +kernel

theorem context_13_110739_392461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110739 ⟨392461, by decide⟩ :=
  accepted_of_selected 13 110739 ⟨392461, by decide⟩ ⟨13, 2, 0, 392461, 110739, 677, 16384⟩
    (by decide) selected_cut_15258

theorem unmarked_context_12_27684_392462 : frontier 9 ⟨392462, by decide⟩
    (prefixCache 12 27684) (prefixPartial 12 27684) = false := by
  decide +kernel

theorem node_context_12_27684_392462 : EJMOriginalGlobalDAGData.nodes 9 ⟨392462, by decide⟩ =
    .split (coordinate 12) (![⟨392416, by decide⟩,⟨392438, by decide⟩,⟨392456, by decide⟩,⟨392461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27684_392462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27684 ⟨392462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27684
    ⟨392462, by decide⟩ (by decide) (![⟨392416, by decide⟩,⟨392438, by decide⟩,⟨392456, by decide⟩,⟨392461, by decide⟩]) unmarked_context_12_27684_392462 node_context_12_27684_392462
  intro a
  fin_cases a
  · exact context_13_110736_392416
  · exact context_13_110737_392438
  · exact context_13_110738_392456
  · exact context_13_110739_392461

theorem selected_cut_15259 : selected 8 ⟨392476, by decide⟩
    (prefixPartial 13 110740) = some ⟨13, 2, 0, 392476, 110740, 873, 16384⟩ := by
  decide +kernel

theorem context_13_110740_392476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110740 ⟨392476, by decide⟩ :=
  accepted_of_selected 13 110740 ⟨392476, by decide⟩ ⟨13, 2, 0, 392476, 110740, 873, 16384⟩
    (by decide) selected_cut_15259

theorem selected_cut_15260 : selected 8 ⟨392499, by decide⟩
    (prefixPartial 13 110741) = some ⟨13, 2, 0, 392499, 110741, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_110741_392499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110741 ⟨392499, by decide⟩ :=
  accepted_of_selected 13 110741 ⟨392499, by decide⟩ ⟨13, 2, 0, 392499, 110741, 1605, 16384⟩
    (by decide) selected_cut_15260

theorem selected_cut_15261 : selected 8 ⟨392517, by decide⟩
    (prefixPartial 13 110742) = some ⟨13, 2, 0, 392517, 110742, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_110742_392517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110742 ⟨392517, by decide⟩ :=
  accepted_of_selected 13 110742 ⟨392517, by decide⟩ ⟨13, 2, 0, 392517, 110742, 1437, 16384⟩
    (by decide) selected_cut_15261

theorem selected_cut_15262 : selected 8 ⟨392523, by decide⟩
    (prefixPartial 13 110743) = some ⟨13, 2, 0, 392523, 110743, 789, 16384⟩ := by
  decide +kernel

theorem context_13_110743_392523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110743 ⟨392523, by decide⟩ :=
  accepted_of_selected 13 110743 ⟨392523, by decide⟩ ⟨13, 2, 0, 392523, 110743, 789, 16384⟩
    (by decide) selected_cut_15262

theorem unmarked_context_12_27685_392524 : frontier 9 ⟨392524, by decide⟩
    (prefixCache 12 27685) (prefixPartial 12 27685) = false := by
  decide +kernel

theorem node_context_12_27685_392524 : EJMOriginalGlobalDAGData.nodes 9 ⟨392524, by decide⟩ =
    .split (coordinate 12) (![⟨392476, by decide⟩,⟨392499, by decide⟩,⟨392517, by decide⟩,⟨392523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27685_392524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27685 ⟨392524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27685
    ⟨392524, by decide⟩ (by decide) (![⟨392476, by decide⟩,⟨392499, by decide⟩,⟨392517, by decide⟩,⟨392523, by decide⟩]) unmarked_context_12_27685_392524 node_context_12_27685_392524
  intro a
  fin_cases a
  · exact context_13_110740_392476
  · exact context_13_110741_392499
  · exact context_13_110742_392517
  · exact context_13_110743_392523

theorem selected_cut_15263 : selected 8 ⟨392536, by decide⟩
    (prefixPartial 13 110744) = some ⟨13, 2, 0, 392536, 110744, 801, 16384⟩ := by
  decide +kernel

theorem context_13_110744_392536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110744 ⟨392536, by decide⟩ :=
  accepted_of_selected 13 110744 ⟨392536, by decide⟩ ⟨13, 2, 0, 392536, 110744, 801, 16384⟩
    (by decide) selected_cut_15263

theorem selected_cut_15264 : selected 8 ⟨392558, by decide⟩
    (prefixPartial 13 110745) = some ⟨13, 2, 0, 392558, 110745, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_110745_392558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110745 ⟨392558, by decide⟩ :=
  accepted_of_selected 13 110745 ⟨392558, by decide⟩ ⟨13, 2, 0, 392558, 110745, 1965, 16384⟩
    (by decide) selected_cut_15264

theorem selected_cut_15265 : selected 8 ⟨392573, by decide⟩
    (prefixPartial 13 110746) = some ⟨13, 2, 0, 392573, 110746, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_110746_392573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110746 ⟨392573, by decide⟩ :=
  accepted_of_selected 13 110746 ⟨392573, by decide⟩ ⟨13, 2, 0, 392573, 110746, 1281, 16384⟩
    (by decide) selected_cut_15265

theorem selected_cut_15266 : selected 8 ⟨392585, by decide⟩
    (prefixPartial 13 110747) = some ⟨13, 2, 0, 392585, 110747, 833, 16384⟩ := by
  decide +kernel

theorem context_13_110747_392585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110747 ⟨392585, by decide⟩ :=
  accepted_of_selected 13 110747 ⟨392585, by decide⟩ ⟨13, 2, 0, 392585, 110747, 833, 16384⟩
    (by decide) selected_cut_15266

theorem unmarked_context_12_27686_392586 : frontier 9 ⟨392586, by decide⟩
    (prefixCache 12 27686) (prefixPartial 12 27686) = false := by
  decide +kernel

theorem node_context_12_27686_392586 : EJMOriginalGlobalDAGData.nodes 9 ⟨392586, by decide⟩ =
    .split (coordinate 12) (![⟨392536, by decide⟩,⟨392558, by decide⟩,⟨392573, by decide⟩,⟨392585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27686_392586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27686 ⟨392586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27686
    ⟨392586, by decide⟩ (by decide) (![⟨392536, by decide⟩,⟨392558, by decide⟩,⟨392573, by decide⟩,⟨392585, by decide⟩]) unmarked_context_12_27686_392586 node_context_12_27686_392586
  intro a
  fin_cases a
  · exact context_13_110744_392536
  · exact context_13_110745_392558
  · exact context_13_110746_392573
  · exact context_13_110747_392585

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
