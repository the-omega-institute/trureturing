/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover392
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_300296_1010835 : frontier 9 ⟨1010835, by decide⟩
    (prefixCache 12 300296) (prefixPartial 12 300296) = false := by
  decide +kernel

theorem node_context_12_300296_1010835 : EJMOriginalGlobalDAGData.nodes 9 ⟨1010835, by decide⟩ =
    .split (coordinate 12) (![⟨1010765, by decide⟩,⟨1010795, by decide⟩,⟨1010825, by decide⟩,⟨1010834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300296_1010835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300296 ⟨1010835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300296
    ⟨1010835, by decide⟩ (by decide) (![⟨1010765, by decide⟩,⟨1010795, by decide⟩,⟨1010825, by decide⟩,⟨1010834, by decide⟩]) unmarked_context_12_300296_1010835 node_context_12_300296_1010835
  intro a
  fin_cases a
  · exact context_13_1201184_1010765
  · exact context_13_1201185_1010795
  · exact context_13_1201186_1010825
  · exact context_13_1201187_1010834

theorem selected_cut_37731 : selected 9 ⟨1010898, by decide⟩
    (prefixPartial 12 300297) = some ⟨12, 2, 0, 1010898, 300297, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_300297_1010898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300297 ⟨1010898, by decide⟩ :=
  accepted_of_selected 12 300297 ⟨1010898, by decide⟩ ⟨12, 2, 0, 1010898, 300297, 3513, 65536⟩
    (by decide) selected_cut_37731

theorem selected_cut_37732 : selected 9 ⟨1010986, by decide⟩
    (prefixPartial 12 300298) = some ⟨12, 2, 0, 1010986, 300298, 4025, 65536⟩ := by
  decide +kernel

theorem context_12_300298_1010986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300298 ⟨1010986, by decide⟩ :=
  accepted_of_selected 12 300298 ⟨1010986, by decide⟩ ⟨12, 2, 0, 1010986, 300298, 4025, 65536⟩
    (by decide) selected_cut_37732

theorem selected_cut_37733 : selected 9 ⟨1011053, by decide⟩
    (prefixPartial 12 300299) = some ⟨12, 2, 0, 1011053, 300299, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_300299_1011053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300299 ⟨1011053, by decide⟩ :=
  accepted_of_selected 12 300299 ⟨1011053, by decide⟩ ⟨12, 2, 0, 1011053, 300299, 3861, 65536⟩
    (by decide) selected_cut_37733

theorem unmarked_context_11_75074_1011054 : frontier 10 ⟨1011054, by decide⟩
    (prefixCache 11 75074) (prefixPartial 11 75074) = false := by
  decide +kernel

theorem node_context_11_75074_1011054 : EJMOriginalGlobalDAGData.nodes 10 ⟨1011054, by decide⟩ =
    .split (coordinate 11) (![⟨1010835, by decide⟩,⟨1010898, by decide⟩,⟨1010986, by decide⟩,⟨1011053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75074_1011054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75074 ⟨1011054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75074
    ⟨1011054, by decide⟩ (by decide) (![⟨1010835, by decide⟩,⟨1010898, by decide⟩,⟨1010986, by decide⟩,⟨1011053, by decide⟩]) unmarked_context_11_75074_1011054 node_context_11_75074_1011054
  intro a
  fin_cases a
  · exact context_12_300296_1010835
  · exact context_12_300297_1010898
  · exact context_12_300298_1010986
  · exact context_12_300299_1011053

theorem selected_cut_37734 : selected 8 ⟨1011075, by decide⟩
    (prefixPartial 13 1201200) = some ⟨13, 2, 0, 1011075, 1201200, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_1201200_1011075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201200 ⟨1011075, by decide⟩ :=
  accepted_of_selected 13 1201200 ⟨1011075, by decide⟩ ⟨13, 2, 0, 1011075, 1201200, 1025, 16384⟩
    (by decide) selected_cut_37734

theorem selected_cut_37735 : selected 8 ⟨1011100, by decide⟩
    (prefixPartial 13 1201201) = some ⟨13, 2, 0, 1011100, 1201201, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_1201201_1011100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201201 ⟨1011100, by decide⟩ :=
  accepted_of_selected 13 1201201 ⟨1011100, by decide⟩ ⟨13, 2, 0, 1011100, 1201201, 1577, 16384⟩
    (by decide) selected_cut_37735

theorem selected_cut_37736 : selected 8 ⟨1011122, by decide⟩
    (prefixPartial 13 1201202) = some ⟨13, 2, 0, 1011122, 1201202, 885, 16384⟩ := by
  decide +kernel

theorem context_13_1201202_1011122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201202 ⟨1011122, by decide⟩ :=
  accepted_of_selected 13 1201202 ⟨1011122, by decide⟩ ⟨13, 2, 0, 1011122, 1201202, 885, 16384⟩
    (by decide) selected_cut_37736

theorem selected_cut_37737 : selected 8 ⟨1011140, by decide⟩
    (prefixPartial 13 1201203) = some ⟨13, 2, 0, 1011140, 1201203, 701, 16384⟩ := by
  decide +kernel

theorem context_13_1201203_1011140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201203 ⟨1011140, by decide⟩ :=
  accepted_of_selected 13 1201203 ⟨1011140, by decide⟩ ⟨13, 2, 0, 1011140, 1201203, 701, 16384⟩
    (by decide) selected_cut_37737

theorem unmarked_context_12_300300_1011141 : frontier 9 ⟨1011141, by decide⟩
    (prefixCache 12 300300) (prefixPartial 12 300300) = false := by
  decide +kernel

theorem node_context_12_300300_1011141 : EJMOriginalGlobalDAGData.nodes 9 ⟨1011141, by decide⟩ =
    .split (coordinate 12) (![⟨1011075, by decide⟩,⟨1011100, by decide⟩,⟨1011122, by decide⟩,⟨1011140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300300_1011141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300300 ⟨1011141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300300
    ⟨1011141, by decide⟩ (by decide) (![⟨1011075, by decide⟩,⟨1011100, by decide⟩,⟨1011122, by decide⟩,⟨1011140, by decide⟩]) unmarked_context_12_300300_1011141 node_context_12_300300_1011141
  intro a
  fin_cases a
  · exact context_13_1201200_1011075
  · exact context_13_1201201_1011100
  · exact context_13_1201202_1011122
  · exact context_13_1201203_1011140

theorem selected_cut_37738 : selected 9 ⟨1011213, by decide⟩
    (prefixPartial 12 300301) = some ⟨12, 2, 0, 1011213, 300301, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_300301_1011213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300301 ⟨1011213, by decide⟩ :=
  accepted_of_selected 12 300301 ⟨1011213, by decide⟩ ⟨12, 2, 0, 1011213, 300301, 3597, 65536⟩
    (by decide) selected_cut_37738

theorem selected_cut_37739 : selected 9 ⟨1011283, by decide⟩
    (prefixPartial 12 300302) = some ⟨12, 2, 0, 1011283, 300302, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_300302_1011283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300302 ⟨1011283, by decide⟩ :=
  accepted_of_selected 12 300302 ⟨1011283, by decide⟩ ⟨12, 2, 0, 1011283, 300302, 3901, 65536⟩
    (by decide) selected_cut_37739

theorem selected_cut_37740 : selected 8 ⟨1011302, by decide⟩
    (prefixPartial 13 1201212) = some ⟨13, 2, 0, 1011302, 1201212, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_1201212_1011302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201212 ⟨1011302, by decide⟩ :=
  accepted_of_selected 13 1201212 ⟨1011302, by decide⟩ ⟨13, 2, 0, 1011302, 1201212, 1173, 16384⟩
    (by decide) selected_cut_37740

theorem selected_cut_37741 : selected 8 ⟨1011327, by decide⟩
    (prefixPartial 13 1201213) = some ⟨13, 2, 0, 1011327, 1201213, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_1201213_1011327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201213 ⟨1011327, by decide⟩ :=
  accepted_of_selected 13 1201213 ⟨1011327, by decide⟩ ⟨13, 2, 0, 1011327, 1201213, 1501, 16384⟩
    (by decide) selected_cut_37741

theorem selected_cut_37742 : selected 8 ⟨1011347, by decide⟩
    (prefixPartial 13 1201214) = some ⟨13, 2, 0, 1011347, 1201214, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1201214_1011347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201214 ⟨1011347, by decide⟩ :=
  accepted_of_selected 13 1201214 ⟨1011347, by decide⟩ ⟨13, 2, 0, 1011347, 1201214, 853, 16384⟩
    (by decide) selected_cut_37742

theorem selected_cut_37743 : selected 8 ⟨1011359, by decide⟩
    (prefixPartial 13 1201215) = some ⟨13, 2, 0, 1011359, 1201215, 653, 16384⟩ := by
  decide +kernel

theorem context_13_1201215_1011359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201215 ⟨1011359, by decide⟩ :=
  accepted_of_selected 13 1201215 ⟨1011359, by decide⟩ ⟨13, 2, 0, 1011359, 1201215, 653, 16384⟩
    (by decide) selected_cut_37743

theorem unmarked_context_12_300303_1011360 : frontier 9 ⟨1011360, by decide⟩
    (prefixCache 12 300303) (prefixPartial 12 300303) = false := by
  decide +kernel

theorem node_context_12_300303_1011360 : EJMOriginalGlobalDAGData.nodes 9 ⟨1011360, by decide⟩ =
    .split (coordinate 12) (![⟨1011302, by decide⟩,⟨1011327, by decide⟩,⟨1011347, by decide⟩,⟨1011359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300303_1011360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300303 ⟨1011360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300303
    ⟨1011360, by decide⟩ (by decide) (![⟨1011302, by decide⟩,⟨1011327, by decide⟩,⟨1011347, by decide⟩,⟨1011359, by decide⟩]) unmarked_context_12_300303_1011360 node_context_12_300303_1011360
  intro a
  fin_cases a
  · exact context_13_1201212_1011302
  · exact context_13_1201213_1011327
  · exact context_13_1201214_1011347
  · exact context_13_1201215_1011359

theorem unmarked_context_11_75075_1011361 : frontier 10 ⟨1011361, by decide⟩
    (prefixCache 11 75075) (prefixPartial 11 75075) = false := by
  decide +kernel

theorem node_context_11_75075_1011361 : EJMOriginalGlobalDAGData.nodes 10 ⟨1011361, by decide⟩ =
    .split (coordinate 11) (![⟨1011141, by decide⟩,⟨1011213, by decide⟩,⟨1011283, by decide⟩,⟨1011360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75075_1011361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75075 ⟨1011361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75075
    ⟨1011361, by decide⟩ (by decide) (![⟨1011141, by decide⟩,⟨1011213, by decide⟩,⟨1011283, by decide⟩,⟨1011360, by decide⟩]) unmarked_context_11_75075_1011361 node_context_11_75075_1011361
  intro a
  fin_cases a
  · exact context_12_300300_1011141
  · exact context_12_300301_1011213
  · exact context_12_300302_1011283
  · exact context_12_300303_1011360

theorem unmarked_context_10_18768_1011362 : frontier 11 ⟨1011362, by decide⟩
    (prefixCache 10 18768) (prefixPartial 10 18768) = false := by
  decide +kernel

theorem node_context_10_18768_1011362 : EJMOriginalGlobalDAGData.nodes 11 ⟨1011362, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1010751, by decide⟩,⟨1011054, by decide⟩,⟨1011361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18768_1011362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18768 ⟨1011362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18768
    ⟨1011362, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1010751, by decide⟩,⟨1011054, by decide⟩,⟨1011361, by decide⟩]) unmarked_context_10_18768_1011362 node_context_10_18768_1011362
  intro a
  fin_cases a
  · exact context_11_75072_167448
  · exact context_11_75073_1010751
  · exact context_11_75074_1011054
  · exact context_11_75075_1011361

theorem selected_cut_37744 : selected 9 ⟨1011406, by decide⟩
    (prefixPartial 12 300304) = some ⟨12, 2, 0, 1011406, 300304, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_300304_1011406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300304 ⟨1011406, by decide⟩ :=
  accepted_of_selected 12 300304 ⟨1011406, by decide⟩ ⟨12, 2, 0, 1011406, 300304, 1685, 65536⟩
    (by decide) selected_cut_37744

theorem selected_cut_37745 : selected 9 ⟨1011456, by decide⟩
    (prefixPartial 12 300305) = some ⟨12, 2, 0, 1011456, 300305, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_300305_1011456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300305 ⟨1011456, by decide⟩ :=
  accepted_of_selected 12 300305 ⟨1011456, by decide⟩ ⟨12, 2, 0, 1011456, 300305, 2233, 65536⟩
    (by decide) selected_cut_37745

theorem selected_cut_37746 : selected 9 ⟨1011491, by decide⟩
    (prefixPartial 12 300306) = some ⟨12, 2, 0, 1011491, 300306, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_300306_1011491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300306 ⟨1011491, by decide⟩ :=
  accepted_of_selected 12 300306 ⟨1011491, by decide⟩ ⟨12, 2, 0, 1011491, 300306, 2373, 65536⟩
    (by decide) selected_cut_37746

theorem selected_cut_37747 : selected 9 ⟨1011531, by decide⟩
    (prefixPartial 12 300307) = some ⟨12, 2, 0, 1011531, 300307, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_300307_1011531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300307 ⟨1011531, by decide⟩ :=
  accepted_of_selected 12 300307 ⟨1011531, by decide⟩ ⟨12, 2, 0, 1011531, 300307, 2449, 65536⟩
    (by decide) selected_cut_37747

theorem unmarked_context_11_75076_1011532 : frontier 10 ⟨1011532, by decide⟩
    (prefixCache 11 75076) (prefixPartial 11 75076) = false := by
  decide +kernel

theorem node_context_11_75076_1011532 : EJMOriginalGlobalDAGData.nodes 10 ⟨1011532, by decide⟩ =
    .split (coordinate 11) (![⟨1011406, by decide⟩,⟨1011456, by decide⟩,⟨1011491, by decide⟩,⟨1011531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75076_1011532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75076 ⟨1011532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75076
    ⟨1011532, by decide⟩ (by decide) (![⟨1011406, by decide⟩,⟨1011456, by decide⟩,⟨1011491, by decide⟩,⟨1011531, by decide⟩]) unmarked_context_11_75076_1011532 node_context_11_75076_1011532
  intro a
  fin_cases a
  · exact context_12_300304_1011406
  · exact context_12_300305_1011456
  · exact context_12_300306_1011491
  · exact context_12_300307_1011531

theorem selected_cut_37748 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75077) = some ⟨11, 1, 0, 892405, 75077, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75077_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75077 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75077 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75077, 1, 262144⟩
    (by decide) selected_cut_37748

theorem selected_cut_37749 : selected 9 ⟨1011574, by decide⟩
    (prefixPartial 12 300312) = some ⟨12, 2, 0, 1011574, 300312, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_300312_1011574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300312 ⟨1011574, by decide⟩ :=
  accepted_of_selected 12 300312 ⟨1011574, by decide⟩ ⟨12, 2, 0, 1011574, 300312, 2649, 65536⟩
    (by decide) selected_cut_37749

theorem selected_cut_37750 : selected 9 ⟨1011617, by decide⟩
    (prefixPartial 12 300313) = some ⟨12, 2, 0, 1011617, 300313, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_300313_1011617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300313 ⟨1011617, by decide⟩ :=
  accepted_of_selected 12 300313 ⟨1011617, by decide⟩ ⟨12, 2, 0, 1011617, 300313, 2401, 65536⟩
    (by decide) selected_cut_37750

theorem selected_cut_37751 : selected 9 ⟨1011658, by decide⟩
    (prefixPartial 12 300314) = some ⟨12, 2, 0, 1011658, 300314, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_300314_1011658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300314 ⟨1011658, by decide⟩ :=
  accepted_of_selected 12 300314 ⟨1011658, by decide⟩ ⟨12, 2, 0, 1011658, 300314, 2681, 65536⟩
    (by decide) selected_cut_37751

theorem selected_cut_37752 : selected 9 ⟨1011698, by decide⟩
    (prefixPartial 12 300315) = some ⟨12, 2, 0, 1011698, 300315, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_300315_1011698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300315 ⟨1011698, by decide⟩ :=
  accepted_of_selected 12 300315 ⟨1011698, by decide⟩ ⟨12, 2, 0, 1011698, 300315, 2673, 65536⟩
    (by decide) selected_cut_37752

theorem unmarked_context_11_75078_1011699 : frontier 10 ⟨1011699, by decide⟩
    (prefixCache 11 75078) (prefixPartial 11 75078) = false := by
  decide +kernel

theorem node_context_11_75078_1011699 : EJMOriginalGlobalDAGData.nodes 10 ⟨1011699, by decide⟩ =
    .split (coordinate 11) (![⟨1011574, by decide⟩,⟨1011617, by decide⟩,⟨1011658, by decide⟩,⟨1011698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75078_1011699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75078 ⟨1011699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75078
    ⟨1011699, by decide⟩ (by decide) (![⟨1011574, by decide⟩,⟨1011617, by decide⟩,⟨1011658, by decide⟩,⟨1011698, by decide⟩]) unmarked_context_11_75078_1011699 node_context_11_75078_1011699
  intro a
  fin_cases a
  · exact context_12_300312_1011574
  · exact context_12_300313_1011617
  · exact context_12_300314_1011658
  · exact context_12_300315_1011698

theorem selected_cut_37753 : selected 9 ⟨1011738, by decide⟩
    (prefixPartial 12 300316) = some ⟨12, 2, 0, 1011738, 300316, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_300316_1011738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300316 ⟨1011738, by decide⟩ :=
  accepted_of_selected 12 300316 ⟨1011738, by decide⟩ ⟨12, 2, 0, 1011738, 300316, 2733, 65536⟩
    (by decide) selected_cut_37753

theorem selected_cut_37754 : selected 9 ⟨1011773, by decide⟩
    (prefixPartial 12 300317) = some ⟨12, 2, 0, 1011773, 300317, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_300317_1011773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300317 ⟨1011773, by decide⟩ :=
  accepted_of_selected 12 300317 ⟨1011773, by decide⟩ ⟨12, 2, 0, 1011773, 300317, 2401, 65536⟩
    (by decide) selected_cut_37754

theorem selected_cut_37755 : selected 9 ⟨1011812, by decide⟩
    (prefixPartial 12 300318) = some ⟨12, 2, 0, 1011812, 300318, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_300318_1011812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300318 ⟨1011812, by decide⟩ :=
  accepted_of_selected 12 300318 ⟨1011812, by decide⟩ ⟨12, 2, 0, 1011812, 300318, 2669, 65536⟩
    (by decide) selected_cut_37755

theorem selected_cut_37756 : selected 9 ⟨1011865, by decide⟩
    (prefixPartial 12 300319) = some ⟨12, 2, 0, 1011865, 300319, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_300319_1011865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300319 ⟨1011865, by decide⟩ :=
  accepted_of_selected 12 300319 ⟨1011865, by decide⟩ ⟨12, 2, 0, 1011865, 300319, 2905, 65536⟩
    (by decide) selected_cut_37756

theorem unmarked_context_11_75079_1011866 : frontier 10 ⟨1011866, by decide⟩
    (prefixCache 11 75079) (prefixPartial 11 75079) = false := by
  decide +kernel

theorem node_context_11_75079_1011866 : EJMOriginalGlobalDAGData.nodes 10 ⟨1011866, by decide⟩ =
    .split (coordinate 11) (![⟨1011738, by decide⟩,⟨1011773, by decide⟩,⟨1011812, by decide⟩,⟨1011865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75079_1011866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75079 ⟨1011866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75079
    ⟨1011866, by decide⟩ (by decide) (![⟨1011738, by decide⟩,⟨1011773, by decide⟩,⟨1011812, by decide⟩,⟨1011865, by decide⟩]) unmarked_context_11_75079_1011866 node_context_11_75079_1011866
  intro a
  fin_cases a
  · exact context_12_300316_1011738
  · exact context_12_300317_1011773
  · exact context_12_300318_1011812
  · exact context_12_300319_1011865

theorem unmarked_context_10_18769_1011867 : frontier 11 ⟨1011867, by decide⟩
    (prefixCache 10 18769) (prefixPartial 10 18769) = false := by
  decide +kernel

theorem node_context_10_18769_1011867 : EJMOriginalGlobalDAGData.nodes 11 ⟨1011867, by decide⟩ =
    .split (coordinate 10) (![⟨1011532, by decide⟩,⟨892405, by decide⟩,⟨1011699, by decide⟩,⟨1011866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18769_1011867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18769 ⟨1011867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18769
    ⟨1011867, by decide⟩ (by decide) (![⟨1011532, by decide⟩,⟨892405, by decide⟩,⟨1011699, by decide⟩,⟨1011866, by decide⟩]) unmarked_context_10_18769_1011867 node_context_10_18769_1011867
  intro a
  fin_cases a
  · exact context_11_75076_1011532
  · exact context_11_75077_892405
  · exact context_11_75078_1011699
  · exact context_11_75079_1011866

theorem selected_cut_37757 : selected 9 ⟨1011938, by decide⟩
    (prefixPartial 12 300320) = some ⟨12, 2, 0, 1011938, 300320, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_300320_1011938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300320 ⟨1011938, by decide⟩ :=
  accepted_of_selected 12 300320 ⟨1011938, by decide⟩ ⟨12, 2, 0, 1011938, 300320, 3161, 65536⟩
    (by decide) selected_cut_37757

theorem selected_cut_37758 : selected 9 ⟨1011992, by decide⟩
    (prefixPartial 12 300321) = some ⟨12, 2, 0, 1011992, 300321, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_300321_1011992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300321 ⟨1011992, by decide⟩ :=
  accepted_of_selected 12 300321 ⟨1011992, by decide⟩ ⟨12, 2, 0, 1011992, 300321, 2929, 65536⟩
    (by decide) selected_cut_37758

theorem selected_cut_37759 : selected 9 ⟨1012037, by decide⟩
    (prefixPartial 12 300322) = some ⟨12, 2, 0, 1012037, 300322, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_300322_1012037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300322 ⟨1012037, by decide⟩ :=
  accepted_of_selected 12 300322 ⟨1012037, by decide⟩ ⟨12, 2, 0, 1012037, 300322, 2817, 65536⟩
    (by decide) selected_cut_37759

theorem selected_cut_37760 : selected 9 ⟨1012089, by decide⟩
    (prefixPartial 12 300323) = some ⟨12, 2, 0, 1012089, 300323, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_300323_1012089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300323 ⟨1012089, by decide⟩ :=
  accepted_of_selected 12 300323 ⟨1012089, by decide⟩ ⟨12, 2, 0, 1012089, 300323, 3101, 65536⟩
    (by decide) selected_cut_37760

theorem unmarked_context_11_75080_1012090 : frontier 10 ⟨1012090, by decide⟩
    (prefixCache 11 75080) (prefixPartial 11 75080) = false := by
  decide +kernel

theorem node_context_11_75080_1012090 : EJMOriginalGlobalDAGData.nodes 10 ⟨1012090, by decide⟩ =
    .split (coordinate 11) (![⟨1011938, by decide⟩,⟨1011992, by decide⟩,⟨1012037, by decide⟩,⟨1012089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75080_1012090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75080 ⟨1012090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75080
    ⟨1012090, by decide⟩ (by decide) (![⟨1011938, by decide⟩,⟨1011992, by decide⟩,⟨1012037, by decide⟩,⟨1012089, by decide⟩]) unmarked_context_11_75080_1012090 node_context_11_75080_1012090
  intro a
  fin_cases a
  · exact context_12_300320_1011938
  · exact context_12_300321_1011992
  · exact context_12_300322_1012037
  · exact context_12_300323_1012089

theorem selected_cut_37761 : selected 9 ⟨1012146, by decide⟩
    (prefixPartial 12 300324) = some ⟨12, 2, 0, 1012146, 300324, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_300324_1012146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300324 ⟨1012146, by decide⟩ :=
  accepted_of_selected 12 300324 ⟨1012146, by decide⟩ ⟨12, 2, 0, 1012146, 300324, 3205, 65536⟩
    (by decide) selected_cut_37761

theorem selected_cut_37762 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 300325) = some ⟨12, 1, 0, 891951, 300325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300325_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300325 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 300325 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 300325, 1, 65536⟩
    (by decide) selected_cut_37762

theorem selected_cut_37763 : selected 9 ⟨1012187, by decide⟩
    (prefixPartial 12 300326) = some ⟨12, 2, 0, 1012187, 300326, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_300326_1012187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300326 ⟨1012187, by decide⟩ :=
  accepted_of_selected 12 300326 ⟨1012187, by decide⟩ ⟨12, 2, 0, 1012187, 300326, 2729, 65536⟩
    (by decide) selected_cut_37763

theorem selected_cut_37764 : selected 9 ⟨1012240, by decide⟩
    (prefixPartial 12 300327) = some ⟨12, 2, 0, 1012240, 300327, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_300327_1012240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300327 ⟨1012240, by decide⟩ :=
  accepted_of_selected 12 300327 ⟨1012240, by decide⟩ ⟨12, 2, 0, 1012240, 300327, 2997, 65536⟩
    (by decide) selected_cut_37764

theorem unmarked_context_11_75081_1012241 : frontier 10 ⟨1012241, by decide⟩
    (prefixCache 11 75081) (prefixPartial 11 75081) = false := by
  decide +kernel

theorem node_context_11_75081_1012241 : EJMOriginalGlobalDAGData.nodes 10 ⟨1012241, by decide⟩ =
    .split (coordinate 11) (![⟨1012146, by decide⟩,⟨891951, by decide⟩,⟨1012187, by decide⟩,⟨1012240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75081_1012241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75081 ⟨1012241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75081
    ⟨1012241, by decide⟩ (by decide) (![⟨1012146, by decide⟩,⟨891951, by decide⟩,⟨1012187, by decide⟩,⟨1012240, by decide⟩]) unmarked_context_11_75081_1012241 node_context_11_75081_1012241
  intro a
  fin_cases a
  · exact context_12_300324_1012146
  · exact context_12_300325_891951
  · exact context_12_300326_1012187
  · exact context_12_300327_1012240

theorem selected_cut_37765 : selected 9 ⟨1012303, by decide⟩
    (prefixPartial 12 300328) = some ⟨12, 2, 0, 1012303, 300328, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_300328_1012303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300328 ⟨1012303, by decide⟩ :=
  accepted_of_selected 12 300328 ⟨1012303, by decide⟩ ⟨12, 2, 0, 1012303, 300328, 3269, 65536⟩
    (by decide) selected_cut_37765

theorem selected_cut_37766 : selected 9 ⟨1012357, by decide⟩
    (prefixPartial 12 300329) = some ⟨12, 2, 0, 1012357, 300329, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_300329_1012357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300329 ⟨1012357, by decide⟩ :=
  accepted_of_selected 12 300329 ⟨1012357, by decide⟩ ⟨12, 2, 0, 1012357, 300329, 2893, 65536⟩
    (by decide) selected_cut_37766

theorem selected_cut_37767 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 300330) = some ⟨12, 1, 0, 661671, 300330, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300330_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300330 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 300330 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 300330, 1, 65536⟩
    (by decide) selected_cut_37767

theorem selected_cut_37768 : selected 9 ⟨1012426, by decide⟩
    (prefixPartial 12 300331) = some ⟨12, 2, 0, 1012426, 300331, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_300331_1012426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300331 ⟨1012426, by decide⟩ :=
  accepted_of_selected 12 300331 ⟨1012426, by decide⟩ ⟨12, 2, 0, 1012426, 300331, 3437, 65536⟩
    (by decide) selected_cut_37768

theorem unmarked_context_11_75082_1012427 : frontier 10 ⟨1012427, by decide⟩
    (prefixCache 11 75082) (prefixPartial 11 75082) = false := by
  decide +kernel

theorem node_context_11_75082_1012427 : EJMOriginalGlobalDAGData.nodes 10 ⟨1012427, by decide⟩ =
    .split (coordinate 11) (![⟨1012303, by decide⟩,⟨1012357, by decide⟩,⟨661671, by decide⟩,⟨1012426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75082_1012427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75082 ⟨1012427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75082
    ⟨1012427, by decide⟩ (by decide) (![⟨1012303, by decide⟩,⟨1012357, by decide⟩,⟨661671, by decide⟩,⟨1012426, by decide⟩]) unmarked_context_11_75082_1012427 node_context_11_75082_1012427
  intro a
  fin_cases a
  · exact context_12_300328_1012303
  · exact context_12_300329_1012357
  · exact context_12_300330_661671
  · exact context_12_300331_1012426

theorem selected_cut_37769 : selected 9 ⟨1012477, by decide⟩
    (prefixPartial 12 300332) = some ⟨12, 2, 0, 1012477, 300332, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_300332_1012477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300332 ⟨1012477, by decide⟩ :=
  accepted_of_selected 12 300332 ⟨1012477, by decide⟩ ⟨12, 2, 0, 1012477, 300332, 3049, 65536⟩
    (by decide) selected_cut_37769

theorem selected_cut_37770 : selected 9 ⟨1012528, by decide⟩
    (prefixPartial 12 300333) = some ⟨12, 2, 0, 1012528, 300333, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_300333_1012528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300333 ⟨1012528, by decide⟩ :=
  accepted_of_selected 12 300333 ⟨1012528, by decide⟩ ⟨12, 2, 0, 1012528, 300333, 2925, 65536⟩
    (by decide) selected_cut_37770

theorem selected_cut_37771 : selected 9 ⟨1012582, by decide⟩
    (prefixPartial 12 300334) = some ⟨12, 2, 0, 1012582, 300334, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_300334_1012582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300334 ⟨1012582, by decide⟩ :=
  accepted_of_selected 12 300334 ⟨1012582, by decide⟩ ⟨12, 2, 0, 1012582, 300334, 2993, 65536⟩
    (by decide) selected_cut_37771

theorem selected_cut_37772 : selected 9 ⟨1012645, by decide⟩
    (prefixPartial 12 300335) = some ⟨12, 2, 0, 1012645, 300335, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_300335_1012645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300335 ⟨1012645, by decide⟩ :=
  accepted_of_selected 12 300335 ⟨1012645, by decide⟩ ⟨12, 2, 0, 1012645, 300335, 3429, 65536⟩
    (by decide) selected_cut_37772

theorem unmarked_context_11_75083_1012646 : frontier 10 ⟨1012646, by decide⟩
    (prefixCache 11 75083) (prefixPartial 11 75083) = false := by
  decide +kernel

theorem node_context_11_75083_1012646 : EJMOriginalGlobalDAGData.nodes 10 ⟨1012646, by decide⟩ =
    .split (coordinate 11) (![⟨1012477, by decide⟩,⟨1012528, by decide⟩,⟨1012582, by decide⟩,⟨1012645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75083_1012646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75083 ⟨1012646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75083
    ⟨1012646, by decide⟩ (by decide) (![⟨1012477, by decide⟩,⟨1012528, by decide⟩,⟨1012582, by decide⟩,⟨1012645, by decide⟩]) unmarked_context_11_75083_1012646 node_context_11_75083_1012646
  intro a
  fin_cases a
  · exact context_12_300332_1012477
  · exact context_12_300333_1012528
  · exact context_12_300334_1012582
  · exact context_12_300335_1012645

theorem unmarked_context_10_18770_1012647 : frontier 11 ⟨1012647, by decide⟩
    (prefixCache 10 18770) (prefixPartial 10 18770) = false := by
  decide +kernel

theorem node_context_10_18770_1012647 : EJMOriginalGlobalDAGData.nodes 11 ⟨1012647, by decide⟩ =
    .split (coordinate 10) (![⟨1012090, by decide⟩,⟨1012241, by decide⟩,⟨1012427, by decide⟩,⟨1012646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18770_1012647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18770 ⟨1012647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18770
    ⟨1012647, by decide⟩ (by decide) (![⟨1012090, by decide⟩,⟨1012241, by decide⟩,⟨1012427, by decide⟩,⟨1012646, by decide⟩]) unmarked_context_10_18770_1012647 node_context_10_18770_1012647
  intro a
  fin_cases a
  · exact context_11_75080_1012090
  · exact context_11_75081_1012241
  · exact context_11_75082_1012427
  · exact context_11_75083_1012646

theorem selected_cut_37773 : selected 9 ⟨1012693, by decide⟩
    (prefixPartial 12 300336) = some ⟨12, 2, 0, 1012693, 300336, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_300336_1012693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300336 ⟨1012693, by decide⟩ :=
  accepted_of_selected 12 300336 ⟨1012693, by decide⟩ ⟨12, 2, 0, 1012693, 300336, 2717, 65536⟩
    (by decide) selected_cut_37773

theorem selected_cut_37774 : selected 9 ⟨1012737, by decide⟩
    (prefixPartial 12 300337) = some ⟨12, 2, 0, 1012737, 300337, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_300337_1012737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300337 ⟨1012737, by decide⟩ :=
  accepted_of_selected 12 300337 ⟨1012737, by decide⟩ ⟨12, 2, 0, 1012737, 300337, 2581, 65536⟩
    (by decide) selected_cut_37774

theorem selected_cut_37775 : selected 9 ⟨1012771, by decide⟩
    (prefixPartial 12 300338) = some ⟨12, 2, 0, 1012771, 300338, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_300338_1012771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300338 ⟨1012771, by decide⟩ :=
  accepted_of_selected 12 300338 ⟨1012771, by decide⟩ ⟨12, 2, 0, 1012771, 300338, 2405, 65536⟩
    (by decide) selected_cut_37775

theorem selected_cut_37776 : selected 9 ⟨1012821, by decide⟩
    (prefixPartial 12 300339) = some ⟨12, 2, 0, 1012821, 300339, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_300339_1012821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300339 ⟨1012821, by decide⟩ :=
  accepted_of_selected 12 300339 ⟨1012821, by decide⟩ ⟨12, 2, 0, 1012821, 300339, 2741, 65536⟩
    (by decide) selected_cut_37776

theorem unmarked_context_11_75084_1012822 : frontier 10 ⟨1012822, by decide⟩
    (prefixCache 11 75084) (prefixPartial 11 75084) = false := by
  decide +kernel

theorem node_context_11_75084_1012822 : EJMOriginalGlobalDAGData.nodes 10 ⟨1012822, by decide⟩ =
    .split (coordinate 11) (![⟨1012693, by decide⟩,⟨1012737, by decide⟩,⟨1012771, by decide⟩,⟨1012821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75084_1012822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75084 ⟨1012822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75084
    ⟨1012822, by decide⟩ (by decide) (![⟨1012693, by decide⟩,⟨1012737, by decide⟩,⟨1012771, by decide⟩,⟨1012821, by decide⟩]) unmarked_context_11_75084_1012822 node_context_11_75084_1012822
  intro a
  fin_cases a
  · exact context_12_300336_1012693
  · exact context_12_300337_1012737
  · exact context_12_300338_1012771
  · exact context_12_300339_1012821

theorem selected_cut_37777 : selected 9 ⟨1012883, by decide⟩
    (prefixPartial 12 300340) = some ⟨12, 2, 0, 1012883, 300340, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_300340_1012883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300340 ⟨1012883, by decide⟩ :=
  accepted_of_selected 12 300340 ⟨1012883, by decide⟩ ⟨12, 2, 0, 1012883, 300340, 2973, 65536⟩
    (by decide) selected_cut_37777

theorem selected_cut_37778 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 300341) = some ⟨12, 1, 0, 891951, 300341, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300341_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300341 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 300341 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 300341, 1, 65536⟩
    (by decide) selected_cut_37778

theorem selected_cut_37779 : selected 9 ⟨1012921, by decide⟩
    (prefixPartial 12 300342) = some ⟨12, 2, 0, 1012921, 300342, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_300342_1012921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300342 ⟨1012921, by decide⟩ :=
  accepted_of_selected 12 300342 ⟨1012921, by decide⟩ ⟨12, 2, 0, 1012921, 300342, 2441, 65536⟩
    (by decide) selected_cut_37779

theorem selected_cut_37780 : selected 9 ⟨1012965, by decide⟩
    (prefixPartial 12 300343) = some ⟨12, 2, 0, 1012965, 300343, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_300343_1012965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300343 ⟨1012965, by decide⟩ :=
  accepted_of_selected 12 300343 ⟨1012965, by decide⟩ ⟨12, 2, 0, 1012965, 300343, 2685, 65536⟩
    (by decide) selected_cut_37780

theorem unmarked_context_11_75085_1012966 : frontier 10 ⟨1012966, by decide⟩
    (prefixCache 11 75085) (prefixPartial 11 75085) = false := by
  decide +kernel

theorem node_context_11_75085_1012966 : EJMOriginalGlobalDAGData.nodes 10 ⟨1012966, by decide⟩ =
    .split (coordinate 11) (![⟨1012883, by decide⟩,⟨891951, by decide⟩,⟨1012921, by decide⟩,⟨1012965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75085_1012966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75085 ⟨1012966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75085
    ⟨1012966, by decide⟩ (by decide) (![⟨1012883, by decide⟩,⟨891951, by decide⟩,⟨1012921, by decide⟩,⟨1012965, by decide⟩]) unmarked_context_11_75085_1012966 node_context_11_75085_1012966
  intro a
  fin_cases a
  · exact context_12_300340_1012883
  · exact context_12_300341_891951
  · exact context_12_300342_1012921
  · exact context_12_300343_1012965

theorem selected_cut_37781 : selected 9 ⟨1013002, by decide⟩
    (prefixPartial 12 300344) = some ⟨12, 2, 0, 1013002, 300344, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_300344_1013002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300344 ⟨1013002, by decide⟩ :=
  accepted_of_selected 12 300344 ⟨1013002, by decide⟩ ⟨12, 2, 0, 1013002, 300344, 2569, 65536⟩
    (by decide) selected_cut_37781

theorem selected_cut_37782 : selected 9 ⟨1013035, by decide⟩
    (prefixPartial 12 300345) = some ⟨12, 2, 0, 1013035, 300345, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_300345_1013035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300345 ⟨1013035, by decide⟩ :=
  accepted_of_selected 12 300345 ⟨1013035, by decide⟩ ⟨12, 2, 0, 1013035, 300345, 2365, 65536⟩
    (by decide) selected_cut_37782

theorem selected_cut_37783 : selected 9 ⟨1013080, by decide⟩
    (prefixPartial 12 300346) = some ⟨12, 2, 0, 1013080, 300346, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_300346_1013080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300346 ⟨1013080, by decide⟩ :=
  accepted_of_selected 12 300346 ⟨1013080, by decide⟩ ⟨12, 2, 0, 1013080, 300346, 2701, 65536⟩
    (by decide) selected_cut_37783

theorem selected_cut_37784 : selected 9 ⟨1013126, by decide⟩
    (prefixPartial 12 300347) = some ⟨12, 2, 0, 1013126, 300347, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_300347_1013126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300347 ⟨1013126, by decide⟩ :=
  accepted_of_selected 12 300347 ⟨1013126, by decide⟩ ⟨12, 2, 0, 1013126, 300347, 2661, 65536⟩
    (by decide) selected_cut_37784

theorem unmarked_context_11_75086_1013127 : frontier 10 ⟨1013127, by decide⟩
    (prefixCache 11 75086) (prefixPartial 11 75086) = false := by
  decide +kernel

theorem node_context_11_75086_1013127 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013127, by decide⟩ =
    .split (coordinate 11) (![⟨1013002, by decide⟩,⟨1013035, by decide⟩,⟨1013080, by decide⟩,⟨1013126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75086_1013127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75086 ⟨1013127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75086
    ⟨1013127, by decide⟩ (by decide) (![⟨1013002, by decide⟩,⟨1013035, by decide⟩,⟨1013080, by decide⟩,⟨1013126, by decide⟩]) unmarked_context_11_75086_1013127 node_context_11_75086_1013127
  intro a
  fin_cases a
  · exact context_12_300344_1013002
  · exact context_12_300345_1013035
  · exact context_12_300346_1013080
  · exact context_12_300347_1013126

theorem selected_cut_37785 : selected 9 ⟨1013168, by decide⟩
    (prefixPartial 12 300348) = some ⟨12, 2, 0, 1013168, 300348, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_300348_1013168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300348 ⟨1013168, by decide⟩ :=
  accepted_of_selected 12 300348 ⟨1013168, by decide⟩ ⟨12, 2, 0, 1013168, 300348, 2421, 65536⟩
    (by decide) selected_cut_37785

theorem selected_cut_37786 : selected 9 ⟨1013200, by decide⟩
    (prefixPartial 12 300349) = some ⟨12, 2, 0, 1013200, 300349, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_300349_1013200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300349 ⟨1013200, by decide⟩ :=
  accepted_of_selected 12 300349 ⟨1013200, by decide⟩ ⟨12, 2, 0, 1013200, 300349, 2161, 65536⟩
    (by decide) selected_cut_37786

theorem selected_cut_37787 : selected 9 ⟨1013237, by decide⟩
    (prefixPartial 12 300350) = some ⟨12, 2, 0, 1013237, 300350, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_300350_1013237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300350 ⟨1013237, by decide⟩ :=
  accepted_of_selected 12 300350 ⟨1013237, by decide⟩ ⟨12, 2, 0, 1013237, 300350, 2317, 65536⟩
    (by decide) selected_cut_37787

theorem selected_cut_37788 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 300351) = some ⟨12, 1, 0, 762108, 300351, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300351_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300351 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 300351 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 300351, 1, 65536⟩
    (by decide) selected_cut_37788

theorem unmarked_context_11_75087_1013238 : frontier 10 ⟨1013238, by decide⟩
    (prefixCache 11 75087) (prefixPartial 11 75087) = false := by
  decide +kernel

theorem node_context_11_75087_1013238 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013238, by decide⟩ =
    .split (coordinate 11) (![⟨1013168, by decide⟩,⟨1013200, by decide⟩,⟨1013237, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75087_1013238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75087 ⟨1013238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75087
    ⟨1013238, by decide⟩ (by decide) (![⟨1013168, by decide⟩,⟨1013200, by decide⟩,⟨1013237, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_75087_1013238 node_context_11_75087_1013238
  intro a
  fin_cases a
  · exact context_12_300348_1013168
  · exact context_12_300349_1013200
  · exact context_12_300350_1013237
  · exact context_12_300351_762108

theorem unmarked_context_10_18771_1013239 : frontier 11 ⟨1013239, by decide⟩
    (prefixCache 10 18771) (prefixPartial 10 18771) = false := by
  decide +kernel

theorem node_context_10_18771_1013239 : EJMOriginalGlobalDAGData.nodes 11 ⟨1013239, by decide⟩ =
    .split (coordinate 10) (![⟨1012822, by decide⟩,⟨1012966, by decide⟩,⟨1013127, by decide⟩,⟨1013238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18771_1013239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18771 ⟨1013239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18771
    ⟨1013239, by decide⟩ (by decide) (![⟨1012822, by decide⟩,⟨1012966, by decide⟩,⟨1013127, by decide⟩,⟨1013238, by decide⟩]) unmarked_context_10_18771_1013239 node_context_10_18771_1013239
  intro a
  fin_cases a
  · exact context_11_75084_1012822
  · exact context_11_75085_1012966
  · exact context_11_75086_1013127
  · exact context_11_75087_1013238

theorem unmarked_context_9_4692_1013240 : frontier 12 ⟨1013240, by decide⟩
    (prefixCache 9 4692) (prefixPartial 9 4692) = false := by
  decide +kernel

theorem node_context_9_4692_1013240 : EJMOriginalGlobalDAGData.nodes 12 ⟨1013240, by decide⟩ =
    .split (coordinate 9) (![⟨1011362, by decide⟩,⟨1011867, by decide⟩,⟨1012647, by decide⟩,⟨1013239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4692_1013240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4692 ⟨1013240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4692
    ⟨1013240, by decide⟩ (by decide) (![⟨1011362, by decide⟩,⟨1011867, by decide⟩,⟨1012647, by decide⟩,⟨1013239, by decide⟩]) unmarked_context_9_4692_1013240 node_context_9_4692_1013240
  intro a
  fin_cases a
  · exact context_10_18768_1011362
  · exact context_10_18769_1011867
  · exact context_10_18770_1012647
  · exact context_10_18771_1013239

theorem selected_cut_37789 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 300352) = some ⟨12, 1, 0, 169790, 300352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300352_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300352 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 300352 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 300352, 1, 65536⟩
    (by decide) selected_cut_37789

theorem selected_cut_37790 : selected 9 ⟨1013274, by decide⟩
    (prefixPartial 12 300353) = some ⟨12, 2, 0, 1013274, 300353, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_300353_1013274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300353 ⟨1013274, by decide⟩ :=
  accepted_of_selected 12 300353 ⟨1013274, by decide⟩ ⟨12, 2, 0, 1013274, 300353, 1853, 65536⟩
    (by decide) selected_cut_37790

theorem selected_cut_37791 : selected 9 ⟨1013305, by decide⟩
    (prefixPartial 12 300354) = some ⟨12, 2, 0, 1013305, 300354, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_300354_1013305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300354 ⟨1013305, by decide⟩ :=
  accepted_of_selected 12 300354 ⟨1013305, by decide⟩ ⟨12, 2, 0, 1013305, 300354, 1965, 65536⟩
    (by decide) selected_cut_37791

theorem selected_cut_37792 : selected 9 ⟨1013333, by decide⟩
    (prefixPartial 12 300355) = some ⟨12, 2, 0, 1013333, 300355, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_300355_1013333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300355 ⟨1013333, by decide⟩ :=
  accepted_of_selected 12 300355 ⟨1013333, by decide⟩ ⟨12, 2, 0, 1013333, 300355, 2029, 65536⟩
    (by decide) selected_cut_37792

theorem unmarked_context_11_75088_1013334 : frontier 10 ⟨1013334, by decide⟩
    (prefixCache 11 75088) (prefixPartial 11 75088) = false := by
  decide +kernel

theorem node_context_11_75088_1013334 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013334, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨1013274, by decide⟩,⟨1013305, by decide⟩,⟨1013333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75088_1013334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75088 ⟨1013334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75088
    ⟨1013334, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨1013274, by decide⟩,⟨1013305, by decide⟩,⟨1013333, by decide⟩]) unmarked_context_11_75088_1013334 node_context_11_75088_1013334
  intro a
  fin_cases a
  · exact context_12_300352_169790
  · exact context_12_300353_1013274
  · exact context_12_300354_1013305
  · exact context_12_300355_1013333

theorem selected_cut_37793 : selected 9 ⟨1013387, by decide⟩
    (prefixPartial 12 300356) = some ⟨12, 2, 0, 1013387, 300356, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_300356_1013387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300356 ⟨1013387, by decide⟩ :=
  accepted_of_selected 12 300356 ⟨1013387, by decide⟩ ⟨12, 2, 0, 1013387, 300356, 2809, 65536⟩
    (by decide) selected_cut_37793

theorem selected_cut_37794 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 300357) = some ⟨12, 1, 0, 891951, 300357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300357_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300357 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 300357 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 300357, 1, 65536⟩
    (by decide) selected_cut_37794

theorem selected_cut_37795 : selected 9 ⟨1013417, by decide⟩
    (prefixPartial 12 300358) = some ⟨12, 2, 0, 1013417, 300358, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_300358_1013417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300358 ⟨1013417, by decide⟩ :=
  accepted_of_selected 12 300358 ⟨1013417, by decide⟩ ⟨12, 2, 0, 1013417, 300358, 1925, 65536⟩
    (by decide) selected_cut_37795

theorem selected_cut_37796 : selected 9 ⟨1013447, by decide⟩
    (prefixPartial 12 300359) = some ⟨12, 2, 0, 1013447, 300359, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_300359_1013447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300359 ⟨1013447, by decide⟩ :=
  accepted_of_selected 12 300359 ⟨1013447, by decide⟩ ⟨12, 2, 0, 1013447, 300359, 1985, 65536⟩
    (by decide) selected_cut_37796

theorem unmarked_context_11_75089_1013448 : frontier 10 ⟨1013448, by decide⟩
    (prefixCache 11 75089) (prefixPartial 11 75089) = false := by
  decide +kernel

theorem node_context_11_75089_1013448 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013448, by decide⟩ =
    .split (coordinate 11) (![⟨1013387, by decide⟩,⟨891951, by decide⟩,⟨1013417, by decide⟩,⟨1013447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75089_1013448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75089 ⟨1013448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75089
    ⟨1013448, by decide⟩ (by decide) (![⟨1013387, by decide⟩,⟨891951, by decide⟩,⟨1013417, by decide⟩,⟨1013447, by decide⟩]) unmarked_context_11_75089_1013448 node_context_11_75089_1013448
  intro a
  fin_cases a
  · exact context_12_300356_1013387
  · exact context_12_300357_891951
  · exact context_12_300358_1013417
  · exact context_12_300359_1013447

theorem selected_cut_37797 : selected 9 ⟨1013501, by decide⟩
    (prefixPartial 12 300360) = some ⟨12, 2, 0, 1013501, 300360, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_300360_1013501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300360 ⟨1013501, by decide⟩ :=
  accepted_of_selected 12 300360 ⟨1013501, by decide⟩ ⟨12, 2, 0, 1013501, 300360, 2921, 65536⟩
    (by decide) selected_cut_37797

theorem selected_cut_37798 : selected 9 ⟨1013531, by decide⟩
    (prefixPartial 12 300361) = some ⟨12, 2, 0, 1013531, 300361, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_300361_1013531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300361 ⟨1013531, by decide⟩ :=
  accepted_of_selected 12 300361 ⟨1013531, by decide⟩ ⟨12, 2, 0, 1013531, 300361, 1965, 65536⟩
    (by decide) selected_cut_37798

theorem selected_cut_37799 : selected 9 ⟨1013579, by decide⟩
    (prefixPartial 12 300362) = some ⟨12, 2, 0, 1013579, 300362, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_300362_1013579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300362 ⟨1013579, by decide⟩ :=
  accepted_of_selected 12 300362 ⟨1013579, by decide⟩ ⟨12, 2, 0, 1013579, 300362, 2433, 65536⟩
    (by decide) selected_cut_37799

theorem selected_cut_37800 : selected 9 ⟨1013613, by decide⟩
    (prefixPartial 12 300363) = some ⟨12, 2, 0, 1013613, 300363, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_300363_1013613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300363 ⟨1013613, by decide⟩ :=
  accepted_of_selected 12 300363 ⟨1013613, by decide⟩ ⟨12, 2, 0, 1013613, 300363, 2269, 65536⟩
    (by decide) selected_cut_37800

theorem unmarked_context_11_75090_1013614 : frontier 10 ⟨1013614, by decide⟩
    (prefixCache 11 75090) (prefixPartial 11 75090) = false := by
  decide +kernel

theorem node_context_11_75090_1013614 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013614, by decide⟩ =
    .split (coordinate 11) (![⟨1013501, by decide⟩,⟨1013531, by decide⟩,⟨1013579, by decide⟩,⟨1013613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75090_1013614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75090 ⟨1013614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75090
    ⟨1013614, by decide⟩ (by decide) (![⟨1013501, by decide⟩,⟨1013531, by decide⟩,⟨1013579, by decide⟩,⟨1013613, by decide⟩]) unmarked_context_11_75090_1013614 node_context_11_75090_1013614
  intro a
  fin_cases a
  · exact context_12_300360_1013501
  · exact context_12_300361_1013531
  · exact context_12_300362_1013579
  · exact context_12_300363_1013613

theorem selected_cut_37801 : selected 9 ⟨1013668, by decide⟩
    (prefixPartial 12 300364) = some ⟨12, 2, 0, 1013668, 300364, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_300364_1013668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300364 ⟨1013668, by decide⟩ :=
  accepted_of_selected 12 300364 ⟨1013668, by decide⟩ ⟨12, 2, 0, 1013668, 300364, 2793, 65536⟩
    (by decide) selected_cut_37801

theorem selected_cut_37802 : selected 9 ⟨1013706, by decide⟩
    (prefixPartial 12 300365) = some ⟨12, 2, 0, 1013706, 300365, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_300365_1013706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300365 ⟨1013706, by decide⟩ :=
  accepted_of_selected 12 300365 ⟨1013706, by decide⟩ ⟨12, 2, 0, 1013706, 300365, 1937, 65536⟩
    (by decide) selected_cut_37802

theorem selected_cut_37803 : selected 9 ⟨1013749, by decide⟩
    (prefixPartial 12 300366) = some ⟨12, 2, 0, 1013749, 300366, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_300366_1013749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300366 ⟨1013749, by decide⟩ :=
  accepted_of_selected 12 300366 ⟨1013749, by decide⟩ ⟨12, 2, 0, 1013749, 300366, 2217, 65536⟩
    (by decide) selected_cut_37803

theorem selected_cut_37804 : selected 9 ⟨1013787, by decide⟩
    (prefixPartial 12 300367) = some ⟨12, 2, 0, 1013787, 300367, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_300367_1013787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300367 ⟨1013787, by decide⟩ :=
  accepted_of_selected 12 300367 ⟨1013787, by decide⟩ ⟨12, 2, 0, 1013787, 300367, 2317, 65536⟩
    (by decide) selected_cut_37804

theorem unmarked_context_11_75091_1013788 : frontier 10 ⟨1013788, by decide⟩
    (prefixCache 11 75091) (prefixPartial 11 75091) = false := by
  decide +kernel

theorem node_context_11_75091_1013788 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013788, by decide⟩ =
    .split (coordinate 11) (![⟨1013668, by decide⟩,⟨1013706, by decide⟩,⟨1013749, by decide⟩,⟨1013787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75091_1013788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75091 ⟨1013788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75091
    ⟨1013788, by decide⟩ (by decide) (![⟨1013668, by decide⟩,⟨1013706, by decide⟩,⟨1013749, by decide⟩,⟨1013787, by decide⟩]) unmarked_context_11_75091_1013788 node_context_11_75091_1013788
  intro a
  fin_cases a
  · exact context_12_300364_1013668
  · exact context_12_300365_1013706
  · exact context_12_300366_1013749
  · exact context_12_300367_1013787

theorem unmarked_context_10_18772_1013789 : frontier 11 ⟨1013789, by decide⟩
    (prefixCache 10 18772) (prefixPartial 10 18772) = false := by
  decide +kernel

theorem node_context_10_18772_1013789 : EJMOriginalGlobalDAGData.nodes 11 ⟨1013789, by decide⟩ =
    .split (coordinate 10) (![⟨1013334, by decide⟩,⟨1013448, by decide⟩,⟨1013614, by decide⟩,⟨1013788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18772_1013789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18772 ⟨1013789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18772
    ⟨1013789, by decide⟩ (by decide) (![⟨1013334, by decide⟩,⟨1013448, by decide⟩,⟨1013614, by decide⟩,⟨1013788, by decide⟩]) unmarked_context_10_18772_1013789 node_context_10_18772_1013789
  intro a
  fin_cases a
  · exact context_11_75088_1013334
  · exact context_11_75089_1013448
  · exact context_11_75090_1013614
  · exact context_11_75091_1013788

theorem selected_cut_37805 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18773) = some ⟨10, 1, 0, 893098, 18773, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18773_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18773 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18773 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18773, 1, 1048576⟩
    (by decide) selected_cut_37805

theorem selected_cut_37806 : selected 9 ⟨1013826, by decide⟩
    (prefixPartial 12 300384) = some ⟨12, 2, 0, 1013826, 300384, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_300384_1013826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300384 ⟨1013826, by decide⟩ :=
  accepted_of_selected 12 300384 ⟨1013826, by decide⟩ ⟨12, 2, 0, 1013826, 300384, 2165, 65536⟩
    (by decide) selected_cut_37806

theorem selected_cut_37807 : selected 9 ⟨1013858, by decide⟩
    (prefixPartial 12 300385) = some ⟨12, 2, 0, 1013858, 300385, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_300385_1013858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300385 ⟨1013858, by decide⟩ :=
  accepted_of_selected 12 300385 ⟨1013858, by decide⟩ ⟨12, 2, 0, 1013858, 300385, 1853, 65536⟩
    (by decide) selected_cut_37807

theorem selected_cut_37808 : selected 9 ⟨1013884, by decide⟩
    (prefixPartial 12 300386) = some ⟨12, 2, 0, 1013884, 300386, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_300386_1013884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300386 ⟨1013884, by decide⟩ :=
  accepted_of_selected 12 300386 ⟨1013884, by decide⟩ ⟨12, 2, 0, 1013884, 300386, 1837, 65536⟩
    (by decide) selected_cut_37808

theorem selected_cut_37809 : selected 9 ⟨1013913, by decide⟩
    (prefixPartial 12 300387) = some ⟨12, 2, 0, 1013913, 300387, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_300387_1013913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300387 ⟨1013913, by decide⟩ :=
  accepted_of_selected 12 300387 ⟨1013913, by decide⟩ ⟨12, 2, 0, 1013913, 300387, 1877, 65536⟩
    (by decide) selected_cut_37809

theorem unmarked_context_11_75096_1013914 : frontier 10 ⟨1013914, by decide⟩
    (prefixCache 11 75096) (prefixPartial 11 75096) = false := by
  decide +kernel

theorem node_context_11_75096_1013914 : EJMOriginalGlobalDAGData.nodes 10 ⟨1013914, by decide⟩ =
    .split (coordinate 11) (![⟨1013826, by decide⟩,⟨1013858, by decide⟩,⟨1013884, by decide⟩,⟨1013913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75096_1013914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75096 ⟨1013914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75096
    ⟨1013914, by decide⟩ (by decide) (![⟨1013826, by decide⟩,⟨1013858, by decide⟩,⟨1013884, by decide⟩,⟨1013913, by decide⟩]) unmarked_context_11_75096_1013914 node_context_11_75096_1013914
  intro a
  fin_cases a
  · exact context_12_300384_1013826
  · exact context_12_300385_1013858
  · exact context_12_300386_1013884
  · exact context_12_300387_1013913

theorem selected_cut_37810 : selected 9 ⟨1013951, by decide⟩
    (prefixPartial 12 300388) = some ⟨12, 2, 0, 1013951, 300388, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_300388_1013951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300388 ⟨1013951, by decide⟩ :=
  accepted_of_selected 12 300388 ⟨1013951, by decide⟩ ⟨12, 2, 0, 1013951, 300388, 2073, 65536⟩
    (by decide) selected_cut_37810

theorem selected_cut_37811 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 300389) = some ⟨12, 1, 0, 891951, 300389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300389_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300389 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 300389 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 300389, 1, 65536⟩
    (by decide) selected_cut_37811

theorem selected_cut_37812 : selected 9 ⟨1013980, by decide⟩
    (prefixPartial 12 300390) = some ⟨12, 2, 0, 1013980, 300390, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_300390_1013980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300390 ⟨1013980, by decide⟩ :=
  accepted_of_selected 12 300390 ⟨1013980, by decide⟩ ⟨12, 2, 0, 1013980, 300390, 1633, 65536⟩
    (by decide) selected_cut_37812

theorem selected_cut_37813 : selected 9 ⟨1014008, by decide⟩
    (prefixPartial 12 300391) = some ⟨12, 2, 0, 1014008, 300391, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_300391_1014008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300391 ⟨1014008, by decide⟩ :=
  accepted_of_selected 12 300391 ⟨1014008, by decide⟩ ⟨12, 2, 0, 1014008, 300391, 1737, 65536⟩
    (by decide) selected_cut_37813

theorem unmarked_context_11_75097_1014009 : frontier 10 ⟨1014009, by decide⟩
    (prefixCache 11 75097) (prefixPartial 11 75097) = false := by
  decide +kernel

theorem node_context_11_75097_1014009 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014009, by decide⟩ =
    .split (coordinate 11) (![⟨1013951, by decide⟩,⟨891951, by decide⟩,⟨1013980, by decide⟩,⟨1014008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75097_1014009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75097 ⟨1014009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75097
    ⟨1014009, by decide⟩ (by decide) (![⟨1013951, by decide⟩,⟨891951, by decide⟩,⟨1013980, by decide⟩,⟨1014008, by decide⟩]) unmarked_context_11_75097_1014009 node_context_11_75097_1014009
  intro a
  fin_cases a
  · exact context_12_300388_1013951
  · exact context_12_300389_891951
  · exact context_12_300390_1013980
  · exact context_12_300391_1014008

theorem selected_cut_37814 : selected 9 ⟨1014046, by decide⟩
    (prefixPartial 12 300392) = some ⟨12, 2, 0, 1014046, 300392, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_300392_1014046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300392 ⟨1014046, by decide⟩ :=
  accepted_of_selected 12 300392 ⟨1014046, by decide⟩ ⟨12, 2, 0, 1014046, 300392, 2109, 65536⟩
    (by decide) selected_cut_37814

theorem selected_cut_37815 : selected 9 ⟨1014079, by decide⟩
    (prefixPartial 12 300393) = some ⟨12, 2, 0, 1014079, 300393, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_300393_1014079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300393 ⟨1014079, by decide⟩ :=
  accepted_of_selected 12 300393 ⟨1014079, by decide⟩ ⟨12, 2, 0, 1014079, 300393, 1833, 65536⟩
    (by decide) selected_cut_37815

theorem selected_cut_37816 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 300394) = some ⟨12, 1, 0, 661671, 300394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300394_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300394 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 300394 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 300394, 1, 65536⟩
    (by decide) selected_cut_37816

theorem selected_cut_37817 : selected 9 ⟨1014114, by decide⟩
    (prefixPartial 12 300395) = some ⟨12, 2, 0, 1014114, 300395, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_300395_1014114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300395 ⟨1014114, by decide⟩ :=
  accepted_of_selected 12 300395 ⟨1014114, by decide⟩ ⟨12, 2, 0, 1014114, 300395, 2001, 65536⟩
    (by decide) selected_cut_37817

theorem unmarked_context_11_75098_1014115 : frontier 10 ⟨1014115, by decide⟩
    (prefixCache 11 75098) (prefixPartial 11 75098) = false := by
  decide +kernel

theorem node_context_11_75098_1014115 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014115, by decide⟩ =
    .split (coordinate 11) (![⟨1014046, by decide⟩,⟨1014079, by decide⟩,⟨661671, by decide⟩,⟨1014114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75098_1014115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75098 ⟨1014115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75098
    ⟨1014115, by decide⟩ (by decide) (![⟨1014046, by decide⟩,⟨1014079, by decide⟩,⟨661671, by decide⟩,⟨1014114, by decide⟩]) unmarked_context_11_75098_1014115 node_context_11_75098_1014115
  intro a
  fin_cases a
  · exact context_12_300392_1014046
  · exact context_12_300393_1014079
  · exact context_12_300394_661671
  · exact context_12_300395_1014114

theorem selected_cut_37818 : selected 9 ⟨1014149, by decide⟩
    (prefixPartial 12 300396) = some ⟨12, 2, 0, 1014149, 300396, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_300396_1014149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300396 ⟨1014149, by decide⟩ :=
  accepted_of_selected 12 300396 ⟨1014149, by decide⟩ ⟨12, 2, 0, 1014149, 300396, 1993, 65536⟩
    (by decide) selected_cut_37818

theorem selected_cut_37819 : selected 9 ⟨1014178, by decide⟩
    (prefixPartial 12 300397) = some ⟨12, 2, 0, 1014178, 300397, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_300397_1014178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300397 ⟨1014178, by decide⟩ :=
  accepted_of_selected 12 300397 ⟨1014178, by decide⟩ ⟨12, 2, 0, 1014178, 300397, 1697, 65536⟩
    (by decide) selected_cut_37819

theorem selected_cut_37820 : selected 9 ⟨1014207, by decide⟩
    (prefixPartial 12 300398) = some ⟨12, 2, 0, 1014207, 300398, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_300398_1014207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300398 ⟨1014207, by decide⟩ :=
  accepted_of_selected 12 300398 ⟨1014207, by decide⟩ ⟨12, 2, 0, 1014207, 300398, 1829, 65536⟩
    (by decide) selected_cut_37820

theorem selected_cut_37821 : selected 9 ⟨1014242, by decide⟩
    (prefixPartial 12 300399) = some ⟨12, 2, 0, 1014242, 300399, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_300399_1014242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300399 ⟨1014242, by decide⟩ :=
  accepted_of_selected 12 300399 ⟨1014242, by decide⟩ ⟨12, 2, 0, 1014242, 300399, 1945, 65536⟩
    (by decide) selected_cut_37821

theorem unmarked_context_11_75099_1014243 : frontier 10 ⟨1014243, by decide⟩
    (prefixCache 11 75099) (prefixPartial 11 75099) = false := by
  decide +kernel

theorem node_context_11_75099_1014243 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014243, by decide⟩ =
    .split (coordinate 11) (![⟨1014149, by decide⟩,⟨1014178, by decide⟩,⟨1014207, by decide⟩,⟨1014242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75099_1014243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75099 ⟨1014243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75099
    ⟨1014243, by decide⟩ (by decide) (![⟨1014149, by decide⟩,⟨1014178, by decide⟩,⟨1014207, by decide⟩,⟨1014242, by decide⟩]) unmarked_context_11_75099_1014243 node_context_11_75099_1014243
  intro a
  fin_cases a
  · exact context_12_300396_1014149
  · exact context_12_300397_1014178
  · exact context_12_300398_1014207
  · exact context_12_300399_1014242

theorem unmarked_context_10_18774_1014244 : frontier 11 ⟨1014244, by decide⟩
    (prefixCache 10 18774) (prefixPartial 10 18774) = false := by
  decide +kernel

theorem node_context_10_18774_1014244 : EJMOriginalGlobalDAGData.nodes 11 ⟨1014244, by decide⟩ =
    .split (coordinate 10) (![⟨1013914, by decide⟩,⟨1014009, by decide⟩,⟨1014115, by decide⟩,⟨1014243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18774_1014244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18774 ⟨1014244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18774
    ⟨1014244, by decide⟩ (by decide) (![⟨1013914, by decide⟩,⟨1014009, by decide⟩,⟨1014115, by decide⟩,⟨1014243, by decide⟩]) unmarked_context_10_18774_1014244 node_context_10_18774_1014244
  intro a
  fin_cases a
  · exact context_11_75096_1013914
  · exact context_11_75097_1014009
  · exact context_11_75098_1014115
  · exact context_11_75099_1014243

theorem selected_cut_37822 : selected 9 ⟨1014270, by decide⟩
    (prefixPartial 12 300400) = some ⟨12, 2, 0, 1014270, 300400, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_300400_1014270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300400 ⟨1014270, by decide⟩ :=
  accepted_of_selected 12 300400 ⟨1014270, by decide⟩ ⟨12, 2, 0, 1014270, 300400, 1785, 65536⟩
    (by decide) selected_cut_37822

theorem selected_cut_37823 : selected 9 ⟨1014291, by decide⟩
    (prefixPartial 12 300401) = some ⟨12, 2, 0, 1014291, 300401, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_300401_1014291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300401 ⟨1014291, by decide⟩ :=
  accepted_of_selected 12 300401 ⟨1014291, by decide⟩ ⟨12, 2, 0, 1014291, 300401, 1497, 65536⟩
    (by decide) selected_cut_37823

theorem selected_cut_37824 : selected 9 ⟨1014315, by decide⟩
    (prefixPartial 12 300402) = some ⟨12, 2, 0, 1014315, 300402, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_300402_1014315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300402 ⟨1014315, by decide⟩ :=
  accepted_of_selected 12 300402 ⟨1014315, by decide⟩ ⟨12, 2, 0, 1014315, 300402, 1513, 65536⟩
    (by decide) selected_cut_37824

theorem selected_cut_37825 : selected 9 ⟨1014334, by decide⟩
    (prefixPartial 12 300403) = some ⟨12, 2, 0, 1014334, 300403, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_300403_1014334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300403 ⟨1014334, by decide⟩ :=
  accepted_of_selected 12 300403 ⟨1014334, by decide⟩ ⟨12, 2, 0, 1014334, 300403, 1469, 65536⟩
    (by decide) selected_cut_37825

theorem unmarked_context_11_75100_1014335 : frontier 10 ⟨1014335, by decide⟩
    (prefixCache 11 75100) (prefixPartial 11 75100) = false := by
  decide +kernel

theorem node_context_11_75100_1014335 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014335, by decide⟩ =
    .split (coordinate 11) (![⟨1014270, by decide⟩,⟨1014291, by decide⟩,⟨1014315, by decide⟩,⟨1014334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75100_1014335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75100 ⟨1014335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75100
    ⟨1014335, by decide⟩ (by decide) (![⟨1014270, by decide⟩,⟨1014291, by decide⟩,⟨1014315, by decide⟩,⟨1014334, by decide⟩]) unmarked_context_11_75100_1014335 node_context_11_75100_1014335
  intro a
  fin_cases a
  · exact context_12_300400_1014270
  · exact context_12_300401_1014291
  · exact context_12_300402_1014315
  · exact context_12_300403_1014334

theorem selected_cut_37826 : selected 9 ⟨1014369, by decide⟩
    (prefixPartial 12 300404) = some ⟨12, 2, 0, 1014369, 300404, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_300404_1014369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300404 ⟨1014369, by decide⟩ :=
  accepted_of_selected 12 300404 ⟨1014369, by decide⟩ ⟨12, 2, 0, 1014369, 300404, 1777, 65536⟩
    (by decide) selected_cut_37826

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
