/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover391
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37635 : selected 9 ⟨1007958, by decide⟩
    (prefixPartial 12 300093) = some ⟨12, 2, 0, 1007958, 300093, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_300093_1007958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300093 ⟨1007958, by decide⟩ :=
  accepted_of_selected 12 300093 ⟨1007958, by decide⟩ ⟨12, 2, 0, 1007958, 300093, 2793, 65536⟩
    (by decide) selected_cut_37635

theorem selected_cut_37636 : selected 9 ⟨1008009, by decide⟩
    (prefixPartial 12 300094) = some ⟨12, 2, 0, 1008009, 300094, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_300094_1008009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300094 ⟨1008009, by decide⟩ :=
  accepted_of_selected 12 300094 ⟨1008009, by decide⟩ ⟨12, 2, 0, 1008009, 300094, 3009, 65536⟩
    (by decide) selected_cut_37636

theorem selected_cut_37637 : selected 9 ⟨1008057, by decide⟩
    (prefixPartial 12 300095) = some ⟨12, 2, 0, 1008057, 300095, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_300095_1008057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300095 ⟨1008057, by decide⟩ :=
  accepted_of_selected 12 300095 ⟨1008057, by decide⟩ ⟨12, 2, 0, 1008057, 300095, 2885, 65536⟩
    (by decide) selected_cut_37637

theorem unmarked_context_11_75023_1008058 : frontier 10 ⟨1008058, by decide⟩
    (prefixCache 11 75023) (prefixPartial 11 75023) = false := by
  decide +kernel

theorem node_context_11_75023_1008058 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008058, by decide⟩ =
    .split (coordinate 11) (![⟨1007910, by decide⟩,⟨1007958, by decide⟩,⟨1008009, by decide⟩,⟨1008057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75023_1008058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75023 ⟨1008058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75023
    ⟨1008058, by decide⟩ (by decide) (![⟨1007910, by decide⟩,⟨1007958, by decide⟩,⟨1008009, by decide⟩,⟨1008057, by decide⟩]) unmarked_context_11_75023_1008058 node_context_11_75023_1008058
  intro a
  fin_cases a
  · exact context_12_300092_1007910
  · exact context_12_300093_1007958
  · exact context_12_300094_1008009
  · exact context_12_300095_1008057

theorem unmarked_context_10_18755_1008059 : frontier 11 ⟨1008059, by decide⟩
    (prefixCache 10 18755) (prefixPartial 10 18755) = false := by
  decide +kernel

theorem node_context_10_18755_1008059 : EJMOriginalGlobalDAGData.nodes 11 ⟨1008059, by decide⟩ =
    .split (coordinate 10) (![⟨1007431, by decide⟩,⟨1007636, by decide⟩,⟨1007867, by decide⟩,⟨1008058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18755_1008059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18755 ⟨1008059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18755
    ⟨1008059, by decide⟩ (by decide) (![⟨1007431, by decide⟩,⟨1007636, by decide⟩,⟨1007867, by decide⟩,⟨1008058, by decide⟩]) unmarked_context_10_18755_1008059 node_context_10_18755_1008059
  intro a
  fin_cases a
  · exact context_11_75020_1007431
  · exact context_11_75021_1007636
  · exact context_11_75022_1007867
  · exact context_11_75023_1008058

theorem unmarked_context_9_4688_1008060 : frontier 12 ⟨1008060, by decide⟩
    (prefixCache 9 4688) (prefixPartial 9 4688) = false := by
  decide +kernel

theorem node_context_9_4688_1008060 : EJMOriginalGlobalDAGData.nodes 12 ⟨1008060, by decide⟩ =
    .split (coordinate 9) (![⟨1005851, by decide⟩,⟨1006487, by decide⟩,⟨1007303, by decide⟩,⟨1008059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4688_1008060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4688 ⟨1008060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4688
    ⟨1008060, by decide⟩ (by decide) (![⟨1005851, by decide⟩,⟨1006487, by decide⟩,⟨1007303, by decide⟩,⟨1008059, by decide⟩]) unmarked_context_9_4688_1008060 node_context_9_4688_1008060
  intro a
  fin_cases a
  · exact context_10_18752_1005851
  · exact context_10_18753_1006487
  · exact context_10_18754_1007303
  · exact context_10_18755_1008059

theorem selected_cut_37638 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 300096) = some ⟨12, 1, 0, 169790, 300096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300096_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300096 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 300096 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 300096, 1, 65536⟩
    (by decide) selected_cut_37638

theorem selected_cut_37639 : selected 9 ⟨1008092, by decide⟩
    (prefixPartial 12 300097) = some ⟨12, 2, 0, 1008092, 300097, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_300097_1008092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300097 ⟨1008092, by decide⟩ :=
  accepted_of_selected 12 300097 ⟨1008092, by decide⟩ ⟨12, 2, 0, 1008092, 300097, 1989, 65536⟩
    (by decide) selected_cut_37639

theorem selected_cut_37640 : selected 9 ⟨1008136, by decide⟩
    (prefixPartial 12 300098) = some ⟨12, 2, 0, 1008136, 300098, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_300098_1008136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300098 ⟨1008136, by decide⟩ :=
  accepted_of_selected 12 300098 ⟨1008136, by decide⟩ ⟨12, 2, 0, 1008136, 300098, 2037, 65536⟩
    (by decide) selected_cut_37640

theorem selected_cut_37641 : selected 9 ⟨1008173, by decide⟩
    (prefixPartial 12 300099) = some ⟨12, 2, 0, 1008173, 300099, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_300099_1008173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300099 ⟨1008173, by decide⟩ :=
  accepted_of_selected 12 300099 ⟨1008173, by decide⟩ ⟨12, 2, 0, 1008173, 300099, 2141, 65536⟩
    (by decide) selected_cut_37641

theorem unmarked_context_11_75024_1008174 : frontier 10 ⟨1008174, by decide⟩
    (prefixCache 11 75024) (prefixPartial 11 75024) = false := by
  decide +kernel

theorem node_context_11_75024_1008174 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008174, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨1008092, by decide⟩,⟨1008136, by decide⟩,⟨1008173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75024_1008174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75024 ⟨1008174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75024
    ⟨1008174, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨1008092, by decide⟩,⟨1008136, by decide⟩,⟨1008173, by decide⟩]) unmarked_context_11_75024_1008174 node_context_11_75024_1008174
  intro a
  fin_cases a
  · exact context_12_300096_169790
  · exact context_12_300097_1008092
  · exact context_12_300098_1008136
  · exact context_12_300099_1008173

theorem selected_cut_37642 : selected 9 ⟨1008219, by decide⟩
    (prefixPartial 12 300100) = some ⟨12, 2, 0, 1008219, 300100, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_300100_1008219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300100 ⟨1008219, by decide⟩ :=
  accepted_of_selected 12 300100 ⟨1008219, by decide⟩ ⟨12, 2, 0, 1008219, 300100, 2545, 65536⟩
    (by decide) selected_cut_37642

theorem selected_cut_37643 : selected 9 ⟨1008220, by decide⟩
    (prefixPartial 12 300101) = some ⟨12, 1, 0, 1008220, 300101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300101_1008220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300101 ⟨1008220, by decide⟩ :=
  accepted_of_selected 12 300101 ⟨1008220, by decide⟩ ⟨12, 1, 0, 1008220, 300101, 1, 65536⟩
    (by decide) selected_cut_37643

theorem selected_cut_37644 : selected 9 ⟨1008257, by decide⟩
    (prefixPartial 12 300102) = some ⟨12, 2, 0, 1008257, 300102, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_300102_1008257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300102 ⟨1008257, by decide⟩ :=
  accepted_of_selected 12 300102 ⟨1008257, by decide⟩ ⟨12, 2, 0, 1008257, 300102, 2121, 65536⟩
    (by decide) selected_cut_37644

theorem selected_cut_37645 : selected 9 ⟨1008292, by decide⟩
    (prefixPartial 12 300103) = some ⟨12, 2, 0, 1008292, 300103, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_300103_1008292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300103 ⟨1008292, by decide⟩ :=
  accepted_of_selected 12 300103 ⟨1008292, by decide⟩ ⟨12, 2, 0, 1008292, 300103, 2177, 65536⟩
    (by decide) selected_cut_37645

theorem unmarked_context_11_75025_1008293 : frontier 10 ⟨1008293, by decide⟩
    (prefixCache 11 75025) (prefixPartial 11 75025) = false := by
  decide +kernel

theorem node_context_11_75025_1008293 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008293, by decide⟩ =
    .split (coordinate 11) (![⟨1008219, by decide⟩,⟨1008220, by decide⟩,⟨1008257, by decide⟩,⟨1008292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75025_1008293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75025 ⟨1008293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75025
    ⟨1008293, by decide⟩ (by decide) (![⟨1008219, by decide⟩,⟨1008220, by decide⟩,⟨1008257, by decide⟩,⟨1008292, by decide⟩]) unmarked_context_11_75025_1008293 node_context_11_75025_1008293
  intro a
  fin_cases a
  · exact context_12_300100_1008219
  · exact context_12_300101_1008220
  · exact context_12_300102_1008257
  · exact context_12_300103_1008292

theorem selected_cut_37646 : selected 9 ⟨1008346, by decide⟩
    (prefixPartial 12 300104) = some ⟨12, 2, 0, 1008346, 300104, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_300104_1008346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300104 ⟨1008346, by decide⟩ :=
  accepted_of_selected 12 300104 ⟨1008346, by decide⟩ ⟨12, 2, 0, 1008346, 300104, 2725, 65536⟩
    (by decide) selected_cut_37646

theorem selected_cut_37647 : selected 9 ⟨1008387, by decide⟩
    (prefixPartial 12 300105) = some ⟨12, 2, 0, 1008387, 300105, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_300105_1008387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300105 ⟨1008387, by decide⟩ :=
  accepted_of_selected 12 300105 ⟨1008387, by decide⟩ ⟨12, 2, 0, 1008387, 300105, 2145, 65536⟩
    (by decide) selected_cut_37647

theorem selected_cut_37648 : selected 9 ⟨1008425, by decide⟩
    (prefixPartial 12 300106) = some ⟨12, 2, 0, 1008425, 300106, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_300106_1008425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300106 ⟨1008425, by decide⟩ :=
  accepted_of_selected 12 300106 ⟨1008425, by decide⟩ ⟨12, 2, 0, 1008425, 300106, 2393, 65536⟩
    (by decide) selected_cut_37648

theorem selected_cut_37649 : selected 9 ⟨1008480, by decide⟩
    (prefixPartial 12 300107) = some ⟨12, 2, 0, 1008480, 300107, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_300107_1008480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300107 ⟨1008480, by decide⟩ :=
  accepted_of_selected 12 300107 ⟨1008480, by decide⟩ ⟨12, 2, 0, 1008480, 300107, 2641, 65536⟩
    (by decide) selected_cut_37649

theorem unmarked_context_11_75026_1008481 : frontier 10 ⟨1008481, by decide⟩
    (prefixCache 11 75026) (prefixPartial 11 75026) = false := by
  decide +kernel

theorem node_context_11_75026_1008481 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008481, by decide⟩ =
    .split (coordinate 11) (![⟨1008346, by decide⟩,⟨1008387, by decide⟩,⟨1008425, by decide⟩,⟨1008480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75026_1008481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75026 ⟨1008481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75026
    ⟨1008481, by decide⟩ (by decide) (![⟨1008346, by decide⟩,⟨1008387, by decide⟩,⟨1008425, by decide⟩,⟨1008480, by decide⟩]) unmarked_context_11_75026_1008481 node_context_11_75026_1008481
  intro a
  fin_cases a
  · exact context_12_300104_1008346
  · exact context_12_300105_1008387
  · exact context_12_300106_1008425
  · exact context_12_300107_1008480

theorem selected_cut_37650 : selected 9 ⟨1008535, by decide⟩
    (prefixPartial 12 300108) = some ⟨12, 2, 0, 1008535, 300108, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_300108_1008535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300108 ⟨1008535, by decide⟩ :=
  accepted_of_selected 12 300108 ⟨1008535, by decide⟩ ⟨12, 2, 0, 1008535, 300108, 2725, 65536⟩
    (by decide) selected_cut_37650

theorem selected_cut_37651 : selected 9 ⟨1008570, by decide⟩
    (prefixPartial 12 300109) = some ⟨12, 2, 0, 1008570, 300109, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_300109_1008570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300109 ⟨1008570, by decide⟩ :=
  accepted_of_selected 12 300109 ⟨1008570, by decide⟩ ⟨12, 2, 0, 1008570, 300109, 2085, 65536⟩
    (by decide) selected_cut_37651

theorem selected_cut_37652 : selected 9 ⟨1008630, by decide⟩
    (prefixPartial 12 300110) = some ⟨12, 2, 0, 1008630, 300110, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_300110_1008630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300110 ⟨1008630, by decide⟩ :=
  accepted_of_selected 12 300110 ⟨1008630, by decide⟩ ⟨12, 2, 0, 1008630, 300110, 2649, 65536⟩
    (by decide) selected_cut_37652

theorem selected_cut_37653 : selected 9 ⟨1008671, by decide⟩
    (prefixPartial 12 300111) = some ⟨12, 2, 0, 1008671, 300111, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_300111_1008671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300111 ⟨1008671, by decide⟩ :=
  accepted_of_selected 12 300111 ⟨1008671, by decide⟩ ⟨12, 2, 0, 1008671, 300111, 2273, 65536⟩
    (by decide) selected_cut_37653

theorem unmarked_context_11_75027_1008672 : frontier 10 ⟨1008672, by decide⟩
    (prefixCache 11 75027) (prefixPartial 11 75027) = false := by
  decide +kernel

theorem node_context_11_75027_1008672 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008672, by decide⟩ =
    .split (coordinate 11) (![⟨1008535, by decide⟩,⟨1008570, by decide⟩,⟨1008630, by decide⟩,⟨1008671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75027_1008672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75027 ⟨1008672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75027
    ⟨1008672, by decide⟩ (by decide) (![⟨1008535, by decide⟩,⟨1008570, by decide⟩,⟨1008630, by decide⟩,⟨1008671, by decide⟩]) unmarked_context_11_75027_1008672 node_context_11_75027_1008672
  intro a
  fin_cases a
  · exact context_12_300108_1008535
  · exact context_12_300109_1008570
  · exact context_12_300110_1008630
  · exact context_12_300111_1008671

theorem unmarked_context_10_18756_1008673 : frontier 11 ⟨1008673, by decide⟩
    (prefixCache 10 18756) (prefixPartial 10 18756) = false := by
  decide +kernel

theorem node_context_10_18756_1008673 : EJMOriginalGlobalDAGData.nodes 11 ⟨1008673, by decide⟩ =
    .split (coordinate 10) (![⟨1008174, by decide⟩,⟨1008293, by decide⟩,⟨1008481, by decide⟩,⟨1008672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18756_1008673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18756 ⟨1008673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18756
    ⟨1008673, by decide⟩ (by decide) (![⟨1008174, by decide⟩,⟨1008293, by decide⟩,⟨1008481, by decide⟩,⟨1008672, by decide⟩]) unmarked_context_10_18756_1008673 node_context_10_18756_1008673
  intro a
  fin_cases a
  · exact context_11_75024_1008174
  · exact context_11_75025_1008293
  · exact context_11_75026_1008481
  · exact context_11_75027_1008672

theorem selected_cut_37654 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18757) = some ⟨10, 1, 0, 893098, 18757, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18757_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18757 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18757 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18757, 1, 1048576⟩
    (by decide) selected_cut_37654

theorem selected_cut_37655 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 300128) = some ⟨12, 1, 0, 985390, 300128, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300128_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300128 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 300128 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 300128, 1, 65536⟩
    (by decide) selected_cut_37655

theorem selected_cut_37656 : selected 9 ⟨1008704, by decide⟩
    (prefixPartial 12 300129) = some ⟨12, 2, 0, 1008704, 300129, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_300129_1008704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300129 ⟨1008704, by decide⟩ :=
  accepted_of_selected 12 300129 ⟨1008704, by decide⟩ ⟨12, 2, 0, 1008704, 300129, 1813, 65536⟩
    (by decide) selected_cut_37656

theorem selected_cut_37657 : selected 9 ⟨1008736, by decide⟩
    (prefixPartial 12 300130) = some ⟨12, 2, 0, 1008736, 300130, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_300130_1008736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300130 ⟨1008736, by decide⟩ :=
  accepted_of_selected 12 300130 ⟨1008736, by decide⟩ ⟨12, 2, 0, 1008736, 300130, 1873, 65536⟩
    (by decide) selected_cut_37657

theorem selected_cut_37658 : selected 9 ⟨1008764, by decide⟩
    (prefixPartial 12 300131) = some ⟨12, 2, 0, 1008764, 300131, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_300131_1008764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300131 ⟨1008764, by decide⟩ :=
  accepted_of_selected 12 300131 ⟨1008764, by decide⟩ ⟨12, 2, 0, 1008764, 300131, 1825, 65536⟩
    (by decide) selected_cut_37658

theorem unmarked_context_11_75032_1008765 : frontier 10 ⟨1008765, by decide⟩
    (prefixCache 11 75032) (prefixPartial 11 75032) = false := by
  decide +kernel

theorem node_context_11_75032_1008765 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008765, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1008704, by decide⟩,⟨1008736, by decide⟩,⟨1008764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75032_1008765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75032 ⟨1008765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75032
    ⟨1008765, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1008704, by decide⟩,⟨1008736, by decide⟩,⟨1008764, by decide⟩]) unmarked_context_11_75032_1008765 node_context_11_75032_1008765
  intro a
  fin_cases a
  · exact context_12_300128_985390
  · exact context_12_300129_1008704
  · exact context_12_300130_1008736
  · exact context_12_300131_1008764

theorem selected_cut_37659 : selected 9 ⟨1008795, by decide⟩
    (prefixPartial 12 300132) = some ⟨12, 2, 0, 1008795, 300132, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_300132_1008795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300132 ⟨1008795, by decide⟩ :=
  accepted_of_selected 12 300132 ⟨1008795, by decide⟩ ⟨12, 2, 0, 1008795, 300132, 1853, 65536⟩
    (by decide) selected_cut_37659

theorem selected_cut_37660 : selected 9 ⟨417109, by decide⟩
    (prefixPartial 12 300133) = some ⟨12, 1, 0, 417109, 300133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300133_417109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300133 ⟨417109, by decide⟩ :=
  accepted_of_selected 12 300133 ⟨417109, by decide⟩ ⟨12, 1, 0, 417109, 300133, 1, 65536⟩
    (by decide) selected_cut_37660

theorem selected_cut_37661 : selected 9 ⟨1008825, by decide⟩
    (prefixPartial 12 300134) = some ⟨12, 2, 0, 1008825, 300134, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_300134_1008825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300134 ⟨1008825, by decide⟩ :=
  accepted_of_selected 12 300134 ⟨1008825, by decide⟩ ⟨12, 2, 0, 1008825, 300134, 1745, 65536⟩
    (by decide) selected_cut_37661

theorem selected_cut_37662 : selected 9 ⟨1008847, by decide⟩
    (prefixPartial 12 300135) = some ⟨12, 2, 0, 1008847, 300135, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_300135_1008847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300135 ⟨1008847, by decide⟩ :=
  accepted_of_selected 12 300135 ⟨1008847, by decide⟩ ⟨12, 2, 0, 1008847, 300135, 1713, 65536⟩
    (by decide) selected_cut_37662

theorem unmarked_context_11_75033_1008848 : frontier 10 ⟨1008848, by decide⟩
    (prefixCache 11 75033) (prefixPartial 11 75033) = false := by
  decide +kernel

theorem node_context_11_75033_1008848 : EJMOriginalGlobalDAGData.nodes 10 ⟨1008848, by decide⟩ =
    .split (coordinate 11) (![⟨1008795, by decide⟩,⟨417109, by decide⟩,⟨1008825, by decide⟩,⟨1008847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75033_1008848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75033 ⟨1008848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75033
    ⟨1008848, by decide⟩ (by decide) (![⟨1008795, by decide⟩,⟨417109, by decide⟩,⟨1008825, by decide⟩,⟨1008847, by decide⟩]) unmarked_context_11_75033_1008848 node_context_11_75033_1008848
  intro a
  fin_cases a
  · exact context_12_300132_1008795
  · exact context_12_300133_417109
  · exact context_12_300134_1008825
  · exact context_12_300135_1008847

theorem selected_cut_37663 : selected 9 ⟨1008881, by decide⟩
    (prefixPartial 12 300136) = some ⟨12, 2, 0, 1008881, 300136, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_300136_1008881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300136 ⟨1008881, by decide⟩ :=
  accepted_of_selected 12 300136 ⟨1008881, by decide⟩ ⟨12, 2, 0, 1008881, 300136, 1973, 65536⟩
    (by decide) selected_cut_37663

theorem selected_cut_37664 : selected 9 ⟨1008913, by decide⟩
    (prefixPartial 12 300137) = some ⟨12, 2, 0, 1008913, 300137, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_300137_1008913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300137 ⟨1008913, by decide⟩ :=
  accepted_of_selected 12 300137 ⟨1008913, by decide⟩ ⟨12, 2, 0, 1008913, 300137, 1821, 65536⟩
    (by decide) selected_cut_37664

theorem selected_cut_37665 : selected 9 ⟨1008972, by decide⟩
    (prefixPartial 12 300138) = some ⟨12, 2, 0, 1008972, 300138, 905, 65536⟩ := by
  decide +kernel

theorem context_12_300138_1008972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300138 ⟨1008972, by decide⟩ :=
  accepted_of_selected 12 300138 ⟨1008972, by decide⟩ ⟨12, 2, 0, 1008972, 300138, 905, 65536⟩
    (by decide) selected_cut_37665

theorem selected_cut_37666 : selected 9 ⟨1009016, by decide⟩
    (prefixPartial 12 300139) = some ⟨12, 2, 0, 1009016, 300139, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_300139_1009016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300139 ⟨1009016, by decide⟩ :=
  accepted_of_selected 12 300139 ⟨1009016, by decide⟩ ⟨12, 2, 0, 1009016, 300139, 2117, 65536⟩
    (by decide) selected_cut_37666

theorem unmarked_context_11_75034_1009017 : frontier 10 ⟨1009017, by decide⟩
    (prefixCache 11 75034) (prefixPartial 11 75034) = false := by
  decide +kernel

theorem node_context_11_75034_1009017 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009017, by decide⟩ =
    .split (coordinate 11) (![⟨1008881, by decide⟩,⟨1008913, by decide⟩,⟨1008972, by decide⟩,⟨1009016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75034_1009017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75034 ⟨1009017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75034
    ⟨1009017, by decide⟩ (by decide) (![⟨1008881, by decide⟩,⟨1008913, by decide⟩,⟨1008972, by decide⟩,⟨1009016, by decide⟩]) unmarked_context_11_75034_1009017 node_context_11_75034_1009017
  intro a
  fin_cases a
  · exact context_12_300136_1008881
  · exact context_12_300137_1008913
  · exact context_12_300138_1008972
  · exact context_12_300139_1009016

theorem selected_cut_37667 : selected 9 ⟨1009048, by decide⟩
    (prefixPartial 12 300140) = some ⟨12, 2, 0, 1009048, 300140, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_300140_1009048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300140 ⟨1009048, by decide⟩ :=
  accepted_of_selected 12 300140 ⟨1009048, by decide⟩ ⟨12, 2, 0, 1009048, 300140, 1897, 65536⟩
    (by decide) selected_cut_37667

theorem selected_cut_37668 : selected 9 ⟨1009081, by decide⟩
    (prefixPartial 12 300141) = some ⟨12, 2, 0, 1009081, 300141, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_300141_1009081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300141 ⟨1009081, by decide⟩ :=
  accepted_of_selected 12 300141 ⟨1009081, by decide⟩ ⟨12, 2, 0, 1009081, 300141, 1749, 65536⟩
    (by decide) selected_cut_37668

theorem selected_cut_37669 : selected 9 ⟨1009116, by decide⟩
    (prefixPartial 12 300142) = some ⟨12, 2, 0, 1009116, 300142, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_300142_1009116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300142 ⟨1009116, by decide⟩ :=
  accepted_of_selected 12 300142 ⟨1009116, by decide⟩ ⟨12, 2, 0, 1009116, 300142, 2037, 65536⟩
    (by decide) selected_cut_37669

theorem selected_cut_37670 : selected 9 ⟨1009141, by decide⟩
    (prefixPartial 12 300143) = some ⟨12, 2, 0, 1009141, 300143, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_300143_1009141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300143 ⟨1009141, by decide⟩ :=
  accepted_of_selected 12 300143 ⟨1009141, by decide⟩ ⟨12, 2, 0, 1009141, 300143, 1717, 65536⟩
    (by decide) selected_cut_37670

theorem unmarked_context_11_75035_1009142 : frontier 10 ⟨1009142, by decide⟩
    (prefixCache 11 75035) (prefixPartial 11 75035) = false := by
  decide +kernel

theorem node_context_11_75035_1009142 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009142, by decide⟩ =
    .split (coordinate 11) (![⟨1009048, by decide⟩,⟨1009081, by decide⟩,⟨1009116, by decide⟩,⟨1009141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75035_1009142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75035 ⟨1009142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75035
    ⟨1009142, by decide⟩ (by decide) (![⟨1009048, by decide⟩,⟨1009081, by decide⟩,⟨1009116, by decide⟩,⟨1009141, by decide⟩]) unmarked_context_11_75035_1009142 node_context_11_75035_1009142
  intro a
  fin_cases a
  · exact context_12_300140_1009048
  · exact context_12_300141_1009081
  · exact context_12_300142_1009116
  · exact context_12_300143_1009141

theorem unmarked_context_10_18758_1009143 : frontier 11 ⟨1009143, by decide⟩
    (prefixCache 10 18758) (prefixPartial 10 18758) = false := by
  decide +kernel

theorem node_context_10_18758_1009143 : EJMOriginalGlobalDAGData.nodes 11 ⟨1009143, by decide⟩ =
    .split (coordinate 10) (![⟨1008765, by decide⟩,⟨1008848, by decide⟩,⟨1009017, by decide⟩,⟨1009142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18758_1009143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18758 ⟨1009143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18758
    ⟨1009143, by decide⟩ (by decide) (![⟨1008765, by decide⟩,⟨1008848, by decide⟩,⟨1009017, by decide⟩,⟨1009142, by decide⟩]) unmarked_context_10_18758_1009143 node_context_10_18758_1009143
  intro a
  fin_cases a
  · exact context_11_75032_1008765
  · exact context_11_75033_1008848
  · exact context_11_75034_1009017
  · exact context_11_75035_1009142

theorem selected_cut_37671 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 300144) = some ⟨12, 1, 0, 985390, 300144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300144_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300144 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 300144 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 300144, 1, 65536⟩
    (by decide) selected_cut_37671

theorem selected_cut_37672 : selected 9 ⟨1009165, by decide⟩
    (prefixPartial 12 300145) = some ⟨12, 2, 0, 1009165, 300145, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_300145_1009165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300145 ⟨1009165, by decide⟩ :=
  accepted_of_selected 12 300145 ⟨1009165, by decide⟩ ⟨12, 2, 0, 1009165, 300145, 1525, 65536⟩
    (by decide) selected_cut_37672

theorem selected_cut_37673 : selected 9 ⟨1009186, by decide⟩
    (prefixPartial 12 300146) = some ⟨12, 2, 0, 1009186, 300146, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_300146_1009186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300146 ⟨1009186, by decide⟩ :=
  accepted_of_selected 12 300146 ⟨1009186, by decide⟩ ⟨12, 2, 0, 1009186, 300146, 1493, 65536⟩
    (by decide) selected_cut_37673

theorem selected_cut_37674 : selected 9 ⟨1009204, by decide⟩
    (prefixPartial 12 300147) = some ⟨12, 2, 0, 1009204, 300147, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_300147_1009204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300147 ⟨1009204, by decide⟩ :=
  accepted_of_selected 12 300147 ⟨1009204, by decide⟩ ⟨12, 2, 0, 1009204, 300147, 1517, 65536⟩
    (by decide) selected_cut_37674

theorem unmarked_context_11_75036_1009205 : frontier 10 ⟨1009205, by decide⟩
    (prefixCache 11 75036) (prefixPartial 11 75036) = false := by
  decide +kernel

theorem node_context_11_75036_1009205 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009205, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1009165, by decide⟩,⟨1009186, by decide⟩,⟨1009204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75036_1009205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75036 ⟨1009205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75036
    ⟨1009205, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1009165, by decide⟩,⟨1009186, by decide⟩,⟨1009204, by decide⟩]) unmarked_context_11_75036_1009205 node_context_11_75036_1009205
  intro a
  fin_cases a
  · exact context_12_300144_985390
  · exact context_12_300145_1009165
  · exact context_12_300146_1009186
  · exact context_12_300147_1009204

theorem selected_cut_37675 : selected 9 ⟨1009232, by decide⟩
    (prefixPartial 12 300148) = some ⟨12, 2, 0, 1009232, 300148, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_300148_1009232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300148 ⟨1009232, by decide⟩ :=
  accepted_of_selected 12 300148 ⟨1009232, by decide⟩ ⟨12, 2, 0, 1009232, 300148, 1649, 65536⟩
    (by decide) selected_cut_37675

theorem selected_cut_37676 : selected 9 ⟨1009251, by decide⟩
    (prefixPartial 12 300149) = some ⟨12, 2, 0, 1009251, 300149, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_300149_1009251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300149 ⟨1009251, by decide⟩ :=
  accepted_of_selected 12 300149 ⟨1009251, by decide⟩ ⟨12, 2, 0, 1009251, 300149, 1369, 65536⟩
    (by decide) selected_cut_37676

theorem selected_cut_37677 : selected 9 ⟨1009276, by decide⟩
    (prefixPartial 12 300150) = some ⟨12, 2, 0, 1009276, 300150, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_300150_1009276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300150 ⟨1009276, by decide⟩ :=
  accepted_of_selected 12 300150 ⟨1009276, by decide⟩ ⟨12, 2, 0, 1009276, 300150, 1477, 65536⟩
    (by decide) selected_cut_37677

theorem selected_cut_37678 : selected 9 ⟨1009299, by decide⟩
    (prefixPartial 12 300151) = some ⟨12, 2, 0, 1009299, 300151, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_300151_1009299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300151 ⟨1009299, by decide⟩ :=
  accepted_of_selected 12 300151 ⟨1009299, by decide⟩ ⟨12, 2, 0, 1009299, 300151, 1505, 65536⟩
    (by decide) selected_cut_37678

theorem unmarked_context_11_75037_1009300 : frontier 10 ⟨1009300, by decide⟩
    (prefixCache 11 75037) (prefixPartial 11 75037) = false := by
  decide +kernel

theorem node_context_11_75037_1009300 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009300, by decide⟩ =
    .split (coordinate 11) (![⟨1009232, by decide⟩,⟨1009251, by decide⟩,⟨1009276, by decide⟩,⟨1009299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75037_1009300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75037 ⟨1009300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75037
    ⟨1009300, by decide⟩ (by decide) (![⟨1009232, by decide⟩,⟨1009251, by decide⟩,⟨1009276, by decide⟩,⟨1009299, by decide⟩]) unmarked_context_11_75037_1009300 node_context_11_75037_1009300
  intro a
  fin_cases a
  · exact context_12_300148_1009232
  · exact context_12_300149_1009251
  · exact context_12_300150_1009276
  · exact context_12_300151_1009299

theorem selected_cut_37679 : selected 9 ⟨1009331, by decide⟩
    (prefixPartial 12 300152) = some ⟨12, 2, 0, 1009331, 300152, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_300152_1009331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300152 ⟨1009331, by decide⟩ :=
  accepted_of_selected 12 300152 ⟨1009331, by decide⟩ ⟨12, 2, 0, 1009331, 300152, 1625, 65536⟩
    (by decide) selected_cut_37679

theorem selected_cut_37680 : selected 9 ⟨1009354, by decide⟩
    (prefixPartial 12 300153) = some ⟨12, 2, 0, 1009354, 300153, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_300153_1009354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300153 ⟨1009354, by decide⟩ :=
  accepted_of_selected 12 300153 ⟨1009354, by decide⟩ ⟨12, 2, 0, 1009354, 300153, 1469, 65536⟩
    (by decide) selected_cut_37680

theorem selected_cut_37681 : selected 9 ⟨1009379, by decide⟩
    (prefixPartial 12 300154) = some ⟨12, 2, 0, 1009379, 300154, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_300154_1009379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300154 ⟨1009379, by decide⟩ :=
  accepted_of_selected 12 300154 ⟨1009379, by decide⟩ ⟨12, 2, 0, 1009379, 300154, 1537, 65536⟩
    (by decide) selected_cut_37681

theorem selected_cut_37682 : selected 9 ⟨1009417, by decide⟩
    (prefixPartial 12 300155) = some ⟨12, 2, 0, 1009417, 300155, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_300155_1009417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300155 ⟨1009417, by decide⟩ :=
  accepted_of_selected 12 300155 ⟨1009417, by decide⟩ ⟨12, 2, 0, 1009417, 300155, 1701, 65536⟩
    (by decide) selected_cut_37682

theorem unmarked_context_11_75038_1009418 : frontier 10 ⟨1009418, by decide⟩
    (prefixCache 11 75038) (prefixPartial 11 75038) = false := by
  decide +kernel

theorem node_context_11_75038_1009418 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009418, by decide⟩ =
    .split (coordinate 11) (![⟨1009331, by decide⟩,⟨1009354, by decide⟩,⟨1009379, by decide⟩,⟨1009417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75038_1009418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75038 ⟨1009418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75038
    ⟨1009418, by decide⟩ (by decide) (![⟨1009331, by decide⟩,⟨1009354, by decide⟩,⟨1009379, by decide⟩,⟨1009417, by decide⟩]) unmarked_context_11_75038_1009418 node_context_11_75038_1009418
  intro a
  fin_cases a
  · exact context_12_300152_1009331
  · exact context_12_300153_1009354
  · exact context_12_300154_1009379
  · exact context_12_300155_1009417

theorem selected_cut_37683 : selected 9 ⟨1009444, by decide⟩
    (prefixPartial 12 300156) = some ⟨12, 2, 0, 1009444, 300156, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_300156_1009444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300156 ⟨1009444, by decide⟩ :=
  accepted_of_selected 12 300156 ⟨1009444, by decide⟩ ⟨12, 2, 0, 1009444, 300156, 1597, 65536⟩
    (by decide) selected_cut_37683

theorem selected_cut_37684 : selected 9 ⟨1009469, by decide⟩
    (prefixPartial 12 300157) = some ⟨12, 2, 0, 1009469, 300157, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_300157_1009469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300157 ⟨1009469, by decide⟩ :=
  accepted_of_selected 12 300157 ⟨1009469, by decide⟩ ⟨12, 2, 0, 1009469, 300157, 1485, 65536⟩
    (by decide) selected_cut_37684

theorem selected_cut_37685 : selected 9 ⟨1009502, by decide⟩
    (prefixPartial 12 300158) = some ⟨12, 2, 0, 1009502, 300158, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_300158_1009502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300158 ⟨1009502, by decide⟩ :=
  accepted_of_selected 12 300158 ⟨1009502, by decide⟩ ⟨12, 2, 0, 1009502, 300158, 1737, 65536⟩
    (by decide) selected_cut_37685

theorem selected_cut_37686 : selected 9 ⟨1009529, by decide⟩
    (prefixPartial 12 300159) = some ⟨12, 2, 0, 1009529, 300159, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_300159_1009529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300159 ⟨1009529, by decide⟩ :=
  accepted_of_selected 12 300159 ⟨1009529, by decide⟩ ⟨12, 2, 0, 1009529, 300159, 1445, 65536⟩
    (by decide) selected_cut_37686

theorem unmarked_context_11_75039_1009530 : frontier 10 ⟨1009530, by decide⟩
    (prefixCache 11 75039) (prefixPartial 11 75039) = false := by
  decide +kernel

theorem node_context_11_75039_1009530 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009530, by decide⟩ =
    .split (coordinate 11) (![⟨1009444, by decide⟩,⟨1009469, by decide⟩,⟨1009502, by decide⟩,⟨1009529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75039_1009530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75039 ⟨1009530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75039
    ⟨1009530, by decide⟩ (by decide) (![⟨1009444, by decide⟩,⟨1009469, by decide⟩,⟨1009502, by decide⟩,⟨1009529, by decide⟩]) unmarked_context_11_75039_1009530 node_context_11_75039_1009530
  intro a
  fin_cases a
  · exact context_12_300156_1009444
  · exact context_12_300157_1009469
  · exact context_12_300158_1009502
  · exact context_12_300159_1009529

theorem unmarked_context_10_18759_1009531 : frontier 11 ⟨1009531, by decide⟩
    (prefixCache 10 18759) (prefixPartial 10 18759) = false := by
  decide +kernel

theorem node_context_10_18759_1009531 : EJMOriginalGlobalDAGData.nodes 11 ⟨1009531, by decide⟩ =
    .split (coordinate 10) (![⟨1009205, by decide⟩,⟨1009300, by decide⟩,⟨1009418, by decide⟩,⟨1009530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18759_1009531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18759 ⟨1009531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18759
    ⟨1009531, by decide⟩ (by decide) (![⟨1009205, by decide⟩,⟨1009300, by decide⟩,⟨1009418, by decide⟩,⟨1009530, by decide⟩]) unmarked_context_10_18759_1009531 node_context_10_18759_1009531
  intro a
  fin_cases a
  · exact context_11_75036_1009205
  · exact context_11_75037_1009300
  · exact context_11_75038_1009418
  · exact context_11_75039_1009530

theorem unmarked_context_9_4689_1009532 : frontier 12 ⟨1009532, by decide⟩
    (prefixCache 9 4689) (prefixPartial 9 4689) = false := by
  decide +kernel

theorem node_context_9_4689_1009532 : EJMOriginalGlobalDAGData.nodes 12 ⟨1009532, by decide⟩ =
    .split (coordinate 9) (![⟨1008673, by decide⟩,⟨893098, by decide⟩,⟨1009143, by decide⟩,⟨1009531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4689_1009532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4689 ⟨1009532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4689
    ⟨1009532, by decide⟩ (by decide) (![⟨1008673, by decide⟩,⟨893098, by decide⟩,⟨1009143, by decide⟩,⟨1009531, by decide⟩]) unmarked_context_9_4689_1009532 node_context_9_4689_1009532
  intro a
  fin_cases a
  · exact context_10_18756_1008673
  · exact context_10_18757_893098
  · exact context_10_18758_1009143
  · exact context_10_18759_1009531

theorem selected_cut_37687 : selected 10 ⟨1009582, by decide⟩
    (prefixPartial 11 75040) = some ⟨11, 2, 0, 1009582, 75040, 2641, 262144⟩ := by
  decide +kernel

theorem context_11_75040_1009582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75040 ⟨1009582, by decide⟩ :=
  accepted_of_selected 11 75040 ⟨1009582, by decide⟩ ⟨11, 2, 0, 1009582, 75040, 2641, 262144⟩
    (by decide) selected_cut_37687

theorem selected_cut_37688 : selected 9 ⟨1009614, by decide⟩
    (prefixPartial 12 300164) = some ⟨12, 2, 0, 1009614, 300164, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_300164_1009614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300164 ⟨1009614, by decide⟩ :=
  accepted_of_selected 12 300164 ⟨1009614, by decide⟩ ⟨12, 2, 0, 1009614, 300164, 1717, 65536⟩
    (by decide) selected_cut_37688

theorem selected_cut_37689 : selected 9 ⟨1009639, by decide⟩
    (prefixPartial 12 300165) = some ⟨12, 2, 0, 1009639, 300165, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_300165_1009639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300165 ⟨1009639, by decide⟩ :=
  accepted_of_selected 12 300165 ⟨1009639, by decide⟩ ⟨12, 2, 0, 1009639, 300165, 1301, 65536⟩
    (by decide) selected_cut_37689

theorem selected_cut_37690 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300166) = some ⟨12, 1, 0, 984676, 300166, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300166_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300166 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300166 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300166, 1, 65536⟩
    (by decide) selected_cut_37690

theorem selected_cut_37691 : selected 9 ⟨1009665, by decide⟩
    (prefixPartial 12 300167) = some ⟨12, 2, 0, 1009665, 300167, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_300167_1009665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300167 ⟨1009665, by decide⟩ :=
  accepted_of_selected 12 300167 ⟨1009665, by decide⟩ ⟨12, 2, 0, 1009665, 300167, 1509, 65536⟩
    (by decide) selected_cut_37691

theorem unmarked_context_11_75041_1009666 : frontier 10 ⟨1009666, by decide⟩
    (prefixCache 11 75041) (prefixPartial 11 75041) = false := by
  decide +kernel

theorem node_context_11_75041_1009666 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009666, by decide⟩ =
    .split (coordinate 11) (![⟨1009614, by decide⟩,⟨1009639, by decide⟩,⟨984676, by decide⟩,⟨1009665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75041_1009666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75041 ⟨1009666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75041
    ⟨1009666, by decide⟩ (by decide) (![⟨1009614, by decide⟩,⟨1009639, by decide⟩,⟨984676, by decide⟩,⟨1009665, by decide⟩]) unmarked_context_11_75041_1009666 node_context_11_75041_1009666
  intro a
  fin_cases a
  · exact context_12_300164_1009614
  · exact context_12_300165_1009639
  · exact context_12_300166_984676
  · exact context_12_300167_1009665

theorem selected_cut_37692 : selected 9 ⟨1009696, by decide⟩
    (prefixPartial 12 300168) = some ⟨12, 2, 0, 1009696, 300168, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_300168_1009696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300168 ⟨1009696, by decide⟩ :=
  accepted_of_selected 12 300168 ⟨1009696, by decide⟩ ⟨12, 2, 0, 1009696, 300168, 1557, 65536⟩
    (by decide) selected_cut_37692

theorem selected_cut_37693 : selected 9 ⟨1009719, by decide⟩
    (prefixPartial 12 300169) = some ⟨12, 2, 0, 1009719, 300169, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_300169_1009719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300169 ⟨1009719, by decide⟩ :=
  accepted_of_selected 12 300169 ⟨1009719, by decide⟩ ⟨12, 2, 0, 1009719, 300169, 1329, 65536⟩
    (by decide) selected_cut_37693

theorem selected_cut_37694 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300170) = some ⟨12, 1, 0, 984676, 300170, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300170_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300170 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300170 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300170, 1, 65536⟩
    (by decide) selected_cut_37694

theorem selected_cut_37695 : selected 9 ⟨1009755, by decide⟩
    (prefixPartial 12 300171) = some ⟨12, 2, 0, 1009755, 300171, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_300171_1009755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300171 ⟨1009755, by decide⟩ :=
  accepted_of_selected 12 300171 ⟨1009755, by decide⟩ ⟨12, 2, 0, 1009755, 300171, 1569, 65536⟩
    (by decide) selected_cut_37695

theorem unmarked_context_11_75042_1009756 : frontier 10 ⟨1009756, by decide⟩
    (prefixCache 11 75042) (prefixPartial 11 75042) = false := by
  decide +kernel

theorem node_context_11_75042_1009756 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009756, by decide⟩ =
    .split (coordinate 11) (![⟨1009696, by decide⟩,⟨1009719, by decide⟩,⟨984676, by decide⟩,⟨1009755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75042_1009756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75042 ⟨1009756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75042
    ⟨1009756, by decide⟩ (by decide) (![⟨1009696, by decide⟩,⟨1009719, by decide⟩,⟨984676, by decide⟩,⟨1009755, by decide⟩]) unmarked_context_11_75042_1009756 node_context_11_75042_1009756
  intro a
  fin_cases a
  · exact context_12_300168_1009696
  · exact context_12_300169_1009719
  · exact context_12_300170_984676
  · exact context_12_300171_1009755

theorem selected_cut_37696 : selected 9 ⟨1009785, by decide⟩
    (prefixPartial 12 300172) = some ⟨12, 2, 0, 1009785, 300172, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_300172_1009785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300172 ⟨1009785, by decide⟩ :=
  accepted_of_selected 12 300172 ⟨1009785, by decide⟩ ⟨12, 2, 0, 1009785, 300172, 1525, 65536⟩
    (by decide) selected_cut_37696

theorem selected_cut_37697 : selected 9 ⟨1009807, by decide⟩
    (prefixPartial 12 300173) = some ⟨12, 2, 0, 1009807, 300173, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_300173_1009807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300173 ⟨1009807, by decide⟩ :=
  accepted_of_selected 12 300173 ⟨1009807, by decide⟩ ⟨12, 2, 0, 1009807, 300173, 1377, 65536⟩
    (by decide) selected_cut_37697

theorem selected_cut_37698 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300174) = some ⟨12, 1, 0, 984676, 300174, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300174_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300174 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300174 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300174, 1, 65536⟩
    (by decide) selected_cut_37698

theorem selected_cut_37699 : selected 9 ⟨1009829, by decide⟩
    (prefixPartial 12 300175) = some ⟨12, 2, 0, 1009829, 300175, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_300175_1009829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300175 ⟨1009829, by decide⟩ :=
  accepted_of_selected 12 300175 ⟨1009829, by decide⟩ ⟨12, 2, 0, 1009829, 300175, 1357, 65536⟩
    (by decide) selected_cut_37699

theorem unmarked_context_11_75043_1009830 : frontier 10 ⟨1009830, by decide⟩
    (prefixCache 11 75043) (prefixPartial 11 75043) = false := by
  decide +kernel

theorem node_context_11_75043_1009830 : EJMOriginalGlobalDAGData.nodes 10 ⟨1009830, by decide⟩ =
    .split (coordinate 11) (![⟨1009785, by decide⟩,⟨1009807, by decide⟩,⟨984676, by decide⟩,⟨1009829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75043_1009830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75043 ⟨1009830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75043
    ⟨1009830, by decide⟩ (by decide) (![⟨1009785, by decide⟩,⟨1009807, by decide⟩,⟨984676, by decide⟩,⟨1009829, by decide⟩]) unmarked_context_11_75043_1009830 node_context_11_75043_1009830
  intro a
  fin_cases a
  · exact context_12_300172_1009785
  · exact context_12_300173_1009807
  · exact context_12_300174_984676
  · exact context_12_300175_1009829

theorem unmarked_context_10_18760_1009831 : frontier 11 ⟨1009831, by decide⟩
    (prefixCache 10 18760) (prefixPartial 10 18760) = false := by
  decide +kernel

theorem node_context_10_18760_1009831 : EJMOriginalGlobalDAGData.nodes 11 ⟨1009831, by decide⟩ =
    .split (coordinate 10) (![⟨1009582, by decide⟩,⟨1009666, by decide⟩,⟨1009756, by decide⟩,⟨1009830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18760_1009831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18760 ⟨1009831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18760
    ⟨1009831, by decide⟩ (by decide) (![⟨1009582, by decide⟩,⟨1009666, by decide⟩,⟨1009756, by decide⟩,⟨1009830, by decide⟩]) unmarked_context_10_18760_1009831 node_context_10_18760_1009831
  intro a
  fin_cases a
  · exact context_11_75040_1009582
  · exact context_11_75041_1009666
  · exact context_11_75042_1009756
  · exact context_11_75043_1009830

theorem selected_cut_37700 : selected 10 ⟨1009863, by decide⟩
    (prefixPartial 11 75044) = some ⟨11, 2, 0, 1009863, 75044, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_75044_1009863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75044 ⟨1009863, by decide⟩ :=
  accepted_of_selected 11 75044 ⟨1009863, by decide⟩ ⟨11, 2, 0, 1009863, 75044, 1905, 262144⟩
    (by decide) selected_cut_37700

theorem selected_cut_37701 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75045) = some ⟨11, 1, 0, 892405, 75045, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75045_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75045 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75045 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75045, 1, 262144⟩
    (by decide) selected_cut_37701

theorem selected_cut_37702 : selected 10 ⟨1009910, by decide⟩
    (prefixPartial 11 75046) = some ⟨11, 2, 0, 1009910, 75046, 3133, 262144⟩ := by
  decide +kernel

theorem context_11_75046_1009910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75046 ⟨1009910, by decide⟩ :=
  accepted_of_selected 11 75046 ⟨1009910, by decide⟩ ⟨11, 2, 0, 1009910, 75046, 3133, 262144⟩
    (by decide) selected_cut_37702

theorem selected_cut_37703 : selected 10 ⟨1009962, by decide⟩
    (prefixPartial 11 75047) = some ⟨11, 2, 0, 1009962, 75047, 3197, 262144⟩ := by
  decide +kernel

theorem context_11_75047_1009962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75047 ⟨1009962, by decide⟩ :=
  accepted_of_selected 11 75047 ⟨1009962, by decide⟩ ⟨11, 2, 0, 1009962, 75047, 3197, 262144⟩
    (by decide) selected_cut_37703

theorem unmarked_context_10_18761_1009963 : frontier 11 ⟨1009963, by decide⟩
    (prefixCache 10 18761) (prefixPartial 10 18761) = false := by
  decide +kernel

theorem node_context_10_18761_1009963 : EJMOriginalGlobalDAGData.nodes 11 ⟨1009963, by decide⟩ =
    .split (coordinate 10) (![⟨1009863, by decide⟩,⟨892405, by decide⟩,⟨1009910, by decide⟩,⟨1009962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18761_1009963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18761 ⟨1009963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18761
    ⟨1009963, by decide⟩ (by decide) (![⟨1009863, by decide⟩,⟨892405, by decide⟩,⟨1009910, by decide⟩,⟨1009962, by decide⟩]) unmarked_context_10_18761_1009963 node_context_10_18761_1009963
  intro a
  fin_cases a
  · exact context_11_75044_1009863
  · exact context_11_75045_892405
  · exact context_11_75046_1009910
  · exact context_11_75047_1009962

theorem selected_cut_37704 : selected 10 ⟨1009998, by decide⟩
    (prefixPartial 11 75048) = some ⟨11, 2, 0, 1009998, 75048, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_75048_1009998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75048 ⟨1009998, by decide⟩ :=
  accepted_of_selected 11 75048 ⟨1009998, by decide⟩ ⟨11, 2, 0, 1009998, 75048, 1861, 262144⟩
    (by decide) selected_cut_37704

theorem selected_cut_37705 : selected 10 ⟨1010042, by decide⟩
    (prefixPartial 11 75049) = some ⟨11, 2, 0, 1010042, 75049, 2721, 262144⟩ := by
  decide +kernel

theorem context_11_75049_1010042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75049 ⟨1010042, by decide⟩ :=
  accepted_of_selected 11 75049 ⟨1010042, by decide⟩ ⟨11, 2, 0, 1010042, 75049, 2721, 262144⟩
    (by decide) selected_cut_37705

theorem selected_cut_37706 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75050) = some ⟨11, 1, 0, 906566, 75050, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75050_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75050 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75050 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75050, 1, 262144⟩
    (by decide) selected_cut_37706

theorem selected_cut_37707 : selected 10 ⟨1010086, by decide⟩
    (prefixPartial 11 75051) = some ⟨11, 2, 0, 1010086, 75051, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_75051_1010086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75051 ⟨1010086, by decide⟩ :=
  accepted_of_selected 11 75051 ⟨1010086, by decide⟩ ⟨11, 2, 0, 1010086, 75051, 2781, 262144⟩
    (by decide) selected_cut_37707

theorem unmarked_context_10_18762_1010087 : frontier 11 ⟨1010087, by decide⟩
    (prefixCache 10 18762) (prefixPartial 10 18762) = false := by
  decide +kernel

theorem node_context_10_18762_1010087 : EJMOriginalGlobalDAGData.nodes 11 ⟨1010087, by decide⟩ =
    .split (coordinate 10) (![⟨1009998, by decide⟩,⟨1010042, by decide⟩,⟨906566, by decide⟩,⟨1010086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18762_1010087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18762 ⟨1010087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18762
    ⟨1010087, by decide⟩ (by decide) (![⟨1009998, by decide⟩,⟨1010042, by decide⟩,⟨906566, by decide⟩,⟨1010086, by decide⟩]) unmarked_context_10_18762_1010087 node_context_10_18762_1010087
  intro a
  fin_cases a
  · exact context_11_75048_1009998
  · exact context_11_75049_1010042
  · exact context_11_75050_906566
  · exact context_11_75051_1010086

theorem selected_cut_37708 : selected 10 ⟨1010112, by decide⟩
    (prefixPartial 11 75052) = some ⟨11, 2, 0, 1010112, 75052, 1437, 262144⟩ := by
  decide +kernel

theorem context_11_75052_1010112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75052 ⟨1010112, by decide⟩ :=
  accepted_of_selected 11 75052 ⟨1010112, by decide⟩ ⟨11, 2, 0, 1010112, 75052, 1437, 262144⟩
    (by decide) selected_cut_37708

theorem selected_cut_37709 : selected 10 ⟨1010151, by decide⟩
    (prefixPartial 11 75053) = some ⟨11, 2, 0, 1010151, 75053, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_75053_1010151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75053 ⟨1010151, by decide⟩ :=
  accepted_of_selected 11 75053 ⟨1010151, by decide⟩ ⟨11, 2, 0, 1010151, 75053, 2329, 262144⟩
    (by decide) selected_cut_37709

theorem selected_cut_37710 : selected 10 ⟨1010185, by decide⟩
    (prefixPartial 11 75054) = some ⟨11, 2, 0, 1010185, 75054, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_75054_1010185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75054 ⟨1010185, by decide⟩ :=
  accepted_of_selected 11 75054 ⟨1010185, by decide⟩ ⟨11, 2, 0, 1010185, 75054, 2061, 262144⟩
    (by decide) selected_cut_37710

theorem selected_cut_37711 : selected 10 ⟨1010216, by decide⟩
    (prefixPartial 11 75055) = some ⟨11, 2, 0, 1010216, 75055, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_75055_1010216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75055 ⟨1010216, by decide⟩ :=
  accepted_of_selected 11 75055 ⟨1010216, by decide⟩ ⟨11, 2, 0, 1010216, 75055, 2113, 262144⟩
    (by decide) selected_cut_37711

theorem unmarked_context_10_18763_1010217 : frontier 11 ⟨1010217, by decide⟩
    (prefixCache 10 18763) (prefixPartial 10 18763) = false := by
  decide +kernel

theorem node_context_10_18763_1010217 : EJMOriginalGlobalDAGData.nodes 11 ⟨1010217, by decide⟩ =
    .split (coordinate 10) (![⟨1010112, by decide⟩,⟨1010151, by decide⟩,⟨1010185, by decide⟩,⟨1010216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18763_1010217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18763 ⟨1010217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18763
    ⟨1010217, by decide⟩ (by decide) (![⟨1010112, by decide⟩,⟨1010151, by decide⟩,⟨1010185, by decide⟩,⟨1010216, by decide⟩]) unmarked_context_10_18763_1010217 node_context_10_18763_1010217
  intro a
  fin_cases a
  · exact context_11_75052_1010112
  · exact context_11_75053_1010151
  · exact context_11_75054_1010185
  · exact context_11_75055_1010216

theorem unmarked_context_9_4690_1010218 : frontier 12 ⟨1010218, by decide⟩
    (prefixCache 9 4690) (prefixPartial 9 4690) = false := by
  decide +kernel

theorem node_context_9_4690_1010218 : EJMOriginalGlobalDAGData.nodes 12 ⟨1010218, by decide⟩ =
    .split (coordinate 9) (![⟨1009831, by decide⟩,⟨1009963, by decide⟩,⟨1010087, by decide⟩,⟨1010217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4690_1010218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4690 ⟨1010218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4690
    ⟨1010218, by decide⟩ (by decide) (![⟨1009831, by decide⟩,⟨1009963, by decide⟩,⟨1010087, by decide⟩,⟨1010217, by decide⟩]) unmarked_context_9_4690_1010218 node_context_9_4690_1010218
  intro a
  fin_cases a
  · exact context_10_18760_1009831
  · exact context_10_18761_1009963
  · exact context_10_18762_1010087
  · exact context_10_18763_1010217

theorem selected_cut_37712 : selected 10 ⟨1010240, by decide⟩
    (prefixPartial 11 75056) = some ⟨11, 2, 0, 1010240, 75056, 1681, 262144⟩ := by
  decide +kernel

theorem context_11_75056_1010240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75056 ⟨1010240, by decide⟩ :=
  accepted_of_selected 11 75056 ⟨1010240, by decide⟩ ⟨11, 2, 0, 1010240, 75056, 1681, 262144⟩
    (by decide) selected_cut_37712

theorem selected_cut_37713 : selected 10 ⟨1010275, by decide⟩
    (prefixPartial 11 75057) = some ⟨11, 2, 0, 1010275, 75057, 2337, 262144⟩ := by
  decide +kernel

theorem context_11_75057_1010275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75057 ⟨1010275, by decide⟩ :=
  accepted_of_selected 11 75057 ⟨1010275, by decide⟩ ⟨11, 2, 0, 1010275, 75057, 2337, 262144⟩
    (by decide) selected_cut_37713

theorem selected_cut_37714 : selected 10 ⟨1010310, by decide⟩
    (prefixPartial 11 75058) = some ⟨11, 2, 0, 1010310, 75058, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_75058_1010310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75058 ⟨1010310, by decide⟩ :=
  accepted_of_selected 11 75058 ⟨1010310, by decide⟩ ⟨11, 2, 0, 1010310, 75058, 2225, 262144⟩
    (by decide) selected_cut_37714

theorem selected_cut_37715 : selected 10 ⟨1010350, by decide⟩
    (prefixPartial 11 75059) = some ⟨11, 2, 0, 1010350, 75059, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_75059_1010350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75059 ⟨1010350, by decide⟩ :=
  accepted_of_selected 11 75059 ⟨1010350, by decide⟩ ⟨11, 2, 0, 1010350, 75059, 2197, 262144⟩
    (by decide) selected_cut_37715

theorem unmarked_context_10_18764_1010351 : frontier 11 ⟨1010351, by decide⟩
    (prefixCache 10 18764) (prefixPartial 10 18764) = false := by
  decide +kernel

theorem node_context_10_18764_1010351 : EJMOriginalGlobalDAGData.nodes 11 ⟨1010351, by decide⟩ =
    .split (coordinate 10) (![⟨1010240, by decide⟩,⟨1010275, by decide⟩,⟨1010310, by decide⟩,⟨1010350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18764_1010351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18764 ⟨1010351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18764
    ⟨1010351, by decide⟩ (by decide) (![⟨1010240, by decide⟩,⟨1010275, by decide⟩,⟨1010310, by decide⟩,⟨1010350, by decide⟩]) unmarked_context_10_18764_1010351 node_context_10_18764_1010351
  intro a
  fin_cases a
  · exact context_11_75056_1010240
  · exact context_11_75057_1010275
  · exact context_11_75058_1010310
  · exact context_11_75059_1010350

theorem selected_cut_37716 : selected 11 ⟨1010406, by decide⟩
    (prefixPartial 10 18765) = some ⟨10, 2, 0, 1010406, 18765, 3741, 1048576⟩ := by
  decide +kernel

theorem context_10_18765_1010406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18765 ⟨1010406, by decide⟩ :=
  accepted_of_selected 10 18765 ⟨1010406, by decide⟩ ⟨10, 2, 0, 1010406, 18765, 3741, 1048576⟩
    (by decide) selected_cut_37716

theorem selected_cut_37717 : selected 11 ⟨1010460, by decide⟩
    (prefixPartial 10 18766) = some ⟨10, 2, 0, 1010460, 18766, 3005, 1048576⟩ := by
  decide +kernel

theorem context_10_18766_1010460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18766 ⟨1010460, by decide⟩ :=
  accepted_of_selected 10 18766 ⟨1010460, by decide⟩ ⟨10, 2, 0, 1010460, 18766, 3005, 1048576⟩
    (by decide) selected_cut_37717

theorem selected_cut_37718 : selected 11 ⟨1010497, by decide⟩
    (prefixPartial 10 18767) = some ⟨10, 2, 0, 1010497, 18767, 761, 1048576⟩ := by
  decide +kernel

theorem context_10_18767_1010497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18767 ⟨1010497, by decide⟩ :=
  accepted_of_selected 10 18767 ⟨1010497, by decide⟩ ⟨10, 2, 0, 1010497, 18767, 761, 1048576⟩
    (by decide) selected_cut_37718

theorem unmarked_context_9_4691_1010498 : frontier 12 ⟨1010498, by decide⟩
    (prefixCache 9 4691) (prefixPartial 9 4691) = false := by
  decide +kernel

theorem node_context_9_4691_1010498 : EJMOriginalGlobalDAGData.nodes 12 ⟨1010498, by decide⟩ =
    .split (coordinate 9) (![⟨1010351, by decide⟩,⟨1010406, by decide⟩,⟨1010460, by decide⟩,⟨1010497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4691_1010498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4691 ⟨1010498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4691
    ⟨1010498, by decide⟩ (by decide) (![⟨1010351, by decide⟩,⟨1010406, by decide⟩,⟨1010460, by decide⟩,⟨1010497, by decide⟩]) unmarked_context_9_4691_1010498 node_context_9_4691_1010498
  intro a
  fin_cases a
  · exact context_10_18764_1010351
  · exact context_10_18765_1010406
  · exact context_10_18766_1010460
  · exact context_10_18767_1010497

theorem unmarked_context_8_1172_1010499 : frontier 13 ⟨1010499, by decide⟩
    (prefixCache 8 1172) (prefixPartial 8 1172) = false := by
  decide +kernel

theorem node_context_8_1172_1010499 : EJMOriginalGlobalDAGData.nodes 13 ⟨1010499, by decide⟩ =
    .split (coordinate 8) (![⟨1008060, by decide⟩,⟨1009532, by decide⟩,⟨1010218, by decide⟩,⟨1010498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1172_1010499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1172 ⟨1010499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1172
    ⟨1010499, by decide⟩ (by decide) (![⟨1008060, by decide⟩,⟨1009532, by decide⟩,⟨1010218, by decide⟩,⟨1010498, by decide⟩]) unmarked_context_8_1172_1010499 node_context_8_1172_1010499
  intro a
  fin_cases a
  · exact context_9_4688_1008060
  · exact context_9_4689_1009532
  · exact context_9_4690_1010218
  · exact context_9_4691_1010498

theorem selected_cut_37719 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 75072) = some ⟨11, 1, 0, 167448, 75072, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75072_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75072 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 75072 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 75072, 1, 262144⟩
    (by decide) selected_cut_37719

theorem selected_cut_37720 : selected 8 ⟨1010534, by decide⟩
    (prefixPartial 13 1201168) = some ⟨13, 2, 0, 1010534, 1201168, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_1201168_1010534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201168 ⟨1010534, by decide⟩ :=
  accepted_of_selected 13 1201168 ⟨1010534, by decide⟩ ⟨13, 2, 0, 1010534, 1201168, 1197, 16384⟩
    (by decide) selected_cut_37720

theorem selected_cut_37721 : selected 8 ⟨1010559, by decide⟩
    (prefixPartial 13 1201169) = some ⟨13, 2, 0, 1010559, 1201169, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_1201169_1010559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201169 ⟨1010559, by decide⟩ :=
  accepted_of_selected 13 1201169 ⟨1010559, by decide⟩ ⟨13, 2, 0, 1010559, 1201169, 1373, 16384⟩
    (by decide) selected_cut_37721

theorem selected_cut_37722 : selected 8 ⟨1010595, by decide⟩
    (prefixPartial 13 1201170) = some ⟨13, 2, 0, 1010595, 1201170, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_1201170_1010595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201170 ⟨1010595, by decide⟩ :=
  accepted_of_selected 13 1201170 ⟨1010595, by decide⟩ ⟨13, 2, 0, 1010595, 1201170, 1065, 16384⟩
    (by decide) selected_cut_37722

theorem selected_cut_37723 : selected 8 ⟨1010612, by decide⟩
    (prefixPartial 13 1201171) = some ⟨13, 2, 0, 1010612, 1201171, 669, 16384⟩ := by
  decide +kernel

theorem context_13_1201171_1010612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201171 ⟨1010612, by decide⟩ :=
  accepted_of_selected 13 1201171 ⟨1010612, by decide⟩ ⟨13, 2, 0, 1010612, 1201171, 669, 16384⟩
    (by decide) selected_cut_37723

theorem unmarked_context_12_300292_1010613 : frontier 9 ⟨1010613, by decide⟩
    (prefixCache 12 300292) (prefixPartial 12 300292) = false := by
  decide +kernel

theorem node_context_12_300292_1010613 : EJMOriginalGlobalDAGData.nodes 9 ⟨1010613, by decide⟩ =
    .split (coordinate 12) (![⟨1010534, by decide⟩,⟨1010559, by decide⟩,⟨1010595, by decide⟩,⟨1010612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300292_1010613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300292 ⟨1010613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300292
    ⟨1010613, by decide⟩ (by decide) (![⟨1010534, by decide⟩,⟨1010559, by decide⟩,⟨1010595, by decide⟩,⟨1010612, by decide⟩]) unmarked_context_12_300292_1010613 node_context_12_300292_1010613
  intro a
  fin_cases a
  · exact context_13_1201168_1010534
  · exact context_13_1201169_1010559
  · exact context_13_1201170_1010595
  · exact context_13_1201171_1010612

theorem selected_cut_37724 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 300293) = some ⟨12, 1, 0, 891951, 300293, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300293_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300293 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 300293 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 300293, 1, 65536⟩
    (by decide) selected_cut_37724

theorem selected_cut_37725 : selected 9 ⟨1010679, by decide⟩
    (prefixPartial 12 300294) = some ⟨12, 2, 0, 1010679, 300294, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_300294_1010679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300294 ⟨1010679, by decide⟩ :=
  accepted_of_selected 12 300294 ⟨1010679, by decide⟩ ⟨12, 2, 0, 1010679, 300294, 3481, 65536⟩
    (by decide) selected_cut_37725

theorem selected_cut_37726 : selected 9 ⟨1010750, by decide⟩
    (prefixPartial 12 300295) = some ⟨12, 2, 0, 1010750, 300295, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_300295_1010750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300295 ⟨1010750, by decide⟩ :=
  accepted_of_selected 12 300295 ⟨1010750, by decide⟩ ⟨12, 2, 0, 1010750, 300295, 3513, 65536⟩
    (by decide) selected_cut_37726

theorem unmarked_context_11_75073_1010751 : frontier 10 ⟨1010751, by decide⟩
    (prefixCache 11 75073) (prefixPartial 11 75073) = false := by
  decide +kernel

theorem node_context_11_75073_1010751 : EJMOriginalGlobalDAGData.nodes 10 ⟨1010751, by decide⟩ =
    .split (coordinate 11) (![⟨1010613, by decide⟩,⟨891951, by decide⟩,⟨1010679, by decide⟩,⟨1010750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75073_1010751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75073 ⟨1010751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75073
    ⟨1010751, by decide⟩ (by decide) (![⟨1010613, by decide⟩,⟨891951, by decide⟩,⟨1010679, by decide⟩,⟨1010750, by decide⟩]) unmarked_context_11_75073_1010751 node_context_11_75073_1010751
  intro a
  fin_cases a
  · exact context_12_300292_1010613
  · exact context_12_300293_891951
  · exact context_12_300294_1010679
  · exact context_12_300295_1010750

theorem selected_cut_37727 : selected 8 ⟨1010765, by decide⟩
    (prefixPartial 13 1201184) = some ⟨13, 2, 0, 1010765, 1201184, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_1201184_1010765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201184 ⟨1010765, by decide⟩ :=
  accepted_of_selected 13 1201184 ⟨1010765, by decide⟩ ⟨13, 2, 0, 1010765, 1201184, 1017, 16384⟩
    (by decide) selected_cut_37727

theorem selected_cut_37728 : selected 8 ⟨1010795, by decide⟩
    (prefixPartial 13 1201185) = some ⟨13, 2, 0, 1010795, 1201185, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_1201185_1010795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201185 ⟨1010795, by decide⟩ :=
  accepted_of_selected 13 1201185 ⟨1010795, by decide⟩ ⟨13, 2, 0, 1010795, 1201185, 1557, 16384⟩
    (by decide) selected_cut_37728

theorem selected_cut_37729 : selected 8 ⟨1010825, by decide⟩
    (prefixPartial 13 1201186) = some ⟨13, 2, 0, 1010825, 1201186, 925, 16384⟩ := by
  decide +kernel

theorem context_13_1201186_1010825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201186 ⟨1010825, by decide⟩ :=
  accepted_of_selected 13 1201186 ⟨1010825, by decide⟩ ⟨13, 2, 0, 1010825, 1201186, 925, 16384⟩
    (by decide) selected_cut_37729

theorem selected_cut_37730 : selected 8 ⟨1010834, by decide⟩
    (prefixPartial 13 1201187) = some ⟨13, 2, 0, 1010834, 1201187, 613, 16384⟩ := by
  decide +kernel

theorem context_13_1201187_1010834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1201187 ⟨1010834, by decide⟩ :=
  accepted_of_selected 13 1201187 ⟨1010834, by decide⟩ ⟨13, 2, 0, 1010834, 1201187, 613, 16384⟩
    (by decide) selected_cut_37730

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
