/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover288
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_27747 : selected 9 ⟨701113, by decide⟩
    (prefixPartial 12 91809) = some ⟨12, 2, 0, 701113, 91809, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_91809_701113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91809 ⟨701113, by decide⟩ :=
  accepted_of_selected 12 91809 ⟨701113, by decide⟩ ⟨12, 2, 0, 701113, 91809, 1353, 65536⟩
    (by decide) selected_cut_27747

theorem selected_cut_27748 : selected 9 ⟨701127, by decide⟩
    (prefixPartial 12 91810) = some ⟨12, 2, 0, 701127, 91810, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_91810_701127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91810 ⟨701127, by decide⟩ :=
  accepted_of_selected 12 91810 ⟨701127, by decide⟩ ⟨12, 2, 0, 701127, 91810, 1217, 65536⟩
    (by decide) selected_cut_27748

theorem selected_cut_27749 : selected 9 ⟨701137, by decide⟩
    (prefixPartial 12 91811) = some ⟨12, 2, 0, 701137, 91811, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_91811_701137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91811 ⟨701137, by decide⟩ :=
  accepted_of_selected 12 91811 ⟨701137, by decide⟩ ⟨12, 2, 0, 701137, 91811, 1273, 65536⟩
    (by decide) selected_cut_27749

theorem unmarked_context_11_22952_701138 : frontier 10 ⟨701138, by decide⟩
    (prefixCache 11 22952) (prefixPartial 11 22952) = false := by
  decide +kernel

theorem node_context_11_22952_701138 : EJMOriginalGlobalDAGData.nodes 10 ⟨701138, by decide⟩ =
    .split (coordinate 11) (![⟨701103, by decide⟩,⟨701113, by decide⟩,⟨701127, by decide⟩,⟨701137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22952_701138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22952 ⟨701138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22952
    ⟨701138, by decide⟩ (by decide) (![⟨701103, by decide⟩,⟨701113, by decide⟩,⟨701127, by decide⟩,⟨701137, by decide⟩]) unmarked_context_11_22952_701138 node_context_11_22952_701138
  intro a
  fin_cases a
  · exact context_12_91808_701103
  · exact context_12_91809_701113
  · exact context_12_91810_701127
  · exact context_12_91811_701137

theorem selected_cut_27750 : selected 9 ⟨701151, by decide⟩
    (prefixPartial 12 91812) = some ⟨12, 2, 0, 701151, 91812, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_91812_701151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91812 ⟨701151, by decide⟩ :=
  accepted_of_selected 12 91812 ⟨701151, by decide⟩ ⟨12, 2, 0, 701151, 91812, 1309, 65536⟩
    (by decide) selected_cut_27750

theorem selected_cut_27751 : selected 9 ⟨701162, by decide⟩
    (prefixPartial 12 91813) = some ⟨12, 2, 0, 701162, 91813, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_91813_701162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91813 ⟨701162, by decide⟩ :=
  accepted_of_selected 12 91813 ⟨701162, by decide⟩ ⟨12, 2, 0, 701162, 91813, 1229, 65536⟩
    (by decide) selected_cut_27751

theorem selected_cut_27752 : selected 9 ⟨701176, by decide⟩
    (prefixPartial 12 91814) = some ⟨12, 2, 0, 701176, 91814, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_91814_701176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91814 ⟨701176, by decide⟩ :=
  accepted_of_selected 12 91814 ⟨701176, by decide⟩ ⟨12, 2, 0, 701176, 91814, 1133, 65536⟩
    (by decide) selected_cut_27752

theorem selected_cut_27753 : selected 9 ⟨701189, by decide⟩
    (prefixPartial 12 91815) = some ⟨12, 2, 0, 701189, 91815, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_91815_701189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91815 ⟨701189, by decide⟩ :=
  accepted_of_selected 12 91815 ⟨701189, by decide⟩ ⟨12, 2, 0, 701189, 91815, 1209, 65536⟩
    (by decide) selected_cut_27753

theorem unmarked_context_11_22953_701190 : frontier 10 ⟨701190, by decide⟩
    (prefixCache 11 22953) (prefixPartial 11 22953) = false := by
  decide +kernel

theorem node_context_11_22953_701190 : EJMOriginalGlobalDAGData.nodes 10 ⟨701190, by decide⟩ =
    .split (coordinate 11) (![⟨701151, by decide⟩,⟨701162, by decide⟩,⟨701176, by decide⟩,⟨701189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22953_701190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22953 ⟨701190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22953
    ⟨701190, by decide⟩ (by decide) (![⟨701151, by decide⟩,⟨701162, by decide⟩,⟨701176, by decide⟩,⟨701189, by decide⟩]) unmarked_context_11_22953_701190 node_context_11_22953_701190
  intro a
  fin_cases a
  · exact context_12_91812_701151
  · exact context_12_91813_701162
  · exact context_12_91814_701176
  · exact context_12_91815_701189

theorem selected_cut_27754 : selected 10 ⟨701226, by decide⟩
    (prefixPartial 11 22954) = some ⟨11, 2, 0, 701226, 22954, 3701, 262144⟩ := by
  decide +kernel

theorem context_11_22954_701226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22954 ⟨701226, by decide⟩ :=
  accepted_of_selected 11 22954 ⟨701226, by decide⟩ ⟨11, 2, 0, 701226, 22954, 3701, 262144⟩
    (by decide) selected_cut_27754

theorem selected_cut_27755 : selected 9 ⟨701243, by decide⟩
    (prefixPartial 12 91820) = some ⟨12, 2, 0, 701243, 91820, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_91820_701243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91820 ⟨701243, by decide⟩ :=
  accepted_of_selected 12 91820 ⟨701243, by decide⟩ ⟨12, 2, 0, 701243, 91820, 1357, 65536⟩
    (by decide) selected_cut_27755

theorem selected_cut_27756 : selected 9 ⟨701254, by decide⟩
    (prefixPartial 12 91821) = some ⟨12, 2, 0, 701254, 91821, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_91821_701254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91821 ⟨701254, by decide⟩ :=
  accepted_of_selected 12 91821 ⟨701254, by decide⟩ ⟨12, 2, 0, 701254, 91821, 1297, 65536⟩
    (by decide) selected_cut_27756

theorem selected_cut_27757 : selected 9 ⟨701268, by decide⟩
    (prefixPartial 12 91822) = some ⟨12, 2, 0, 701268, 91822, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_91822_701268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91822 ⟨701268, by decide⟩ :=
  accepted_of_selected 12 91822 ⟨701268, by decide⟩ ⟨12, 2, 0, 701268, 91822, 1189, 65536⟩
    (by decide) selected_cut_27757

theorem selected_cut_27758 : selected 9 ⟨701282, by decide⟩
    (prefixPartial 12 91823) = some ⟨12, 2, 0, 701282, 91823, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_91823_701282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91823 ⟨701282, by decide⟩ :=
  accepted_of_selected 12 91823 ⟨701282, by decide⟩ ⟨12, 2, 0, 701282, 91823, 1229, 65536⟩
    (by decide) selected_cut_27758

theorem unmarked_context_11_22955_701283 : frontier 10 ⟨701283, by decide⟩
    (prefixCache 11 22955) (prefixPartial 11 22955) = false := by
  decide +kernel

theorem node_context_11_22955_701283 : EJMOriginalGlobalDAGData.nodes 10 ⟨701283, by decide⟩ =
    .split (coordinate 11) (![⟨701243, by decide⟩,⟨701254, by decide⟩,⟨701268, by decide⟩,⟨701282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22955_701283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22955 ⟨701283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22955
    ⟨701283, by decide⟩ (by decide) (![⟨701243, by decide⟩,⟨701254, by decide⟩,⟨701268, by decide⟩,⟨701282, by decide⟩]) unmarked_context_11_22955_701283 node_context_11_22955_701283
  intro a
  fin_cases a
  · exact context_12_91820_701243
  · exact context_12_91821_701254
  · exact context_12_91822_701268
  · exact context_12_91823_701282

theorem unmarked_context_10_5738_701284 : frontier 11 ⟨701284, by decide⟩
    (prefixCache 10 5738) (prefixPartial 10 5738) = false := by
  decide +kernel

theorem node_context_10_5738_701284 : EJMOriginalGlobalDAGData.nodes 11 ⟨701284, by decide⟩ =
    .split (coordinate 10) (![⟨701138, by decide⟩,⟨701190, by decide⟩,⟨701226, by decide⟩,⟨701283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5738_701284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5738 ⟨701284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5738
    ⟨701284, by decide⟩ (by decide) (![⟨701138, by decide⟩,⟨701190, by decide⟩,⟨701226, by decide⟩,⟨701283, by decide⟩]) unmarked_context_10_5738_701284 node_context_10_5738_701284
  intro a
  fin_cases a
  · exact context_11_22952_701138
  · exact context_11_22953_701190
  · exact context_11_22954_701226
  · exact context_11_22955_701283

theorem selected_cut_27759 : selected 9 ⟨701295, by decide⟩
    (prefixPartial 12 91824) = some ⟨12, 2, 0, 701295, 91824, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_91824_701295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91824 ⟨701295, by decide⟩ :=
  accepted_of_selected 12 91824 ⟨701295, by decide⟩ ⟨12, 2, 0, 701295, 91824, 1085, 65536⟩
    (by decide) selected_cut_27759

theorem selected_cut_27760 : selected 9 ⟨701307, by decide⟩
    (prefixPartial 12 91825) = some ⟨12, 2, 0, 701307, 91825, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_91825_701307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91825 ⟨701307, by decide⟩ :=
  accepted_of_selected 12 91825 ⟨701307, by decide⟩ ⟨12, 2, 0, 701307, 91825, 1113, 65536⟩
    (by decide) selected_cut_27760

theorem selected_cut_27761 : selected 9 ⟨701318, by decide⟩
    (prefixPartial 12 91826) = some ⟨12, 2, 0, 701318, 91826, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_91826_701318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91826 ⟨701318, by decide⟩ :=
  accepted_of_selected 12 91826 ⟨701318, by decide⟩ ⟨12, 2, 0, 701318, 91826, 1049, 65536⟩
    (by decide) selected_cut_27761

theorem selected_cut_27762 : selected 9 ⟨701332, by decide⟩
    (prefixPartial 12 91827) = some ⟨12, 2, 0, 701332, 91827, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_91827_701332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91827 ⟨701332, by decide⟩ :=
  accepted_of_selected 12 91827 ⟨701332, by decide⟩ ⟨12, 2, 0, 701332, 91827, 1177, 65536⟩
    (by decide) selected_cut_27762

theorem unmarked_context_11_22956_701333 : frontier 10 ⟨701333, by decide⟩
    (prefixCache 11 22956) (prefixPartial 11 22956) = false := by
  decide +kernel

theorem node_context_11_22956_701333 : EJMOriginalGlobalDAGData.nodes 10 ⟨701333, by decide⟩ =
    .split (coordinate 11) (![⟨701295, by decide⟩,⟨701307, by decide⟩,⟨701318, by decide⟩,⟨701332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22956_701333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22956 ⟨701333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22956
    ⟨701333, by decide⟩ (by decide) (![⟨701295, by decide⟩,⟨701307, by decide⟩,⟨701318, by decide⟩,⟨701332, by decide⟩]) unmarked_context_11_22956_701333 node_context_11_22956_701333
  intro a
  fin_cases a
  · exact context_12_91824_701295
  · exact context_12_91825_701307
  · exact context_12_91826_701318
  · exact context_12_91827_701332

theorem selected_cut_27763 : selected 10 ⟨701375, by decide⟩
    (prefixPartial 11 22957) = some ⟨11, 2, 0, 701375, 22957, 3881, 262144⟩ := by
  decide +kernel

theorem context_11_22957_701375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22957 ⟨701375, by decide⟩ :=
  accepted_of_selected 11 22957 ⟨701375, by decide⟩ ⟨11, 2, 0, 701375, 22957, 3881, 262144⟩
    (by decide) selected_cut_27763

theorem selected_cut_27764 : selected 10 ⟨701409, by decide⟩
    (prefixPartial 11 22958) = some ⟨11, 2, 0, 701409, 22958, 2981, 262144⟩ := by
  decide +kernel

theorem context_11_22958_701409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22958 ⟨701409, by decide⟩ :=
  accepted_of_selected 11 22958 ⟨701409, by decide⟩ ⟨11, 2, 0, 701409, 22958, 2981, 262144⟩
    (by decide) selected_cut_27764

theorem selected_cut_27765 : selected 10 ⟨701442, by decide⟩
    (prefixPartial 11 22959) = some ⟨11, 2, 0, 701442, 22959, 3661, 262144⟩ := by
  decide +kernel

theorem context_11_22959_701442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22959 ⟨701442, by decide⟩ :=
  accepted_of_selected 11 22959 ⟨701442, by decide⟩ ⟨11, 2, 0, 701442, 22959, 3661, 262144⟩
    (by decide) selected_cut_27765

theorem unmarked_context_10_5739_701443 : frontier 11 ⟨701443, by decide⟩
    (prefixCache 10 5739) (prefixPartial 10 5739) = false := by
  decide +kernel

theorem node_context_10_5739_701443 : EJMOriginalGlobalDAGData.nodes 11 ⟨701443, by decide⟩ =
    .split (coordinate 10) (![⟨701333, by decide⟩,⟨701375, by decide⟩,⟨701409, by decide⟩,⟨701442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5739_701443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5739 ⟨701443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5739
    ⟨701443, by decide⟩ (by decide) (![⟨701333, by decide⟩,⟨701375, by decide⟩,⟨701409, by decide⟩,⟨701442, by decide⟩]) unmarked_context_10_5739_701443 node_context_10_5739_701443
  intro a
  fin_cases a
  · exact context_11_22956_701333
  · exact context_11_22957_701375
  · exact context_11_22958_701409
  · exact context_11_22959_701442

theorem unmarked_context_9_1434_701444 : frontier 12 ⟨701444, by decide⟩
    (prefixCache 9 1434) (prefixPartial 9 1434) = false := by
  decide +kernel

theorem node_context_9_1434_701444 : EJMOriginalGlobalDAGData.nodes 12 ⟨701444, by decide⟩ =
    .split (coordinate 9) (![⟨700811, by decide⟩,⟨701091, by decide⟩,⟨701284, by decide⟩,⟨701443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1434_701444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1434 ⟨701444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1434
    ⟨701444, by decide⟩ (by decide) (![⟨700811, by decide⟩,⟨701091, by decide⟩,⟨701284, by decide⟩,⟨701443, by decide⟩]) unmarked_context_9_1434_701444 node_context_9_1434_701444
  intro a
  fin_cases a
  · exact context_10_5736_700811
  · exact context_10_5737_701091
  · exact context_10_5738_701284
  · exact context_10_5739_701443

theorem selected_cut_27766 : selected 10 ⟨701477, by decide⟩
    (prefixPartial 11 22960) = some ⟨11, 2, 0, 701477, 22960, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_22960_701477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22960 ⟨701477, by decide⟩ :=
  accepted_of_selected 11 22960 ⟨701477, by decide⟩ ⟨11, 2, 0, 701477, 22960, 3097, 262144⟩
    (by decide) selected_cut_27766

theorem selected_cut_27767 : selected 10 ⟨701505, by decide⟩
    (prefixPartial 11 22961) = some ⟨11, 2, 0, 701505, 22961, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_22961_701505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22961 ⟨701505, by decide⟩ :=
  accepted_of_selected 11 22961 ⟨701505, by decide⟩ ⟨11, 2, 0, 701505, 22961, 2961, 262144⟩
    (by decide) selected_cut_27767

theorem selected_cut_27768 : selected 10 ⟨701536, by decide⟩
    (prefixPartial 11 22962) = some ⟨11, 2, 0, 701536, 22962, 3021, 262144⟩ := by
  decide +kernel

theorem context_11_22962_701536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22962 ⟨701536, by decide⟩ :=
  accepted_of_selected 11 22962 ⟨701536, by decide⟩ ⟨11, 2, 0, 701536, 22962, 3021, 262144⟩
    (by decide) selected_cut_27768

theorem selected_cut_27769 : selected 10 ⟨701567, by decide⟩
    (prefixPartial 11 22963) = some ⟨11, 2, 0, 701567, 22963, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_22963_701567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22963 ⟨701567, by decide⟩ :=
  accepted_of_selected 11 22963 ⟨701567, by decide⟩ ⟨11, 2, 0, 701567, 22963, 2973, 262144⟩
    (by decide) selected_cut_27769

theorem unmarked_context_10_5740_701568 : frontier 11 ⟨701568, by decide⟩
    (prefixCache 10 5740) (prefixPartial 10 5740) = false := by
  decide +kernel

theorem node_context_10_5740_701568 : EJMOriginalGlobalDAGData.nodes 11 ⟨701568, by decide⟩ =
    .split (coordinate 10) (![⟨701477, by decide⟩,⟨701505, by decide⟩,⟨701536, by decide⟩,⟨701567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5740_701568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5740 ⟨701568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5740
    ⟨701568, by decide⟩ (by decide) (![⟨701477, by decide⟩,⟨701505, by decide⟩,⟨701536, by decide⟩,⟨701567, by decide⟩]) unmarked_context_10_5740_701568 node_context_10_5740_701568
  intro a
  fin_cases a
  · exact context_11_22960_701477
  · exact context_11_22961_701505
  · exact context_11_22962_701536
  · exact context_11_22963_701567

theorem selected_cut_27770 : selected 10 ⟨701589, by decide⟩
    (prefixPartial 11 22964) = some ⟨11, 2, 0, 701589, 22964, 2305, 262144⟩ := by
  decide +kernel

theorem context_11_22964_701589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22964 ⟨701589, by decide⟩ :=
  accepted_of_selected 11 22964 ⟨701589, by decide⟩ ⟨11, 2, 0, 701589, 22964, 2305, 262144⟩
    (by decide) selected_cut_27770

theorem selected_cut_27771 : selected 10 ⟨701610, by decide⟩
    (prefixPartial 11 22965) = some ⟨11, 2, 0, 701610, 22965, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_22965_701610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22965 ⟨701610, by decide⟩ :=
  accepted_of_selected 11 22965 ⟨701610, by decide⟩ ⟨11, 2, 0, 701610, 22965, 2113, 262144⟩
    (by decide) selected_cut_27771

theorem selected_cut_27772 : selected 10 ⟨701628, by decide⟩
    (prefixPartial 11 22966) = some ⟨11, 2, 0, 701628, 22966, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_22966_701628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22966 ⟨701628, by decide⟩ :=
  accepted_of_selected 11 22966 ⟨701628, by decide⟩ ⟨11, 2, 0, 701628, 22966, 1921, 262144⟩
    (by decide) selected_cut_27772

theorem selected_cut_27773 : selected 10 ⟨701648, by decide⟩
    (prefixPartial 11 22967) = some ⟨11, 2, 0, 701648, 22967, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_22967_701648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22967 ⟨701648, by decide⟩ :=
  accepted_of_selected 11 22967 ⟨701648, by decide⟩ ⟨11, 2, 0, 701648, 22967, 1729, 262144⟩
    (by decide) selected_cut_27773

theorem unmarked_context_10_5741_701649 : frontier 11 ⟨701649, by decide⟩
    (prefixCache 10 5741) (prefixPartial 10 5741) = false := by
  decide +kernel

theorem node_context_10_5741_701649 : EJMOriginalGlobalDAGData.nodes 11 ⟨701649, by decide⟩ =
    .split (coordinate 10) (![⟨701589, by decide⟩,⟨701610, by decide⟩,⟨701628, by decide⟩,⟨701648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5741_701649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5741 ⟨701649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5741
    ⟨701649, by decide⟩ (by decide) (![⟨701589, by decide⟩,⟨701610, by decide⟩,⟨701628, by decide⟩,⟨701648, by decide⟩]) unmarked_context_10_5741_701649 node_context_10_5741_701649
  intro a
  fin_cases a
  · exact context_11_22964_701589
  · exact context_11_22965_701610
  · exact context_11_22966_701628
  · exact context_11_22967_701648

theorem selected_cut_27774 : selected 11 ⟨701701, by decide⟩
    (prefixPartial 10 5742) = some ⟨10, 2, 0, 701701, 5742, 4085, 1048576⟩ := by
  decide +kernel

theorem context_10_5742_701701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5742 ⟨701701, by decide⟩ :=
  accepted_of_selected 10 5742 ⟨701701, by decide⟩ ⟨10, 2, 0, 701701, 5742, 4085, 1048576⟩
    (by decide) selected_cut_27774

theorem selected_cut_27775 : selected 11 ⟨701737, by decide⟩
    (prefixPartial 10 5743) = some ⟨10, 2, 0, 701737, 5743, 1689, 1048576⟩ := by
  decide +kernel

theorem context_10_5743_701737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5743 ⟨701737, by decide⟩ :=
  accepted_of_selected 10 5743 ⟨701737, by decide⟩ ⟨10, 2, 0, 701737, 5743, 1689, 1048576⟩
    (by decide) selected_cut_27775

theorem unmarked_context_9_1435_701738 : frontier 12 ⟨701738, by decide⟩
    (prefixCache 9 1435) (prefixPartial 9 1435) = false := by
  decide +kernel

theorem node_context_9_1435_701738 : EJMOriginalGlobalDAGData.nodes 12 ⟨701738, by decide⟩ =
    .split (coordinate 9) (![⟨701568, by decide⟩,⟨701649, by decide⟩,⟨701701, by decide⟩,⟨701737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1435_701738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1435 ⟨701738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1435
    ⟨701738, by decide⟩ (by decide) (![⟨701568, by decide⟩,⟨701649, by decide⟩,⟨701701, by decide⟩,⟨701737, by decide⟩]) unmarked_context_9_1435_701738 node_context_9_1435_701738
  intro a
  fin_cases a
  · exact context_10_5740_701568
  · exact context_10_5741_701649
  · exact context_10_5742_701701
  · exact context_10_5743_701737

theorem unmarked_context_8_358_701739 : frontier 13 ⟨701739, by decide⟩
    (prefixCache 8 358) (prefixPartial 8 358) = false := by
  decide +kernel

theorem node_context_8_358_701739 : EJMOriginalGlobalDAGData.nodes 13 ⟨701739, by decide⟩ =
    .split (coordinate 8) (![⟨698118, by decide⟩,⟨700477, by decide⟩,⟨701444, by decide⟩,⟨701738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_358_701739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 358 ⟨701739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 358
    ⟨701739, by decide⟩ (by decide) (![⟨698118, by decide⟩,⟨700477, by decide⟩,⟨701444, by decide⟩,⟨701738, by decide⟩]) unmarked_context_8_358_701739 node_context_8_358_701739
  intro a
  fin_cases a
  · exact context_9_1432_698118
  · exact context_9_1433_700477
  · exact context_9_1434_701444
  · exact context_9_1435_701738

theorem selected_cut_27776 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 22976) = some ⟨11, 1, 0, 434745, 22976, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22976_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22976 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 22976 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 22976, 1, 262144⟩
    (by decide) selected_cut_27776

theorem selected_cut_27777 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91908) = some ⟨12, 1, 0, 448748, 91908, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91908_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91908 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91908 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91908, 1, 65536⟩
    (by decide) selected_cut_27777

theorem selected_cut_27778 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 91909) = some ⟨12, 1, 0, 34034, 91909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91909_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91909 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 91909 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 91909, 1, 65536⟩
    (by decide) selected_cut_27778

theorem selected_cut_27779 : selected 8 ⟨701821, by decide⟩
    (prefixPartial 13 367640) = some ⟨13, 2, 0, 701821, 367640, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_367640_701821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367640 ⟨701821, by decide⟩ :=
  accepted_of_selected 13 367640 ⟨701821, by decide⟩ ⟨13, 2, 0, 701821, 367640, 2749, 16384⟩
    (by decide) selected_cut_27779

theorem selected_cut_27780 : selected 8 ⟨701894, by decide⟩
    (prefixPartial 13 367641) = some ⟨13, 2, 0, 701894, 367641, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_367641_701894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367641 ⟨701894, by decide⟩ :=
  accepted_of_selected 13 367641 ⟨701894, by decide⟩ ⟨13, 2, 0, 701894, 367641, 1533, 16384⟩
    (by decide) selected_cut_27780

theorem selected_cut_27781 : selected 8 ⟨701907, by decide⟩
    (prefixPartial 13 367642) = some ⟨13, 2, 0, 701907, 367642, 585, 16384⟩ := by
  decide +kernel

theorem context_13_367642_701907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367642 ⟨701907, by decide⟩ :=
  accepted_of_selected 13 367642 ⟨701907, by decide⟩ ⟨13, 2, 0, 701907, 367642, 585, 16384⟩
    (by decide) selected_cut_27781

theorem selected_cut_27782 : selected 8 ⟨701910, by decide⟩
    (prefixPartial 13 367643) = some ⟨13, 2, 0, 701910, 367643, 97, 16384⟩ := by
  decide +kernel

theorem context_13_367643_701910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367643 ⟨701910, by decide⟩ :=
  accepted_of_selected 13 367643 ⟨701910, by decide⟩ ⟨13, 2, 0, 701910, 367643, 97, 16384⟩
    (by decide) selected_cut_27782

theorem unmarked_context_12_91910_701911 : frontier 9 ⟨701911, by decide⟩
    (prefixCache 12 91910) (prefixPartial 12 91910) = false := by
  decide +kernel

theorem node_context_12_91910_701911 : EJMOriginalGlobalDAGData.nodes 9 ⟨701911, by decide⟩ =
    .split (coordinate 12) (![⟨701821, by decide⟩,⟨701894, by decide⟩,⟨701907, by decide⟩,⟨701910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91910_701911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91910 ⟨701911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91910
    ⟨701911, by decide⟩ (by decide) (![⟨701821, by decide⟩,⟨701894, by decide⟩,⟨701907, by decide⟩,⟨701910, by decide⟩]) unmarked_context_12_91910_701911 node_context_12_91910_701911
  intro a
  fin_cases a
  · exact context_13_367640_701821
  · exact context_13_367641_701894
  · exact context_13_367642_701907
  · exact context_13_367643_701910

theorem selected_cut_27783 : selected 9 ⟨334876, by decide⟩
    (prefixPartial 12 91911) = some ⟨12, 1, 0, 334876, 91911, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91911_334876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91911 ⟨334876, by decide⟩ :=
  accepted_of_selected 12 91911 ⟨334876, by decide⟩ ⟨12, 1, 0, 334876, 91911, 1, 65536⟩
    (by decide) selected_cut_27783

theorem unmarked_context_11_22977_701912 : frontier 10 ⟨701912, by decide⟩
    (prefixCache 11 22977) (prefixPartial 11 22977) = false := by
  decide +kernel

theorem node_context_11_22977_701912 : EJMOriginalGlobalDAGData.nodes 10 ⟨701912, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨701911, by decide⟩,⟨334876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22977_701912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22977 ⟨701912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22977
    ⟨701912, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨701911, by decide⟩,⟨334876, by decide⟩]) unmarked_context_11_22977_701912 node_context_11_22977_701912
  intro a
  fin_cases a
  · exact context_12_91908_448748
  · exact context_12_91909_34034
  · exact context_12_91910_701911
  · exact context_12_91911_334876

theorem selected_cut_27784 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91912) = some ⟨12, 1, 0, 448748, 91912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91912_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91912 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91912 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91912, 1, 65536⟩
    (by decide) selected_cut_27784

theorem selected_cut_27785 : selected 8 ⟨702014, by decide⟩
    (prefixPartial 13 367652) = some ⟨13, 2, 0, 702014, 367652, 3969, 16384⟩ := by
  decide +kernel

theorem context_13_367652_702014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367652 ⟨702014, by decide⟩ :=
  accepted_of_selected 13 367652 ⟨702014, by decide⟩ ⟨13, 2, 0, 702014, 367652, 3969, 16384⟩
    (by decide) selected_cut_27785

theorem selected_cut_27786 : selected 8 ⟨702131, by decide⟩
    (prefixPartial 13 367653) = some ⟨13, 2, 0, 702131, 367653, 3469, 16384⟩ := by
  decide +kernel

theorem context_13_367653_702131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367653 ⟨702131, by decide⟩ :=
  accepted_of_selected 13 367653 ⟨702131, by decide⟩ ⟨13, 2, 0, 702131, 367653, 3469, 16384⟩
    (by decide) selected_cut_27786

theorem selected_cut_27787 : selected 8 ⟨702183, by decide⟩
    (prefixPartial 13 367654) = some ⟨13, 2, 0, 702183, 367654, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_367654_702183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367654 ⟨702183, by decide⟩ :=
  accepted_of_selected 13 367654 ⟨702183, by decide⟩ ⟨13, 2, 0, 702183, 367654, 2449, 16384⟩
    (by decide) selected_cut_27787

theorem selected_cut_27788 : selected 8 ⟨702197, by decide⟩
    (prefixPartial 13 367655) = some ⟨13, 2, 0, 702197, 367655, 829, 16384⟩ := by
  decide +kernel

theorem context_13_367655_702197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367655 ⟨702197, by decide⟩ :=
  accepted_of_selected 13 367655 ⟨702197, by decide⟩ ⟨13, 2, 0, 702197, 367655, 829, 16384⟩
    (by decide) selected_cut_27788

theorem unmarked_context_12_91913_702198 : frontier 9 ⟨702198, by decide⟩
    (prefixCache 12 91913) (prefixPartial 12 91913) = false := by
  decide +kernel

theorem node_context_12_91913_702198 : EJMOriginalGlobalDAGData.nodes 9 ⟨702198, by decide⟩ =
    .split (coordinate 12) (![⟨702014, by decide⟩,⟨702131, by decide⟩,⟨702183, by decide⟩,⟨702197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91913_702198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91913 ⟨702198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91913
    ⟨702198, by decide⟩ (by decide) (![⟨702014, by decide⟩,⟨702131, by decide⟩,⟨702183, by decide⟩,⟨702197, by decide⟩]) unmarked_context_12_91913_702198 node_context_12_91913_702198
  intro a
  fin_cases a
  · exact context_13_367652_702014
  · exact context_13_367653_702131
  · exact context_13_367654_702183
  · exact context_13_367655_702197

theorem selected_cut_27789 : selected 8 ⟨702259, by decide⟩
    (prefixPartial 13 367656) = some ⟨13, 2, 0, 702259, 367656, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_367656_702259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367656 ⟨702259, by decide⟩ :=
  accepted_of_selected 13 367656 ⟨702259, by decide⟩ ⟨13, 2, 0, 702259, 367656, 3441, 16384⟩
    (by decide) selected_cut_27789

theorem selected_cut_27790 : selected 8 ⟨702337, by decide⟩
    (prefixPartial 13 367657) = some ⟨13, 2, 0, 702337, 367657, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_367657_702337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367657 ⟨702337, by decide⟩ :=
  accepted_of_selected 13 367657 ⟨702337, by decide⟩ ⟨13, 2, 0, 702337, 367657, 3317, 16384⟩
    (by decide) selected_cut_27790

theorem selected_cut_27791 : selected 8 ⟨702368, by decide⟩
    (prefixPartial 13 367658) = some ⟨13, 2, 0, 702368, 367658, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_367658_702368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367658 ⟨702368, by decide⟩ :=
  accepted_of_selected 13 367658 ⟨702368, by decide⟩ ⟨13, 2, 0, 702368, 367658, 2281, 16384⟩
    (by decide) selected_cut_27791

theorem selected_cut_27792 : selected 8 ⟨702379, by decide⟩
    (prefixPartial 13 367659) = some ⟨13, 2, 0, 702379, 367659, 841, 16384⟩ := by
  decide +kernel

theorem context_13_367659_702379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367659 ⟨702379, by decide⟩ :=
  accepted_of_selected 13 367659 ⟨702379, by decide⟩ ⟨13, 2, 0, 702379, 367659, 841, 16384⟩
    (by decide) selected_cut_27792

theorem unmarked_context_12_91914_702380 : frontier 9 ⟨702380, by decide⟩
    (prefixCache 12 91914) (prefixPartial 12 91914) = false := by
  decide +kernel

theorem node_context_12_91914_702380 : EJMOriginalGlobalDAGData.nodes 9 ⟨702380, by decide⟩ =
    .split (coordinate 12) (![⟨702259, by decide⟩,⟨702337, by decide⟩,⟨702368, by decide⟩,⟨702379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91914_702380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91914 ⟨702380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91914
    ⟨702380, by decide⟩ (by decide) (![⟨702259, by decide⟩,⟨702337, by decide⟩,⟨702368, by decide⟩,⟨702379, by decide⟩]) unmarked_context_12_91914_702380 node_context_12_91914_702380
  intro a
  fin_cases a
  · exact context_13_367656_702259
  · exact context_13_367657_702337
  · exact context_13_367658_702368
  · exact context_13_367659_702379

theorem selected_cut_27793 : selected 8 ⟨702445, by decide⟩
    (prefixPartial 13 367660) = some ⟨13, 2, 0, 702445, 367660, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_367660_702445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367660 ⟨702445, by decide⟩ :=
  accepted_of_selected 13 367660 ⟨702445, by decide⟩ ⟨13, 2, 0, 702445, 367660, 3221, 16384⟩
    (by decide) selected_cut_27793

theorem selected_cut_27794 : selected 8 ⟨702536, by decide⟩
    (prefixPartial 13 367661) = some ⟨13, 2, 0, 702536, 367661, 3577, 16384⟩ := by
  decide +kernel

theorem context_13_367661_702536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367661 ⟨702536, by decide⟩ :=
  accepted_of_selected 13 367661 ⟨702536, by decide⟩ ⟨13, 2, 0, 702536, 367661, 3577, 16384⟩
    (by decide) selected_cut_27794

theorem selected_cut_27795 : selected 8 ⟨702576, by decide⟩
    (prefixPartial 13 367662) = some ⟨13, 2, 0, 702576, 367662, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_367662_702576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367662 ⟨702576, by decide⟩ :=
  accepted_of_selected 13 367662 ⟨702576, by decide⟩ ⟨13, 2, 0, 702576, 367662, 2477, 16384⟩
    (by decide) selected_cut_27795

theorem selected_cut_27796 : selected 8 ⟨702583, by decide⟩
    (prefixPartial 13 367663) = some ⟨13, 2, 0, 702583, 367663, 769, 16384⟩ := by
  decide +kernel

theorem context_13_367663_702583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367663 ⟨702583, by decide⟩ :=
  accepted_of_selected 13 367663 ⟨702583, by decide⟩ ⟨13, 2, 0, 702583, 367663, 769, 16384⟩
    (by decide) selected_cut_27796

theorem unmarked_context_12_91915_702584 : frontier 9 ⟨702584, by decide⟩
    (prefixCache 12 91915) (prefixPartial 12 91915) = false := by
  decide +kernel

theorem node_context_12_91915_702584 : EJMOriginalGlobalDAGData.nodes 9 ⟨702584, by decide⟩ =
    .split (coordinate 12) (![⟨702445, by decide⟩,⟨702536, by decide⟩,⟨702576, by decide⟩,⟨702583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91915_702584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91915 ⟨702584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91915
    ⟨702584, by decide⟩ (by decide) (![⟨702445, by decide⟩,⟨702536, by decide⟩,⟨702576, by decide⟩,⟨702583, by decide⟩]) unmarked_context_12_91915_702584 node_context_12_91915_702584
  intro a
  fin_cases a
  · exact context_13_367660_702445
  · exact context_13_367661_702536
  · exact context_13_367662_702576
  · exact context_13_367663_702583

theorem unmarked_context_11_22978_702585 : frontier 10 ⟨702585, by decide⟩
    (prefixCache 11 22978) (prefixPartial 11 22978) = false := by
  decide +kernel

theorem node_context_11_22978_702585 : EJMOriginalGlobalDAGData.nodes 10 ⟨702585, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨702198, by decide⟩,⟨702380, by decide⟩,⟨702584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22978_702585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22978 ⟨702585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22978
    ⟨702585, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨702198, by decide⟩,⟨702380, by decide⟩,⟨702584, by decide⟩]) unmarked_context_11_22978_702585 node_context_11_22978_702585
  intro a
  fin_cases a
  · exact context_12_91912_448748
  · exact context_12_91913_702198
  · exact context_12_91914_702380
  · exact context_12_91915_702584

theorem selected_cut_27797 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91916) = some ⟨12, 1, 0, 448748, 91916, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91916_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91916 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91916 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91916, 1, 65536⟩
    (by decide) selected_cut_27797

theorem selected_cut_27798 : selected 9 ⟨292651, by decide⟩
    (prefixPartial 12 91917) = some ⟨12, 1, 0, 292651, 91917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91917_292651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91917 ⟨292651, by decide⟩ :=
  accepted_of_selected 12 91917 ⟨292651, by decide⟩ ⟨12, 1, 0, 292651, 91917, 1, 65536⟩
    (by decide) selected_cut_27798

theorem selected_cut_27799 : selected 8 ⟨702655, by decide⟩
    (prefixPartial 13 367672) = some ⟨13, 2, 0, 702655, 367672, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_367672_702655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367672 ⟨702655, by decide⟩ :=
  accepted_of_selected 13 367672 ⟨702655, by decide⟩ ⟨13, 2, 0, 702655, 367672, 3333, 16384⟩
    (by decide) selected_cut_27799

theorem selected_cut_27800 : selected 8 ⟨702722, by decide⟩
    (prefixPartial 13 367673) = some ⟨13, 2, 0, 702722, 367673, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_367673_702722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367673 ⟨702722, by decide⟩ :=
  accepted_of_selected 13 367673 ⟨702722, by decide⟩ ⟨13, 2, 0, 702722, 367673, 3033, 16384⟩
    (by decide) selected_cut_27800

theorem selected_cut_27801 : selected 8 ⟨702745, by decide⟩
    (prefixPartial 13 367674) = some ⟨13, 2, 0, 702745, 367674, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_367674_702745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367674 ⟨702745, by decide⟩ :=
  accepted_of_selected 13 367674 ⟨702745, by decide⟩ ⟨13, 2, 0, 702745, 367674, 1737, 16384⟩
    (by decide) selected_cut_27801

theorem selected_cut_27802 : selected 8 ⟨702758, by decide⟩
    (prefixPartial 13 367675) = some ⟨13, 2, 0, 702758, 367675, 801, 16384⟩ := by
  decide +kernel

theorem context_13_367675_702758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367675 ⟨702758, by decide⟩ :=
  accepted_of_selected 13 367675 ⟨702758, by decide⟩ ⟨13, 2, 0, 702758, 367675, 801, 16384⟩
    (by decide) selected_cut_27802

theorem unmarked_context_12_91918_702759 : frontier 9 ⟨702759, by decide⟩
    (prefixCache 12 91918) (prefixPartial 12 91918) = false := by
  decide +kernel

theorem node_context_12_91918_702759 : EJMOriginalGlobalDAGData.nodes 9 ⟨702759, by decide⟩ =
    .split (coordinate 12) (![⟨702655, by decide⟩,⟨702722, by decide⟩,⟨702745, by decide⟩,⟨702758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91918_702759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91918 ⟨702759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91918
    ⟨702759, by decide⟩ (by decide) (![⟨702655, by decide⟩,⟨702722, by decide⟩,⟨702745, by decide⟩,⟨702758, by decide⟩]) unmarked_context_12_91918_702759 node_context_12_91918_702759
  intro a
  fin_cases a
  · exact context_13_367672_702655
  · exact context_13_367673_702722
  · exact context_13_367674_702745
  · exact context_13_367675_702758

theorem selected_cut_27803 : selected 7 ⟨702767, by decide⟩
    (prefixPartial 14 1470704) = some ⟨14, 2, 0, 702767, 1470704, 309, 4096⟩ := by
  decide +kernel

theorem context_14_1470704_702767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470704 ⟨702767, by decide⟩ :=
  accepted_of_selected 14 1470704 ⟨702767, by decide⟩ ⟨14, 2, 0, 702767, 1470704, 309, 4096⟩
    (by decide) selected_cut_27803

theorem selected_cut_27804 : selected 7 ⟨702811, by decide⟩
    (prefixPartial 14 1470705) = some ⟨14, 2, 0, 702811, 1470705, 1649, 4096⟩ := by
  decide +kernel

theorem context_14_1470705_702811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470705 ⟨702811, by decide⟩ :=
  accepted_of_selected 14 1470705 ⟨702811, by decide⟩ ⟨14, 2, 0, 702811, 1470705, 1649, 4096⟩
    (by decide) selected_cut_27804

theorem selected_cut_27805 : selected 7 ⟨702847, by decide⟩
    (prefixPartial 14 1470706) = some ⟨14, 2, 0, 702847, 1470706, 1745, 4096⟩ := by
  decide +kernel

theorem context_14_1470706_702847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470706 ⟨702847, by decide⟩ :=
  accepted_of_selected 14 1470706 ⟨702847, by decide⟩ ⟨14, 2, 0, 702847, 1470706, 1745, 4096⟩
    (by decide) selected_cut_27805

theorem selected_cut_27806 : selected 7 ⟨702872, by decide⟩
    (prefixPartial 14 1470707) = some ⟨14, 2, 0, 702872, 1470707, 1233, 4096⟩ := by
  decide +kernel

theorem context_14_1470707_702872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470707 ⟨702872, by decide⟩ :=
  accepted_of_selected 14 1470707 ⟨702872, by decide⟩ ⟨14, 2, 0, 702872, 1470707, 1233, 4096⟩
    (by decide) selected_cut_27806

theorem unmarked_context_13_367676_702873 : frontier 8 ⟨702873, by decide⟩
    (prefixCache 13 367676) (prefixPartial 13 367676) = false := by
  decide +kernel

theorem node_context_13_367676_702873 : EJMOriginalGlobalDAGData.nodes 8 ⟨702873, by decide⟩ =
    .split (coordinate 13) (![⟨702767, by decide⟩,⟨702811, by decide⟩,⟨702847, by decide⟩,⟨702872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_367676_702873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367676 ⟨702873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 367676
    ⟨702873, by decide⟩ (by decide) (![⟨702767, by decide⟩,⟨702811, by decide⟩,⟨702847, by decide⟩,⟨702872, by decide⟩]) unmarked_context_13_367676_702873 node_context_13_367676_702873
  intro a
  fin_cases a
  · exact context_14_1470704_702767
  · exact context_14_1470705_702811
  · exact context_14_1470706_702847
  · exact context_14_1470707_702872

theorem selected_cut_27807 : selected 7 ⟨702904, by decide⟩
    (prefixPartial 14 1470708) = some ⟨14, 2, 0, 702904, 1470708, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_1470708_702904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470708 ⟨702904, by decide⟩ :=
  accepted_of_selected 14 1470708 ⟨702904, by decide⟩ ⟨14, 2, 0, 702904, 1470708, 1429, 4096⟩
    (by decide) selected_cut_27807

theorem selected_cut_27808 : selected 7 ⟨702929, by decide⟩
    (prefixPartial 14 1470709) = some ⟨14, 2, 0, 702929, 1470709, 821, 4096⟩ := by
  decide +kernel

theorem context_14_1470709_702929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470709 ⟨702929, by decide⟩ :=
  accepted_of_selected 14 1470709 ⟨702929, by decide⟩ ⟨14, 2, 0, 702929, 1470709, 821, 4096⟩
    (by decide) selected_cut_27808

theorem selected_cut_27809 : selected 7 ⟨702980, by decide⟩
    (prefixPartial 14 1470710) = some ⟨14, 2, 0, 702980, 1470710, 1645, 4096⟩ := by
  decide +kernel

theorem context_14_1470710_702980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470710 ⟨702980, by decide⟩ :=
  accepted_of_selected 14 1470710 ⟨702980, by decide⟩ ⟨14, 2, 0, 702980, 1470710, 1645, 4096⟩
    (by decide) selected_cut_27809

theorem selected_cut_27810 : selected 7 ⟨703005, by decide⟩
    (prefixPartial 14 1470711) = some ⟨14, 2, 0, 703005, 1470711, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_1470711_703005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1470711 ⟨703005, by decide⟩ :=
  accepted_of_selected 14 1470711 ⟨703005, by decide⟩ ⟨14, 2, 0, 703005, 1470711, 1113, 4096⟩
    (by decide) selected_cut_27810

theorem unmarked_context_13_367677_703006 : frontier 8 ⟨703006, by decide⟩
    (prefixCache 13 367677) (prefixPartial 13 367677) = false := by
  decide +kernel

theorem node_context_13_367677_703006 : EJMOriginalGlobalDAGData.nodes 8 ⟨703006, by decide⟩ =
    .split (coordinate 13) (![⟨702904, by decide⟩,⟨702929, by decide⟩,⟨702980, by decide⟩,⟨703005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_367677_703006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367677 ⟨703006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 367677
    ⟨703006, by decide⟩ (by decide) (![⟨702904, by decide⟩,⟨702929, by decide⟩,⟨702980, by decide⟩,⟨703005, by decide⟩]) unmarked_context_13_367677_703006 node_context_13_367677_703006
  intro a
  fin_cases a
  · exact context_14_1470708_702904
  · exact context_14_1470709_702929
  · exact context_14_1470710_702980
  · exact context_14_1470711_703005

theorem selected_cut_27811 : selected 8 ⟨703102, by decide⟩
    (prefixPartial 13 367678) = some ⟨13, 2, 0, 703102, 367678, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_367678_703102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367678 ⟨703102, by decide⟩ :=
  accepted_of_selected 13 367678 ⟨703102, by decide⟩ ⟨13, 2, 0, 703102, 367678, 3457, 16384⟩
    (by decide) selected_cut_27811

theorem selected_cut_27812 : selected 8 ⟨703136, by decide⟩
    (prefixPartial 13 367679) = some ⟨13, 2, 0, 703136, 367679, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_367679_703136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367679 ⟨703136, by decide⟩ :=
  accepted_of_selected 13 367679 ⟨703136, by decide⟩ ⟨13, 2, 0, 703136, 367679, 1157, 16384⟩
    (by decide) selected_cut_27812

theorem unmarked_context_12_91919_703137 : frontier 9 ⟨703137, by decide⟩
    (prefixCache 12 91919) (prefixPartial 12 91919) = false := by
  decide +kernel

theorem node_context_12_91919_703137 : EJMOriginalGlobalDAGData.nodes 9 ⟨703137, by decide⟩ =
    .split (coordinate 12) (![⟨702873, by decide⟩,⟨703006, by decide⟩,⟨703102, by decide⟩,⟨703136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91919_703137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91919 ⟨703137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91919
    ⟨703137, by decide⟩ (by decide) (![⟨702873, by decide⟩,⟨703006, by decide⟩,⟨703102, by decide⟩,⟨703136, by decide⟩]) unmarked_context_12_91919_703137 node_context_12_91919_703137
  intro a
  fin_cases a
  · exact context_13_367676_702873
  · exact context_13_367677_703006
  · exact context_13_367678_703102
  · exact context_13_367679_703136

theorem unmarked_context_11_22979_703138 : frontier 10 ⟨703138, by decide⟩
    (prefixCache 11 22979) (prefixPartial 11 22979) = false := by
  decide +kernel

theorem node_context_11_22979_703138 : EJMOriginalGlobalDAGData.nodes 10 ⟨703138, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨292651, by decide⟩,⟨702759, by decide⟩,⟨703137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22979_703138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22979 ⟨703138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22979
    ⟨703138, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨292651, by decide⟩,⟨702759, by decide⟩,⟨703137, by decide⟩]) unmarked_context_11_22979_703138 node_context_11_22979_703138
  intro a
  fin_cases a
  · exact context_12_91916_448748
  · exact context_12_91917_292651
  · exact context_12_91918_702759
  · exact context_12_91919_703137

theorem unmarked_context_10_5744_703139 : frontier 11 ⟨703139, by decide⟩
    (prefixCache 10 5744) (prefixPartial 10 5744) = false := by
  decide +kernel

theorem node_context_10_5744_703139 : EJMOriginalGlobalDAGData.nodes 11 ⟨703139, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨701912, by decide⟩,⟨702585, by decide⟩,⟨703138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5744_703139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5744 ⟨703139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5744
    ⟨703139, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨701912, by decide⟩,⟨702585, by decide⟩,⟨703138, by decide⟩]) unmarked_context_10_5744_703139 node_context_10_5744_703139
  intro a
  fin_cases a
  · exact context_11_22976_434745
  · exact context_11_22977_701912
  · exact context_11_22978_702585
  · exact context_11_22979_703138

theorem selected_cut_27813 : selected 8 ⟨703167, by decide⟩
    (prefixPartial 13 367680) = some ⟨13, 2, 0, 703167, 367680, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_367680_703167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367680 ⟨703167, by decide⟩ :=
  accepted_of_selected 13 367680 ⟨703167, by decide⟩ ⟨13, 2, 0, 703167, 367680, 1973, 16384⟩
    (by decide) selected_cut_27813

theorem selected_cut_27814 : selected 8 ⟨703186, by decide⟩
    (prefixPartial 13 367681) = some ⟨13, 2, 0, 703186, 367681, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_367681_703186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367681 ⟨703186, by decide⟩ :=
  accepted_of_selected 13 367681 ⟨703186, by decide⟩ ⟨13, 2, 0, 703186, 367681, 1333, 16384⟩
    (by decide) selected_cut_27814

theorem selected_cut_27815 : selected 8 ⟨703203, by decide⟩
    (prefixPartial 13 367682) = some ⟨13, 2, 0, 703203, 367682, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_367682_703203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367682 ⟨703203, by decide⟩ :=
  accepted_of_selected 13 367682 ⟨703203, by decide⟩ ⟨13, 2, 0, 703203, 367682, 1397, 16384⟩
    (by decide) selected_cut_27815

theorem selected_cut_27816 : selected 8 ⟨703209, by decide⟩
    (prefixPartial 13 367683) = some ⟨13, 2, 0, 703209, 367683, 669, 16384⟩ := by
  decide +kernel

theorem context_13_367683_703209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367683 ⟨703209, by decide⟩ :=
  accepted_of_selected 13 367683 ⟨703209, by decide⟩ ⟨13, 2, 0, 703209, 367683, 669, 16384⟩
    (by decide) selected_cut_27816

theorem unmarked_context_12_91920_703210 : frontier 9 ⟨703210, by decide⟩
    (prefixCache 12 91920) (prefixPartial 12 91920) = false := by
  decide +kernel

theorem node_context_12_91920_703210 : EJMOriginalGlobalDAGData.nodes 9 ⟨703210, by decide⟩ =
    .split (coordinate 12) (![⟨703167, by decide⟩,⟨703186, by decide⟩,⟨703203, by decide⟩,⟨703209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91920_703210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91920 ⟨703210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91920
    ⟨703210, by decide⟩ (by decide) (![⟨703167, by decide⟩,⟨703186, by decide⟩,⟨703203, by decide⟩,⟨703209, by decide⟩]) unmarked_context_12_91920_703210 node_context_12_91920_703210
  intro a
  fin_cases a
  · exact context_13_367680_703167
  · exact context_13_367681_703186
  · exact context_13_367682_703203
  · exact context_13_367683_703209

theorem selected_cut_27817 : selected 8 ⟨703245, by decide⟩
    (prefixPartial 13 367684) = some ⟨13, 2, 0, 703245, 367684, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_367684_703245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367684 ⟨703245, by decide⟩ :=
  accepted_of_selected 13 367684 ⟨703245, by decide⟩ ⟨13, 2, 0, 703245, 367684, 2297, 16384⟩
    (by decide) selected_cut_27817

theorem selected_cut_27818 : selected 8 ⟨703274, by decide⟩
    (prefixPartial 13 367685) = some ⟨13, 2, 0, 703274, 367685, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_367685_703274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367685 ⟨703274, by decide⟩ :=
  accepted_of_selected 13 367685 ⟨703274, by decide⟩ ⟨13, 2, 0, 703274, 367685, 1641, 16384⟩
    (by decide) selected_cut_27818

theorem selected_cut_27819 : selected 8 ⟨703297, by decide⟩
    (prefixPartial 13 367686) = some ⟨13, 2, 0, 703297, 367686, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_367686_703297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367686 ⟨703297, by decide⟩ :=
  accepted_of_selected 13 367686 ⟨703297, by decide⟩ ⟨13, 2, 0, 703297, 367686, 1629, 16384⟩
    (by decide) selected_cut_27819

theorem selected_cut_27820 : selected 8 ⟨703301, by decide⟩
    (prefixPartial 13 367687) = some ⟨13, 2, 0, 703301, 367687, 561, 16384⟩ := by
  decide +kernel

theorem context_13_367687_703301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367687 ⟨703301, by decide⟩ :=
  accepted_of_selected 13 367687 ⟨703301, by decide⟩ ⟨13, 2, 0, 703301, 367687, 561, 16384⟩
    (by decide) selected_cut_27820

theorem unmarked_context_12_91921_703302 : frontier 9 ⟨703302, by decide⟩
    (prefixCache 12 91921) (prefixPartial 12 91921) = false := by
  decide +kernel

theorem node_context_12_91921_703302 : EJMOriginalGlobalDAGData.nodes 9 ⟨703302, by decide⟩ =
    .split (coordinate 12) (![⟨703245, by decide⟩,⟨703274, by decide⟩,⟨703297, by decide⟩,⟨703301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91921_703302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91921 ⟨703302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91921
    ⟨703302, by decide⟩ (by decide) (![⟨703245, by decide⟩,⟨703274, by decide⟩,⟨703297, by decide⟩,⟨703301, by decide⟩]) unmarked_context_12_91921_703302 node_context_12_91921_703302
  intro a
  fin_cases a
  · exact context_13_367684_703245
  · exact context_13_367685_703274
  · exact context_13_367686_703297
  · exact context_13_367687_703301

theorem selected_cut_27821 : selected 8 ⟨703334, by decide⟩
    (prefixPartial 13 367688) = some ⟨13, 2, 0, 703334, 367688, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_367688_703334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367688 ⟨703334, by decide⟩ :=
  accepted_of_selected 13 367688 ⟨703334, by decide⟩ ⟨13, 2, 0, 703334, 367688, 1997, 16384⟩
    (by decide) selected_cut_27821

theorem selected_cut_27822 : selected 8 ⟨703360, by decide⟩
    (prefixPartial 13 367689) = some ⟨13, 2, 0, 703360, 367689, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_367689_703360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367689 ⟨703360, by decide⟩ :=
  accepted_of_selected 13 367689 ⟨703360, by decide⟩ ⟨13, 2, 0, 703360, 367689, 1589, 16384⟩
    (by decide) selected_cut_27822

theorem selected_cut_27823 : selected 8 ⟨703386, by decide⟩
    (prefixPartial 13 367690) = some ⟨13, 2, 0, 703386, 367690, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_367690_703386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367690 ⟨703386, by decide⟩ :=
  accepted_of_selected 13 367690 ⟨703386, by decide⟩ ⟨13, 2, 0, 703386, 367690, 1649, 16384⟩
    (by decide) selected_cut_27823

theorem selected_cut_27824 : selected 8 ⟨703392, by decide⟩
    (prefixPartial 13 367691) = some ⟨13, 2, 0, 703392, 367691, 657, 16384⟩ := by
  decide +kernel

theorem context_13_367691_703392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367691 ⟨703392, by decide⟩ :=
  accepted_of_selected 13 367691 ⟨703392, by decide⟩ ⟨13, 2, 0, 703392, 367691, 657, 16384⟩
    (by decide) selected_cut_27824

theorem unmarked_context_12_91922_703393 : frontier 9 ⟨703393, by decide⟩
    (prefixCache 12 91922) (prefixPartial 12 91922) = false := by
  decide +kernel

theorem node_context_12_91922_703393 : EJMOriginalGlobalDAGData.nodes 9 ⟨703393, by decide⟩ =
    .split (coordinate 12) (![⟨703334, by decide⟩,⟨703360, by decide⟩,⟨703386, by decide⟩,⟨703392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91922_703393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91922 ⟨703393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91922
    ⟨703393, by decide⟩ (by decide) (![⟨703334, by decide⟩,⟨703360, by decide⟩,⟨703386, by decide⟩,⟨703392, by decide⟩]) unmarked_context_12_91922_703393 node_context_12_91922_703393
  intro a
  fin_cases a
  · exact context_13_367688_703334
  · exact context_13_367689_703360
  · exact context_13_367690_703386
  · exact context_13_367691_703392

theorem selected_cut_27825 : selected 8 ⟨703424, by decide⟩
    (prefixPartial 13 367692) = some ⟨13, 2, 0, 703424, 367692, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_367692_703424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367692 ⟨703424, by decide⟩ :=
  accepted_of_selected 13 367692 ⟨703424, by decide⟩ ⟨13, 2, 0, 703424, 367692, 1745, 16384⟩
    (by decide) selected_cut_27825

theorem selected_cut_27826 : selected 8 ⟨703443, by decide⟩
    (prefixPartial 13 367693) = some ⟨13, 2, 0, 703443, 367693, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_367693_703443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367693 ⟨703443, by decide⟩ :=
  accepted_of_selected 13 367693 ⟨703443, by decide⟩ ⟨13, 2, 0, 703443, 367693, 1533, 16384⟩
    (by decide) selected_cut_27826

theorem selected_cut_27827 : selected 8 ⟨703469, by decide⟩
    (prefixPartial 13 367694) = some ⟨13, 2, 0, 703469, 367694, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_367694_703469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367694 ⟨703469, by decide⟩ :=
  accepted_of_selected 13 367694 ⟨703469, by decide⟩ ⟨13, 2, 0, 703469, 367694, 1649, 16384⟩
    (by decide) selected_cut_27827

theorem selected_cut_27828 : selected 8 ⟨703472, by decide⟩
    (prefixPartial 13 367695) = some ⟨13, 2, 0, 703472, 367695, 573, 16384⟩ := by
  decide +kernel

theorem context_13_367695_703472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367695 ⟨703472, by decide⟩ :=
  accepted_of_selected 13 367695 ⟨703472, by decide⟩ ⟨13, 2, 0, 703472, 367695, 573, 16384⟩
    (by decide) selected_cut_27828

theorem unmarked_context_12_91923_703473 : frontier 9 ⟨703473, by decide⟩
    (prefixCache 12 91923) (prefixPartial 12 91923) = false := by
  decide +kernel

theorem node_context_12_91923_703473 : EJMOriginalGlobalDAGData.nodes 9 ⟨703473, by decide⟩ =
    .split (coordinate 12) (![⟨703424, by decide⟩,⟨703443, by decide⟩,⟨703469, by decide⟩,⟨703472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91923_703473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91923 ⟨703473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91923
    ⟨703473, by decide⟩ (by decide) (![⟨703424, by decide⟩,⟨703443, by decide⟩,⟨703469, by decide⟩,⟨703472, by decide⟩]) unmarked_context_12_91923_703473 node_context_12_91923_703473
  intro a
  fin_cases a
  · exact context_13_367692_703424
  · exact context_13_367693_703443
  · exact context_13_367694_703469
  · exact context_13_367695_703472

theorem unmarked_context_11_22980_703474 : frontier 10 ⟨703474, by decide⟩
    (prefixCache 11 22980) (prefixPartial 11 22980) = false := by
  decide +kernel

theorem node_context_11_22980_703474 : EJMOriginalGlobalDAGData.nodes 10 ⟨703474, by decide⟩ =
    .split (coordinate 11) (![⟨703210, by decide⟩,⟨703302, by decide⟩,⟨703393, by decide⟩,⟨703473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22980_703474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22980 ⟨703474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22980
    ⟨703474, by decide⟩ (by decide) (![⟨703210, by decide⟩,⟨703302, by decide⟩,⟨703393, by decide⟩,⟨703473, by decide⟩]) unmarked_context_11_22980_703474 node_context_11_22980_703474
  intro a
  fin_cases a
  · exact context_12_91920_703210
  · exact context_12_91921_703302
  · exact context_12_91922_703393
  · exact context_12_91923_703473

theorem selected_cut_27829 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 91924) = some ⟨12, 1, 0, 308705, 91924, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91924_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91924 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 91924 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 91924, 1, 65536⟩
    (by decide) selected_cut_27829

theorem selected_cut_27830 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 91925) = some ⟨12, 1, 0, 308705, 91925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91925_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91925 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 91925 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 91925, 1, 65536⟩
    (by decide) selected_cut_27830

theorem selected_cut_27831 : selected 8 ⟨703530, by decide⟩
    (prefixPartial 13 367704) = some ⟨13, 2, 0, 703530, 367704, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_367704_703530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367704 ⟨703530, by decide⟩ :=
  accepted_of_selected 13 367704 ⟨703530, by decide⟩ ⟨13, 2, 0, 703530, 367704, 2965, 16384⟩
    (by decide) selected_cut_27831

theorem selected_cut_27832 : selected 8 ⟨703592, by decide⟩
    (prefixPartial 13 367705) = some ⟨13, 2, 0, 703592, 367705, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_367705_703592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367705 ⟨703592, by decide⟩ :=
  accepted_of_selected 13 367705 ⟨703592, by decide⟩ ⟨13, 2, 0, 703592, 367705, 2653, 16384⟩
    (by decide) selected_cut_27832

theorem selected_cut_27833 : selected 8 ⟨703621, by decide⟩
    (prefixPartial 13 367706) = some ⟨13, 2, 0, 703621, 367706, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_367706_703621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367706 ⟨703621, by decide⟩ :=
  accepted_of_selected 13 367706 ⟨703621, by decide⟩ ⟨13, 2, 0, 703621, 367706, 2133, 16384⟩
    (by decide) selected_cut_27833

theorem selected_cut_27834 : selected 8 ⟨703631, by decide⟩
    (prefixPartial 13 367707) = some ⟨13, 2, 0, 703631, 367707, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_367707_703631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367707 ⟨703631, by decide⟩ :=
  accepted_of_selected 13 367707 ⟨703631, by decide⟩ ⟨13, 2, 0, 703631, 367707, 1033, 16384⟩
    (by decide) selected_cut_27834

theorem unmarked_context_12_91926_703632 : frontier 9 ⟨703632, by decide⟩
    (prefixCache 12 91926) (prefixPartial 12 91926) = false := by
  decide +kernel

theorem node_context_12_91926_703632 : EJMOriginalGlobalDAGData.nodes 9 ⟨703632, by decide⟩ =
    .split (coordinate 12) (![⟨703530, by decide⟩,⟨703592, by decide⟩,⟨703621, by decide⟩,⟨703631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91926_703632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91926 ⟨703632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91926
    ⟨703632, by decide⟩ (by decide) (![⟨703530, by decide⟩,⟨703592, by decide⟩,⟨703621, by decide⟩,⟨703631, by decide⟩]) unmarked_context_12_91926_703632 node_context_12_91926_703632
  intro a
  fin_cases a
  · exact context_13_367704_703530
  · exact context_13_367705_703592
  · exact context_13_367706_703621
  · exact context_13_367707_703631

theorem selected_cut_27835 : selected 8 ⟨703676, by decide⟩
    (prefixPartial 13 367708) = some ⟨13, 2, 0, 703676, 367708, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_367708_703676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367708 ⟨703676, by decide⟩ :=
  accepted_of_selected 13 367708 ⟨703676, by decide⟩ ⟨13, 2, 0, 703676, 367708, 2645, 16384⟩
    (by decide) selected_cut_27835

theorem selected_cut_27836 : selected 8 ⟨703742, by decide⟩
    (prefixPartial 13 367709) = some ⟨13, 2, 0, 703742, 367709, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_367709_703742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367709 ⟨703742, by decide⟩ :=
  accepted_of_selected 13 367709 ⟨703742, by decide⟩ ⟨13, 2, 0, 703742, 367709, 2769, 16384⟩
    (by decide) selected_cut_27836

theorem selected_cut_27837 : selected 8 ⟨703787, by decide⟩
    (prefixPartial 13 367710) = some ⟨13, 2, 0, 703787, 367710, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_367710_703787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367710 ⟨703787, by decide⟩ :=
  accepted_of_selected 13 367710 ⟨703787, by decide⟩ ⟨13, 2, 0, 703787, 367710, 2325, 16384⟩
    (by decide) selected_cut_27837

theorem selected_cut_27838 : selected 8 ⟨703795, by decide⟩
    (prefixPartial 13 367711) = some ⟨13, 2, 0, 703795, 367711, 925, 16384⟩ := by
  decide +kernel

theorem context_13_367711_703795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367711 ⟨703795, by decide⟩ :=
  accepted_of_selected 13 367711 ⟨703795, by decide⟩ ⟨13, 2, 0, 703795, 367711, 925, 16384⟩
    (by decide) selected_cut_27838

theorem unmarked_context_12_91927_703796 : frontier 9 ⟨703796, by decide⟩
    (prefixCache 12 91927) (prefixPartial 12 91927) = false := by
  decide +kernel

theorem node_context_12_91927_703796 : EJMOriginalGlobalDAGData.nodes 9 ⟨703796, by decide⟩ =
    .split (coordinate 12) (![⟨703676, by decide⟩,⟨703742, by decide⟩,⟨703787, by decide⟩,⟨703795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91927_703796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91927 ⟨703796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91927
    ⟨703796, by decide⟩ (by decide) (![⟨703676, by decide⟩,⟨703742, by decide⟩,⟨703787, by decide⟩,⟨703795, by decide⟩]) unmarked_context_12_91927_703796 node_context_12_91927_703796
  intro a
  fin_cases a
  · exact context_13_367708_703676
  · exact context_13_367709_703742
  · exact context_13_367710_703787
  · exact context_13_367711_703795

theorem unmarked_context_11_22981_703797 : frontier 10 ⟨703797, by decide⟩
    (prefixCache 11 22981) (prefixPartial 11 22981) = false := by
  decide +kernel

theorem node_context_11_22981_703797 : EJMOriginalGlobalDAGData.nodes 10 ⟨703797, by decide⟩ =
    .split (coordinate 11) (![⟨308705, by decide⟩,⟨308705, by decide⟩,⟨703632, by decide⟩,⟨703796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22981_703797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22981 ⟨703797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22981
    ⟨703797, by decide⟩ (by decide) (![⟨308705, by decide⟩,⟨308705, by decide⟩,⟨703632, by decide⟩,⟨703796, by decide⟩]) unmarked_context_11_22981_703797 node_context_11_22981_703797
  intro a
  fin_cases a
  · exact context_12_91924_308705
  · exact context_12_91925_308705
  · exact context_12_91926_703632
  · exact context_12_91927_703796

theorem selected_cut_27839 : selected 8 ⟨703817, by decide⟩
    (prefixPartial 13 367712) = some ⟨13, 2, 0, 703817, 367712, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_367712_703817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367712 ⟨703817, by decide⟩ :=
  accepted_of_selected 13 367712 ⟨703817, by decide⟩ ⟨13, 2, 0, 703817, 367712, 1589, 16384⟩
    (by decide) selected_cut_27839

theorem selected_cut_27840 : selected 8 ⟨703847, by decide⟩
    (prefixPartial 13 367713) = some ⟨13, 2, 0, 703847, 367713, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_367713_703847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367713 ⟨703847, by decide⟩ :=
  accepted_of_selected 13 367713 ⟨703847, by decide⟩ ⟨13, 2, 0, 703847, 367713, 1529, 16384⟩
    (by decide) selected_cut_27840

theorem selected_cut_27841 : selected 8 ⟨703866, by decide⟩
    (prefixPartial 13 367714) = some ⟨13, 2, 0, 703866, 367714, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_367714_703866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367714 ⟨703866, by decide⟩ :=
  accepted_of_selected 13 367714 ⟨703866, by decide⟩ ⟨13, 2, 0, 703866, 367714, 1673, 16384⟩
    (by decide) selected_cut_27841

theorem selected_cut_27842 : selected 8 ⟨703875, by decide⟩
    (prefixPartial 13 367715) = some ⟨13, 2, 0, 703875, 367715, 729, 16384⟩ := by
  decide +kernel

theorem context_13_367715_703875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367715 ⟨703875, by decide⟩ :=
  accepted_of_selected 13 367715 ⟨703875, by decide⟩ ⟨13, 2, 0, 703875, 367715, 729, 16384⟩
    (by decide) selected_cut_27842

theorem unmarked_context_12_91928_703876 : frontier 9 ⟨703876, by decide⟩
    (prefixCache 12 91928) (prefixPartial 12 91928) = false := by
  decide +kernel

theorem node_context_12_91928_703876 : EJMOriginalGlobalDAGData.nodes 9 ⟨703876, by decide⟩ =
    .split (coordinate 12) (![⟨703817, by decide⟩,⟨703847, by decide⟩,⟨703866, by decide⟩,⟨703875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91928_703876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91928 ⟨703876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91928
    ⟨703876, by decide⟩ (by decide) (![⟨703817, by decide⟩,⟨703847, by decide⟩,⟨703866, by decide⟩,⟨703875, by decide⟩]) unmarked_context_12_91928_703876 node_context_12_91928_703876
  intro a
  fin_cases a
  · exact context_13_367712_703817
  · exact context_13_367713_703847
  · exact context_13_367714_703866
  · exact context_13_367715_703875

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
