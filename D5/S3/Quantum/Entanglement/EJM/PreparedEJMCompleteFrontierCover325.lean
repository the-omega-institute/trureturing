/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover324
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31203 : selected 7 ⟨796483, by decide⟩
    (prefixPartial 14 1691760) = some ⟨14, 2, 0, 796483, 1691760, 577, 4096⟩ := by
  decide +kernel

theorem context_14_1691760_796483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691760 ⟨796483, by decide⟩ :=
  accepted_of_selected 14 1691760 ⟨796483, by decide⟩ ⟨14, 2, 0, 796483, 1691760, 577, 4096⟩
    (by decide) selected_cut_31203

theorem selected_cut_31204 : selected 7 ⟨796523, by decide⟩
    (prefixPartial 14 1691761) = some ⟨14, 2, 0, 796523, 1691761, 1381, 4096⟩ := by
  decide +kernel

theorem context_14_1691761_796523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691761 ⟨796523, by decide⟩ :=
  accepted_of_selected 14 1691761 ⟨796523, by decide⟩ ⟨14, 2, 0, 796523, 1691761, 1381, 4096⟩
    (by decide) selected_cut_31204

theorem selected_cut_31205 : selected 7 ⟨796592, by decide⟩
    (prefixPartial 14 1691762) = some ⟨14, 2, 0, 796592, 1691762, 1845, 4096⟩ := by
  decide +kernel

theorem context_14_1691762_796592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691762 ⟨796592, by decide⟩ :=
  accepted_of_selected 14 1691762 ⟨796592, by decide⟩ ⟨14, 2, 0, 796592, 1691762, 1845, 4096⟩
    (by decide) selected_cut_31205

theorem selected_cut_31206 : selected 7 ⟨796624, by decide⟩
    (prefixPartial 14 1691763) = some ⟨14, 2, 0, 796624, 1691763, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_1691763_796624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691763 ⟨796624, by decide⟩ :=
  accepted_of_selected 14 1691763 ⟨796624, by decide⟩ ⟨14, 2, 0, 796624, 1691763, 1169, 4096⟩
    (by decide) selected_cut_31206

theorem unmarked_context_13_422940_796625 : frontier 8 ⟨796625, by decide⟩
    (prefixCache 13 422940) (prefixPartial 13 422940) = false := by
  decide +kernel

theorem node_context_13_422940_796625 : EJMOriginalGlobalDAGData.nodes 8 ⟨796625, by decide⟩ =
    .split (coordinate 13) (![⟨796483, by decide⟩,⟨796523, by decide⟩,⟨796592, by decide⟩,⟨796624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_422940_796625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422940 ⟨796625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 422940
    ⟨796625, by decide⟩ (by decide) (![⟨796483, by decide⟩,⟨796523, by decide⟩,⟨796592, by decide⟩,⟨796624, by decide⟩]) unmarked_context_13_422940_796625 node_context_13_422940_796625
  intro a
  fin_cases a
  · exact context_14_1691760_796483
  · exact context_14_1691761_796523
  · exact context_14_1691762_796592
  · exact context_14_1691763_796624

theorem selected_cut_31207 : selected 7 ⟨796662, by decide⟩
    (prefixPartial 14 1691764) = some ⟨14, 2, 0, 796662, 1691764, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_1691764_796662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691764 ⟨796662, by decide⟩ :=
  accepted_of_selected 14 1691764 ⟨796662, by decide⟩ ⟨14, 2, 0, 796662, 1691764, 1313, 4096⟩
    (by decide) selected_cut_31207

theorem selected_cut_31208 : selected 7 ⟨796699, by decide⟩
    (prefixPartial 14 1691765) = some ⟨14, 2, 0, 796699, 1691765, 1469, 4096⟩ := by
  decide +kernel

theorem context_14_1691765_796699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691765 ⟨796699, by decide⟩ :=
  accepted_of_selected 14 1691765 ⟨796699, by decide⟩ ⟨14, 2, 0, 796699, 1691765, 1469, 4096⟩
    (by decide) selected_cut_31208

theorem selected_cut_31209 : selected 7 ⟨796752, by decide⟩
    (prefixPartial 14 1691766) = some ⟨14, 2, 0, 796752, 1691766, 1765, 4096⟩ := by
  decide +kernel

theorem context_14_1691766_796752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691766 ⟨796752, by decide⟩ :=
  accepted_of_selected 14 1691766 ⟨796752, by decide⟩ ⟨14, 2, 0, 796752, 1691766, 1765, 4096⟩
    (by decide) selected_cut_31209

theorem selected_cut_31210 : selected 7 ⟨796788, by decide⟩
    (prefixPartial 14 1691767) = some ⟨14, 2, 0, 796788, 1691767, 1489, 4096⟩ := by
  decide +kernel

theorem context_14_1691767_796788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691767 ⟨796788, by decide⟩ :=
  accepted_of_selected 14 1691767 ⟨796788, by decide⟩ ⟨14, 2, 0, 796788, 1691767, 1489, 4096⟩
    (by decide) selected_cut_31210

theorem unmarked_context_13_422941_796789 : frontier 8 ⟨796789, by decide⟩
    (prefixCache 13 422941) (prefixPartial 13 422941) = false := by
  decide +kernel

theorem node_context_13_422941_796789 : EJMOriginalGlobalDAGData.nodes 8 ⟨796789, by decide⟩ =
    .split (coordinate 13) (![⟨796662, by decide⟩,⟨796699, by decide⟩,⟨796752, by decide⟩,⟨796788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_422941_796789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422941 ⟨796789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 422941
    ⟨796789, by decide⟩ (by decide) (![⟨796662, by decide⟩,⟨796699, by decide⟩,⟨796752, by decide⟩,⟨796788, by decide⟩]) unmarked_context_13_422941_796789 node_context_13_422941_796789
  intro a
  fin_cases a
  · exact context_14_1691764_796662
  · exact context_14_1691765_796699
  · exact context_14_1691766_796752
  · exact context_14_1691767_796788

theorem selected_cut_31211 : selected 8 ⟨796939, by decide⟩
    (prefixPartial 13 422942) = some ⟨13, 2, 0, 796939, 422942, 3353, 16384⟩ := by
  decide +kernel

theorem context_13_422942_796939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422942 ⟨796939, by decide⟩ :=
  accepted_of_selected 13 422942 ⟨796939, by decide⟩ ⟨13, 2, 0, 796939, 422942, 3353, 16384⟩
    (by decide) selected_cut_31211

theorem selected_cut_31212 : selected 8 ⟨797012, by decide⟩
    (prefixPartial 13 422943) = some ⟨13, 2, 0, 797012, 422943, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_422943_797012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422943 ⟨797012, by decide⟩ :=
  accepted_of_selected 13 422943 ⟨797012, by decide⟩ ⟨13, 2, 0, 797012, 422943, 1585, 16384⟩
    (by decide) selected_cut_31212

theorem unmarked_context_12_105735_797013 : frontier 9 ⟨797013, by decide⟩
    (prefixCache 12 105735) (prefixPartial 12 105735) = false := by
  decide +kernel

theorem node_context_12_105735_797013 : EJMOriginalGlobalDAGData.nodes 9 ⟨797013, by decide⟩ =
    .split (coordinate 12) (![⟨796625, by decide⟩,⟨796789, by decide⟩,⟨796939, by decide⟩,⟨797012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105735_797013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105735 ⟨797013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105735
    ⟨797013, by decide⟩ (by decide) (![⟨796625, by decide⟩,⟨796789, by decide⟩,⟨796939, by decide⟩,⟨797012, by decide⟩]) unmarked_context_12_105735_797013 node_context_12_105735_797013
  intro a
  fin_cases a
  · exact context_13_422940_796625
  · exact context_13_422941_796789
  · exact context_13_422942_796939
  · exact context_13_422943_797012

theorem unmarked_context_11_26433_797014 : frontier 10 ⟨797014, by decide⟩
    (prefixCache 11 26433) (prefixPartial 11 26433) = false := by
  decide +kernel

theorem node_context_11_26433_797014 : EJMOriginalGlobalDAGData.nodes 10 ⟨797014, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨796455, by decide⟩,⟨763842, by decide⟩,⟨797013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26433_797014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26433 ⟨797014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26433
    ⟨797014, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨796455, by decide⟩,⟨763842, by decide⟩,⟨797013, by decide⟩]) unmarked_context_11_26433_797014 node_context_11_26433_797014
  intro a
  fin_cases a
  · exact context_12_105732_14169
  · exact context_12_105733_796455
  · exact context_12_105734_763842
  · exact context_12_105735_797013

theorem selected_cut_31213 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105736) = some ⟨12, 1, 0, 14169, 105736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105736_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105736 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105736 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105736, 1, 65536⟩
    (by decide) selected_cut_31213

theorem selected_cut_31214 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105737) = some ⟨12, 1, 0, 14169, 105737, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105737_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105737 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105737 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105737, 1, 65536⟩
    (by decide) selected_cut_31214

theorem selected_cut_31215 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105738) = some ⟨12, 1, 0, 763842, 105738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105738_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105738 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105738 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105738, 1, 65536⟩
    (by decide) selected_cut_31215

theorem selected_cut_31216 : selected 7 ⟨797023, by decide⟩
    (prefixPartial 14 1691824) = some ⟨14, 2, 0, 797023, 1691824, 157, 4096⟩ := by
  decide +kernel

theorem context_14_1691824_797023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691824 ⟨797023, by decide⟩ :=
  accepted_of_selected 14 1691824 ⟨797023, by decide⟩ ⟨14, 2, 0, 797023, 1691824, 157, 4096⟩
    (by decide) selected_cut_31216

theorem selected_cut_31217 : selected 7 ⟨797069, by decide⟩
    (prefixPartial 14 1691825) = some ⟨14, 2, 0, 797069, 1691825, 1529, 4096⟩ := by
  decide +kernel

theorem context_14_1691825_797069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691825 ⟨797069, by decide⟩ :=
  accepted_of_selected 14 1691825 ⟨797069, by decide⟩ ⟨14, 2, 0, 797069, 1691825, 1529, 4096⟩
    (by decide) selected_cut_31217

theorem selected_cut_31218 : selected 7 ⟨797138, by decide⟩
    (prefixPartial 14 1691826) = some ⟨14, 2, 0, 797138, 1691826, 1981, 4096⟩ := by
  decide +kernel

theorem context_14_1691826_797138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691826 ⟨797138, by decide⟩ :=
  accepted_of_selected 14 1691826 ⟨797138, by decide⟩ ⟨14, 2, 0, 797138, 1691826, 1981, 4096⟩
    (by decide) selected_cut_31218

theorem selected_cut_31219 : selected 7 ⟨797183, by decide⟩
    (prefixPartial 14 1691827) = some ⟨14, 2, 0, 797183, 1691827, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_1691827_797183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691827 ⟨797183, by decide⟩ :=
  accepted_of_selected 14 1691827 ⟨797183, by decide⟩ ⟨14, 2, 0, 797183, 1691827, 1229, 4096⟩
    (by decide) selected_cut_31219

theorem unmarked_context_13_422956_797184 : frontier 8 ⟨797184, by decide⟩
    (prefixCache 13 422956) (prefixPartial 13 422956) = false := by
  decide +kernel

theorem node_context_13_422956_797184 : EJMOriginalGlobalDAGData.nodes 8 ⟨797184, by decide⟩ =
    .split (coordinate 13) (![⟨797023, by decide⟩,⟨797069, by decide⟩,⟨797138, by decide⟩,⟨797183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_422956_797184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422956 ⟨797184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 422956
    ⟨797184, by decide⟩ (by decide) (![⟨797023, by decide⟩,⟨797069, by decide⟩,⟨797138, by decide⟩,⟨797183, by decide⟩]) unmarked_context_13_422956_797184 node_context_13_422956_797184
  intro a
  fin_cases a
  · exact context_14_1691824_797023
  · exact context_14_1691825_797069
  · exact context_14_1691826_797138
  · exact context_14_1691827_797183

theorem selected_cut_31220 : selected 8 ⟨797353, by decide⟩
    (prefixPartial 13 422957) = some ⟨13, 2, 0, 797353, 422957, 3445, 16384⟩ := by
  decide +kernel

theorem context_13_422957_797353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422957 ⟨797353, by decide⟩ :=
  accepted_of_selected 13 422957 ⟨797353, by decide⟩ ⟨13, 2, 0, 797353, 422957, 3445, 16384⟩
    (by decide) selected_cut_31220

theorem selected_cut_31221 : selected 8 ⟨797425, by decide⟩
    (prefixPartial 13 422958) = some ⟨13, 2, 0, 797425, 422958, 909, 16384⟩ := by
  decide +kernel

theorem context_13_422958_797425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422958 ⟨797425, by decide⟩ :=
  accepted_of_selected 13 422958 ⟨797425, by decide⟩ ⟨13, 2, 0, 797425, 422958, 909, 16384⟩
    (by decide) selected_cut_31221

theorem selected_cut_31222 : selected 8 ⟨797443, by decide⟩
    (prefixPartial 13 422959) = some ⟨13, 2, 0, 797443, 422959, 169, 16384⟩ := by
  decide +kernel

theorem context_13_422959_797443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422959 ⟨797443, by decide⟩ :=
  accepted_of_selected 13 422959 ⟨797443, by decide⟩ ⟨13, 2, 0, 797443, 422959, 169, 16384⟩
    (by decide) selected_cut_31222

theorem unmarked_context_12_105739_797444 : frontier 9 ⟨797444, by decide⟩
    (prefixCache 12 105739) (prefixPartial 12 105739) = false := by
  decide +kernel

theorem node_context_12_105739_797444 : EJMOriginalGlobalDAGData.nodes 9 ⟨797444, by decide⟩ =
    .split (coordinate 12) (![⟨797184, by decide⟩,⟨797353, by decide⟩,⟨797425, by decide⟩,⟨797443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105739_797444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105739 ⟨797444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105739
    ⟨797444, by decide⟩ (by decide) (![⟨797184, by decide⟩,⟨797353, by decide⟩,⟨797425, by decide⟩,⟨797443, by decide⟩]) unmarked_context_12_105739_797444 node_context_12_105739_797444
  intro a
  fin_cases a
  · exact context_13_422956_797184
  · exact context_13_422957_797353
  · exact context_13_422958_797425
  · exact context_13_422959_797443

theorem unmarked_context_11_26434_797445 : frontier 10 ⟨797445, by decide⟩
    (prefixCache 11 26434) (prefixPartial 11 26434) = false := by
  decide +kernel

theorem node_context_11_26434_797445 : EJMOriginalGlobalDAGData.nodes 10 ⟨797445, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨14169, by decide⟩,⟨763842, by decide⟩,⟨797444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26434_797445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26434 ⟨797445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26434
    ⟨797445, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨14169, by decide⟩,⟨763842, by decide⟩,⟨797444, by decide⟩]) unmarked_context_11_26434_797445 node_context_11_26434_797445
  intro a
  fin_cases a
  · exact context_12_105736_14169
  · exact context_12_105737_14169
  · exact context_12_105738_763842
  · exact context_12_105739_797444

theorem selected_cut_31223 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 26435) = some ⟨11, 1, 0, 789341, 26435, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26435_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26435 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 26435 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 26435, 1, 262144⟩
    (by decide) selected_cut_31223

theorem unmarked_context_10_6608_797446 : frontier 11 ⟨797446, by decide⟩
    (prefixCache 10 6608) (prefixPartial 10 6608) = false := by
  decide +kernel

theorem node_context_10_6608_797446 : EJMOriginalGlobalDAGData.nodes 11 ⟨797446, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨797014, by decide⟩,⟨797445, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6608_797446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6608 ⟨797446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6608
    ⟨797446, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨797014, by decide⟩,⟨797445, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6608_797446 node_context_10_6608_797446
  intro a
  fin_cases a
  · exact context_11_26432_434745
  · exact context_11_26433_797014
  · exact context_11_26434_797445
  · exact context_11_26435_789341

theorem selected_cut_31224 : selected 8 ⟨797505, by decide⟩
    (prefixPartial 13 422976) = some ⟨13, 2, 0, 797505, 422976, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_422976_797505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422976 ⟨797505, by decide⟩ :=
  accepted_of_selected 13 422976 ⟨797505, by decide⟩ ⟨13, 2, 0, 797505, 422976, 2373, 16384⟩
    (by decide) selected_cut_31224

theorem selected_cut_31225 : selected 8 ⟨797546, by decide⟩
    (prefixPartial 13 422977) = some ⟨13, 2, 0, 797546, 422977, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_422977_797546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422977 ⟨797546, by decide⟩ :=
  accepted_of_selected 13 422977 ⟨797546, by decide⟩ ⟨13, 2, 0, 797546, 422977, 2369, 16384⟩
    (by decide) selected_cut_31225

theorem selected_cut_31226 : selected 8 ⟨797588, by decide⟩
    (prefixPartial 13 422978) = some ⟨13, 2, 0, 797588, 422978, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_422978_797588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422978 ⟨797588, by decide⟩ :=
  accepted_of_selected 13 422978 ⟨797588, by decide⟩ ⟨13, 2, 0, 797588, 422978, 1553, 16384⟩
    (by decide) selected_cut_31226

theorem selected_cut_31227 : selected 8 ⟨797608, by decide⟩
    (prefixPartial 13 422979) = some ⟨13, 2, 0, 797608, 422979, 913, 16384⟩ := by
  decide +kernel

theorem context_13_422979_797608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422979 ⟨797608, by decide⟩ :=
  accepted_of_selected 13 422979 ⟨797608, by decide⟩ ⟨13, 2, 0, 797608, 422979, 913, 16384⟩
    (by decide) selected_cut_31227

theorem unmarked_context_12_105744_797609 : frontier 9 ⟨797609, by decide⟩
    (prefixCache 12 105744) (prefixPartial 12 105744) = false := by
  decide +kernel

theorem node_context_12_105744_797609 : EJMOriginalGlobalDAGData.nodes 9 ⟨797609, by decide⟩ =
    .split (coordinate 12) (![⟨797505, by decide⟩,⟨797546, by decide⟩,⟨797588, by decide⟩,⟨797608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105744_797609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105744 ⟨797609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105744
    ⟨797609, by decide⟩ (by decide) (![⟨797505, by decide⟩,⟨797546, by decide⟩,⟨797588, by decide⟩,⟨797608, by decide⟩]) unmarked_context_12_105744_797609 node_context_12_105744_797609
  intro a
  fin_cases a
  · exact context_13_422976_797505
  · exact context_13_422977_797546
  · exact context_13_422978_797588
  · exact context_13_422979_797608

theorem selected_cut_31228 : selected 8 ⟨797666, by decide⟩
    (prefixPartial 13 422980) = some ⟨13, 2, 0, 797666, 422980, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_422980_797666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422980 ⟨797666, by decide⟩ :=
  accepted_of_selected 13 422980 ⟨797666, by decide⟩ ⟨13, 2, 0, 797666, 422980, 2401, 16384⟩
    (by decide) selected_cut_31228

theorem selected_cut_31229 : selected 8 ⟨797715, by decide⟩
    (prefixPartial 13 422981) = some ⟨13, 2, 0, 797715, 422981, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_422981_797715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422981 ⟨797715, by decide⟩ :=
  accepted_of_selected 13 422981 ⟨797715, by decide⟩ ⟨13, 2, 0, 797715, 422981, 1833, 16384⟩
    (by decide) selected_cut_31229

theorem selected_cut_31230 : selected 8 ⟨797756, by decide⟩
    (prefixPartial 13 422982) = some ⟨13, 2, 0, 797756, 422982, 717, 16384⟩ := by
  decide +kernel

theorem context_13_422982_797756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422982 ⟨797756, by decide⟩ :=
  accepted_of_selected 13 422982 ⟨797756, by decide⟩ ⟨13, 2, 0, 797756, 422982, 717, 16384⟩
    (by decide) selected_cut_31230

theorem selected_cut_31231 : selected 8 ⟨797776, by decide⟩
    (prefixPartial 13 422983) = some ⟨13, 2, 0, 797776, 422983, 253, 16384⟩ := by
  decide +kernel

theorem context_13_422983_797776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422983 ⟨797776, by decide⟩ :=
  accepted_of_selected 13 422983 ⟨797776, by decide⟩ ⟨13, 2, 0, 797776, 422983, 253, 16384⟩
    (by decide) selected_cut_31231

theorem unmarked_context_12_105745_797777 : frontier 9 ⟨797777, by decide⟩
    (prefixCache 12 105745) (prefixPartial 12 105745) = false := by
  decide +kernel

theorem node_context_12_105745_797777 : EJMOriginalGlobalDAGData.nodes 9 ⟨797777, by decide⟩ =
    .split (coordinate 12) (![⟨797666, by decide⟩,⟨797715, by decide⟩,⟨797756, by decide⟩,⟨797776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105745_797777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105745 ⟨797777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105745
    ⟨797777, by decide⟩ (by decide) (![⟨797666, by decide⟩,⟨797715, by decide⟩,⟨797756, by decide⟩,⟨797776, by decide⟩]) unmarked_context_12_105745_797777 node_context_12_105745_797777
  intro a
  fin_cases a
  · exact context_13_422980_797666
  · exact context_13_422981_797715
  · exact context_13_422982_797756
  · exact context_13_422983_797776

theorem selected_cut_31232 : selected 8 ⟨797836, by decide⟩
    (prefixPartial 13 422984) = some ⟨13, 2, 0, 797836, 422984, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_422984_797836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422984 ⟨797836, by decide⟩ :=
  accepted_of_selected 13 422984 ⟨797836, by decide⟩ ⟨13, 2, 0, 797836, 422984, 2649, 16384⟩
    (by decide) selected_cut_31232

theorem selected_cut_31233 : selected 8 ⟨797897, by decide⟩
    (prefixPartial 13 422985) = some ⟨13, 2, 0, 797897, 422985, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_422985_797897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422985 ⟨797897, by decide⟩ :=
  accepted_of_selected 13 422985 ⟨797897, by decide⟩ ⟨13, 2, 0, 797897, 422985, 2901, 16384⟩
    (by decide) selected_cut_31233

theorem selected_cut_31234 : selected 8 ⟨797961, by decide⟩
    (prefixPartial 13 422986) = some ⟨13, 2, 0, 797961, 422986, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_422986_797961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422986 ⟨797961, by decide⟩ :=
  accepted_of_selected 13 422986 ⟨797961, by decide⟩ ⟨13, 2, 0, 797961, 422986, 1713, 16384⟩
    (by decide) selected_cut_31234

theorem selected_cut_31235 : selected 8 ⟨797986, by decide⟩
    (prefixPartial 13 422987) = some ⟨13, 2, 0, 797986, 422987, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_422987_797986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422987 ⟨797986, by decide⟩ :=
  accepted_of_selected 13 422987 ⟨797986, by decide⟩ ⟨13, 2, 0, 797986, 422987, 1173, 16384⟩
    (by decide) selected_cut_31235

theorem unmarked_context_12_105746_797987 : frontier 9 ⟨797987, by decide⟩
    (prefixCache 12 105746) (prefixPartial 12 105746) = false := by
  decide +kernel

theorem node_context_12_105746_797987 : EJMOriginalGlobalDAGData.nodes 9 ⟨797987, by decide⟩ =
    .split (coordinate 12) (![⟨797836, by decide⟩,⟨797897, by decide⟩,⟨797961, by decide⟩,⟨797986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105746_797987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105746 ⟨797987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105746
    ⟨797987, by decide⟩ (by decide) (![⟨797836, by decide⟩,⟨797897, by decide⟩,⟨797961, by decide⟩,⟨797986, by decide⟩]) unmarked_context_12_105746_797987 node_context_12_105746_797987
  intro a
  fin_cases a
  · exact context_13_422984_797836
  · exact context_13_422985_797897
  · exact context_13_422986_797961
  · exact context_13_422987_797986

theorem selected_cut_31236 : selected 8 ⟨798060, by decide⟩
    (prefixPartial 13 422988) = some ⟨13, 2, 0, 798060, 422988, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_422988_798060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422988 ⟨798060, by decide⟩ :=
  accepted_of_selected 13 422988 ⟨798060, by decide⟩ ⟨13, 2, 0, 798060, 422988, 2869, 16384⟩
    (by decide) selected_cut_31236

theorem selected_cut_31237 : selected 8 ⟨798131, by decide⟩
    (prefixPartial 13 422989) = some ⟨13, 2, 0, 798131, 422989, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_422989_798131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422989 ⟨798131, by decide⟩ :=
  accepted_of_selected 13 422989 ⟨798131, by decide⟩ ⟨13, 2, 0, 798131, 422989, 2961, 16384⟩
    (by decide) selected_cut_31237

theorem selected_cut_31238 : selected 8 ⟨798234, by decide⟩
    (prefixPartial 13 422990) = some ⟨13, 2, 0, 798234, 422990, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_422990_798234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422990 ⟨798234, by decide⟩ :=
  accepted_of_selected 13 422990 ⟨798234, by decide⟩ ⟨13, 2, 0, 798234, 422990, 2261, 16384⟩
    (by decide) selected_cut_31238

theorem selected_cut_31239 : selected 8 ⟨798259, by decide⟩
    (prefixPartial 13 422991) = some ⟨13, 2, 0, 798259, 422991, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_422991_798259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422991 ⟨798259, by decide⟩ :=
  accepted_of_selected 13 422991 ⟨798259, by decide⟩ ⟨13, 2, 0, 798259, 422991, 1133, 16384⟩
    (by decide) selected_cut_31239

theorem unmarked_context_12_105747_798260 : frontier 9 ⟨798260, by decide⟩
    (prefixCache 12 105747) (prefixPartial 12 105747) = false := by
  decide +kernel

theorem node_context_12_105747_798260 : EJMOriginalGlobalDAGData.nodes 9 ⟨798260, by decide⟩ =
    .split (coordinate 12) (![⟨798060, by decide⟩,⟨798131, by decide⟩,⟨798234, by decide⟩,⟨798259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105747_798260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105747 ⟨798260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105747
    ⟨798260, by decide⟩ (by decide) (![⟨798060, by decide⟩,⟨798131, by decide⟩,⟨798234, by decide⟩,⟨798259, by decide⟩]) unmarked_context_12_105747_798260 node_context_12_105747_798260
  intro a
  fin_cases a
  · exact context_13_422988_798060
  · exact context_13_422989_798131
  · exact context_13_422990_798234
  · exact context_13_422991_798259

theorem unmarked_context_11_26436_798261 : frontier 10 ⟨798261, by decide⟩
    (prefixCache 11 26436) (prefixPartial 11 26436) = false := by
  decide +kernel

theorem node_context_11_26436_798261 : EJMOriginalGlobalDAGData.nodes 10 ⟨798261, by decide⟩ =
    .split (coordinate 11) (![⟨797609, by decide⟩,⟨797777, by decide⟩,⟨797987, by decide⟩,⟨798260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26436_798261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26436 ⟨798261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26436
    ⟨798261, by decide⟩ (by decide) (![⟨797609, by decide⟩,⟨797777, by decide⟩,⟨797987, by decide⟩,⟨798260, by decide⟩]) unmarked_context_11_26436_798261 node_context_11_26436_798261
  intro a
  fin_cases a
  · exact context_12_105744_797609
  · exact context_12_105745_797777
  · exact context_12_105746_797987
  · exact context_12_105747_798260

theorem selected_cut_31240 : selected 8 ⟨798302, by decide⟩
    (prefixPartial 13 422992) = some ⟨13, 2, 0, 798302, 422992, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_422992_798302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422992 ⟨798302, by decide⟩ :=
  accepted_of_selected 13 422992 ⟨798302, by decide⟩ ⟨13, 2, 0, 798302, 422992, 1857, 16384⟩
    (by decide) selected_cut_31240

theorem selected_cut_31241 : selected 8 ⟨798370, by decide⟩
    (prefixPartial 13 422993) = some ⟨13, 2, 0, 798370, 422993, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_422993_798370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422993 ⟨798370, by decide⟩ :=
  accepted_of_selected 13 422993 ⟨798370, by decide⟩ ⟨13, 2, 0, 798370, 422993, 1777, 16384⟩
    (by decide) selected_cut_31241

theorem selected_cut_31242 : selected 8 ⟨798424, by decide⟩
    (prefixPartial 13 422994) = some ⟨13, 2, 0, 798424, 422994, 737, 16384⟩ := by
  decide +kernel

theorem context_13_422994_798424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422994 ⟨798424, by decide⟩ :=
  accepted_of_selected 13 422994 ⟨798424, by decide⟩ ⟨13, 2, 0, 798424, 422994, 737, 16384⟩
    (by decide) selected_cut_31242

theorem selected_cut_31243 : selected 8 ⟨798441, by decide⟩
    (prefixPartial 13 422995) = some ⟨13, 2, 0, 798441, 422995, 209, 16384⟩ := by
  decide +kernel

theorem context_13_422995_798441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422995 ⟨798441, by decide⟩ :=
  accepted_of_selected 13 422995 ⟨798441, by decide⟩ ⟨13, 2, 0, 798441, 422995, 209, 16384⟩
    (by decide) selected_cut_31243

theorem unmarked_context_12_105748_798442 : frontier 9 ⟨798442, by decide⟩
    (prefixCache 12 105748) (prefixPartial 12 105748) = false := by
  decide +kernel

theorem node_context_12_105748_798442 : EJMOriginalGlobalDAGData.nodes 9 ⟨798442, by decide⟩ =
    .split (coordinate 12) (![⟨798302, by decide⟩,⟨798370, by decide⟩,⟨798424, by decide⟩,⟨798441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105748_798442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105748 ⟨798442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105748
    ⟨798442, by decide⟩ (by decide) (![⟨798302, by decide⟩,⟨798370, by decide⟩,⟨798424, by decide⟩,⟨798441, by decide⟩]) unmarked_context_12_105748_798442 node_context_12_105748_798442
  intro a
  fin_cases a
  · exact context_13_422992_798302
  · exact context_13_422993_798370
  · exact context_13_422994_798424
  · exact context_13_422995_798441

theorem selected_cut_31244 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 105749) = some ⟨12, 1, 0, 772506, 105749, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105749_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105749 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 105749 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 105749, 1, 65536⟩
    (by decide) selected_cut_31244

theorem selected_cut_31245 : selected 8 ⟨798500, by decide⟩
    (prefixPartial 13 423000) = some ⟨13, 2, 0, 798500, 423000, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_423000_798500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423000 ⟨798500, by decide⟩ :=
  accepted_of_selected 13 423000 ⟨798500, by decide⟩ ⟨13, 2, 0, 798500, 423000, 2269, 16384⟩
    (by decide) selected_cut_31245

theorem selected_cut_31246 : selected 8 ⟨798538, by decide⟩
    (prefixPartial 13 423001) = some ⟨13, 2, 0, 798538, 423001, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_423001_798538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423001 ⟨798538, by decide⟩ :=
  accepted_of_selected 13 423001 ⟨798538, by decide⟩ ⟨13, 2, 0, 798538, 423001, 2601, 16384⟩
    (by decide) selected_cut_31246

theorem selected_cut_31247 : selected 8 ⟨798572, by decide⟩
    (prefixPartial 13 423002) = some ⟨13, 2, 0, 798572, 423002, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_423002_798572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423002 ⟨798572, by decide⟩ :=
  accepted_of_selected 13 423002 ⟨798572, by decide⟩ ⟨13, 2, 0, 798572, 423002, 1505, 16384⟩
    (by decide) selected_cut_31247

theorem selected_cut_31248 : selected 8 ⟨798585, by decide⟩
    (prefixPartial 13 423003) = some ⟨13, 2, 0, 798585, 423003, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_423003_798585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423003 ⟨798585, by decide⟩ :=
  accepted_of_selected 13 423003 ⟨798585, by decide⟩ ⟨13, 2, 0, 798585, 423003, 1137, 16384⟩
    (by decide) selected_cut_31248

theorem unmarked_context_12_105750_798586 : frontier 9 ⟨798586, by decide⟩
    (prefixCache 12 105750) (prefixPartial 12 105750) = false := by
  decide +kernel

theorem node_context_12_105750_798586 : EJMOriginalGlobalDAGData.nodes 9 ⟨798586, by decide⟩ =
    .split (coordinate 12) (![⟨798500, by decide⟩,⟨798538, by decide⟩,⟨798572, by decide⟩,⟨798585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105750_798586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105750 ⟨798586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105750
    ⟨798586, by decide⟩ (by decide) (![⟨798500, by decide⟩,⟨798538, by decide⟩,⟨798572, by decide⟩,⟨798585, by decide⟩]) unmarked_context_12_105750_798586 node_context_12_105750_798586
  intro a
  fin_cases a
  · exact context_13_423000_798500
  · exact context_13_423001_798538
  · exact context_13_423002_798572
  · exact context_13_423003_798585

theorem selected_cut_31249 : selected 8 ⟨798643, by decide⟩
    (prefixPartial 13 423004) = some ⟨13, 2, 0, 798643, 423004, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_423004_798643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423004 ⟨798643, by decide⟩ :=
  accepted_of_selected 13 423004 ⟨798643, by decide⟩ ⟨13, 2, 0, 798643, 423004, 2389, 16384⟩
    (by decide) selected_cut_31249

theorem selected_cut_31250 : selected 8 ⟨798700, by decide⟩
    (prefixPartial 13 423005) = some ⟨13, 2, 0, 798700, 423005, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_423005_798700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423005 ⟨798700, by decide⟩ :=
  accepted_of_selected 13 423005 ⟨798700, by decide⟩ ⟨13, 2, 0, 798700, 423005, 2669, 16384⟩
    (by decide) selected_cut_31250

theorem selected_cut_31251 : selected 8 ⟨798785, by decide⟩
    (prefixPartial 13 423006) = some ⟨13, 2, 0, 798785, 423006, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_423006_798785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423006 ⟨798785, by decide⟩ :=
  accepted_of_selected 13 423006 ⟨798785, by decide⟩ ⟨13, 2, 0, 798785, 423006, 2173, 16384⟩
    (by decide) selected_cut_31251

theorem selected_cut_31252 : selected 8 ⟨798804, by decide⟩
    (prefixPartial 13 423007) = some ⟨13, 2, 0, 798804, 423007, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_423007_798804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423007 ⟨798804, by decide⟩ :=
  accepted_of_selected 13 423007 ⟨798804, by decide⟩ ⟨13, 2, 0, 798804, 423007, 1049, 16384⟩
    (by decide) selected_cut_31252

theorem unmarked_context_12_105751_798805 : frontier 9 ⟨798805, by decide⟩
    (prefixCache 12 105751) (prefixPartial 12 105751) = false := by
  decide +kernel

theorem node_context_12_105751_798805 : EJMOriginalGlobalDAGData.nodes 9 ⟨798805, by decide⟩ =
    .split (coordinate 12) (![⟨798643, by decide⟩,⟨798700, by decide⟩,⟨798785, by decide⟩,⟨798804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105751_798805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105751 ⟨798805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105751
    ⟨798805, by decide⟩ (by decide) (![⟨798643, by decide⟩,⟨798700, by decide⟩,⟨798785, by decide⟩,⟨798804, by decide⟩]) unmarked_context_12_105751_798805 node_context_12_105751_798805
  intro a
  fin_cases a
  · exact context_13_423004_798643
  · exact context_13_423005_798700
  · exact context_13_423006_798785
  · exact context_13_423007_798804

theorem unmarked_context_11_26437_798806 : frontier 10 ⟨798806, by decide⟩
    (prefixCache 11 26437) (prefixPartial 11 26437) = false := by
  decide +kernel

theorem node_context_11_26437_798806 : EJMOriginalGlobalDAGData.nodes 10 ⟨798806, by decide⟩ =
    .split (coordinate 11) (![⟨798442, by decide⟩,⟨772506, by decide⟩,⟨798586, by decide⟩,⟨798805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26437_798806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26437 ⟨798806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26437
    ⟨798806, by decide⟩ (by decide) (![⟨798442, by decide⟩,⟨772506, by decide⟩,⟨798586, by decide⟩,⟨798805, by decide⟩]) unmarked_context_11_26437_798806 node_context_11_26437_798806
  intro a
  fin_cases a
  · exact context_12_105748_798442
  · exact context_12_105749_772506
  · exact context_12_105750_798586
  · exact context_12_105751_798805

theorem selected_cut_31253 : selected 8 ⟨798843, by decide⟩
    (prefixPartial 13 423008) = some ⟨13, 2, 0, 798843, 423008, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_423008_798843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423008 ⟨798843, by decide⟩ :=
  accepted_of_selected 13 423008 ⟨798843, by decide⟩ ⟨13, 2, 0, 798843, 423008, 2101, 16384⟩
    (by decide) selected_cut_31253

theorem selected_cut_31254 : selected 8 ⟨798918, by decide⟩
    (prefixPartial 13 423009) = some ⟨13, 2, 0, 798918, 423009, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_423009_798918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423009 ⟨798918, by decide⟩ :=
  accepted_of_selected 13 423009 ⟨798918, by decide⟩ ⟨13, 2, 0, 798918, 423009, 2525, 16384⟩
    (by decide) selected_cut_31254

theorem selected_cut_31255 : selected 8 ⟨798994, by decide⟩
    (prefixPartial 13 423010) = some ⟨13, 2, 0, 798994, 423010, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_423010_798994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423010 ⟨798994, by decide⟩ :=
  accepted_of_selected 13 423010 ⟨798994, by decide⟩ ⟨13, 2, 0, 798994, 423010, 1881, 16384⟩
    (by decide) selected_cut_31255

theorem selected_cut_31256 : selected 8 ⟨799008, by decide⟩
    (prefixPartial 13 423011) = some ⟨13, 2, 0, 799008, 423011, 909, 16384⟩ := by
  decide +kernel

theorem context_13_423011_799008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423011 ⟨799008, by decide⟩ :=
  accepted_of_selected 13 423011 ⟨799008, by decide⟩ ⟨13, 2, 0, 799008, 423011, 909, 16384⟩
    (by decide) selected_cut_31256

theorem unmarked_context_12_105752_799009 : frontier 9 ⟨799009, by decide⟩
    (prefixCache 12 105752) (prefixPartial 12 105752) = false := by
  decide +kernel

theorem node_context_12_105752_799009 : EJMOriginalGlobalDAGData.nodes 9 ⟨799009, by decide⟩ =
    .split (coordinate 12) (![⟨798843, by decide⟩,⟨798918, by decide⟩,⟨798994, by decide⟩,⟨799008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105752_799009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105752 ⟨799009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105752
    ⟨799009, by decide⟩ (by decide) (![⟨798843, by decide⟩,⟨798918, by decide⟩,⟨798994, by decide⟩,⟨799008, by decide⟩]) unmarked_context_12_105752_799009 node_context_12_105752_799009
  intro a
  fin_cases a
  · exact context_13_423008_798843
  · exact context_13_423009_798918
  · exact context_13_423010_798994
  · exact context_13_423011_799008

theorem selected_cut_31257 : selected 8 ⟨799052, by decide⟩
    (prefixPartial 13 423012) = some ⟨13, 2, 0, 799052, 423012, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_423012_799052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423012 ⟨799052, by decide⟩ :=
  accepted_of_selected 13 423012 ⟨799052, by decide⟩ ⟨13, 2, 0, 799052, 423012, 2045, 16384⟩
    (by decide) selected_cut_31257

theorem selected_cut_31258 : selected 8 ⟨799091, by decide⟩
    (prefixPartial 13 423013) = some ⟨13, 2, 0, 799091, 423013, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_423013_799091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423013 ⟨799091, by decide⟩ :=
  accepted_of_selected 13 423013 ⟨799091, by decide⟩ ⟨13, 2, 0, 799091, 423013, 2153, 16384⟩
    (by decide) selected_cut_31258

theorem selected_cut_31259 : selected 8 ⟨799153, by decide⟩
    (prefixPartial 13 423014) = some ⟨13, 2, 0, 799153, 423014, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_423014_799153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423014 ⟨799153, by decide⟩ :=
  accepted_of_selected 13 423014 ⟨799153, by decide⟩ ⟨13, 2, 0, 799153, 423014, 1789, 16384⟩
    (by decide) selected_cut_31259

theorem selected_cut_31260 : selected 8 ⟨799160, by decide⟩
    (prefixPartial 13 423015) = some ⟨13, 2, 0, 799160, 423015, 953, 16384⟩ := by
  decide +kernel

theorem context_13_423015_799160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423015 ⟨799160, by decide⟩ :=
  accepted_of_selected 13 423015 ⟨799160, by decide⟩ ⟨13, 2, 0, 799160, 423015, 953, 16384⟩
    (by decide) selected_cut_31260

theorem unmarked_context_12_105753_799161 : frontier 9 ⟨799161, by decide⟩
    (prefixCache 12 105753) (prefixPartial 12 105753) = false := by
  decide +kernel

theorem node_context_12_105753_799161 : EJMOriginalGlobalDAGData.nodes 9 ⟨799161, by decide⟩ =
    .split (coordinate 12) (![⟨799052, by decide⟩,⟨799091, by decide⟩,⟨799153, by decide⟩,⟨799160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105753_799161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105753 ⟨799161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105753
    ⟨799161, by decide⟩ (by decide) (![⟨799052, by decide⟩,⟨799091, by decide⟩,⟨799153, by decide⟩,⟨799160, by decide⟩]) unmarked_context_12_105753_799161 node_context_12_105753_799161
  intro a
  fin_cases a
  · exact context_13_423012_799052
  · exact context_13_423013_799091
  · exact context_13_423014_799153
  · exact context_13_423015_799160

theorem selected_cut_31261 : selected 8 ⟨799200, by decide⟩
    (prefixPartial 13 423016) = some ⟨13, 2, 0, 799200, 423016, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_423016_799200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423016 ⟨799200, by decide⟩ :=
  accepted_of_selected 13 423016 ⟨799200, by decide⟩ ⟨13, 2, 0, 799200, 423016, 2017, 16384⟩
    (by decide) selected_cut_31261

theorem selected_cut_31262 : selected 8 ⟨799251, by decide⟩
    (prefixPartial 13 423017) = some ⟨13, 2, 0, 799251, 423017, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_423017_799251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423017 ⟨799251, by decide⟩ :=
  accepted_of_selected 13 423017 ⟨799251, by decide⟩ ⟨13, 2, 0, 799251, 423017, 2509, 16384⟩
    (by decide) selected_cut_31262

theorem selected_cut_31263 : selected 8 ⟨799288, by decide⟩
    (prefixPartial 13 423018) = some ⟨13, 2, 0, 799288, 423018, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_423018_799288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423018 ⟨799288, by decide⟩ :=
  accepted_of_selected 13 423018 ⟨799288, by decide⟩ ⟨13, 2, 0, 799288, 423018, 1665, 16384⟩
    (by decide) selected_cut_31263

theorem selected_cut_31264 : selected 8 ⟨799303, by decide⟩
    (prefixPartial 13 423019) = some ⟨13, 2, 0, 799303, 423019, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_423019_799303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423019 ⟨799303, by decide⟩ :=
  accepted_of_selected 13 423019 ⟨799303, by decide⟩ ⟨13, 2, 0, 799303, 423019, 1041, 16384⟩
    (by decide) selected_cut_31264

theorem unmarked_context_12_105754_799304 : frontier 9 ⟨799304, by decide⟩
    (prefixCache 12 105754) (prefixPartial 12 105754) = false := by
  decide +kernel

theorem node_context_12_105754_799304 : EJMOriginalGlobalDAGData.nodes 9 ⟨799304, by decide⟩ =
    .split (coordinate 12) (![⟨799200, by decide⟩,⟨799251, by decide⟩,⟨799288, by decide⟩,⟨799303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105754_799304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105754 ⟨799304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105754
    ⟨799304, by decide⟩ (by decide) (![⟨799200, by decide⟩,⟨799251, by decide⟩,⟨799288, by decide⟩,⟨799303, by decide⟩]) unmarked_context_12_105754_799304 node_context_12_105754_799304
  intro a
  fin_cases a
  · exact context_13_423016_799200
  · exact context_13_423017_799251
  · exact context_13_423018_799288
  · exact context_13_423019_799303

theorem selected_cut_31265 : selected 8 ⟨799356, by decide⟩
    (prefixPartial 13 423020) = some ⟨13, 2, 0, 799356, 423020, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_423020_799356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423020 ⟨799356, by decide⟩ :=
  accepted_of_selected 13 423020 ⟨799356, by decide⟩ ⟨13, 2, 0, 799356, 423020, 2205, 16384⟩
    (by decide) selected_cut_31265

theorem selected_cut_31266 : selected 8 ⟨799421, by decide⟩
    (prefixPartial 13 423021) = some ⟨13, 2, 0, 799421, 423021, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_423021_799421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423021 ⟨799421, by decide⟩ :=
  accepted_of_selected 13 423021 ⟨799421, by decide⟩ ⟨13, 2, 0, 799421, 423021, 2705, 16384⟩
    (by decide) selected_cut_31266

theorem selected_cut_31267 : selected 8 ⟨799502, by decide⟩
    (prefixPartial 13 423022) = some ⟨13, 2, 0, 799502, 423022, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_423022_799502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423022 ⟨799502, by decide⟩ :=
  accepted_of_selected 13 423022 ⟨799502, by decide⟩ ⟨13, 2, 0, 799502, 423022, 2309, 16384⟩
    (by decide) selected_cut_31267

theorem selected_cut_31268 : selected 8 ⟨799525, by decide⟩
    (prefixPartial 13 423023) = some ⟨13, 2, 0, 799525, 423023, 997, 16384⟩ := by
  decide +kernel

theorem context_13_423023_799525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423023 ⟨799525, by decide⟩ :=
  accepted_of_selected 13 423023 ⟨799525, by decide⟩ ⟨13, 2, 0, 799525, 423023, 997, 16384⟩
    (by decide) selected_cut_31268

theorem unmarked_context_12_105755_799526 : frontier 9 ⟨799526, by decide⟩
    (prefixCache 12 105755) (prefixPartial 12 105755) = false := by
  decide +kernel

theorem node_context_12_105755_799526 : EJMOriginalGlobalDAGData.nodes 9 ⟨799526, by decide⟩ =
    .split (coordinate 12) (![⟨799356, by decide⟩,⟨799421, by decide⟩,⟨799502, by decide⟩,⟨799525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105755_799526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105755 ⟨799526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105755
    ⟨799526, by decide⟩ (by decide) (![⟨799356, by decide⟩,⟨799421, by decide⟩,⟨799502, by decide⟩,⟨799525, by decide⟩]) unmarked_context_12_105755_799526 node_context_12_105755_799526
  intro a
  fin_cases a
  · exact context_13_423020_799356
  · exact context_13_423021_799421
  · exact context_13_423022_799502
  · exact context_13_423023_799525

theorem unmarked_context_11_26438_799527 : frontier 10 ⟨799527, by decide⟩
    (prefixCache 11 26438) (prefixPartial 11 26438) = false := by
  decide +kernel

theorem node_context_11_26438_799527 : EJMOriginalGlobalDAGData.nodes 10 ⟨799527, by decide⟩ =
    .split (coordinate 11) (![⟨799009, by decide⟩,⟨799161, by decide⟩,⟨799304, by decide⟩,⟨799526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26438_799527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26438 ⟨799527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26438
    ⟨799527, by decide⟩ (by decide) (![⟨799009, by decide⟩,⟨799161, by decide⟩,⟨799304, by decide⟩,⟨799526, by decide⟩]) unmarked_context_11_26438_799527 node_context_11_26438_799527
  intro a
  fin_cases a
  · exact context_12_105752_799009
  · exact context_12_105753_799161
  · exact context_12_105754_799304
  · exact context_12_105755_799526

theorem selected_cut_31269 : selected 8 ⟨799569, by decide⟩
    (prefixPartial 13 423024) = some ⟨13, 2, 0, 799569, 423024, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_423024_799569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423024 ⟨799569, by decide⟩ :=
  accepted_of_selected 13 423024 ⟨799569, by decide⟩ ⟨13, 2, 0, 799569, 423024, 1789, 16384⟩
    (by decide) selected_cut_31269

theorem selected_cut_31270 : selected 8 ⟨799611, by decide⟩
    (prefixPartial 13 423025) = some ⟨13, 2, 0, 799611, 423025, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_423025_799611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423025 ⟨799611, by decide⟩ :=
  accepted_of_selected 13 423025 ⟨799611, by decide⟩ ⟨13, 2, 0, 799611, 423025, 2013, 16384⟩
    (by decide) selected_cut_31270

theorem selected_cut_31271 : selected 8 ⟨799672, by decide⟩
    (prefixPartial 13 423026) = some ⟨13, 2, 0, 799672, 423026, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_423026_799672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423026 ⟨799672, by decide⟩ :=
  accepted_of_selected 13 423026 ⟨799672, by decide⟩ ⟨13, 2, 0, 799672, 423026, 1697, 16384⟩
    (by decide) selected_cut_31271

theorem selected_cut_31272 : selected 8 ⟨799694, by decide⟩
    (prefixPartial 13 423027) = some ⟨13, 2, 0, 799694, 423027, 841, 16384⟩ := by
  decide +kernel

theorem context_13_423027_799694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423027 ⟨799694, by decide⟩ :=
  accepted_of_selected 13 423027 ⟨799694, by decide⟩ ⟨13, 2, 0, 799694, 423027, 841, 16384⟩
    (by decide) selected_cut_31272

theorem unmarked_context_12_105756_799695 : frontier 9 ⟨799695, by decide⟩
    (prefixCache 12 105756) (prefixPartial 12 105756) = false := by
  decide +kernel

theorem node_context_12_105756_799695 : EJMOriginalGlobalDAGData.nodes 9 ⟨799695, by decide⟩ =
    .split (coordinate 12) (![⟨799569, by decide⟩,⟨799611, by decide⟩,⟨799672, by decide⟩,⟨799694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105756_799695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105756 ⟨799695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105756
    ⟨799695, by decide⟩ (by decide) (![⟨799569, by decide⟩,⟨799611, by decide⟩,⟨799672, by decide⟩,⟨799694, by decide⟩]) unmarked_context_12_105756_799695 node_context_12_105756_799695
  intro a
  fin_cases a
  · exact context_13_423024_799569
  · exact context_13_423025_799611
  · exact context_13_423026_799672
  · exact context_13_423027_799694

theorem selected_cut_31273 : selected 8 ⟨799736, by decide⟩
    (prefixPartial 13 423028) = some ⟨13, 2, 0, 799736, 423028, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_423028_799736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423028 ⟨799736, by decide⟩ :=
  accepted_of_selected 13 423028 ⟨799736, by decide⟩ ⟨13, 2, 0, 799736, 423028, 1769, 16384⟩
    (by decide) selected_cut_31273

theorem selected_cut_31274 : selected 8 ⟨799781, by decide⟩
    (prefixPartial 13 423029) = some ⟨13, 2, 0, 799781, 423029, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_423029_799781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423029 ⟨799781, by decide⟩ :=
  accepted_of_selected 13 423029 ⟨799781, by decide⟩ ⟨13, 2, 0, 799781, 423029, 1985, 16384⟩
    (by decide) selected_cut_31274

theorem selected_cut_31275 : selected 8 ⟨799835, by decide⟩
    (prefixPartial 13 423030) = some ⟨13, 2, 0, 799835, 423030, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_423030_799835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423030 ⟨799835, by decide⟩ :=
  accepted_of_selected 13 423030 ⟨799835, by decide⟩ ⟨13, 2, 0, 799835, 423030, 1697, 16384⟩
    (by decide) selected_cut_31275

theorem selected_cut_31276 : selected 8 ⟨799842, by decide⟩
    (prefixPartial 13 423031) = some ⟨13, 2, 0, 799842, 423031, 897, 16384⟩ := by
  decide +kernel

theorem context_13_423031_799842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423031 ⟨799842, by decide⟩ :=
  accepted_of_selected 13 423031 ⟨799842, by decide⟩ ⟨13, 2, 0, 799842, 423031, 897, 16384⟩
    (by decide) selected_cut_31276

theorem unmarked_context_12_105757_799843 : frontier 9 ⟨799843, by decide⟩
    (prefixCache 12 105757) (prefixPartial 12 105757) = false := by
  decide +kernel

theorem node_context_12_105757_799843 : EJMOriginalGlobalDAGData.nodes 9 ⟨799843, by decide⟩ =
    .split (coordinate 12) (![⟨799736, by decide⟩,⟨799781, by decide⟩,⟨799835, by decide⟩,⟨799842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105757_799843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105757 ⟨799843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105757
    ⟨799843, by decide⟩ (by decide) (![⟨799736, by decide⟩,⟨799781, by decide⟩,⟨799835, by decide⟩,⟨799842, by decide⟩]) unmarked_context_12_105757_799843 node_context_12_105757_799843
  intro a
  fin_cases a
  · exact context_13_423028_799736
  · exact context_13_423029_799781
  · exact context_13_423030_799835
  · exact context_13_423031_799842

theorem selected_cut_31277 : selected 8 ⟨799890, by decide⟩
    (prefixPartial 13 423032) = some ⟨13, 2, 0, 799890, 423032, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_423032_799890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423032 ⟨799890, by decide⟩ :=
  accepted_of_selected 13 423032 ⟨799890, by decide⟩ ⟨13, 2, 0, 799890, 423032, 1777, 16384⟩
    (by decide) selected_cut_31277

theorem selected_cut_31278 : selected 8 ⟨799930, by decide⟩
    (prefixPartial 13 423033) = some ⟨13, 2, 0, 799930, 423033, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_423033_799930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423033 ⟨799930, by decide⟩ :=
  accepted_of_selected 13 423033 ⟨799930, by decide⟩ ⟨13, 2, 0, 799930, 423033, 2137, 16384⟩
    (by decide) selected_cut_31278

theorem selected_cut_31279 : selected 8 ⟨799974, by decide⟩
    (prefixPartial 13 423034) = some ⟨13, 2, 0, 799974, 423034, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_423034_799974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423034 ⟨799974, by decide⟩ :=
  accepted_of_selected 13 423034 ⟨799974, by decide⟩ ⟨13, 2, 0, 799974, 423034, 1549, 16384⟩
    (by decide) selected_cut_31279

theorem selected_cut_31280 : selected 8 ⟨799994, by decide⟩
    (prefixPartial 13 423035) = some ⟨13, 2, 0, 799994, 423035, 961, 16384⟩ := by
  decide +kernel

theorem context_13_423035_799994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423035 ⟨799994, by decide⟩ :=
  accepted_of_selected 13 423035 ⟨799994, by decide⟩ ⟨13, 2, 0, 799994, 423035, 961, 16384⟩
    (by decide) selected_cut_31280

theorem unmarked_context_12_105758_799995 : frontier 9 ⟨799995, by decide⟩
    (prefixCache 12 105758) (prefixPartial 12 105758) = false := by
  decide +kernel

theorem node_context_12_105758_799995 : EJMOriginalGlobalDAGData.nodes 9 ⟨799995, by decide⟩ =
    .split (coordinate 12) (![⟨799890, by decide⟩,⟨799930, by decide⟩,⟨799974, by decide⟩,⟨799994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105758_799995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105758 ⟨799995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105758
    ⟨799995, by decide⟩ (by decide) (![⟨799890, by decide⟩,⟨799930, by decide⟩,⟨799974, by decide⟩,⟨799994, by decide⟩]) unmarked_context_12_105758_799995 node_context_12_105758_799995
  intro a
  fin_cases a
  · exact context_13_423032_799890
  · exact context_13_423033_799930
  · exact context_13_423034_799974
  · exact context_13_423035_799994

theorem selected_cut_31281 : selected 8 ⟨800049, by decide⟩
    (prefixPartial 13 423036) = some ⟨13, 2, 0, 800049, 423036, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_423036_800049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423036 ⟨800049, by decide⟩ :=
  accepted_of_selected 13 423036 ⟨800049, by decide⟩ ⟨13, 2, 0, 800049, 423036, 1813, 16384⟩
    (by decide) selected_cut_31281

theorem selected_cut_31282 : selected 8 ⟨800101, by decide⟩
    (prefixPartial 13 423037) = some ⟨13, 2, 0, 800101, 423037, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_423037_800101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423037 ⟨800101, by decide⟩ :=
  accepted_of_selected 13 423037 ⟨800101, by decide⟩ ⟨13, 2, 0, 800101, 423037, 2133, 16384⟩
    (by decide) selected_cut_31282

theorem selected_cut_31283 : selected 8 ⟨800196, by decide⟩
    (prefixPartial 13 423038) = some ⟨13, 2, 0, 800196, 423038, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_423038_800196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423038 ⟨800196, by decide⟩ :=
  accepted_of_selected 13 423038 ⟨800196, by decide⟩ ⟨13, 2, 0, 800196, 423038, 1969, 16384⟩
    (by decide) selected_cut_31283

theorem selected_cut_31284 : selected 8 ⟨800216, by decide⟩
    (prefixPartial 13 423039) = some ⟨13, 2, 0, 800216, 423039, 973, 16384⟩ := by
  decide +kernel

theorem context_13_423039_800216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423039 ⟨800216, by decide⟩ :=
  accepted_of_selected 13 423039 ⟨800216, by decide⟩ ⟨13, 2, 0, 800216, 423039, 973, 16384⟩
    (by decide) selected_cut_31284

theorem unmarked_context_12_105759_800217 : frontier 9 ⟨800217, by decide⟩
    (prefixCache 12 105759) (prefixPartial 12 105759) = false := by
  decide +kernel

theorem node_context_12_105759_800217 : EJMOriginalGlobalDAGData.nodes 9 ⟨800217, by decide⟩ =
    .split (coordinate 12) (![⟨800049, by decide⟩,⟨800101, by decide⟩,⟨800196, by decide⟩,⟨800216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105759_800217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105759 ⟨800217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105759
    ⟨800217, by decide⟩ (by decide) (![⟨800049, by decide⟩,⟨800101, by decide⟩,⟨800196, by decide⟩,⟨800216, by decide⟩]) unmarked_context_12_105759_800217 node_context_12_105759_800217
  intro a
  fin_cases a
  · exact context_13_423036_800049
  · exact context_13_423037_800101
  · exact context_13_423038_800196
  · exact context_13_423039_800216

theorem unmarked_context_11_26439_800218 : frontier 10 ⟨800218, by decide⟩
    (prefixCache 11 26439) (prefixPartial 11 26439) = false := by
  decide +kernel

theorem node_context_11_26439_800218 : EJMOriginalGlobalDAGData.nodes 10 ⟨800218, by decide⟩ =
    .split (coordinate 11) (![⟨799695, by decide⟩,⟨799843, by decide⟩,⟨799995, by decide⟩,⟨800217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26439_800218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26439 ⟨800218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26439
    ⟨800218, by decide⟩ (by decide) (![⟨799695, by decide⟩,⟨799843, by decide⟩,⟨799995, by decide⟩,⟨800217, by decide⟩]) unmarked_context_11_26439_800218 node_context_11_26439_800218
  intro a
  fin_cases a
  · exact context_12_105756_799695
  · exact context_12_105757_799843
  · exact context_12_105758_799995
  · exact context_12_105759_800217

theorem unmarked_context_10_6609_800219 : frontier 11 ⟨800219, by decide⟩
    (prefixCache 10 6609) (prefixPartial 10 6609) = false := by
  decide +kernel

theorem node_context_10_6609_800219 : EJMOriginalGlobalDAGData.nodes 11 ⟨800219, by decide⟩ =
    .split (coordinate 10) (![⟨798261, by decide⟩,⟨798806, by decide⟩,⟨799527, by decide⟩,⟨800218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6609_800219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6609 ⟨800219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6609
    ⟨800219, by decide⟩ (by decide) (![⟨798261, by decide⟩,⟨798806, by decide⟩,⟨799527, by decide⟩,⟨800218, by decide⟩]) unmarked_context_10_6609_800219 node_context_10_6609_800219
  intro a
  fin_cases a
  · exact context_11_26436_798261
  · exact context_11_26437_798806
  · exact context_11_26438_799527
  · exact context_11_26439_800218

theorem selected_cut_31285 : selected 8 ⟨800277, by decide⟩
    (prefixPartial 13 423040) = some ⟨13, 2, 0, 800277, 423040, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_423040_800277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423040 ⟨800277, by decide⟩ :=
  accepted_of_selected 13 423040 ⟨800277, by decide⟩ ⟨13, 2, 0, 800277, 423040, 1477, 16384⟩
    (by decide) selected_cut_31285

theorem selected_cut_31286 : selected 8 ⟨800310, by decide⟩
    (prefixPartial 13 423041) = some ⟨13, 2, 0, 800310, 423041, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_423041_800310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423041 ⟨800310, by decide⟩ :=
  accepted_of_selected 13 423041 ⟨800310, by decide⟩ ⟨13, 2, 0, 800310, 423041, 1925, 16384⟩
    (by decide) selected_cut_31286

theorem selected_cut_31287 : selected 8 ⟨800344, by decide⟩
    (prefixPartial 13 423042) = some ⟨13, 2, 0, 800344, 423042, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_423042_800344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423042 ⟨800344, by decide⟩ :=
  accepted_of_selected 13 423042 ⟨800344, by decide⟩ ⟨13, 2, 0, 800344, 423042, 1329, 16384⟩
    (by decide) selected_cut_31287

theorem selected_cut_31288 : selected 8 ⟨800367, by decide⟩
    (prefixPartial 13 423043) = some ⟨13, 2, 0, 800367, 423043, 905, 16384⟩ := by
  decide +kernel

theorem context_13_423043_800367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423043 ⟨800367, by decide⟩ :=
  accepted_of_selected 13 423043 ⟨800367, by decide⟩ ⟨13, 2, 0, 800367, 423043, 905, 16384⟩
    (by decide) selected_cut_31288

theorem unmarked_context_12_105760_800368 : frontier 9 ⟨800368, by decide⟩
    (prefixCache 12 105760) (prefixPartial 12 105760) = false := by
  decide +kernel

theorem node_context_12_105760_800368 : EJMOriginalGlobalDAGData.nodes 9 ⟨800368, by decide⟩ =
    .split (coordinate 12) (![⟨800277, by decide⟩,⟨800310, by decide⟩,⟨800344, by decide⟩,⟨800367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105760_800368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105760 ⟨800368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105760
    ⟨800368, by decide⟩ (by decide) (![⟨800277, by decide⟩,⟨800310, by decide⟩,⟨800344, by decide⟩,⟨800367, by decide⟩]) unmarked_context_12_105760_800368 node_context_12_105760_800368
  intro a
  fin_cases a
  · exact context_13_423040_800277
  · exact context_13_423041_800310
  · exact context_13_423042_800344
  · exact context_13_423043_800367

theorem selected_cut_31289 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 105761) = some ⟨12, 1, 0, 772506, 105761, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105761_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105761 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 105761 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 105761, 1, 65536⟩
    (by decide) selected_cut_31289

theorem selected_cut_31290 : selected 8 ⟨800414, by decide⟩
    (prefixPartial 13 423048) = some ⟨13, 2, 0, 800414, 423048, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_423048_800414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423048 ⟨800414, by decide⟩ :=
  accepted_of_selected 13 423048 ⟨800414, by decide⟩ ⟨13, 2, 0, 800414, 423048, 1609, 16384⟩
    (by decide) selected_cut_31290

theorem selected_cut_31291 : selected 8 ⟨800455, by decide⟩
    (prefixPartial 13 423049) = some ⟨13, 2, 0, 800455, 423049, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_423049_800455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423049 ⟨800455, by decide⟩ :=
  accepted_of_selected 13 423049 ⟨800455, by decide⟩ ⟨13, 2, 0, 800455, 423049, 2109, 16384⟩
    (by decide) selected_cut_31291

theorem selected_cut_31292 : selected 8 ⟨800487, by decide⟩
    (prefixPartial 13 423050) = some ⟨13, 2, 0, 800487, 423050, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_423050_800487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423050 ⟨800487, by decide⟩ :=
  accepted_of_selected 13 423050 ⟨800487, by decide⟩ ⟨13, 2, 0, 800487, 423050, 1405, 16384⟩
    (by decide) selected_cut_31292

theorem selected_cut_31293 : selected 8 ⟨800523, by decide⟩
    (prefixPartial 13 423051) = some ⟨13, 2, 0, 800523, 423051, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_423051_800523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423051 ⟨800523, by decide⟩ :=
  accepted_of_selected 13 423051 ⟨800523, by decide⟩ ⟨13, 2, 0, 800523, 423051, 1021, 16384⟩
    (by decide) selected_cut_31293

theorem unmarked_context_12_105762_800524 : frontier 9 ⟨800524, by decide⟩
    (prefixCache 12 105762) (prefixPartial 12 105762) = false := by
  decide +kernel

theorem node_context_12_105762_800524 : EJMOriginalGlobalDAGData.nodes 9 ⟨800524, by decide⟩ =
    .split (coordinate 12) (![⟨800414, by decide⟩,⟨800455, by decide⟩,⟨800487, by decide⟩,⟨800523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105762_800524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105762 ⟨800524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105762
    ⟨800524, by decide⟩ (by decide) (![⟨800414, by decide⟩,⟨800455, by decide⟩,⟨800487, by decide⟩,⟨800523, by decide⟩]) unmarked_context_12_105762_800524 node_context_12_105762_800524
  intro a
  fin_cases a
  · exact context_13_423048_800414
  · exact context_13_423049_800455
  · exact context_13_423050_800487
  · exact context_13_423051_800523

theorem selected_cut_31294 : selected 8 ⟨800580, by decide⟩
    (prefixPartial 13 423052) = some ⟨13, 2, 0, 800580, 423052, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_423052_800580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423052 ⟨800580, by decide⟩ :=
  accepted_of_selected 13 423052 ⟨800580, by decide⟩ ⟨13, 2, 0, 800580, 423052, 1645, 16384⟩
    (by decide) selected_cut_31294

theorem selected_cut_31295 : selected 8 ⟨800639, by decide⟩
    (prefixPartial 13 423053) = some ⟨13, 2, 0, 800639, 423053, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_423053_800639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423053 ⟨800639, by decide⟩ :=
  accepted_of_selected 13 423053 ⟨800639, by decide⟩ ⟨13, 2, 0, 800639, 423053, 2097, 16384⟩
    (by decide) selected_cut_31295

theorem selected_cut_31296 : selected 8 ⟨800712, by decide⟩
    (prefixPartial 13 423054) = some ⟨13, 2, 0, 800712, 423054, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_423054_800712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423054 ⟨800712, by decide⟩ :=
  accepted_of_selected 13 423054 ⟨800712, by decide⟩ ⟨13, 2, 0, 800712, 423054, 1665, 16384⟩
    (by decide) selected_cut_31296

theorem selected_cut_31297 : selected 8 ⟨800747, by decide⟩
    (prefixPartial 13 423055) = some ⟨13, 2, 0, 800747, 423055, 989, 16384⟩ := by
  decide +kernel

theorem context_13_423055_800747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423055 ⟨800747, by decide⟩ :=
  accepted_of_selected 13 423055 ⟨800747, by decide⟩ ⟨13, 2, 0, 800747, 423055, 989, 16384⟩
    (by decide) selected_cut_31297

theorem unmarked_context_12_105763_800748 : frontier 9 ⟨800748, by decide⟩
    (prefixCache 12 105763) (prefixPartial 12 105763) = false := by
  decide +kernel

theorem node_context_12_105763_800748 : EJMOriginalGlobalDAGData.nodes 9 ⟨800748, by decide⟩ =
    .split (coordinate 12) (![⟨800580, by decide⟩,⟨800639, by decide⟩,⟨800712, by decide⟩,⟨800747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105763_800748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105763 ⟨800748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105763
    ⟨800748, by decide⟩ (by decide) (![⟨800580, by decide⟩,⟨800639, by decide⟩,⟨800712, by decide⟩,⟨800747, by decide⟩]) unmarked_context_12_105763_800748 node_context_12_105763_800748
  intro a
  fin_cases a
  · exact context_13_423052_800580
  · exact context_13_423053_800639
  · exact context_13_423054_800712
  · exact context_13_423055_800747

theorem unmarked_context_11_26440_800749 : frontier 10 ⟨800749, by decide⟩
    (prefixCache 11 26440) (prefixPartial 11 26440) = false := by
  decide +kernel

theorem node_context_11_26440_800749 : EJMOriginalGlobalDAGData.nodes 10 ⟨800749, by decide⟩ =
    .split (coordinate 11) (![⟨800368, by decide⟩,⟨772506, by decide⟩,⟨800524, by decide⟩,⟨800748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26440_800749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26440 ⟨800749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26440
    ⟨800749, by decide⟩ (by decide) (![⟨800368, by decide⟩,⟨772506, by decide⟩,⟨800524, by decide⟩,⟨800748, by decide⟩]) unmarked_context_11_26440_800749 node_context_11_26440_800749
  intro a
  fin_cases a
  · exact context_12_105760_800368
  · exact context_12_105761_772506
  · exact context_12_105762_800524
  · exact context_12_105763_800748

theorem selected_cut_31298 : selected 9 ⟨461082, by decide⟩
    (prefixPartial 12 105764) = some ⟨12, 1, 0, 461082, 105764, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105764_461082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105764 ⟨461082, by decide⟩ :=
  accepted_of_selected 12 105764 ⟨461082, by decide⟩ ⟨12, 1, 0, 461082, 105764, 1, 65536⟩
    (by decide) selected_cut_31298

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
