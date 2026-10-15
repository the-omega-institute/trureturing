/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover151
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14595 : selected 9 ⟨376185, by decide⟩
    (prefixPartial 12 27312) = some ⟨12, 2, 0, 376185, 27312, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_27312_376185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27312 ⟨376185, by decide⟩ :=
  accepted_of_selected 12 27312 ⟨376185, by decide⟩ ⟨12, 2, 0, 376185, 27312, 1297, 65536⟩
    (by decide) selected_cut_14595

theorem selected_cut_14596 : selected 9 ⟨376196, by decide⟩
    (prefixPartial 12 27313) = some ⟨12, 2, 0, 376196, 27313, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_27313_376196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27313 ⟨376196, by decide⟩ :=
  accepted_of_selected 12 27313 ⟨376196, by decide⟩ ⟨12, 2, 0, 376196, 27313, 1389, 65536⟩
    (by decide) selected_cut_14596

theorem selected_cut_14597 : selected 9 ⟨376207, by decide⟩
    (prefixPartial 12 27314) = some ⟨12, 2, 0, 376207, 27314, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_27314_376207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27314 ⟨376207, by decide⟩ :=
  accepted_of_selected 12 27314 ⟨376207, by decide⟩ ⟨12, 2, 0, 376207, 27314, 1157, 65536⟩
    (by decide) selected_cut_14597

theorem selected_cut_14598 : selected 9 ⟨376219, by decide⟩
    (prefixPartial 12 27315) = some ⟨12, 2, 0, 376219, 27315, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_27315_376219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27315 ⟨376219, by decide⟩ :=
  accepted_of_selected 12 27315 ⟨376219, by decide⟩ ⟨12, 2, 0, 376219, 27315, 1393, 65536⟩
    (by decide) selected_cut_14598

theorem unmarked_context_11_6828_376220 : frontier 10 ⟨376220, by decide⟩
    (prefixCache 11 6828) (prefixPartial 11 6828) = false := by
  decide +kernel

theorem node_context_11_6828_376220 : EJMOriginalGlobalDAGData.nodes 10 ⟨376220, by decide⟩ =
    .split (coordinate 11) (![⟨376185, by decide⟩,⟨376196, by decide⟩,⟨376207, by decide⟩,⟨376219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6828_376220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6828 ⟨376220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6828
    ⟨376220, by decide⟩ (by decide) (![⟨376185, by decide⟩,⟨376196, by decide⟩,⟨376207, by decide⟩,⟨376219, by decide⟩]) unmarked_context_11_6828_376220 node_context_11_6828_376220
  intro a
  fin_cases a
  · exact context_12_27312_376185
  · exact context_12_27313_376196
  · exact context_12_27314_376207
  · exact context_12_27315_376219

theorem selected_cut_14599 : selected 9 ⟨376233, by decide⟩
    (prefixPartial 12 27316) = some ⟨12, 2, 0, 376233, 27316, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_27316_376233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27316 ⟨376233, by decide⟩ :=
  accepted_of_selected 12 27316 ⟨376233, by decide⟩ ⟨12, 2, 0, 376233, 27316, 1221, 65536⟩
    (by decide) selected_cut_14599

theorem selected_cut_14600 : selected 9 ⟨376247, by decide⟩
    (prefixPartial 12 27317) = some ⟨12, 2, 0, 376247, 27317, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_27317_376247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27317 ⟨376247, by decide⟩ :=
  accepted_of_selected 12 27317 ⟨376247, by decide⟩ ⟨12, 2, 0, 376247, 27317, 1209, 65536⟩
    (by decide) selected_cut_14600

theorem selected_cut_14601 : selected 9 ⟨376263, by decide⟩
    (prefixPartial 12 27318) = some ⟨12, 2, 0, 376263, 27318, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_27318_376263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27318 ⟨376263, by decide⟩ :=
  accepted_of_selected 12 27318 ⟨376263, by decide⟩ ⟨12, 2, 0, 376263, 27318, 1133, 65536⟩
    (by decide) selected_cut_14601

theorem selected_cut_14602 : selected 9 ⟨376280, by decide⟩
    (prefixPartial 12 27319) = some ⟨12, 2, 0, 376280, 27319, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_27319_376280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27319 ⟨376280, by decide⟩ :=
  accepted_of_selected 12 27319 ⟨376280, by decide⟩ ⟨12, 2, 0, 376280, 27319, 1253, 65536⟩
    (by decide) selected_cut_14602

theorem unmarked_context_11_6829_376281 : frontier 10 ⟨376281, by decide⟩
    (prefixCache 11 6829) (prefixPartial 11 6829) = false := by
  decide +kernel

theorem node_context_11_6829_376281 : EJMOriginalGlobalDAGData.nodes 10 ⟨376281, by decide⟩ =
    .split (coordinate 11) (![⟨376233, by decide⟩,⟨376247, by decide⟩,⟨376263, by decide⟩,⟨376280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6829_376281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6829 ⟨376281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6829
    ⟨376281, by decide⟩ (by decide) (![⟨376233, by decide⟩,⟨376247, by decide⟩,⟨376263, by decide⟩,⟨376280, by decide⟩]) unmarked_context_11_6829_376281 node_context_11_6829_376281
  intro a
  fin_cases a
  · exact context_12_27316_376233
  · exact context_12_27317_376247
  · exact context_12_27318_376263
  · exact context_12_27319_376280

theorem selected_cut_14603 : selected 10 ⟨376321, by decide⟩
    (prefixPartial 11 6830) = some ⟨11, 2, 0, 376321, 6830, 3185, 262144⟩ := by
  decide +kernel

theorem context_11_6830_376321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6830 ⟨376321, by decide⟩ :=
  accepted_of_selected 11 6830 ⟨376321, by decide⟩ ⟨11, 2, 0, 376321, 6830, 3185, 262144⟩
    (by decide) selected_cut_14603

theorem selected_cut_14604 : selected 9 ⟨376330, by decide⟩
    (prefixPartial 12 27324) = some ⟨12, 2, 0, 376330, 27324, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_27324_376330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27324 ⟨376330, by decide⟩ :=
  accepted_of_selected 12 27324 ⟨376330, by decide⟩ ⟨12, 2, 0, 376330, 27324, 1173, 65536⟩
    (by decide) selected_cut_14604

theorem selected_cut_14605 : selected 9 ⟨376338, by decide⟩
    (prefixPartial 12 27325) = some ⟨12, 2, 0, 376338, 27325, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_27325_376338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27325 ⟨376338, by decide⟩ :=
  accepted_of_selected 12 27325 ⟨376338, by decide⟩ ⟨12, 2, 0, 376338, 27325, 1137, 65536⟩
    (by decide) selected_cut_14605

theorem selected_cut_14606 : selected 9 ⟨376346, by decide⟩
    (prefixPartial 12 27326) = some ⟨12, 2, 0, 376346, 27326, 973, 65536⟩ := by
  decide +kernel

theorem context_12_27326_376346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27326 ⟨376346, by decide⟩ :=
  accepted_of_selected 12 27326 ⟨376346, by decide⟩ ⟨12, 2, 0, 376346, 27326, 973, 65536⟩
    (by decide) selected_cut_14606

theorem selected_cut_14607 : selected 9 ⟨376357, by decide⟩
    (prefixPartial 12 27327) = some ⟨12, 2, 0, 376357, 27327, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_27327_376357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27327 ⟨376357, by decide⟩ :=
  accepted_of_selected 12 27327 ⟨376357, by decide⟩ ⟨12, 2, 0, 376357, 27327, 1085, 65536⟩
    (by decide) selected_cut_14607

theorem unmarked_context_11_6831_376358 : frontier 10 ⟨376358, by decide⟩
    (prefixCache 11 6831) (prefixPartial 11 6831) = false := by
  decide +kernel

theorem node_context_11_6831_376358 : EJMOriginalGlobalDAGData.nodes 10 ⟨376358, by decide⟩ =
    .split (coordinate 11) (![⟨376330, by decide⟩,⟨376338, by decide⟩,⟨376346, by decide⟩,⟨376357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6831_376358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6831 ⟨376358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6831
    ⟨376358, by decide⟩ (by decide) (![⟨376330, by decide⟩,⟨376338, by decide⟩,⟨376346, by decide⟩,⟨376357, by decide⟩]) unmarked_context_11_6831_376358 node_context_11_6831_376358
  intro a
  fin_cases a
  · exact context_12_27324_376330
  · exact context_12_27325_376338
  · exact context_12_27326_376346
  · exact context_12_27327_376357

theorem unmarked_context_10_1707_376359 : frontier 11 ⟨376359, by decide⟩
    (prefixCache 10 1707) (prefixPartial 10 1707) = false := by
  decide +kernel

theorem node_context_10_1707_376359 : EJMOriginalGlobalDAGData.nodes 11 ⟨376359, by decide⟩ =
    .split (coordinate 10) (![⟨376220, by decide⟩,⟨376281, by decide⟩,⟨376321, by decide⟩,⟨376358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1707_376359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1707 ⟨376359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1707
    ⟨376359, by decide⟩ (by decide) (![⟨376220, by decide⟩,⟨376281, by decide⟩,⟨376321, by decide⟩,⟨376358, by decide⟩]) unmarked_context_10_1707_376359 node_context_10_1707_376359
  intro a
  fin_cases a
  · exact context_11_6828_376220
  · exact context_11_6829_376281
  · exact context_11_6830_376321
  · exact context_11_6831_376358

theorem unmarked_context_9_426_376360 : frontier 12 ⟨376360, by decide⟩
    (prefixCache 9 426) (prefixPartial 9 426) = false := by
  decide +kernel

theorem node_context_9_426_376360 : EJMOriginalGlobalDAGData.nodes 12 ⟨376360, by decide⟩ =
    .split (coordinate 9) (![⟨375668, by decide⟩,⟨375987, by decide⟩,⟨376174, by decide⟩,⟨376359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_426_376360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 426 ⟨376360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 426
    ⟨376360, by decide⟩ (by decide) (![⟨375668, by decide⟩,⟨375987, by decide⟩,⟨376174, by decide⟩,⟨376359, by decide⟩]) unmarked_context_9_426_376360 node_context_9_426_376360
  intro a
  fin_cases a
  · exact context_10_1704_375668
  · exact context_10_1705_375987
  · exact context_10_1706_376174
  · exact context_10_1707_376359

theorem selected_cut_14608 : selected 9 ⟨376369, by decide⟩
    (prefixPartial 12 27328) = some ⟨12, 2, 0, 376369, 27328, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_27328_376369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27328 ⟨376369, by decide⟩ :=
  accepted_of_selected 12 27328 ⟨376369, by decide⟩ ⟨12, 2, 0, 376369, 27328, 1093, 65536⟩
    (by decide) selected_cut_14608

theorem selected_cut_14609 : selected 9 ⟨376376, by decide⟩
    (prefixPartial 12 27329) = some ⟨12, 2, 0, 376376, 27329, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_27329_376376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27329 ⟨376376, by decide⟩ :=
  accepted_of_selected 12 27329 ⟨376376, by decide⟩ ⟨12, 2, 0, 376376, 27329, 1177, 65536⟩
    (by decide) selected_cut_14609

theorem selected_cut_14610 : selected 9 ⟨376384, by decide⟩
    (prefixPartial 12 27330) = some ⟨12, 2, 0, 376384, 27330, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_27330_376384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27330 ⟨376384, by decide⟩ :=
  accepted_of_selected 12 27330 ⟨376384, by decide⟩ ⟨12, 2, 0, 376384, 27330, 1089, 65536⟩
    (by decide) selected_cut_14610

theorem selected_cut_14611 : selected 9 ⟨376392, by decide⟩
    (prefixPartial 12 27331) = some ⟨12, 2, 0, 376392, 27331, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_27331_376392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27331 ⟨376392, by decide⟩ :=
  accepted_of_selected 12 27331 ⟨376392, by decide⟩ ⟨12, 2, 0, 376392, 27331, 1081, 65536⟩
    (by decide) selected_cut_14611

theorem unmarked_context_11_6832_376393 : frontier 10 ⟨376393, by decide⟩
    (prefixCache 11 6832) (prefixPartial 11 6832) = false := by
  decide +kernel

theorem node_context_11_6832_376393 : EJMOriginalGlobalDAGData.nodes 10 ⟨376393, by decide⟩ =
    .split (coordinate 11) (![⟨376369, by decide⟩,⟨376376, by decide⟩,⟨376384, by decide⟩,⟨376392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6832_376393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6832 ⟨376393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6832
    ⟨376393, by decide⟩ (by decide) (![⟨376369, by decide⟩,⟨376376, by decide⟩,⟨376384, by decide⟩,⟨376392, by decide⟩]) unmarked_context_11_6832_376393 node_context_11_6832_376393
  intro a
  fin_cases a
  · exact context_12_27328_376369
  · exact context_12_27329_376376
  · exact context_12_27330_376384
  · exact context_12_27331_376392

theorem selected_cut_14612 : selected 10 ⟨376429, by decide⟩
    (prefixPartial 11 6833) = some ⟨11, 2, 0, 376429, 6833, 3885, 262144⟩ := by
  decide +kernel

theorem context_11_6833_376429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6833 ⟨376429, by decide⟩ :=
  accepted_of_selected 11 6833 ⟨376429, by decide⟩ ⟨11, 2, 0, 376429, 6833, 3885, 262144⟩
    (by decide) selected_cut_14612

theorem selected_cut_14613 : selected 10 ⟨376460, by decide⟩
    (prefixPartial 11 6834) = some ⟨11, 2, 0, 376460, 6834, 3629, 262144⟩ := by
  decide +kernel

theorem context_11_6834_376460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6834 ⟨376460, by decide⟩ :=
  accepted_of_selected 11 6834 ⟨376460, by decide⟩ ⟨11, 2, 0, 376460, 6834, 3629, 262144⟩
    (by decide) selected_cut_14613

theorem selected_cut_14614 : selected 10 ⟨376496, by decide⟩
    (prefixPartial 11 6835) = some ⟨11, 2, 0, 376496, 6835, 3441, 262144⟩ := by
  decide +kernel

theorem context_11_6835_376496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6835 ⟨376496, by decide⟩ :=
  accepted_of_selected 11 6835 ⟨376496, by decide⟩ ⟨11, 2, 0, 376496, 6835, 3441, 262144⟩
    (by decide) selected_cut_14614

theorem unmarked_context_10_1708_376497 : frontier 11 ⟨376497, by decide⟩
    (prefixCache 10 1708) (prefixPartial 10 1708) = false := by
  decide +kernel

theorem node_context_10_1708_376497 : EJMOriginalGlobalDAGData.nodes 11 ⟨376497, by decide⟩ =
    .split (coordinate 10) (![⟨376393, by decide⟩,⟨376429, by decide⟩,⟨376460, by decide⟩,⟨376496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1708_376497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1708 ⟨376497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1708
    ⟨376497, by decide⟩ (by decide) (![⟨376393, by decide⟩,⟨376429, by decide⟩,⟨376460, by decide⟩,⟨376496, by decide⟩]) unmarked_context_10_1708_376497 node_context_10_1708_376497
  intro a
  fin_cases a
  · exact context_11_6832_376393
  · exact context_11_6833_376429
  · exact context_11_6834_376460
  · exact context_11_6835_376496

theorem selected_cut_14615 : selected 10 ⟨376528, by decide⟩
    (prefixPartial 11 6836) = some ⟨11, 2, 0, 376528, 6836, 3193, 262144⟩ := by
  decide +kernel

theorem context_11_6836_376528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6836 ⟨376528, by decide⟩ :=
  accepted_of_selected 11 6836 ⟨376528, by decide⟩ ⟨11, 2, 0, 376528, 6836, 3193, 262144⟩
    (by decide) selected_cut_14615

theorem selected_cut_14616 : selected 10 ⟨376546, by decide⟩
    (prefixPartial 11 6837) = some ⟨11, 2, 0, 376546, 6837, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_6837_376546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6837 ⟨376546, by decide⟩ :=
  accepted_of_selected 11 6837 ⟨376546, by decide⟩ ⟨11, 2, 0, 376546, 6837, 2665, 262144⟩
    (by decide) selected_cut_14616

theorem selected_cut_14617 : selected 10 ⟨376563, by decide⟩
    (prefixPartial 11 6838) = some ⟨11, 2, 0, 376563, 6838, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_6838_376563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6838 ⟨376563, by decide⟩ :=
  accepted_of_selected 11 6838 ⟨376563, by decide⟩ ⟨11, 2, 0, 376563, 6838, 2197, 262144⟩
    (by decide) selected_cut_14617

theorem selected_cut_14618 : selected 10 ⟨376584, by decide⟩
    (prefixPartial 11 6839) = some ⟨11, 2, 0, 376584, 6839, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_6839_376584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6839 ⟨376584, by decide⟩ :=
  accepted_of_selected 11 6839 ⟨376584, by decide⟩ ⟨11, 2, 0, 376584, 6839, 1949, 262144⟩
    (by decide) selected_cut_14618

theorem unmarked_context_10_1709_376585 : frontier 11 ⟨376585, by decide⟩
    (prefixCache 10 1709) (prefixPartial 10 1709) = false := by
  decide +kernel

theorem node_context_10_1709_376585 : EJMOriginalGlobalDAGData.nodes 11 ⟨376585, by decide⟩ =
    .split (coordinate 10) (![⟨376528, by decide⟩,⟨376546, by decide⟩,⟨376563, by decide⟩,⟨376584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1709_376585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1709 ⟨376585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1709
    ⟨376585, by decide⟩ (by decide) (![⟨376528, by decide⟩,⟨376546, by decide⟩,⟨376563, by decide⟩,⟨376584, by decide⟩]) unmarked_context_10_1709_376585 node_context_10_1709_376585
  intro a
  fin_cases a
  · exact context_11_6836_376528
  · exact context_11_6837_376546
  · exact context_11_6838_376563
  · exact context_11_6839_376584

theorem selected_cut_14619 : selected 10 ⟨376601, by decide⟩
    (prefixPartial 11 6840) = some ⟨11, 2, 0, 376601, 6840, 1485, 262144⟩ := by
  decide +kernel

theorem context_11_6840_376601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6840 ⟨376601, by decide⟩ :=
  accepted_of_selected 11 6840 ⟨376601, by decide⟩ ⟨11, 2, 0, 376601, 6840, 1485, 262144⟩
    (by decide) selected_cut_14619

theorem selected_cut_14620 : selected 10 ⟨376616, by decide⟩
    (prefixPartial 11 6841) = some ⟨11, 2, 0, 376616, 6841, 1193, 262144⟩ := by
  decide +kernel

theorem context_11_6841_376616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6841 ⟨376616, by decide⟩ :=
  accepted_of_selected 11 6841 ⟨376616, by decide⟩ ⟨11, 2, 0, 376616, 6841, 1193, 262144⟩
    (by decide) selected_cut_14620

theorem selected_cut_14621 : selected 10 ⟨376630, by decide⟩
    (prefixPartial 11 6842) = some ⟨11, 2, 0, 376630, 6842, 893, 262144⟩ := by
  decide +kernel

theorem context_11_6842_376630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6842 ⟨376630, by decide⟩ :=
  accepted_of_selected 11 6842 ⟨376630, by decide⟩ ⟨11, 2, 0, 376630, 6842, 893, 262144⟩
    (by decide) selected_cut_14621

theorem selected_cut_14622 : selected 10 ⟨376642, by decide⟩
    (prefixPartial 11 6843) = some ⟨11, 2, 0, 376642, 6843, 833, 262144⟩ := by
  decide +kernel

theorem context_11_6843_376642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6843 ⟨376642, by decide⟩ :=
  accepted_of_selected 11 6843 ⟨376642, by decide⟩ ⟨11, 2, 0, 376642, 6843, 833, 262144⟩
    (by decide) selected_cut_14622

theorem unmarked_context_10_1710_376643 : frontier 11 ⟨376643, by decide⟩
    (prefixCache 10 1710) (prefixPartial 10 1710) = false := by
  decide +kernel

theorem node_context_10_1710_376643 : EJMOriginalGlobalDAGData.nodes 11 ⟨376643, by decide⟩ =
    .split (coordinate 10) (![⟨376601, by decide⟩,⟨376616, by decide⟩,⟨376630, by decide⟩,⟨376642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1710_376643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1710 ⟨376643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1710
    ⟨376643, by decide⟩ (by decide) (![⟨376601, by decide⟩,⟨376616, by decide⟩,⟨376630, by decide⟩,⟨376642, by decide⟩]) unmarked_context_10_1710_376643 node_context_10_1710_376643
  intro a
  fin_cases a
  · exact context_11_6840_376601
  · exact context_11_6841_376616
  · exact context_11_6842_376630
  · exact context_11_6843_376642

theorem selected_cut_14623 : selected 11 ⟨376677, by decide⟩
    (prefixPartial 10 1711) = some ⟨10, 2, 0, 376677, 1711, 1941, 1048576⟩ := by
  decide +kernel

theorem context_10_1711_376677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1711 ⟨376677, by decide⟩ :=
  accepted_of_selected 10 1711 ⟨376677, by decide⟩ ⟨10, 2, 0, 376677, 1711, 1941, 1048576⟩
    (by decide) selected_cut_14623

theorem unmarked_context_9_427_376678 : frontier 12 ⟨376678, by decide⟩
    (prefixCache 9 427) (prefixPartial 9 427) = false := by
  decide +kernel

theorem node_context_9_427_376678 : EJMOriginalGlobalDAGData.nodes 12 ⟨376678, by decide⟩ =
    .split (coordinate 9) (![⟨376497, by decide⟩,⟨376585, by decide⟩,⟨376643, by decide⟩,⟨376677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_427_376678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 427 ⟨376678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 427
    ⟨376678, by decide⟩ (by decide) (![⟨376497, by decide⟩,⟨376585, by decide⟩,⟨376643, by decide⟩,⟨376677, by decide⟩]) unmarked_context_9_427_376678 node_context_9_427_376678
  intro a
  fin_cases a
  · exact context_10_1708_376497
  · exact context_10_1709_376585
  · exact context_10_1710_376643
  · exact context_10_1711_376677

theorem unmarked_context_8_106_376679 : frontier 13 ⟨376679, by decide⟩
    (prefixCache 8 106) (prefixPartial 8 106) = false := by
  decide +kernel

theorem node_context_8_106_376679 : EJMOriginalGlobalDAGData.nodes 13 ⟨376679, by decide⟩ =
    .split (coordinate 8) (![⟨372224, by decide⟩,⟨375297, by decide⟩,⟨376360, by decide⟩,⟨376678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_106_376679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 106 ⟨376679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 106
    ⟨376679, by decide⟩ (by decide) (![⟨372224, by decide⟩,⟨375297, by decide⟩,⟨376360, by decide⟩,⟨376678, by decide⟩]) unmarked_context_8_106_376679 node_context_8_106_376679
  intro a
  fin_cases a
  · exact context_9_424_372224
  · exact context_9_425_375297
  · exact context_9_426_376360
  · exact context_9_427_376678

theorem selected_cut_14624 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27392) = some ⟨12, 1, 0, 34034, 27392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27392_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27392 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27392 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27392, 1, 65536⟩
    (by decide) selected_cut_14624

theorem selected_cut_14625 : selected 8 ⟨376756, by decide⟩
    (prefixPartial 13 109572) = some ⟨13, 2, 0, 376756, 109572, 3433, 16384⟩ := by
  decide +kernel

theorem context_13_109572_376756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109572 ⟨376756, by decide⟩ :=
  accepted_of_selected 13 109572 ⟨376756, by decide⟩ ⟨13, 2, 0, 376756, 109572, 3433, 16384⟩
    (by decide) selected_cut_14625

theorem selected_cut_14626 : selected 8 ⟨376826, by decide⟩
    (prefixPartial 13 109573) = some ⟨13, 2, 0, 376826, 109573, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_109573_376826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109573 ⟨376826, by decide⟩ :=
  accepted_of_selected 13 109573 ⟨376826, by decide⟩ ⟨13, 2, 0, 376826, 109573, 1953, 16384⟩
    (by decide) selected_cut_14626

theorem selected_cut_14627 : selected 8 ⟨376857, by decide⟩
    (prefixPartial 13 109574) = some ⟨13, 2, 0, 376857, 109574, 581, 16384⟩ := by
  decide +kernel

theorem context_13_109574_376857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109574 ⟨376857, by decide⟩ :=
  accepted_of_selected 13 109574 ⟨376857, by decide⟩ ⟨13, 2, 0, 376857, 109574, 581, 16384⟩
    (by decide) selected_cut_14627

theorem selected_cut_14628 : selected 8 ⟨250286, by decide⟩
    (prefixPartial 13 109575) = some ⟨13, 2, 0, 250286, 109575, 97, 16384⟩ := by
  decide +kernel

theorem context_13_109575_250286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109575 ⟨250286, by decide⟩ :=
  accepted_of_selected 13 109575 ⟨250286, by decide⟩ ⟨13, 2, 0, 250286, 109575, 97, 16384⟩
    (by decide) selected_cut_14628

theorem unmarked_context_12_27393_376858 : frontier 9 ⟨376858, by decide⟩
    (prefixCache 12 27393) (prefixPartial 12 27393) = false := by
  decide +kernel

theorem node_context_12_27393_376858 : EJMOriginalGlobalDAGData.nodes 9 ⟨376858, by decide⟩ =
    .split (coordinate 12) (![⟨376756, by decide⟩,⟨376826, by decide⟩,⟨376857, by decide⟩,⟨250286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27393_376858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27393 ⟨376858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27393
    ⟨376858, by decide⟩ (by decide) (![⟨376756, by decide⟩,⟨376826, by decide⟩,⟨376857, by decide⟩,⟨250286, by decide⟩]) unmarked_context_12_27393_376858 node_context_12_27393_376858
  intro a
  fin_cases a
  · exact context_13_109572_376756
  · exact context_13_109573_376826
  · exact context_13_109574_376857
  · exact context_13_109575_250286

theorem selected_cut_14629 : selected 9 ⟨347601, by decide⟩
    (prefixPartial 12 27394) = some ⟨12, 1, 0, 347601, 27394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27394_347601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27394 ⟨347601, by decide⟩ :=
  accepted_of_selected 12 27394 ⟨347601, by decide⟩ ⟨12, 1, 0, 347601, 27394, 1, 65536⟩
    (by decide) selected_cut_14629

theorem selected_cut_14630 : selected 8 ⟨376909, by decide⟩
    (prefixPartial 13 109580) = some ⟨13, 2, 0, 376909, 109580, 3781, 16384⟩ := by
  decide +kernel

theorem context_13_109580_376909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109580 ⟨376909, by decide⟩ :=
  accepted_of_selected 13 109580 ⟨376909, by decide⟩ ⟨13, 2, 0, 376909, 109580, 3781, 16384⟩
    (by decide) selected_cut_14630

theorem selected_cut_14631 : selected 8 ⟨376977, by decide⟩
    (prefixPartial 13 109581) = some ⟨13, 2, 0, 376977, 109581, 3909, 16384⟩ := by
  decide +kernel

theorem context_13_109581_376977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109581 ⟨376977, by decide⟩ :=
  accepted_of_selected 13 109581 ⟨376977, by decide⟩ ⟨13, 2, 0, 376977, 109581, 3909, 16384⟩
    (by decide) selected_cut_14631

theorem selected_cut_14632 : selected 8 ⟨377006, by decide⟩
    (prefixPartial 13 109582) = some ⟨13, 2, 0, 377006, 109582, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_109582_377006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109582 ⟨377006, by decide⟩ :=
  accepted_of_selected 13 109582 ⟨377006, by decide⟩ ⟨13, 2, 0, 377006, 109582, 2113, 16384⟩
    (by decide) selected_cut_14632

theorem selected_cut_14633 : selected 8 ⟨377013, by decide⟩
    (prefixPartial 13 109583) = some ⟨13, 2, 0, 377013, 109583, 833, 16384⟩ := by
  decide +kernel

theorem context_13_109583_377013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109583 ⟨377013, by decide⟩ :=
  accepted_of_selected 13 109583 ⟨377013, by decide⟩ ⟨13, 2, 0, 377013, 109583, 833, 16384⟩
    (by decide) selected_cut_14633

theorem unmarked_context_12_27395_377014 : frontier 9 ⟨377014, by decide⟩
    (prefixCache 12 27395) (prefixPartial 12 27395) = false := by
  decide +kernel

theorem node_context_12_27395_377014 : EJMOriginalGlobalDAGData.nodes 9 ⟨377014, by decide⟩ =
    .split (coordinate 12) (![⟨376909, by decide⟩,⟨376977, by decide⟩,⟨377006, by decide⟩,⟨377013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27395_377014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27395 ⟨377014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27395
    ⟨377014, by decide⟩ (by decide) (![⟨376909, by decide⟩,⟨376977, by decide⟩,⟨377006, by decide⟩,⟨377013, by decide⟩]) unmarked_context_12_27395_377014 node_context_12_27395_377014
  intro a
  fin_cases a
  · exact context_13_109580_376909
  · exact context_13_109581_376977
  · exact context_13_109582_377006
  · exact context_13_109583_377013

theorem unmarked_context_11_6848_377015 : frontier 10 ⟨377015, by decide⟩
    (prefixCache 11 6848) (prefixPartial 11 6848) = false := by
  decide +kernel

theorem node_context_11_6848_377015 : EJMOriginalGlobalDAGData.nodes 10 ⟨377015, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨376858, by decide⟩,⟨347601, by decide⟩,⟨377014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6848_377015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6848 ⟨377015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6848
    ⟨377015, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨376858, by decide⟩,⟨347601, by decide⟩,⟨377014, by decide⟩]) unmarked_context_11_6848_377015 node_context_11_6848_377015
  intro a
  fin_cases a
  · exact context_12_27392_34034
  · exact context_12_27393_376858
  · exact context_12_27394_347601
  · exact context_12_27395_377014

theorem selected_cut_14634 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27396) = some ⟨12, 1, 0, 34034, 27396, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27396_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27396 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27396 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27396, 1, 65536⟩
    (by decide) selected_cut_14634

theorem selected_cut_14635 : selected 8 ⟨377074, by decide⟩
    (prefixPartial 13 109588) = some ⟨13, 2, 0, 377074, 109588, 3941, 16384⟩ := by
  decide +kernel

theorem context_13_109588_377074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109588 ⟨377074, by decide⟩ :=
  accepted_of_selected 13 109588 ⟨377074, by decide⟩ ⟨13, 2, 0, 377074, 109588, 3941, 16384⟩
    (by decide) selected_cut_14635

theorem selected_cut_14636 : selected 8 ⟨377131, by decide⟩
    (prefixPartial 13 109589) = some ⟨13, 2, 0, 377131, 109589, 3593, 16384⟩ := by
  decide +kernel

theorem context_13_109589_377131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109589 ⟨377131, by decide⟩ :=
  accepted_of_selected 13 109589 ⟨377131, by decide⟩ ⟨13, 2, 0, 377131, 109589, 3593, 16384⟩
    (by decide) selected_cut_14636

theorem selected_cut_14637 : selected 8 ⟨377179, by decide⟩
    (prefixPartial 13 109590) = some ⟨13, 2, 0, 377179, 109590, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_109590_377179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109590 ⟨377179, by decide⟩ :=
  accepted_of_selected 13 109590 ⟨377179, by decide⟩ ⟨13, 2, 0, 377179, 109590, 2413, 16384⟩
    (by decide) selected_cut_14637

theorem selected_cut_14638 : selected 8 ⟨377185, by decide⟩
    (prefixPartial 13 109591) = some ⟨13, 2, 0, 377185, 109591, 941, 16384⟩ := by
  decide +kernel

theorem context_13_109591_377185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109591 ⟨377185, by decide⟩ :=
  accepted_of_selected 13 109591 ⟨377185, by decide⟩ ⟨13, 2, 0, 377185, 109591, 941, 16384⟩
    (by decide) selected_cut_14638

theorem unmarked_context_12_27397_377186 : frontier 9 ⟨377186, by decide⟩
    (prefixCache 12 27397) (prefixPartial 12 27397) = false := by
  decide +kernel

theorem node_context_12_27397_377186 : EJMOriginalGlobalDAGData.nodes 9 ⟨377186, by decide⟩ =
    .split (coordinate 12) (![⟨377074, by decide⟩,⟨377131, by decide⟩,⟨377179, by decide⟩,⟨377185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27397_377186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27397 ⟨377186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27397
    ⟨377186, by decide⟩ (by decide) (![⟨377074, by decide⟩,⟨377131, by decide⟩,⟨377179, by decide⟩,⟨377185, by decide⟩]) unmarked_context_12_27397_377186 node_context_12_27397_377186
  intro a
  fin_cases a
  · exact context_13_109588_377074
  · exact context_13_109589_377131
  · exact context_13_109590_377179
  · exact context_13_109591_377185

theorem selected_cut_14639 : selected 8 ⟨377245, by decide⟩
    (prefixPartial 13 109592) = some ⟨13, 2, 0, 377245, 109592, 3853, 16384⟩ := by
  decide +kernel

theorem context_13_109592_377245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109592 ⟨377245, by decide⟩ :=
  accepted_of_selected 13 109592 ⟨377245, by decide⟩ ⟨13, 2, 0, 377245, 109592, 3853, 16384⟩
    (by decide) selected_cut_14639

theorem selected_cut_14640 : selected 7 ⟨377276, by decide⟩
    (prefixPartial 14 438372) = some ⟨14, 2, 0, 377276, 438372, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_438372_377276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438372 ⟨377276, by decide⟩ :=
  accepted_of_selected 14 438372 ⟨377276, by decide⟩ ⟨14, 2, 0, 377276, 438372, 1229, 4096⟩
    (by decide) selected_cut_14640

theorem selected_cut_14641 : selected 7 ⟨377292, by decide⟩
    (prefixPartial 14 438373) = some ⟨14, 2, 0, 377292, 438373, 1029, 4096⟩ := by
  decide +kernel

theorem context_14_438373_377292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438373 ⟨377292, by decide⟩ :=
  accepted_of_selected 14 438373 ⟨377292, by decide⟩ ⟨14, 2, 0, 377292, 438373, 1029, 4096⟩
    (by decide) selected_cut_14641

theorem selected_cut_14642 : selected 7 ⟨377312, by decide⟩
    (prefixPartial 14 438374) = some ⟨14, 2, 0, 377312, 438374, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_438374_377312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438374 ⟨377312, by decide⟩ :=
  accepted_of_selected 14 438374 ⟨377312, by decide⟩ ⟨14, 2, 0, 377312, 438374, 1061, 4096⟩
    (by decide) selected_cut_14642

theorem selected_cut_14643 : selected 7 ⟨377329, by decide⟩
    (prefixPartial 14 438375) = some ⟨14, 2, 0, 377329, 438375, 849, 4096⟩ := by
  decide +kernel

theorem context_14_438375_377329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438375 ⟨377329, by decide⟩ :=
  accepted_of_selected 14 438375 ⟨377329, by decide⟩ ⟨14, 2, 0, 377329, 438375, 849, 4096⟩
    (by decide) selected_cut_14643

theorem unmarked_context_13_109593_377330 : frontier 8 ⟨377330, by decide⟩
    (prefixCache 13 109593) (prefixPartial 13 109593) = false := by
  decide +kernel

theorem node_context_13_109593_377330 : EJMOriginalGlobalDAGData.nodes 8 ⟨377330, by decide⟩ =
    .split (coordinate 13) (![⟨377276, by decide⟩,⟨377292, by decide⟩,⟨377312, by decide⟩,⟨377329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109593_377330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109593 ⟨377330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109593
    ⟨377330, by decide⟩ (by decide) (![⟨377276, by decide⟩,⟨377292, by decide⟩,⟨377312, by decide⟩,⟨377329, by decide⟩]) unmarked_context_13_109593_377330 node_context_13_109593_377330
  intro a
  fin_cases a
  · exact context_14_438372_377276
  · exact context_14_438373_377292
  · exact context_14_438374_377312
  · exact context_14_438375_377329

theorem selected_cut_14644 : selected 8 ⟨377383, by decide⟩
    (prefixPartial 13 109594) = some ⟨13, 2, 0, 377383, 109594, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_109594_377383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109594 ⟨377383, by decide⟩ :=
  accepted_of_selected 13 109594 ⟨377383, by decide⟩ ⟨13, 2, 0, 377383, 109594, 2613, 16384⟩
    (by decide) selected_cut_14644

theorem selected_cut_14645 : selected 8 ⟨377396, by decide⟩
    (prefixPartial 13 109595) = some ⟨13, 2, 0, 377396, 109595, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_109595_377396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109595 ⟨377396, by decide⟩ :=
  accepted_of_selected 13 109595 ⟨377396, by decide⟩ ⟨13, 2, 0, 377396, 109595, 1065, 16384⟩
    (by decide) selected_cut_14645

theorem unmarked_context_12_27398_377397 : frontier 9 ⟨377397, by decide⟩
    (prefixCache 12 27398) (prefixPartial 12 27398) = false := by
  decide +kernel

theorem node_context_12_27398_377397 : EJMOriginalGlobalDAGData.nodes 9 ⟨377397, by decide⟩ =
    .split (coordinate 12) (![⟨377245, by decide⟩,⟨377330, by decide⟩,⟨377383, by decide⟩,⟨377396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27398_377397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27398 ⟨377397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27398
    ⟨377397, by decide⟩ (by decide) (![⟨377245, by decide⟩,⟨377330, by decide⟩,⟨377383, by decide⟩,⟨377396, by decide⟩]) unmarked_context_12_27398_377397 node_context_12_27398_377397
  intro a
  fin_cases a
  · exact context_13_109592_377245
  · exact context_13_109593_377330
  · exact context_13_109594_377383
  · exact context_13_109595_377396

theorem selected_cut_14646 : selected 8 ⟨377441, by decide⟩
    (prefixPartial 13 109596) = some ⟨13, 2, 0, 377441, 109596, 3669, 16384⟩ := by
  decide +kernel

theorem context_13_109596_377441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109596 ⟨377441, by decide⟩ :=
  accepted_of_selected 13 109596 ⟨377441, by decide⟩ ⟨13, 2, 0, 377441, 109596, 3669, 16384⟩
    (by decide) selected_cut_14646

theorem selected_cut_14647 : selected 8 ⟨377511, by decide⟩
    (prefixPartial 13 109597) = some ⟨13, 2, 0, 377511, 109597, 4009, 16384⟩ := by
  decide +kernel

theorem context_13_109597_377511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109597 ⟨377511, by decide⟩ :=
  accepted_of_selected 13 109597 ⟨377511, by decide⟩ ⟨13, 2, 0, 377511, 109597, 4009, 16384⟩
    (by decide) selected_cut_14647

theorem selected_cut_14648 : selected 8 ⟨377538, by decide⟩
    (prefixPartial 13 109598) = some ⟨13, 2, 0, 377538, 109598, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_109598_377538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109598 ⟨377538, by decide⟩ :=
  accepted_of_selected 13 109598 ⟨377538, by decide⟩ ⟨13, 2, 0, 377538, 109598, 2437, 16384⟩
    (by decide) selected_cut_14648

theorem selected_cut_14649 : selected 8 ⟨377550, by decide⟩
    (prefixPartial 13 109599) = some ⟨13, 2, 0, 377550, 109599, 973, 16384⟩ := by
  decide +kernel

theorem context_13_109599_377550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109599 ⟨377550, by decide⟩ :=
  accepted_of_selected 13 109599 ⟨377550, by decide⟩ ⟨13, 2, 0, 377550, 109599, 973, 16384⟩
    (by decide) selected_cut_14649

theorem unmarked_context_12_27399_377551 : frontier 9 ⟨377551, by decide⟩
    (prefixCache 12 27399) (prefixPartial 12 27399) = false := by
  decide +kernel

theorem node_context_12_27399_377551 : EJMOriginalGlobalDAGData.nodes 9 ⟨377551, by decide⟩ =
    .split (coordinate 12) (![⟨377441, by decide⟩,⟨377511, by decide⟩,⟨377538, by decide⟩,⟨377550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27399_377551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27399 ⟨377551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27399
    ⟨377551, by decide⟩ (by decide) (![⟨377441, by decide⟩,⟨377511, by decide⟩,⟨377538, by decide⟩,⟨377550, by decide⟩]) unmarked_context_12_27399_377551 node_context_12_27399_377551
  intro a
  fin_cases a
  · exact context_13_109596_377441
  · exact context_13_109597_377511
  · exact context_13_109598_377538
  · exact context_13_109599_377550

theorem unmarked_context_11_6849_377552 : frontier 10 ⟨377552, by decide⟩
    (prefixCache 11 6849) (prefixPartial 11 6849) = false := by
  decide +kernel

theorem node_context_11_6849_377552 : EJMOriginalGlobalDAGData.nodes 10 ⟨377552, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨377186, by decide⟩,⟨377397, by decide⟩,⟨377551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6849_377552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6849 ⟨377552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6849
    ⟨377552, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨377186, by decide⟩,⟨377397, by decide⟩,⟨377551, by decide⟩]) unmarked_context_11_6849_377552 node_context_11_6849_377552
  intro a
  fin_cases a
  · exact context_12_27396_34034
  · exact context_12_27397_377186
  · exact context_12_27398_377397
  · exact context_12_27399_377551

theorem selected_cut_14650 : selected 8 ⟨377609, by decide⟩
    (prefixPartial 13 109600) = some ⟨13, 2, 0, 377609, 109600, 3345, 16384⟩ := by
  decide +kernel

theorem context_13_109600_377609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109600 ⟨377609, by decide⟩ :=
  accepted_of_selected 13 109600 ⟨377609, by decide⟩ ⟨13, 2, 0, 377609, 109600, 3345, 16384⟩
    (by decide) selected_cut_14650

theorem selected_cut_14651 : selected 7 ⟨377647, by decide⟩
    (prefixPartial 14 438404) = some ⟨14, 2, 0, 377647, 438404, 1601, 4096⟩ := by
  decide +kernel

theorem context_14_438404_377647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438404 ⟨377647, by decide⟩ :=
  accepted_of_selected 14 438404 ⟨377647, by decide⟩ ⟨14, 2, 0, 377647, 438404, 1601, 4096⟩
    (by decide) selected_cut_14651

theorem selected_cut_14652 : selected 7 ⟨377668, by decide⟩
    (prefixPartial 14 438405) = some ⟨14, 2, 0, 377668, 438405, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_438405_377668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438405 ⟨377668, by decide⟩ :=
  accepted_of_selected 14 438405 ⟨377668, by decide⟩ ⟨14, 2, 0, 377668, 438405, 1021, 4096⟩
    (by decide) selected_cut_14652

theorem selected_cut_14653 : selected 7 ⟨377696, by decide⟩
    (prefixPartial 14 438406) = some ⟨14, 2, 0, 377696, 438406, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_438406_377696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438406 ⟨377696, by decide⟩ :=
  accepted_of_selected 14 438406 ⟨377696, by decide⟩ ⟨14, 2, 0, 377696, 438406, 1321, 4096⟩
    (by decide) selected_cut_14653

theorem selected_cut_14654 : selected 7 ⟨377715, by decide⟩
    (prefixPartial 14 438407) = some ⟨14, 2, 0, 377715, 438407, 833, 4096⟩ := by
  decide +kernel

theorem context_14_438407_377715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438407 ⟨377715, by decide⟩ :=
  accepted_of_selected 14 438407 ⟨377715, by decide⟩ ⟨14, 2, 0, 377715, 438407, 833, 4096⟩
    (by decide) selected_cut_14654

theorem unmarked_context_13_109601_377716 : frontier 8 ⟨377716, by decide⟩
    (prefixCache 13 109601) (prefixPartial 13 109601) = false := by
  decide +kernel

theorem node_context_13_109601_377716 : EJMOriginalGlobalDAGData.nodes 8 ⟨377716, by decide⟩ =
    .split (coordinate 13) (![⟨377647, by decide⟩,⟨377668, by decide⟩,⟨377696, by decide⟩,⟨377715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109601_377716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109601 ⟨377716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109601
    ⟨377716, by decide⟩ (by decide) (![⟨377647, by decide⟩,⟨377668, by decide⟩,⟨377696, by decide⟩,⟨377715, by decide⟩]) unmarked_context_13_109601_377716 node_context_13_109601_377716
  intro a
  fin_cases a
  · exact context_14_438404_377647
  · exact context_14_438405_377668
  · exact context_14_438406_377696
  · exact context_14_438407_377715

theorem selected_cut_14655 : selected 8 ⟨377778, by decide⟩
    (prefixPartial 13 109602) = some ⟨13, 2, 0, 377778, 109602, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_109602_377778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109602 ⟨377778, by decide⟩ :=
  accepted_of_selected 13 109602 ⟨377778, by decide⟩ ⟨13, 2, 0, 377778, 109602, 2429, 16384⟩
    (by decide) selected_cut_14655

theorem selected_cut_14656 : selected 8 ⟨377808, by decide⟩
    (prefixPartial 13 109603) = some ⟨13, 2, 0, 377808, 109603, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_109603_377808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109603 ⟨377808, by decide⟩ :=
  accepted_of_selected 13 109603 ⟨377808, by decide⟩ ⟨13, 2, 0, 377808, 109603, 1157, 16384⟩
    (by decide) selected_cut_14656

theorem unmarked_context_12_27400_377809 : frontier 9 ⟨377809, by decide⟩
    (prefixCache 12 27400) (prefixPartial 12 27400) = false := by
  decide +kernel

theorem node_context_12_27400_377809 : EJMOriginalGlobalDAGData.nodes 9 ⟨377809, by decide⟩ =
    .split (coordinate 12) (![⟨377609, by decide⟩,⟨377716, by decide⟩,⟨377778, by decide⟩,⟨377808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27400_377809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27400 ⟨377809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27400
    ⟨377809, by decide⟩ (by decide) (![⟨377609, by decide⟩,⟨377716, by decide⟩,⟨377778, by decide⟩,⟨377808, by decide⟩]) unmarked_context_12_27400_377809 node_context_12_27400_377809
  intro a
  fin_cases a
  · exact context_13_109600_377609
  · exact context_13_109601_377716
  · exact context_13_109602_377778
  · exact context_13_109603_377808

theorem selected_cut_14657 : selected 8 ⟨377873, by decide⟩
    (prefixPartial 13 109604) = some ⟨13, 2, 0, 377873, 109604, 3797, 16384⟩ := by
  decide +kernel

theorem context_13_109604_377873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109604 ⟨377873, by decide⟩ :=
  accepted_of_selected 13 109604 ⟨377873, by decide⟩ ⟨13, 2, 0, 377873, 109604, 3797, 16384⟩
    (by decide) selected_cut_14657

theorem selected_cut_14658 : selected 8 ⟨377951, by decide⟩
    (prefixPartial 13 109605) = some ⟨13, 2, 0, 377951, 109605, 4049, 16384⟩ := by
  decide +kernel

theorem context_13_109605_377951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109605 ⟨377951, by decide⟩ :=
  accepted_of_selected 13 109605 ⟨377951, by decide⟩ ⟨13, 2, 0, 377951, 109605, 4049, 16384⟩
    (by decide) selected_cut_14658

theorem selected_cut_14659 : selected 8 ⟨377990, by decide⟩
    (prefixPartial 13 109606) = some ⟨13, 2, 0, 377990, 109606, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_109606_377990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109606 ⟨377990, by decide⟩ :=
  accepted_of_selected 13 109606 ⟨377990, by decide⟩ ⟨13, 2, 0, 377990, 109606, 2249, 16384⟩
    (by decide) selected_cut_14659

theorem selected_cut_14660 : selected 8 ⟨378006, by decide⟩
    (prefixPartial 13 109607) = some ⟨13, 2, 0, 378006, 109607, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_109607_378006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109607 ⟨378006, by decide⟩ :=
  accepted_of_selected 13 109607 ⟨378006, by decide⟩ ⟨13, 2, 0, 378006, 109607, 1045, 16384⟩
    (by decide) selected_cut_14660

theorem unmarked_context_12_27401_378007 : frontier 9 ⟨378007, by decide⟩
    (prefixCache 12 27401) (prefixPartial 12 27401) = false := by
  decide +kernel

theorem node_context_12_27401_378007 : EJMOriginalGlobalDAGData.nodes 9 ⟨378007, by decide⟩ =
    .split (coordinate 12) (![⟨377873, by decide⟩,⟨377951, by decide⟩,⟨377990, by decide⟩,⟨378006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27401_378007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27401 ⟨378007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27401
    ⟨378007, by decide⟩ (by decide) (![⟨377873, by decide⟩,⟨377951, by decide⟩,⟨377990, by decide⟩,⟨378006, by decide⟩]) unmarked_context_12_27401_378007 node_context_12_27401_378007
  intro a
  fin_cases a
  · exact context_13_109604_377873
  · exact context_13_109605_377951
  · exact context_13_109606_377990
  · exact context_13_109607_378006

theorem selected_cut_14661 : selected 8 ⟨378051, by decide⟩
    (prefixPartial 13 109608) = some ⟨13, 2, 0, 378051, 109608, 3353, 16384⟩ := by
  decide +kernel

theorem context_13_109608_378051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109608 ⟨378051, by decide⟩ :=
  accepted_of_selected 13 109608 ⟨378051, by decide⟩ ⟨13, 2, 0, 378051, 109608, 3353, 16384⟩
    (by decide) selected_cut_14661

theorem selected_cut_14662 : selected 7 ⟨378089, by decide⟩
    (prefixPartial 14 438436) = some ⟨14, 2, 0, 378089, 438436, 1413, 4096⟩ := by
  decide +kernel

theorem context_14_438436_378089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438436 ⟨378089, by decide⟩ :=
  accepted_of_selected 14 438436 ⟨378089, by decide⟩ ⟨14, 2, 0, 378089, 438436, 1413, 4096⟩
    (by decide) selected_cut_14662

theorem selected_cut_14663 : selected 7 ⟨378105, by decide⟩
    (prefixPartial 14 438437) = some ⟨14, 2, 0, 378105, 438437, 953, 4096⟩ := by
  decide +kernel

theorem context_14_438437_378105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438437 ⟨378105, by decide⟩ :=
  accepted_of_selected 14 438437 ⟨378105, by decide⟩ ⟨14, 2, 0, 378105, 438437, 953, 4096⟩
    (by decide) selected_cut_14663

theorem selected_cut_14664 : selected 7 ⟨378120, by decide⟩
    (prefixPartial 14 438438) = some ⟨14, 2, 0, 378120, 438438, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_438438_378120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438438 ⟨378120, by decide⟩ :=
  accepted_of_selected 14 438438 ⟨378120, by decide⟩ ⟨14, 2, 0, 378120, 438438, 1065, 4096⟩
    (by decide) selected_cut_14664

theorem selected_cut_14665 : selected 7 ⟨378134, by decide⟩
    (prefixPartial 14 438439) = some ⟨14, 2, 0, 378134, 438439, 817, 4096⟩ := by
  decide +kernel

theorem context_14_438439_378134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438439 ⟨378134, by decide⟩ :=
  accepted_of_selected 14 438439 ⟨378134, by decide⟩ ⟨14, 2, 0, 378134, 438439, 817, 4096⟩
    (by decide) selected_cut_14665

theorem unmarked_context_13_109609_378135 : frontier 8 ⟨378135, by decide⟩
    (prefixCache 13 109609) (prefixPartial 13 109609) = false := by
  decide +kernel

theorem node_context_13_109609_378135 : EJMOriginalGlobalDAGData.nodes 8 ⟨378135, by decide⟩ =
    .split (coordinate 13) (![⟨378089, by decide⟩,⟨378105, by decide⟩,⟨378120, by decide⟩,⟨378134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109609_378135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109609 ⟨378135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109609
    ⟨378135, by decide⟩ (by decide) (![⟨378089, by decide⟩,⟨378105, by decide⟩,⟨378120, by decide⟩,⟨378134, by decide⟩]) unmarked_context_13_109609_378135 node_context_13_109609_378135
  intro a
  fin_cases a
  · exact context_14_438436_378089
  · exact context_14_438437_378105
  · exact context_14_438438_378120
  · exact context_14_438439_378134

theorem selected_cut_14666 : selected 8 ⟨378181, by decide⟩
    (prefixPartial 13 109610) = some ⟨13, 2, 0, 378181, 109610, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_109610_378181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109610 ⟨378181, by decide⟩ :=
  accepted_of_selected 13 109610 ⟨378181, by decide⟩ ⟨13, 2, 0, 378181, 109610, 2533, 16384⟩
    (by decide) selected_cut_14666

theorem selected_cut_14667 : selected 8 ⟨378196, by decide⟩
    (prefixPartial 13 109611) = some ⟨13, 2, 0, 378196, 109611, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_109611_378196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109611 ⟨378196, by decide⟩ :=
  accepted_of_selected 13 109611 ⟨378196, by decide⟩ ⟨13, 2, 0, 378196, 109611, 1001, 16384⟩
    (by decide) selected_cut_14667

theorem unmarked_context_12_27402_378197 : frontier 9 ⟨378197, by decide⟩
    (prefixCache 12 27402) (prefixPartial 12 27402) = false := by
  decide +kernel

theorem node_context_12_27402_378197 : EJMOriginalGlobalDAGData.nodes 9 ⟨378197, by decide⟩ =
    .split (coordinate 12) (![⟨378051, by decide⟩,⟨378135, by decide⟩,⟨378181, by decide⟩,⟨378196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27402_378197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27402 ⟨378197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27402
    ⟨378197, by decide⟩ (by decide) (![⟨378051, by decide⟩,⟨378135, by decide⟩,⟨378181, by decide⟩,⟨378196, by decide⟩]) unmarked_context_12_27402_378197 node_context_12_27402_378197
  intro a
  fin_cases a
  · exact context_13_109608_378051
  · exact context_13_109609_378135
  · exact context_13_109610_378181
  · exact context_13_109611_378196

theorem selected_cut_14668 : selected 8 ⟨378241, by decide⟩
    (prefixPartial 13 109612) = some ⟨13, 2, 0, 378241, 109612, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_109612_378241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109612 ⟨378241, by decide⟩ :=
  accepted_of_selected 13 109612 ⟨378241, by decide⟩ ⟨13, 2, 0, 378241, 109612, 3205, 16384⟩
    (by decide) selected_cut_14668

theorem selected_cut_14669 : selected 7 ⟨378268, by decide⟩
    (prefixPartial 14 438452) = some ⟨14, 2, 0, 378268, 438452, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_438452_378268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438452 ⟨378268, by decide⟩ :=
  accepted_of_selected 14 438452 ⟨378268, by decide⟩ ⟨14, 2, 0, 378268, 438452, 1357, 4096⟩
    (by decide) selected_cut_14669

theorem selected_cut_14670 : selected 7 ⟨378293, by decide⟩
    (prefixPartial 14 438453) = some ⟨14, 2, 0, 378293, 438453, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_438453_378293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438453 ⟨378293, by decide⟩ :=
  accepted_of_selected 14 438453 ⟨378293, by decide⟩ ⟨14, 2, 0, 378293, 438453, 1033, 4096⟩
    (by decide) selected_cut_14670

theorem selected_cut_14671 : selected 7 ⟨378309, by decide⟩
    (prefixPartial 14 438454) = some ⟨14, 2, 0, 378309, 438454, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_438454_378309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438454 ⟨378309, by decide⟩ :=
  accepted_of_selected 14 438454 ⟨378309, by decide⟩ ⟨14, 2, 0, 378309, 438454, 1077, 4096⟩
    (by decide) selected_cut_14671

theorem selected_cut_14672 : selected 7 ⟨378322, by decide⟩
    (prefixPartial 14 438455) = some ⟨14, 2, 0, 378322, 438455, 881, 4096⟩ := by
  decide +kernel

theorem context_14_438455_378322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438455 ⟨378322, by decide⟩ :=
  accepted_of_selected 14 438455 ⟨378322, by decide⟩ ⟨14, 2, 0, 378322, 438455, 881, 4096⟩
    (by decide) selected_cut_14672

theorem unmarked_context_13_109613_378323 : frontier 8 ⟨378323, by decide⟩
    (prefixCache 13 109613) (prefixPartial 13 109613) = false := by
  decide +kernel

theorem node_context_13_109613_378323 : EJMOriginalGlobalDAGData.nodes 8 ⟨378323, by decide⟩ =
    .split (coordinate 13) (![⟨378268, by decide⟩,⟨378293, by decide⟩,⟨378309, by decide⟩,⟨378322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109613_378323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109613 ⟨378323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109613
    ⟨378323, by decide⟩ (by decide) (![⟨378268, by decide⟩,⟨378293, by decide⟩,⟨378309, by decide⟩,⟨378322, by decide⟩]) unmarked_context_13_109613_378323 node_context_13_109613_378323
  intro a
  fin_cases a
  · exact context_14_438452_378268
  · exact context_14_438453_378293
  · exact context_14_438454_378309
  · exact context_14_438455_378322

theorem selected_cut_14673 : selected 8 ⟨378350, by decide⟩
    (prefixPartial 13 109614) = some ⟨13, 2, 0, 378350, 109614, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_109614_378350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109614 ⟨378350, by decide⟩ :=
  accepted_of_selected 13 109614 ⟨378350, by decide⟩ ⟨13, 2, 0, 378350, 109614, 2133, 16384⟩
    (by decide) selected_cut_14673

theorem selected_cut_14674 : selected 8 ⟨378357, by decide⟩
    (prefixPartial 13 109615) = some ⟨13, 2, 0, 378357, 109615, 881, 16384⟩ := by
  decide +kernel

theorem context_13_109615_378357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109615 ⟨378357, by decide⟩ :=
  accepted_of_selected 13 109615 ⟨378357, by decide⟩ ⟨13, 2, 0, 378357, 109615, 881, 16384⟩
    (by decide) selected_cut_14674

theorem unmarked_context_12_27403_378358 : frontier 9 ⟨378358, by decide⟩
    (prefixCache 12 27403) (prefixPartial 12 27403) = false := by
  decide +kernel

theorem node_context_12_27403_378358 : EJMOriginalGlobalDAGData.nodes 9 ⟨378358, by decide⟩ =
    .split (coordinate 12) (![⟨378241, by decide⟩,⟨378323, by decide⟩,⟨378350, by decide⟩,⟨378357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27403_378358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27403 ⟨378358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27403
    ⟨378358, by decide⟩ (by decide) (![⟨378241, by decide⟩,⟨378323, by decide⟩,⟨378350, by decide⟩,⟨378357, by decide⟩]) unmarked_context_12_27403_378358 node_context_12_27403_378358
  intro a
  fin_cases a
  · exact context_13_109612_378241
  · exact context_13_109613_378323
  · exact context_13_109614_378350
  · exact context_13_109615_378357

theorem unmarked_context_11_6850_378359 : frontier 10 ⟨378359, by decide⟩
    (prefixCache 11 6850) (prefixPartial 11 6850) = false := by
  decide +kernel

theorem node_context_11_6850_378359 : EJMOriginalGlobalDAGData.nodes 10 ⟨378359, by decide⟩ =
    .split (coordinate 11) (![⟨377809, by decide⟩,⟨378007, by decide⟩,⟨378197, by decide⟩,⟨378358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6850_378359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6850 ⟨378359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6850
    ⟨378359, by decide⟩ (by decide) (![⟨377809, by decide⟩,⟨378007, by decide⟩,⟨378197, by decide⟩,⟨378358, by decide⟩]) unmarked_context_11_6850_378359 node_context_11_6850_378359
  intro a
  fin_cases a
  · exact context_12_27400_377809
  · exact context_12_27401_378007
  · exact context_12_27402_378197
  · exact context_12_27403_378358

theorem selected_cut_14675 : selected 8 ⟨378397, by decide⟩
    (prefixPartial 13 109616) = some ⟨13, 2, 0, 378397, 109616, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_109616_378397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109616 ⟨378397, by decide⟩ :=
  accepted_of_selected 13 109616 ⟨378397, by decide⟩ ⟨13, 2, 0, 378397, 109616, 2589, 16384⟩
    (by decide) selected_cut_14675

theorem selected_cut_14676 : selected 8 ⟨378466, by decide⟩
    (prefixPartial 13 109617) = some ⟨13, 2, 0, 378466, 109617, 3949, 16384⟩ := by
  decide +kernel

theorem context_13_109617_378466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109617 ⟨378466, by decide⟩ :=
  accepted_of_selected 13 109617 ⟨378466, by decide⟩ ⟨13, 2, 0, 378466, 109617, 3949, 16384⟩
    (by decide) selected_cut_14676

theorem selected_cut_14677 : selected 8 ⟨378492, by decide⟩
    (prefixPartial 13 109618) = some ⟨13, 2, 0, 378492, 109618, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_109618_378492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109618 ⟨378492, by decide⟩ :=
  accepted_of_selected 13 109618 ⟨378492, by decide⟩ ⟨13, 2, 0, 378492, 109618, 2137, 16384⟩
    (by decide) selected_cut_14677

theorem selected_cut_14678 : selected 8 ⟨378506, by decide⟩
    (prefixPartial 13 109619) = some ⟨13, 2, 0, 378506, 109619, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_109619_378506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109619 ⟨378506, by decide⟩ :=
  accepted_of_selected 13 109619 ⟨378506, by decide⟩ ⟨13, 2, 0, 378506, 109619, 1013, 16384⟩
    (by decide) selected_cut_14678

theorem unmarked_context_12_27404_378507 : frontier 9 ⟨378507, by decide⟩
    (prefixCache 12 27404) (prefixPartial 12 27404) = false := by
  decide +kernel

theorem node_context_12_27404_378507 : EJMOriginalGlobalDAGData.nodes 9 ⟨378507, by decide⟩ =
    .split (coordinate 12) (![⟨378397, by decide⟩,⟨378466, by decide⟩,⟨378492, by decide⟩,⟨378506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27404_378507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27404 ⟨378507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27404
    ⟨378507, by decide⟩ (by decide) (![⟨378397, by decide⟩,⟨378466, by decide⟩,⟨378492, by decide⟩,⟨378506, by decide⟩]) unmarked_context_12_27404_378507 node_context_12_27404_378507
  intro a
  fin_cases a
  · exact context_13_109616_378397
  · exact context_13_109617_378466
  · exact context_13_109618_378492
  · exact context_13_109619_378506

theorem selected_cut_14679 : selected 8 ⟨378551, by decide⟩
    (prefixPartial 13 109620) = some ⟨13, 2, 0, 378551, 109620, 3153, 16384⟩ := by
  decide +kernel

theorem context_13_109620_378551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109620 ⟨378551, by decide⟩ :=
  accepted_of_selected 13 109620 ⟨378551, by decide⟩ ⟨13, 2, 0, 378551, 109620, 3153, 16384⟩
    (by decide) selected_cut_14679

theorem selected_cut_14680 : selected 8 ⟨378612, by decide⟩
    (prefixPartial 13 109621) = some ⟨13, 2, 0, 378612, 109621, 3473, 16384⟩ := by
  decide +kernel

theorem context_13_109621_378612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109621 ⟨378612, by decide⟩ :=
  accepted_of_selected 13 109621 ⟨378612, by decide⟩ ⟨13, 2, 0, 378612, 109621, 3473, 16384⟩
    (by decide) selected_cut_14680

theorem selected_cut_14681 : selected 8 ⟨378646, by decide⟩
    (prefixPartial 13 109622) = some ⟨13, 2, 0, 378646, 109622, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_109622_378646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109622 ⟨378646, by decide⟩ :=
  accepted_of_selected 13 109622 ⟨378646, by decide⟩ ⟨13, 2, 0, 378646, 109622, 2197, 16384⟩
    (by decide) selected_cut_14681

theorem selected_cut_14682 : selected 8 ⟨378655, by decide⟩
    (prefixPartial 13 109623) = some ⟨13, 2, 0, 378655, 109623, 869, 16384⟩ := by
  decide +kernel

theorem context_13_109623_378655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109623 ⟨378655, by decide⟩ :=
  accepted_of_selected 13 109623 ⟨378655, by decide⟩ ⟨13, 2, 0, 378655, 109623, 869, 16384⟩
    (by decide) selected_cut_14682

theorem unmarked_context_12_27405_378656 : frontier 9 ⟨378656, by decide⟩
    (prefixCache 12 27405) (prefixPartial 12 27405) = false := by
  decide +kernel

theorem node_context_12_27405_378656 : EJMOriginalGlobalDAGData.nodes 9 ⟨378656, by decide⟩ =
    .split (coordinate 12) (![⟨378551, by decide⟩,⟨378612, by decide⟩,⟨378646, by decide⟩,⟨378655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27405_378656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27405 ⟨378656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27405
    ⟨378656, by decide⟩ (by decide) (![⟨378551, by decide⟩,⟨378612, by decide⟩,⟨378646, by decide⟩,⟨378655, by decide⟩]) unmarked_context_12_27405_378656 node_context_12_27405_378656
  intro a
  fin_cases a
  · exact context_13_109620_378551
  · exact context_13_109621_378612
  · exact context_13_109622_378646
  · exact context_13_109623_378655

theorem selected_cut_14683 : selected 8 ⟨378715, by decide⟩
    (prefixPartial 13 109624) = some ⟨13, 2, 0, 378715, 109624, 3329, 16384⟩ := by
  decide +kernel

theorem context_13_109624_378715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109624 ⟨378715, by decide⟩ :=
  accepted_of_selected 13 109624 ⟨378715, by decide⟩ ⟨13, 2, 0, 378715, 109624, 3329, 16384⟩
    (by decide) selected_cut_14683

theorem selected_cut_14684 : selected 8 ⟨378788, by decide⟩
    (prefixPartial 13 109625) = some ⟨13, 2, 0, 378788, 109625, 4033, 16384⟩ := by
  decide +kernel

theorem context_13_109625_378788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109625 ⟨378788, by decide⟩ :=
  accepted_of_selected 13 109625 ⟨378788, by decide⟩ ⟨13, 2, 0, 378788, 109625, 4033, 16384⟩
    (by decide) selected_cut_14684

theorem selected_cut_14685 : selected 8 ⟨378823, by decide⟩
    (prefixPartial 13 109626) = some ⟨13, 2, 0, 378823, 109626, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_109626_378823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109626 ⟨378823, by decide⟩ :=
  accepted_of_selected 13 109626 ⟨378823, by decide⟩ ⟨13, 2, 0, 378823, 109626, 2245, 16384⟩
    (by decide) selected_cut_14685

theorem selected_cut_14686 : selected 8 ⟨378833, by decide⟩
    (prefixPartial 13 109627) = some ⟨13, 2, 0, 378833, 109627, 909, 16384⟩ := by
  decide +kernel

theorem context_13_109627_378833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109627 ⟨378833, by decide⟩ :=
  accepted_of_selected 13 109627 ⟨378833, by decide⟩ ⟨13, 2, 0, 378833, 109627, 909, 16384⟩
    (by decide) selected_cut_14686

theorem unmarked_context_12_27406_378834 : frontier 9 ⟨378834, by decide⟩
    (prefixCache 12 27406) (prefixPartial 12 27406) = false := by
  decide +kernel

theorem node_context_12_27406_378834 : EJMOriginalGlobalDAGData.nodes 9 ⟨378834, by decide⟩ =
    .split (coordinate 12) (![⟨378715, by decide⟩,⟨378788, by decide⟩,⟨378823, by decide⟩,⟨378833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27406_378834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27406 ⟨378834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27406
    ⟨378834, by decide⟩ (by decide) (![⟨378715, by decide⟩,⟨378788, by decide⟩,⟨378823, by decide⟩,⟨378833, by decide⟩]) unmarked_context_12_27406_378834 node_context_12_27406_378834
  intro a
  fin_cases a
  · exact context_13_109624_378715
  · exact context_13_109625_378788
  · exact context_13_109626_378823
  · exact context_13_109627_378833

theorem selected_cut_14687 : selected 7 ⟨378840, by decide⟩
    (prefixPartial 14 438512) = some ⟨14, 2, 0, 378840, 438512, 289, 4096⟩ := by
  decide +kernel

theorem context_14_438512_378840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438512 ⟨378840, by decide⟩ :=
  accepted_of_selected 14 438512 ⟨378840, by decide⟩ ⟨14, 2, 0, 378840, 438512, 289, 4096⟩
    (by decide) selected_cut_14687

theorem selected_cut_14688 : selected 7 ⟨378873, by decide⟩
    (prefixPartial 14 438513) = some ⟨14, 2, 0, 378873, 438513, 1789, 4096⟩ := by
  decide +kernel

theorem context_14_438513_378873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438513 ⟨378873, by decide⟩ :=
  accepted_of_selected 14 438513 ⟨378873, by decide⟩ ⟨14, 2, 0, 378873, 438513, 1789, 4096⟩
    (by decide) selected_cut_14688

theorem selected_cut_14689 : selected 7 ⟨378901, by decide⟩
    (prefixPartial 14 438514) = some ⟨14, 2, 0, 378901, 438514, 1485, 4096⟩ := by
  decide +kernel

theorem context_14_438514_378901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438514 ⟨378901, by decide⟩ :=
  accepted_of_selected 14 438514 ⟨378901, by decide⟩ ⟨14, 2, 0, 378901, 438514, 1485, 4096⟩
    (by decide) selected_cut_14689

theorem selected_cut_14690 : selected 7 ⟨378929, by decide⟩
    (prefixPartial 14 438515) = some ⟨14, 2, 0, 378929, 438515, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_438515_378929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438515 ⟨378929, by decide⟩ :=
  accepted_of_selected 14 438515 ⟨378929, by decide⟩ ⟨14, 2, 0, 378929, 438515, 1433, 4096⟩
    (by decide) selected_cut_14690

theorem unmarked_context_13_109628_378930 : frontier 8 ⟨378930, by decide⟩
    (prefixCache 13 109628) (prefixPartial 13 109628) = false := by
  decide +kernel

theorem node_context_13_109628_378930 : EJMOriginalGlobalDAGData.nodes 8 ⟨378930, by decide⟩ =
    .split (coordinate 13) (![⟨378840, by decide⟩,⟨378873, by decide⟩,⟨378901, by decide⟩,⟨378929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109628_378930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109628 ⟨378930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109628
    ⟨378930, by decide⟩ (by decide) (![⟨378840, by decide⟩,⟨378873, by decide⟩,⟨378901, by decide⟩,⟨378929, by decide⟩]) unmarked_context_13_109628_378930 node_context_13_109628_378930
  intro a
  fin_cases a
  · exact context_14_438512_378840
  · exact context_14_438513_378873
  · exact context_14_438514_378901
  · exact context_14_438515_378929

theorem selected_cut_14691 : selected 7 ⟨378977, by decide⟩
    (prefixPartial 14 438516) = some ⟨14, 2, 0, 378977, 438516, 1889, 4096⟩ := by
  decide +kernel

theorem context_14_438516_378977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438516 ⟨378977, by decide⟩ :=
  accepted_of_selected 14 438516 ⟨378977, by decide⟩ ⟨14, 2, 0, 378977, 438516, 1889, 4096⟩
    (by decide) selected_cut_14691

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
