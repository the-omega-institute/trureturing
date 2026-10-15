/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover430
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41379 : selected 10 ⟨1131658, by decide⟩
    (prefixPartial 11 83685) = some ⟨11, 2, 0, 1131658, 83685, 2161, 262144⟩ := by
  decide +kernel

theorem context_11_83685_1131658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83685 ⟨1131658, by decide⟩ :=
  accepted_of_selected 11 83685 ⟨1131658, by decide⟩ ⟨11, 2, 0, 1131658, 83685, 2161, 262144⟩
    (by decide) selected_cut_41379

theorem selected_cut_41380 : selected 10 ⟨1131705, by decide⟩
    (prefixPartial 11 83686) = some ⟨11, 2, 0, 1131705, 83686, 2761, 262144⟩ := by
  decide +kernel

theorem context_11_83686_1131705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83686 ⟨1131705, by decide⟩ :=
  accepted_of_selected 11 83686 ⟨1131705, by decide⟩ ⟨11, 2, 0, 1131705, 83686, 2761, 262144⟩
    (by decide) selected_cut_41380

theorem selected_cut_41381 : selected 10 ⟨1131755, by decide⟩
    (prefixPartial 11 83687) = some ⟨11, 2, 0, 1131755, 83687, 2785, 262144⟩ := by
  decide +kernel

theorem context_11_83687_1131755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83687 ⟨1131755, by decide⟩ :=
  accepted_of_selected 11 83687 ⟨1131755, by decide⟩ ⟨11, 2, 0, 1131755, 83687, 2785, 262144⟩
    (by decide) selected_cut_41381

theorem unmarked_context_10_20921_1131756 : frontier 11 ⟨1131756, by decide⟩
    (prefixCache 10 20921) (prefixPartial 10 20921) = false := by
  decide +kernel

theorem node_context_10_20921_1131756 : EJMOriginalGlobalDAGData.nodes 11 ⟨1131756, by decide⟩ =
    .split (coordinate 10) (![⟨1131594, by decide⟩,⟨1131658, by decide⟩,⟨1131705, by decide⟩,⟨1131755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20921_1131756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20921 ⟨1131756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20921
    ⟨1131756, by decide⟩ (by decide) (![⟨1131594, by decide⟩,⟨1131658, by decide⟩,⟨1131705, by decide⟩,⟨1131755, by decide⟩]) unmarked_context_10_20921_1131756 node_context_10_20921_1131756
  intro a
  fin_cases a
  · exact context_11_83684_1131594
  · exact context_11_83685_1131658
  · exact context_11_83686_1131705
  · exact context_11_83687_1131755

theorem selected_cut_41382 : selected 10 ⟨1131800, by decide⟩
    (prefixPartial 11 83688) = some ⟨11, 2, 0, 1131800, 83688, 2765, 262144⟩ := by
  decide +kernel

theorem context_11_83688_1131800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83688 ⟨1131800, by decide⟩ :=
  accepted_of_selected 11 83688 ⟨1131800, by decide⟩ ⟨11, 2, 0, 1131800, 83688, 2765, 262144⟩
    (by decide) selected_cut_41382

theorem selected_cut_41383 : selected 10 ⟨1131841, by decide⟩
    (prefixPartial 11 83689) = some ⟨11, 2, 0, 1131841, 83689, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_83689_1131841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83689 ⟨1131841, by decide⟩ :=
  accepted_of_selected 11 83689 ⟨1131841, by decide⟩ ⟨11, 2, 0, 1131841, 83689, 1885, 262144⟩
    (by decide) selected_cut_41383

theorem selected_cut_41384 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 83690) = some ⟨11, 1, 0, 1109453, 83690, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83690_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83690 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 83690 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 83690, 1, 262144⟩
    (by decide) selected_cut_41384

theorem selected_cut_41385 : selected 10 ⟨1131867, by decide⟩
    (prefixPartial 11 83691) = some ⟨11, 2, 0, 1131867, 83691, 1545, 262144⟩ := by
  decide +kernel

theorem context_11_83691_1131867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83691 ⟨1131867, by decide⟩ :=
  accepted_of_selected 11 83691 ⟨1131867, by decide⟩ ⟨11, 2, 0, 1131867, 83691, 1545, 262144⟩
    (by decide) selected_cut_41385

theorem unmarked_context_10_20922_1131868 : frontier 11 ⟨1131868, by decide⟩
    (prefixCache 10 20922) (prefixPartial 10 20922) = false := by
  decide +kernel

theorem node_context_10_20922_1131868 : EJMOriginalGlobalDAGData.nodes 11 ⟨1131868, by decide⟩ =
    .split (coordinate 10) (![⟨1131800, by decide⟩,⟨1131841, by decide⟩,⟨1109453, by decide⟩,⟨1131867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20922_1131868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20922 ⟨1131868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20922
    ⟨1131868, by decide⟩ (by decide) (![⟨1131800, by decide⟩,⟨1131841, by decide⟩,⟨1109453, by decide⟩,⟨1131867, by decide⟩]) unmarked_context_10_20922_1131868 node_context_10_20922_1131868
  intro a
  fin_cases a
  · exact context_11_83688_1131800
  · exact context_11_83689_1131841
  · exact context_11_83690_1109453
  · exact context_11_83691_1131867

theorem selected_cut_41386 : selected 10 ⟨1131938, by decide⟩
    (prefixPartial 11 83692) = some ⟨11, 2, 0, 1131938, 83692, 3581, 262144⟩ := by
  decide +kernel

theorem context_11_83692_1131938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83692 ⟨1131938, by decide⟩ :=
  accepted_of_selected 11 83692 ⟨1131938, by decide⟩ ⟨11, 2, 0, 1131938, 83692, 3581, 262144⟩
    (by decide) selected_cut_41386

theorem selected_cut_41387 : selected 10 ⟨1131983, by decide⟩
    (prefixPartial 11 83693) = some ⟨11, 2, 0, 1131983, 83693, 2941, 262144⟩ := by
  decide +kernel

theorem context_11_83693_1131983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83693 ⟨1131983, by decide⟩ :=
  accepted_of_selected 11 83693 ⟨1131983, by decide⟩ ⟨11, 2, 0, 1131983, 83693, 2941, 262144⟩
    (by decide) selected_cut_41387

theorem selected_cut_41388 : selected 10 ⟨1132022, by decide⟩
    (prefixPartial 11 83694) = some ⟨11, 2, 0, 1132022, 83694, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_83694_1132022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83694 ⟨1132022, by decide⟩ :=
  accepted_of_selected 11 83694 ⟨1132022, by decide⟩ ⟨11, 2, 0, 1132022, 83694, 2013, 262144⟩
    (by decide) selected_cut_41388

theorem selected_cut_41389 : selected 10 ⟨1132058, by decide⟩
    (prefixPartial 11 83695) = some ⟨11, 2, 0, 1132058, 83695, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_83695_1132058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83695 ⟨1132058, by decide⟩ :=
  accepted_of_selected 11 83695 ⟨1132058, by decide⟩ ⟨11, 2, 0, 1132058, 83695, 1489, 262144⟩
    (by decide) selected_cut_41389

theorem unmarked_context_10_20923_1132059 : frontier 11 ⟨1132059, by decide⟩
    (prefixCache 10 20923) (prefixPartial 10 20923) = false := by
  decide +kernel

theorem node_context_10_20923_1132059 : EJMOriginalGlobalDAGData.nodes 11 ⟨1132059, by decide⟩ =
    .split (coordinate 10) (![⟨1131938, by decide⟩,⟨1131983, by decide⟩,⟨1132022, by decide⟩,⟨1132058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20923_1132059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20923 ⟨1132059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20923
    ⟨1132059, by decide⟩ (by decide) (![⟨1131938, by decide⟩,⟨1131983, by decide⟩,⟨1132022, by decide⟩,⟨1132058, by decide⟩]) unmarked_context_10_20923_1132059 node_context_10_20923_1132059
  intro a
  fin_cases a
  · exact context_11_83692_1131938
  · exact context_11_83693_1131983
  · exact context_11_83694_1132022
  · exact context_11_83695_1132058

theorem unmarked_context_9_5230_1132060 : frontier 12 ⟨1132060, by decide⟩
    (prefixCache 9 5230) (prefixPartial 9 5230) = false := by
  decide +kernel

theorem node_context_9_5230_1132060 : EJMOriginalGlobalDAGData.nodes 12 ⟨1132060, by decide⟩ =
    .split (coordinate 9) (![⟨1131510, by decide⟩,⟨1131756, by decide⟩,⟨1131868, by decide⟩,⟨1132059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5230_1132060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5230 ⟨1132060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5230
    ⟨1132060, by decide⟩ (by decide) (![⟨1131510, by decide⟩,⟨1131756, by decide⟩,⟨1131868, by decide⟩,⟨1132059, by decide⟩]) unmarked_context_9_5230_1132060 node_context_9_5230_1132060
  intro a
  fin_cases a
  · exact context_10_20920_1131510
  · exact context_10_20921_1131756
  · exact context_10_20922_1131868
  · exact context_10_20923_1132059

theorem selected_cut_41390 : selected 10 ⟨1132076, by decide⟩
    (prefixPartial 11 83696) = some ⟨11, 2, 0, 1132076, 83696, 997, 262144⟩ := by
  decide +kernel

theorem context_11_83696_1132076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83696 ⟨1132076, by decide⟩ :=
  accepted_of_selected 11 83696 ⟨1132076, by decide⟩ ⟨11, 2, 0, 1132076, 83696, 997, 262144⟩
    (by decide) selected_cut_41390

theorem selected_cut_41391 : selected 10 ⟨1132102, by decide⟩
    (prefixPartial 11 83697) = some ⟨11, 2, 0, 1132102, 83697, 1737, 262144⟩ := by
  decide +kernel

theorem context_11_83697_1132102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83697 ⟨1132102, by decide⟩ :=
  accepted_of_selected 11 83697 ⟨1132102, by decide⟩ ⟨11, 2, 0, 1132102, 83697, 1737, 262144⟩
    (by decide) selected_cut_41391

theorem selected_cut_41392 : selected 10 ⟨1132129, by decide⟩
    (prefixPartial 11 83698) = some ⟨11, 2, 0, 1132129, 83698, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_83698_1132129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83698 ⟨1132129, by decide⟩ :=
  accepted_of_selected 11 83698 ⟨1132129, by decide⟩ ⟨11, 2, 0, 1132129, 83698, 1517, 262144⟩
    (by decide) selected_cut_41392

theorem selected_cut_41393 : selected 10 ⟨1132146, by decide⟩
    (prefixPartial 11 83699) = some ⟨11, 2, 0, 1132146, 83699, 1201, 262144⟩ := by
  decide +kernel

theorem context_11_83699_1132146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83699 ⟨1132146, by decide⟩ :=
  accepted_of_selected 11 83699 ⟨1132146, by decide⟩ ⟨11, 2, 0, 1132146, 83699, 1201, 262144⟩
    (by decide) selected_cut_41393

theorem unmarked_context_10_20924_1132147 : frontier 11 ⟨1132147, by decide⟩
    (prefixCache 10 20924) (prefixPartial 10 20924) = false := by
  decide +kernel

theorem node_context_10_20924_1132147 : EJMOriginalGlobalDAGData.nodes 11 ⟨1132147, by decide⟩ =
    .split (coordinate 10) (![⟨1132076, by decide⟩,⟨1132102, by decide⟩,⟨1132129, by decide⟩,⟨1132146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20924_1132147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20924 ⟨1132147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20924
    ⟨1132147, by decide⟩ (by decide) (![⟨1132076, by decide⟩,⟨1132102, by decide⟩,⟨1132129, by decide⟩,⟨1132146, by decide⟩]) unmarked_context_10_20924_1132147 node_context_10_20924_1132147
  intro a
  fin_cases a
  · exact context_11_83696_1132076
  · exact context_11_83697_1132102
  · exact context_11_83698_1132129
  · exact context_11_83699_1132146

theorem selected_cut_41394 : selected 11 ⟨1132205, by decide⟩
    (prefixPartial 10 20925) = some ⟨10, 2, 0, 1132205, 20925, 3737, 1048576⟩ := by
  decide +kernel

theorem context_10_20925_1132205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20925 ⟨1132205, by decide⟩ :=
  accepted_of_selected 10 20925 ⟨1132205, by decide⟩ ⟨10, 2, 0, 1132205, 20925, 3737, 1048576⟩
    (by decide) selected_cut_41394

theorem selected_cut_41395 : selected 11 ⟨1132244, by decide⟩
    (prefixPartial 10 20926) = some ⟨10, 2, 0, 1132244, 20926, 1797, 1048576⟩ := by
  decide +kernel

theorem context_10_20926_1132244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20926 ⟨1132244, by decide⟩ :=
  accepted_of_selected 10 20926 ⟨1132244, by decide⟩ ⟨10, 2, 0, 1132244, 20926, 1797, 1048576⟩
    (by decide) selected_cut_41395

theorem selected_cut_41396 : selected 11 ⟨1132276, by decide⟩
    (prefixPartial 10 20927) = some ⟨10, 2, 0, 1132276, 20927, 489, 1048576⟩ := by
  decide +kernel

theorem context_10_20927_1132276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20927 ⟨1132276, by decide⟩ :=
  accepted_of_selected 10 20927 ⟨1132276, by decide⟩ ⟨10, 2, 0, 1132276, 20927, 489, 1048576⟩
    (by decide) selected_cut_41396

theorem unmarked_context_9_5231_1132277 : frontier 12 ⟨1132277, by decide⟩
    (prefixCache 9 5231) (prefixPartial 9 5231) = false := by
  decide +kernel

theorem node_context_9_5231_1132277 : EJMOriginalGlobalDAGData.nodes 12 ⟨1132277, by decide⟩ =
    .split (coordinate 9) (![⟨1132147, by decide⟩,⟨1132205, by decide⟩,⟨1132244, by decide⟩,⟨1132276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5231_1132277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5231 ⟨1132277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5231
    ⟨1132277, by decide⟩ (by decide) (![⟨1132147, by decide⟩,⟨1132205, by decide⟩,⟨1132244, by decide⟩,⟨1132276, by decide⟩]) unmarked_context_9_5231_1132277 node_context_9_5231_1132277
  intro a
  fin_cases a
  · exact context_10_20924_1132147
  · exact context_10_20925_1132205
  · exact context_10_20926_1132244
  · exact context_10_20927_1132276

theorem unmarked_context_8_1307_1132278 : frontier 13 ⟨1132278, by decide⟩
    (prefixCache 8 1307) (prefixPartial 8 1307) = false := by
  decide +kernel

theorem node_context_8_1307_1132278 : EJMOriginalGlobalDAGData.nodes 13 ⟨1132278, by decide⟩ =
    .split (coordinate 8) (![⟨1129979, by decide⟩,⟨1131190, by decide⟩,⟨1132060, by decide⟩,⟨1132277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1307_1132278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1307 ⟨1132278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1307
    ⟨1132278, by decide⟩ (by decide) (![⟨1129979, by decide⟩,⟨1131190, by decide⟩,⟨1132060, by decide⟩,⟨1132277, by decide⟩]) unmarked_context_8_1307_1132278 node_context_8_1307_1132278
  intro a
  fin_cases a
  · exact context_9_5228_1129979
  · exact context_9_5229_1131190
  · exact context_9_5230_1132060
  · exact context_9_5231_1132277

theorem unmarked_context_7_326_1132279 : frontier 14 ⟨1132279, by decide⟩
    (prefixCache 7 326) (prefixPartial 7 326) = false := by
  decide +kernel

theorem node_context_7_326_1132279 : EJMOriginalGlobalDAGData.nodes 14 ⟨1132279, by decide⟩ =
    .split (coordinate 7) (![⟨1122740, by decide⟩,⟨1109534, by decide⟩,⟨1127697, by decide⟩,⟨1132278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_326_1132279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 326 ⟨1132279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 326
    ⟨1132279, by decide⟩ (by decide) (![⟨1122740, by decide⟩,⟨1109534, by decide⟩,⟨1127697, by decide⟩,⟨1132278, by decide⟩]) unmarked_context_7_326_1132279 node_context_7_326_1132279
  intro a
  fin_cases a
  · exact context_8_1304_1122740
  · exact context_8_1305_1109534
  · exact context_8_1306_1127697
  · exact context_8_1307_1132278

theorem selected_cut_41397 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 327) = some ⟨7, 1, 0, 34032, 327, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_327_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 327 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 327 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 327, 1, 67108864⟩
    (by decide) selected_cut_41397

theorem unmarked_context_6_81_1132280 : frontier 15 ⟨1132280, by decide⟩
    (prefixCache 6 81) (prefixPartial 6 81) = false := by
  decide +kernel

theorem node_context_6_81_1132280 : EJMOriginalGlobalDAGData.nodes 15 ⟨1132280, by decide⟩ =
    .split (coordinate 6) (![⟨1112411, by decide⟩,⟨1118289, by decide⟩,⟨1132279, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_81_1132280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 81 ⟨1132280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 81
    ⟨1132280, by decide⟩ (by decide) (![⟨1112411, by decide⟩,⟨1118289, by decide⟩,⟨1132279, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_81_1132280 node_context_6_81_1132280
  intro a
  fin_cases a
  · exact context_7_324_1112411
  · exact context_7_325_1118289
  · exact context_7_326_1132279
  · exact context_7_327_34032

theorem selected_cut_41398 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 83968) = some ⟨11, 1, 0, 434745, 83968, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83968_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83968 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 83968 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 83968, 1, 262144⟩
    (by decide) selected_cut_41398

theorem selected_cut_41399 : selected 10 ⟨1132393, by decide⟩
    (prefixPartial 11 83969) = some ⟨11, 2, 0, 1132393, 83969, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_83969_1132393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83969 ⟨1132393, by decide⟩ :=
  accepted_of_selected 11 83969 ⟨1132393, by decide⟩ ⟨11, 2, 0, 1132393, 83969, 2557, 262144⟩
    (by decide) selected_cut_41399

theorem selected_cut_41400 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 335880) = some ⟨12, 1, 0, 448748, 335880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335880_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335880 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 335880 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 335880, 1, 65536⟩
    (by decide) selected_cut_41400

theorem selected_cut_41401 : selected 9 ⟨1132439, by decide⟩
    (prefixPartial 12 335881) = some ⟨12, 2, 0, 1132439, 335881, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_335881_1132439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335881 ⟨1132439, by decide⟩ :=
  accepted_of_selected 12 335881 ⟨1132439, by decide⟩ ⟨12, 2, 0, 1132439, 335881, 2281, 65536⟩
    (by decide) selected_cut_41401

theorem selected_cut_41402 : selected 9 ⟨1132479, by decide⟩
    (prefixPartial 12 335882) = some ⟨12, 2, 0, 1132479, 335882, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_335882_1132479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335882 ⟨1132479, by decide⟩ :=
  accepted_of_selected 12 335882 ⟨1132479, by decide⟩ ⟨12, 2, 0, 1132479, 335882, 2057, 65536⟩
    (by decide) selected_cut_41402

theorem selected_cut_41403 : selected 9 ⟨1132516, by decide⟩
    (prefixPartial 12 335883) = some ⟨12, 2, 0, 1132516, 335883, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_335883_1132516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335883 ⟨1132516, by decide⟩ :=
  accepted_of_selected 12 335883 ⟨1132516, by decide⟩ ⟨12, 2, 0, 1132516, 335883, 2301, 65536⟩
    (by decide) selected_cut_41403

theorem unmarked_context_11_83970_1132517 : frontier 10 ⟨1132517, by decide⟩
    (prefixCache 11 83970) (prefixPartial 11 83970) = false := by
  decide +kernel

theorem node_context_11_83970_1132517 : EJMOriginalGlobalDAGData.nodes 10 ⟨1132517, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1132439, by decide⟩,⟨1132479, by decide⟩,⟨1132516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83970_1132517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83970 ⟨1132517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83970
    ⟨1132517, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1132439, by decide⟩,⟨1132479, by decide⟩,⟨1132516, by decide⟩]) unmarked_context_11_83970_1132517 node_context_11_83970_1132517
  intro a
  fin_cases a
  · exact context_12_335880_448748
  · exact context_12_335881_1132439
  · exact context_12_335882_1132479
  · exact context_12_335883_1132516

theorem selected_cut_41404 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 335884) = some ⟨12, 1, 0, 448748, 335884, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335884_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335884 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 335884 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 335884, 1, 65536⟩
    (by decide) selected_cut_41404

theorem selected_cut_41405 : selected 9 ⟨1132552, by decide⟩
    (prefixPartial 12 335885) = some ⟨12, 2, 0, 1132552, 335885, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_335885_1132552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335885 ⟨1132552, by decide⟩ :=
  accepted_of_selected 12 335885 ⟨1132552, by decide⟩ ⟨12, 2, 0, 1132552, 335885, 1161, 65536⟩
    (by decide) selected_cut_41405

theorem selected_cut_41406 : selected 9 ⟨1132591, by decide⟩
    (prefixPartial 12 335886) = some ⟨12, 2, 0, 1132591, 335886, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_335886_1132591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335886 ⟨1132591, by decide⟩ :=
  accepted_of_selected 12 335886 ⟨1132591, by decide⟩ ⟨12, 2, 0, 1132591, 335886, 2029, 65536⟩
    (by decide) selected_cut_41406

theorem selected_cut_41407 : selected 9 ⟨1132629, by decide⟩
    (prefixPartial 12 335887) = some ⟨12, 2, 0, 1132629, 335887, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_335887_1132629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335887 ⟨1132629, by decide⟩ :=
  accepted_of_selected 12 335887 ⟨1132629, by decide⟩ ⟨12, 2, 0, 1132629, 335887, 1925, 65536⟩
    (by decide) selected_cut_41407

theorem unmarked_context_11_83971_1132630 : frontier 10 ⟨1132630, by decide⟩
    (prefixCache 11 83971) (prefixPartial 11 83971) = false := by
  decide +kernel

theorem node_context_11_83971_1132630 : EJMOriginalGlobalDAGData.nodes 10 ⟨1132630, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1132552, by decide⟩,⟨1132591, by decide⟩,⟨1132629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83971_1132630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83971 ⟨1132630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83971
    ⟨1132630, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1132552, by decide⟩,⟨1132591, by decide⟩,⟨1132629, by decide⟩]) unmarked_context_11_83971_1132630 node_context_11_83971_1132630
  intro a
  fin_cases a
  · exact context_12_335884_448748
  · exact context_12_335885_1132552
  · exact context_12_335886_1132591
  · exact context_12_335887_1132629

theorem unmarked_context_10_20992_1132631 : frontier 11 ⟨1132631, by decide⟩
    (prefixCache 10 20992) (prefixPartial 10 20992) = false := by
  decide +kernel

theorem node_context_10_20992_1132631 : EJMOriginalGlobalDAGData.nodes 11 ⟨1132631, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1132393, by decide⟩,⟨1132517, by decide⟩,⟨1132630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20992_1132631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20992 ⟨1132631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20992
    ⟨1132631, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1132393, by decide⟩,⟨1132517, by decide⟩,⟨1132630, by decide⟩]) unmarked_context_10_20992_1132631 node_context_10_20992_1132631
  intro a
  fin_cases a
  · exact context_11_83968_434745
  · exact context_11_83969_1132393
  · exact context_11_83970_1132517
  · exact context_11_83971_1132630

theorem selected_cut_41408 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335888) = some ⟨12, 1, 0, 1108174, 335888, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335888_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335888 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335888 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335888, 1, 65536⟩
    (by decide) selected_cut_41408

theorem selected_cut_41409 : selected 9 ⟨1132666, by decide⟩
    (prefixPartial 12 335889) = some ⟨12, 2, 0, 1132666, 335889, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_335889_1132666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335889 ⟨1132666, by decide⟩ :=
  accepted_of_selected 12 335889 ⟨1132666, by decide⟩ ⟨12, 2, 0, 1132666, 335889, 2017, 65536⟩
    (by decide) selected_cut_41409

theorem selected_cut_41410 : selected 9 ⟨1132698, by decide⟩
    (prefixPartial 12 335890) = some ⟨12, 2, 0, 1132698, 335890, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_335890_1132698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335890 ⟨1132698, by decide⟩ :=
  accepted_of_selected 12 335890 ⟨1132698, by decide⟩ ⟨12, 2, 0, 1132698, 335890, 1841, 65536⟩
    (by decide) selected_cut_41410

theorem selected_cut_41411 : selected 9 ⟨1132726, by decide⟩
    (prefixPartial 12 335891) = some ⟨12, 2, 0, 1132726, 335891, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_335891_1132726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335891 ⟨1132726, by decide⟩ :=
  accepted_of_selected 12 335891 ⟨1132726, by decide⟩ ⟨12, 2, 0, 1132726, 335891, 2017, 65536⟩
    (by decide) selected_cut_41411

theorem unmarked_context_11_83972_1132727 : frontier 10 ⟨1132727, by decide⟩
    (prefixCache 11 83972) (prefixPartial 11 83972) = false := by
  decide +kernel

theorem node_context_11_83972_1132727 : EJMOriginalGlobalDAGData.nodes 10 ⟨1132727, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1132666, by decide⟩,⟨1132698, by decide⟩,⟨1132726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83972_1132727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83972 ⟨1132727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83972
    ⟨1132727, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1132666, by decide⟩,⟨1132698, by decide⟩,⟨1132726, by decide⟩]) unmarked_context_11_83972_1132727 node_context_11_83972_1132727
  intro a
  fin_cases a
  · exact context_12_335888_1108174
  · exact context_12_335889_1132666
  · exact context_12_335890_1132698
  · exact context_12_335891_1132726

theorem selected_cut_41412 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335892) = some ⟨12, 1, 0, 1108174, 335892, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335892_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335892 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335892 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335892, 1, 65536⟩
    (by decide) selected_cut_41412

theorem selected_cut_41413 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 335893) = some ⟨12, 1, 0, 308705, 335893, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335893_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335893 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 335893 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 335893, 1, 65536⟩
    (by decide) selected_cut_41413

theorem selected_cut_41414 : selected 9 ⟨1132769, by decide⟩
    (prefixPartial 12 335894) = some ⟨12, 2, 0, 1132769, 335894, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_335894_1132769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335894 ⟨1132769, by decide⟩ :=
  accepted_of_selected 12 335894 ⟨1132769, by decide⟩ ⟨12, 2, 0, 1132769, 335894, 2341, 65536⟩
    (by decide) selected_cut_41414

theorem selected_cut_41415 : selected 9 ⟨1132811, by decide⟩
    (prefixPartial 12 335895) = some ⟨12, 2, 0, 1132811, 335895, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_335895_1132811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335895 ⟨1132811, by decide⟩ :=
  accepted_of_selected 12 335895 ⟨1132811, by decide⟩ ⟨12, 2, 0, 1132811, 335895, 2429, 65536⟩
    (by decide) selected_cut_41415

theorem unmarked_context_11_83973_1132812 : frontier 10 ⟨1132812, by decide⟩
    (prefixCache 11 83973) (prefixPartial 11 83973) = false := by
  decide +kernel

theorem node_context_11_83973_1132812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1132812, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1132769, by decide⟩,⟨1132811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83973_1132812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83973 ⟨1132812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83973
    ⟨1132812, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1132769, by decide⟩,⟨1132811, by decide⟩]) unmarked_context_11_83973_1132812 node_context_11_83973_1132812
  intro a
  fin_cases a
  · exact context_12_335892_1108174
  · exact context_12_335893_308705
  · exact context_12_335894_1132769
  · exact context_12_335895_1132811

theorem selected_cut_41416 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335896) = some ⟨12, 1, 0, 1108174, 335896, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335896_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335896 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335896 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335896, 1, 65536⟩
    (by decide) selected_cut_41416

theorem selected_cut_41417 : selected 9 ⟨1132841, by decide⟩
    (prefixPartial 12 335897) = some ⟨12, 2, 0, 1132841, 335897, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_335897_1132841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335897 ⟨1132841, by decide⟩ :=
  accepted_of_selected 12 335897 ⟨1132841, by decide⟩ ⟨12, 2, 0, 1132841, 335897, 2209, 65536⟩
    (by decide) selected_cut_41417

theorem selected_cut_41418 : selected 9 ⟨1132866, by decide⟩
    (prefixPartial 12 335898) = some ⟨12, 2, 0, 1132866, 335898, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_335898_1132866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335898 ⟨1132866, by decide⟩ :=
  accepted_of_selected 12 335898 ⟨1132866, by decide⟩ ⟨12, 2, 0, 1132866, 335898, 2113, 65536⟩
    (by decide) selected_cut_41418

theorem selected_cut_41419 : selected 9 ⟨1132890, by decide⟩
    (prefixPartial 12 335899) = some ⟨12, 2, 0, 1132890, 335899, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_335899_1132890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335899 ⟨1132890, by decide⟩ :=
  accepted_of_selected 12 335899 ⟨1132890, by decide⟩ ⟨12, 2, 0, 1132890, 335899, 2297, 65536⟩
    (by decide) selected_cut_41419

theorem unmarked_context_11_83974_1132891 : frontier 10 ⟨1132891, by decide⟩
    (prefixCache 11 83974) (prefixPartial 11 83974) = false := by
  decide +kernel

theorem node_context_11_83974_1132891 : EJMOriginalGlobalDAGData.nodes 10 ⟨1132891, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1132841, by decide⟩,⟨1132866, by decide⟩,⟨1132890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83974_1132891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83974 ⟨1132891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83974
    ⟨1132891, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1132841, by decide⟩,⟨1132866, by decide⟩,⟨1132890, by decide⟩]) unmarked_context_11_83974_1132891 node_context_11_83974_1132891
  intro a
  fin_cases a
  · exact context_12_335896_1108174
  · exact context_12_335897_1132841
  · exact context_12_335898_1132866
  · exact context_12_335899_1132890

theorem selected_cut_41420 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335900) = some ⟨12, 1, 0, 1108174, 335900, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335900_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335900 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335900 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335900, 1, 65536⟩
    (by decide) selected_cut_41420

theorem selected_cut_41421 : selected 9 ⟨1132921, by decide⟩
    (prefixPartial 12 335901) = some ⟨12, 2, 0, 1132921, 335901, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_335901_1132921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335901 ⟨1132921, by decide⟩ :=
  accepted_of_selected 12 335901 ⟨1132921, by decide⟩ ⟨12, 2, 0, 1132921, 335901, 2105, 65536⟩
    (by decide) selected_cut_41421

theorem selected_cut_41422 : selected 9 ⟨1132946, by decide⟩
    (prefixPartial 12 335902) = some ⟨12, 2, 0, 1132946, 335902, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_335902_1132946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335902 ⟨1132946, by decide⟩ :=
  accepted_of_selected 12 335902 ⟨1132946, by decide⟩ ⟨12, 2, 0, 1132946, 335902, 2121, 65536⟩
    (by decide) selected_cut_41422

theorem selected_cut_41423 : selected 9 ⟨1132970, by decide⟩
    (prefixPartial 12 335903) = some ⟨12, 2, 0, 1132970, 335903, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_335903_1132970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335903 ⟨1132970, by decide⟩ :=
  accepted_of_selected 12 335903 ⟨1132970, by decide⟩ ⟨12, 2, 0, 1132970, 335903, 2101, 65536⟩
    (by decide) selected_cut_41423

theorem unmarked_context_11_83975_1132971 : frontier 10 ⟨1132971, by decide⟩
    (prefixCache 11 83975) (prefixPartial 11 83975) = false := by
  decide +kernel

theorem node_context_11_83975_1132971 : EJMOriginalGlobalDAGData.nodes 10 ⟨1132971, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1132921, by decide⟩,⟨1132946, by decide⟩,⟨1132970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83975_1132971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83975 ⟨1132971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83975
    ⟨1132971, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1132921, by decide⟩,⟨1132946, by decide⟩,⟨1132970, by decide⟩]) unmarked_context_11_83975_1132971 node_context_11_83975_1132971
  intro a
  fin_cases a
  · exact context_12_335900_1108174
  · exact context_12_335901_1132921
  · exact context_12_335902_1132946
  · exact context_12_335903_1132970

theorem unmarked_context_10_20993_1132972 : frontier 11 ⟨1132972, by decide⟩
    (prefixCache 10 20993) (prefixPartial 10 20993) = false := by
  decide +kernel

theorem node_context_10_20993_1132972 : EJMOriginalGlobalDAGData.nodes 11 ⟨1132972, by decide⟩ =
    .split (coordinate 10) (![⟨1132727, by decide⟩,⟨1132812, by decide⟩,⟨1132891, by decide⟩,⟨1132971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20993_1132972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20993 ⟨1132972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20993
    ⟨1132972, by decide⟩ (by decide) (![⟨1132727, by decide⟩,⟨1132812, by decide⟩,⟨1132891, by decide⟩,⟨1132971, by decide⟩]) unmarked_context_10_20993_1132972 node_context_10_20993_1132972
  intro a
  fin_cases a
  · exact context_11_83972_1132727
  · exact context_11_83973_1132812
  · exact context_11_83974_1132891
  · exact context_11_83975_1132971

theorem selected_cut_41424 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335904) = some ⟨12, 1, 0, 1108174, 335904, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335904_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335904 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335904 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335904, 1, 65536⟩
    (by decide) selected_cut_41424

theorem selected_cut_41425 : selected 9 ⟨1132997, by decide⟩
    (prefixPartial 12 335905) = some ⟨12, 2, 0, 1132997, 335905, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_335905_1132997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335905 ⟨1132997, by decide⟩ :=
  accepted_of_selected 12 335905 ⟨1132997, by decide⟩ ⟨12, 2, 0, 1132997, 335905, 2041, 65536⟩
    (by decide) selected_cut_41425

theorem selected_cut_41426 : selected 9 ⟨1133023, by decide⟩
    (prefixPartial 12 335906) = some ⟨12, 2, 0, 1133023, 335906, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_335906_1133023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335906 ⟨1133023, by decide⟩ :=
  accepted_of_selected 12 335906 ⟨1133023, by decide⟩ ⟨12, 2, 0, 1133023, 335906, 1901, 65536⟩
    (by decide) selected_cut_41426

theorem selected_cut_41427 : selected 9 ⟨1133043, by decide⟩
    (prefixPartial 12 335907) = some ⟨12, 2, 0, 1133043, 335907, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_335907_1133043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335907 ⟨1133043, by decide⟩ :=
  accepted_of_selected 12 335907 ⟨1133043, by decide⟩ ⟨12, 2, 0, 1133043, 335907, 1985, 65536⟩
    (by decide) selected_cut_41427

theorem unmarked_context_11_83976_1133044 : frontier 10 ⟨1133044, by decide⟩
    (prefixCache 11 83976) (prefixPartial 11 83976) = false := by
  decide +kernel

theorem node_context_11_83976_1133044 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133044, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1132997, by decide⟩,⟨1133023, by decide⟩,⟨1133043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83976_1133044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83976 ⟨1133044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83976
    ⟨1133044, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1132997, by decide⟩,⟨1133023, by decide⟩,⟨1133043, by decide⟩]) unmarked_context_11_83976_1133044 node_context_11_83976_1133044
  intro a
  fin_cases a
  · exact context_12_335904_1108174
  · exact context_12_335905_1132997
  · exact context_12_335906_1133023
  · exact context_12_335907_1133043

theorem selected_cut_41428 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335908) = some ⟨12, 1, 0, 1108174, 335908, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335908_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335908 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335908 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335908, 1, 65536⟩
    (by decide) selected_cut_41428

theorem selected_cut_41429 : selected 9 ⟨1133084, by decide⟩
    (prefixPartial 12 335909) = some ⟨12, 2, 0, 1133084, 335909, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_335909_1133084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335909 ⟨1133084, by decide⟩ :=
  accepted_of_selected 12 335909 ⟨1133084, by decide⟩ ⟨12, 2, 0, 1133084, 335909, 2193, 65536⟩
    (by decide) selected_cut_41429

theorem selected_cut_41430 : selected 9 ⟨1133115, by decide⟩
    (prefixPartial 12 335910) = some ⟨12, 2, 0, 1133115, 335910, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_335910_1133115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335910 ⟨1133115, by decide⟩ :=
  accepted_of_selected 12 335910 ⟨1133115, by decide⟩ ⟨12, 2, 0, 1133115, 335910, 2201, 65536⟩
    (by decide) selected_cut_41430

theorem selected_cut_41431 : selected 9 ⟨1133154, by decide⟩
    (prefixPartial 12 335911) = some ⟨12, 2, 0, 1133154, 335911, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_335911_1133154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335911 ⟨1133154, by decide⟩ :=
  accepted_of_selected 12 335911 ⟨1133154, by decide⟩ ⟨12, 2, 0, 1133154, 335911, 2261, 65536⟩
    (by decide) selected_cut_41431

theorem unmarked_context_11_83977_1133155 : frontier 10 ⟨1133155, by decide⟩
    (prefixCache 11 83977) (prefixPartial 11 83977) = false := by
  decide +kernel

theorem node_context_11_83977_1133155 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133155, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1133084, by decide⟩,⟨1133115, by decide⟩,⟨1133154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83977_1133155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83977 ⟨1133155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83977
    ⟨1133155, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1133084, by decide⟩,⟨1133115, by decide⟩,⟨1133154, by decide⟩]) unmarked_context_11_83977_1133155 node_context_11_83977_1133155
  intro a
  fin_cases a
  · exact context_12_335908_1108174
  · exact context_12_335909_1133084
  · exact context_12_335910_1133115
  · exact context_12_335911_1133154

theorem selected_cut_41432 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335912) = some ⟨12, 1, 0, 1108174, 335912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335912_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335912 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335912 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335912, 1, 65536⟩
    (by decide) selected_cut_41432

theorem selected_cut_41433 : selected 9 ⟨1133187, by decide⟩
    (prefixPartial 12 335913) = some ⟨12, 2, 0, 1133187, 335913, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_335913_1133187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335913 ⟨1133187, by decide⟩ :=
  accepted_of_selected 12 335913 ⟨1133187, by decide⟩ ⟨12, 2, 0, 1133187, 335913, 2221, 65536⟩
    (by decide) selected_cut_41433

theorem selected_cut_41434 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 335914) = some ⟨12, 1, 0, 474208, 335914, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335914_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335914 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 335914 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 335914, 1, 65536⟩
    (by decide) selected_cut_41434

theorem selected_cut_41435 : selected 9 ⟨1133212, by decide⟩
    (prefixPartial 12 335915) = some ⟨12, 2, 0, 1133212, 335915, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_335915_1133212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335915 ⟨1133212, by decide⟩ :=
  accepted_of_selected 12 335915 ⟨1133212, by decide⟩ ⟨12, 2, 0, 1133212, 335915, 2161, 65536⟩
    (by decide) selected_cut_41435

theorem unmarked_context_11_83978_1133213 : frontier 10 ⟨1133213, by decide⟩
    (prefixCache 11 83978) (prefixPartial 11 83978) = false := by
  decide +kernel

theorem node_context_11_83978_1133213 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133213, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1133187, by decide⟩,⟨474208, by decide⟩,⟨1133212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83978_1133213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83978 ⟨1133213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83978
    ⟨1133213, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1133187, by decide⟩,⟨474208, by decide⟩,⟨1133212, by decide⟩]) unmarked_context_11_83978_1133213 node_context_11_83978_1133213
  intro a
  fin_cases a
  · exact context_12_335912_1108174
  · exact context_12_335913_1133187
  · exact context_12_335914_474208
  · exact context_12_335915_1133212

theorem selected_cut_41436 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335916) = some ⟨12, 1, 0, 1108174, 335916, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335916_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335916 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335916 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335916, 1, 65536⟩
    (by decide) selected_cut_41436

theorem selected_cut_41437 : selected 9 ⟨1133246, by decide⟩
    (prefixPartial 12 335917) = some ⟨12, 2, 0, 1133246, 335917, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_335917_1133246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335917 ⟨1133246, by decide⟩ :=
  accepted_of_selected 12 335917 ⟨1133246, by decide⟩ ⟨12, 2, 0, 1133246, 335917, 2161, 65536⟩
    (by decide) selected_cut_41437

theorem selected_cut_41438 : selected 9 ⟨1133270, by decide⟩
    (prefixPartial 12 335918) = some ⟨12, 2, 0, 1133270, 335918, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_335918_1133270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335918 ⟨1133270, by decide⟩ :=
  accepted_of_selected 12 335918 ⟨1133270, by decide⟩ ⟨12, 2, 0, 1133270, 335918, 2021, 65536⟩
    (by decide) selected_cut_41438

theorem selected_cut_41439 : selected 9 ⟨1133293, by decide⟩
    (prefixPartial 12 335919) = some ⟨12, 2, 0, 1133293, 335919, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_335919_1133293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335919 ⟨1133293, by decide⟩ :=
  accepted_of_selected 12 335919 ⟨1133293, by decide⟩ ⟨12, 2, 0, 1133293, 335919, 2065, 65536⟩
    (by decide) selected_cut_41439

theorem unmarked_context_11_83979_1133294 : frontier 10 ⟨1133294, by decide⟩
    (prefixCache 11 83979) (prefixPartial 11 83979) = false := by
  decide +kernel

theorem node_context_11_83979_1133294 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133294, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1133246, by decide⟩,⟨1133270, by decide⟩,⟨1133293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83979_1133294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83979 ⟨1133294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83979
    ⟨1133294, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1133246, by decide⟩,⟨1133270, by decide⟩,⟨1133293, by decide⟩]) unmarked_context_11_83979_1133294 node_context_11_83979_1133294
  intro a
  fin_cases a
  · exact context_12_335916_1108174
  · exact context_12_335917_1133246
  · exact context_12_335918_1133270
  · exact context_12_335919_1133293

theorem unmarked_context_10_20994_1133295 : frontier 11 ⟨1133295, by decide⟩
    (prefixCache 10 20994) (prefixPartial 10 20994) = false := by
  decide +kernel

theorem node_context_10_20994_1133295 : EJMOriginalGlobalDAGData.nodes 11 ⟨1133295, by decide⟩ =
    .split (coordinate 10) (![⟨1133044, by decide⟩,⟨1133155, by decide⟩,⟨1133213, by decide⟩,⟨1133294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20994_1133295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20994 ⟨1133295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20994
    ⟨1133295, by decide⟩ (by decide) (![⟨1133044, by decide⟩,⟨1133155, by decide⟩,⟨1133213, by decide⟩,⟨1133294, by decide⟩]) unmarked_context_10_20994_1133295 node_context_10_20994_1133295
  intro a
  fin_cases a
  · exact context_11_83976_1133044
  · exact context_11_83977_1133155
  · exact context_11_83978_1133213
  · exact context_11_83979_1133294

theorem selected_cut_41440 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335920) = some ⟨12, 1, 0, 1108174, 335920, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335920_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335920 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335920 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335920, 1, 65536⟩
    (by decide) selected_cut_41440

theorem selected_cut_41441 : selected 9 ⟨1133318, by decide⟩
    (prefixPartial 12 335921) = some ⟨12, 2, 0, 1133318, 335921, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_335921_1133318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335921 ⟨1133318, by decide⟩ :=
  accepted_of_selected 12 335921 ⟨1133318, by decide⟩ ⟨12, 2, 0, 1133318, 335921, 1893, 65536⟩
    (by decide) selected_cut_41441

theorem selected_cut_41442 : selected 9 ⟨1133338, by decide⟩
    (prefixPartial 12 335922) = some ⟨12, 2, 0, 1133338, 335922, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_335922_1133338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335922 ⟨1133338, by decide⟩ :=
  accepted_of_selected 12 335922 ⟨1133338, by decide⟩ ⟨12, 2, 0, 1133338, 335922, 1729, 65536⟩
    (by decide) selected_cut_41442

theorem selected_cut_41443 : selected 9 ⟨1133356, by decide⟩
    (prefixPartial 12 335923) = some ⟨12, 2, 0, 1133356, 335923, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_335923_1133356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335923 ⟨1133356, by decide⟩ :=
  accepted_of_selected 12 335923 ⟨1133356, by decide⟩ ⟨12, 2, 0, 1133356, 335923, 1801, 65536⟩
    (by decide) selected_cut_41443

theorem unmarked_context_11_83980_1133357 : frontier 10 ⟨1133357, by decide⟩
    (prefixCache 11 83980) (prefixPartial 11 83980) = false := by
  decide +kernel

theorem node_context_11_83980_1133357 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133357, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1133318, by decide⟩,⟨1133338, by decide⟩,⟨1133356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83980_1133357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83980 ⟨1133357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83980
    ⟨1133357, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1133318, by decide⟩,⟨1133338, by decide⟩,⟨1133356, by decide⟩]) unmarked_context_11_83980_1133357 node_context_11_83980_1133357
  intro a
  fin_cases a
  · exact context_12_335920_1108174
  · exact context_12_335921_1133318
  · exact context_12_335922_1133338
  · exact context_12_335923_1133356

theorem selected_cut_41444 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335924) = some ⟨12, 1, 0, 1108174, 335924, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335924_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335924 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335924 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335924, 1, 65536⟩
    (by decide) selected_cut_41444

theorem selected_cut_41445 : selected 9 ⟨1133391, by decide⟩
    (prefixPartial 12 335925) = some ⟨12, 2, 0, 1133391, 335925, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_335925_1133391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335925 ⟨1133391, by decide⟩ :=
  accepted_of_selected 12 335925 ⟨1133391, by decide⟩ ⟨12, 2, 0, 1133391, 335925, 2061, 65536⟩
    (by decide) selected_cut_41445

theorem selected_cut_41446 : selected 9 ⟨1133417, by decide⟩
    (prefixPartial 12 335926) = some ⟨12, 2, 0, 1133417, 335926, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_335926_1133417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335926 ⟨1133417, by decide⟩ :=
  accepted_of_selected 12 335926 ⟨1133417, by decide⟩ ⟨12, 2, 0, 1133417, 335926, 2025, 65536⟩
    (by decide) selected_cut_41446

theorem selected_cut_41447 : selected 9 ⟨1133456, by decide⟩
    (prefixPartial 12 335927) = some ⟨12, 2, 0, 1133456, 335927, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_335927_1133456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335927 ⟨1133456, by decide⟩ :=
  accepted_of_selected 12 335927 ⟨1133456, by decide⟩ ⟨12, 2, 0, 1133456, 335927, 2237, 65536⟩
    (by decide) selected_cut_41447

theorem unmarked_context_11_83981_1133457 : frontier 10 ⟨1133457, by decide⟩
    (prefixCache 11 83981) (prefixPartial 11 83981) = false := by
  decide +kernel

theorem node_context_11_83981_1133457 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133457, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1133391, by decide⟩,⟨1133417, by decide⟩,⟨1133456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83981_1133457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83981 ⟨1133457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83981
    ⟨1133457, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1133391, by decide⟩,⟨1133417, by decide⟩,⟨1133456, by decide⟩]) unmarked_context_11_83981_1133457 node_context_11_83981_1133457
  intro a
  fin_cases a
  · exact context_12_335924_1108174
  · exact context_12_335925_1133391
  · exact context_12_335926_1133417
  · exact context_12_335927_1133456

theorem selected_cut_41448 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 335928) = some ⟨12, 1, 0, 1108174, 335928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335928_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335928 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 335928 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 335928, 1, 65536⟩
    (by decide) selected_cut_41448

theorem selected_cut_41449 : selected 9 ⟨1133493, by decide⟩
    (prefixPartial 12 335929) = some ⟨12, 2, 0, 1133493, 335929, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_335929_1133493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335929 ⟨1133493, by decide⟩ :=
  accepted_of_selected 12 335929 ⟨1133493, by decide⟩ ⟨12, 2, 0, 1133493, 335929, 2057, 65536⟩
    (by decide) selected_cut_41449

theorem selected_cut_41450 : selected 9 ⟨1133513, by decide⟩
    (prefixPartial 12 335930) = some ⟨12, 2, 0, 1133513, 335930, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_335930_1133513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335930 ⟨1133513, by decide⟩ :=
  accepted_of_selected 12 335930 ⟨1133513, by decide⟩ ⟨12, 2, 0, 1133513, 335930, 1857, 65536⟩
    (by decide) selected_cut_41450

theorem selected_cut_41451 : selected 9 ⟨1133552, by decide⟩
    (prefixPartial 12 335931) = some ⟨12, 2, 0, 1133552, 335931, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_335931_1133552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335931 ⟨1133552, by decide⟩ :=
  accepted_of_selected 12 335931 ⟨1133552, by decide⟩ ⟨12, 2, 0, 1133552, 335931, 2057, 65536⟩
    (by decide) selected_cut_41451

theorem unmarked_context_11_83982_1133553 : frontier 10 ⟨1133553, by decide⟩
    (prefixCache 11 83982) (prefixPartial 11 83982) = false := by
  decide +kernel

theorem node_context_11_83982_1133553 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133553, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1133493, by decide⟩,⟨1133513, by decide⟩,⟨1133552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83982_1133553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83982 ⟨1133553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83982
    ⟨1133553, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1133493, by decide⟩,⟨1133513, by decide⟩,⟨1133552, by decide⟩]) unmarked_context_11_83982_1133553 node_context_11_83982_1133553
  intro a
  fin_cases a
  · exact context_12_335928_1108174
  · exact context_12_335929_1133493
  · exact context_12_335930_1133513
  · exact context_12_335931_1133552

theorem selected_cut_41452 : selected 10 ⟨1133603, by decide⟩
    (prefixPartial 11 83983) = some ⟨11, 2, 0, 1133603, 83983, 3773, 262144⟩ := by
  decide +kernel

theorem context_11_83983_1133603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83983 ⟨1133603, by decide⟩ :=
  accepted_of_selected 11 83983 ⟨1133603, by decide⟩ ⟨11, 2, 0, 1133603, 83983, 3773, 262144⟩
    (by decide) selected_cut_41452

theorem unmarked_context_10_20995_1133604 : frontier 11 ⟨1133604, by decide⟩
    (prefixCache 10 20995) (prefixPartial 10 20995) = false := by
  decide +kernel

theorem node_context_10_20995_1133604 : EJMOriginalGlobalDAGData.nodes 11 ⟨1133604, by decide⟩ =
    .split (coordinate 10) (![⟨1133357, by decide⟩,⟨1133457, by decide⟩,⟨1133553, by decide⟩,⟨1133603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20995_1133604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20995 ⟨1133604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20995
    ⟨1133604, by decide⟩ (by decide) (![⟨1133357, by decide⟩,⟨1133457, by decide⟩,⟨1133553, by decide⟩,⟨1133603, by decide⟩]) unmarked_context_10_20995_1133604 node_context_10_20995_1133604
  intro a
  fin_cases a
  · exact context_11_83980_1133357
  · exact context_11_83981_1133457
  · exact context_11_83982_1133553
  · exact context_11_83983_1133603

theorem unmarked_context_9_5248_1133605 : frontier 12 ⟨1133605, by decide⟩
    (prefixCache 9 5248) (prefixPartial 9 5248) = false := by
  decide +kernel

theorem node_context_9_5248_1133605 : EJMOriginalGlobalDAGData.nodes 12 ⟨1133605, by decide⟩ =
    .split (coordinate 9) (![⟨1132631, by decide⟩,⟨1132972, by decide⟩,⟨1133295, by decide⟩,⟨1133604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5248_1133605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5248 ⟨1133605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5248
    ⟨1133605, by decide⟩ (by decide) (![⟨1132631, by decide⟩,⟨1132972, by decide⟩,⟨1133295, by decide⟩,⟨1133604, by decide⟩]) unmarked_context_9_5248_1133605 node_context_9_5248_1133605
  intro a
  fin_cases a
  · exact context_10_20992_1132631
  · exact context_10_20993_1132972
  · exact context_10_20994_1133295
  · exact context_10_20995_1133604

theorem selected_cut_41453 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 83984) = some ⟨11, 1, 0, 907917, 83984, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83984_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83984 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 83984 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 83984, 1, 262144⟩
    (by decide) selected_cut_41453

theorem selected_cut_41454 : selected 9 ⟨1133627, by decide⟩
    (prefixPartial 12 335940) = some ⟨12, 2, 0, 1133627, 335940, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_335940_1133627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335940 ⟨1133627, by decide⟩ :=
  accepted_of_selected 12 335940 ⟨1133627, by decide⟩ ⟨12, 2, 0, 1133627, 335940, 1449, 65536⟩
    (by decide) selected_cut_41454

theorem selected_cut_41455 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 335941) = some ⟨12, 1, 0, 170504, 335941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335941_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335941 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 335941 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 335941, 1, 65536⟩
    (by decide) selected_cut_41455

theorem selected_cut_41456 : selected 9 ⟨1133650, by decide⟩
    (prefixPartial 12 335942) = some ⟨12, 2, 0, 1133650, 335942, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_335942_1133650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335942 ⟨1133650, by decide⟩ :=
  accepted_of_selected 12 335942 ⟨1133650, by decide⟩ ⟨12, 2, 0, 1133650, 335942, 1773, 65536⟩
    (by decide) selected_cut_41456

theorem selected_cut_41457 : selected 9 ⟨1133674, by decide⟩
    (prefixPartial 12 335943) = some ⟨12, 2, 0, 1133674, 335943, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_335943_1133674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335943 ⟨1133674, by decide⟩ :=
  accepted_of_selected 12 335943 ⟨1133674, by decide⟩ ⟨12, 2, 0, 1133674, 335943, 1821, 65536⟩
    (by decide) selected_cut_41457

theorem unmarked_context_11_83985_1133675 : frontier 10 ⟨1133675, by decide⟩
    (prefixCache 11 83985) (prefixPartial 11 83985) = false := by
  decide +kernel

theorem node_context_11_83985_1133675 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133675, by decide⟩ =
    .split (coordinate 11) (![⟨1133627, by decide⟩,⟨170504, by decide⟩,⟨1133650, by decide⟩,⟨1133674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83985_1133675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83985 ⟨1133675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83985
    ⟨1133675, by decide⟩ (by decide) (![⟨1133627, by decide⟩,⟨170504, by decide⟩,⟨1133650, by decide⟩,⟨1133674, by decide⟩]) unmarked_context_11_83985_1133675 node_context_11_83985_1133675
  intro a
  fin_cases a
  · exact context_12_335940_1133627
  · exact context_12_335941_170504
  · exact context_12_335942_1133650
  · exact context_12_335943_1133674

theorem selected_cut_41458 : selected 9 ⟨1133696, by decide⟩
    (prefixPartial 12 335944) = some ⟨12, 2, 0, 1133696, 335944, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_335944_1133696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335944 ⟨1133696, by decide⟩ :=
  accepted_of_selected 12 335944 ⟨1133696, by decide⟩ ⟨12, 2, 0, 1133696, 335944, 1497, 65536⟩
    (by decide) selected_cut_41458

theorem selected_cut_41459 : selected 9 ⟨1133725, by decide⟩
    (prefixPartial 12 335945) = some ⟨12, 2, 0, 1133725, 335945, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_335945_1133725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335945 ⟨1133725, by decide⟩ :=
  accepted_of_selected 12 335945 ⟨1133725, by decide⟩ ⟨12, 2, 0, 1133725, 335945, 1705, 65536⟩
    (by decide) selected_cut_41459

theorem selected_cut_41460 : selected 9 ⟨1133748, by decide⟩
    (prefixPartial 12 335946) = some ⟨12, 2, 0, 1133748, 335946, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_335946_1133748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335946 ⟨1133748, by decide⟩ :=
  accepted_of_selected 12 335946 ⟨1133748, by decide⟩ ⟨12, 2, 0, 1133748, 335946, 1725, 65536⟩
    (by decide) selected_cut_41460

theorem selected_cut_41461 : selected 9 ⟨1133782, by decide⟩
    (prefixPartial 12 335947) = some ⟨12, 2, 0, 1133782, 335947, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_335947_1133782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335947 ⟨1133782, by decide⟩ :=
  accepted_of_selected 12 335947 ⟨1133782, by decide⟩ ⟨12, 2, 0, 1133782, 335947, 1853, 65536⟩
    (by decide) selected_cut_41461

theorem unmarked_context_11_83986_1133783 : frontier 10 ⟨1133783, by decide⟩
    (prefixCache 11 83986) (prefixPartial 11 83986) = false := by
  decide +kernel

theorem node_context_11_83986_1133783 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133783, by decide⟩ =
    .split (coordinate 11) (![⟨1133696, by decide⟩,⟨1133725, by decide⟩,⟨1133748, by decide⟩,⟨1133782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83986_1133783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83986 ⟨1133783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83986
    ⟨1133783, by decide⟩ (by decide) (![⟨1133696, by decide⟩,⟨1133725, by decide⟩,⟨1133748, by decide⟩,⟨1133782, by decide⟩]) unmarked_context_11_83986_1133783 node_context_11_83986_1133783
  intro a
  fin_cases a
  · exact context_12_335944_1133696
  · exact context_12_335945_1133725
  · exact context_12_335946_1133748
  · exact context_12_335947_1133782

theorem selected_cut_41462 : selected 9 ⟨1133805, by decide⟩
    (prefixPartial 12 335948) = some ⟨12, 2, 0, 1133805, 335948, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_335948_1133805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335948 ⟨1133805, by decide⟩ :=
  accepted_of_selected 12 335948 ⟨1133805, by decide⟩ ⟨12, 2, 0, 1133805, 335948, 1381, 65536⟩
    (by decide) selected_cut_41462

theorem selected_cut_41463 : selected 9 ⟨1133830, by decide⟩
    (prefixPartial 12 335949) = some ⟨12, 2, 0, 1133830, 335949, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_335949_1133830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335949 ⟨1133830, by decide⟩ :=
  accepted_of_selected 12 335949 ⟨1133830, by decide⟩ ⟨12, 2, 0, 1133830, 335949, 1617, 65536⟩
    (by decide) selected_cut_41463

theorem selected_cut_41464 : selected 9 ⟨1133856, by decide⟩
    (prefixPartial 12 335950) = some ⟨12, 2, 0, 1133856, 335950, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_335950_1133856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335950 ⟨1133856, by decide⟩ :=
  accepted_of_selected 12 335950 ⟨1133856, by decide⟩ ⟨12, 2, 0, 1133856, 335950, 1597, 65536⟩
    (by decide) selected_cut_41464

theorem selected_cut_41465 : selected 9 ⟨1133878, by decide⟩
    (prefixPartial 12 335951) = some ⟨12, 2, 0, 1133878, 335951, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_335951_1133878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335951 ⟨1133878, by decide⟩ :=
  accepted_of_selected 12 335951 ⟨1133878, by decide⟩ ⟨12, 2, 0, 1133878, 335951, 1617, 65536⟩
    (by decide) selected_cut_41465

theorem unmarked_context_11_83987_1133879 : frontier 10 ⟨1133879, by decide⟩
    (prefixCache 11 83987) (prefixPartial 11 83987) = false := by
  decide +kernel

theorem node_context_11_83987_1133879 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133879, by decide⟩ =
    .split (coordinate 11) (![⟨1133805, by decide⟩,⟨1133830, by decide⟩,⟨1133856, by decide⟩,⟨1133878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83987_1133879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83987 ⟨1133879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83987
    ⟨1133879, by decide⟩ (by decide) (![⟨1133805, by decide⟩,⟨1133830, by decide⟩,⟨1133856, by decide⟩,⟨1133878, by decide⟩]) unmarked_context_11_83987_1133879 node_context_11_83987_1133879
  intro a
  fin_cases a
  · exact context_12_335948_1133805
  · exact context_12_335949_1133830
  · exact context_12_335950_1133856
  · exact context_12_335951_1133878

theorem unmarked_context_10_20996_1133880 : frontier 11 ⟨1133880, by decide⟩
    (prefixCache 10 20996) (prefixPartial 10 20996) = false := by
  decide +kernel

theorem node_context_10_20996_1133880 : EJMOriginalGlobalDAGData.nodes 11 ⟨1133880, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1133675, by decide⟩,⟨1133783, by decide⟩,⟨1133879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20996_1133880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20996 ⟨1133880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20996
    ⟨1133880, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1133675, by decide⟩,⟨1133783, by decide⟩,⟨1133879, by decide⟩]) unmarked_context_10_20996_1133880 node_context_10_20996_1133880
  intro a
  fin_cases a
  · exact context_11_83984_907917
  · exact context_11_83985_1133675
  · exact context_11_83986_1133783
  · exact context_11_83987_1133879

theorem selected_cut_41466 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20997) = some ⟨10, 1, 0, 893098, 20997, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20997_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20997 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20997 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20997, 1, 1048576⟩
    (by decide) selected_cut_41466

theorem selected_cut_41467 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 335968) = some ⟨12, 1, 0, 985390, 335968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335968_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335968 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 335968 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 335968, 1, 65536⟩
    (by decide) selected_cut_41467

theorem selected_cut_41468 : selected 9 ⟨1133903, by decide⟩
    (prefixPartial 12 335969) = some ⟨12, 2, 0, 1133903, 335969, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_335969_1133903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335969 ⟨1133903, by decide⟩ :=
  accepted_of_selected 12 335969 ⟨1133903, by decide⟩ ⟨12, 2, 0, 1133903, 335969, 1481, 65536⟩
    (by decide) selected_cut_41468

theorem selected_cut_41469 : selected 9 ⟨1133926, by decide⟩
    (prefixPartial 12 335970) = some ⟨12, 2, 0, 1133926, 335970, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_335970_1133926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335970 ⟨1133926, by decide⟩ :=
  accepted_of_selected 12 335970 ⟨1133926, by decide⟩ ⟨12, 2, 0, 1133926, 335970, 1509, 65536⟩
    (by decide) selected_cut_41469

theorem selected_cut_41470 : selected 9 ⟨1133942, by decide⟩
    (prefixPartial 12 335971) = some ⟨12, 2, 0, 1133942, 335971, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_335971_1133942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335971 ⟨1133942, by decide⟩ :=
  accepted_of_selected 12 335971 ⟨1133942, by decide⟩ ⟨12, 2, 0, 1133942, 335971, 1513, 65536⟩
    (by decide) selected_cut_41470

theorem unmarked_context_11_83992_1133943 : frontier 10 ⟨1133943, by decide⟩
    (prefixCache 11 83992) (prefixPartial 11 83992) = false := by
  decide +kernel

theorem node_context_11_83992_1133943 : EJMOriginalGlobalDAGData.nodes 10 ⟨1133943, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1133903, by decide⟩,⟨1133926, by decide⟩,⟨1133942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83992_1133943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83992 ⟨1133943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83992
    ⟨1133943, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1133903, by decide⟩,⟨1133926, by decide⟩,⟨1133942, by decide⟩]) unmarked_context_11_83992_1133943 node_context_11_83992_1133943
  intro a
  fin_cases a
  · exact context_12_335968_985390
  · exact context_12_335969_1133903
  · exact context_12_335970_1133926
  · exact context_12_335971_1133942

theorem selected_cut_41471 : selected 9 ⟨1133973, by decide⟩
    (prefixPartial 12 335972) = some ⟨12, 2, 0, 1133973, 335972, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_335972_1133973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335972 ⟨1133973, by decide⟩ :=
  accepted_of_selected 12 335972 ⟨1133973, by decide⟩ ⟨12, 2, 0, 1133973, 335972, 1669, 65536⟩
    (by decide) selected_cut_41471

theorem selected_cut_41472 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 335973) = some ⟨12, 1, 0, 642794, 335973, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335973_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335973 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 335973 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 335973, 1, 65536⟩
    (by decide) selected_cut_41472

theorem selected_cut_41473 : selected 9 ⟨1134000, by decide⟩
    (prefixPartial 12 335974) = some ⟨12, 2, 0, 1134000, 335974, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_335974_1134000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335974 ⟨1134000, by decide⟩ :=
  accepted_of_selected 12 335974 ⟨1134000, by decide⟩ ⟨12, 2, 0, 1134000, 335974, 1669, 65536⟩
    (by decide) selected_cut_41473

theorem selected_cut_41474 : selected 9 ⟨1134022, by decide⟩
    (prefixPartial 12 335975) = some ⟨12, 2, 0, 1134022, 335975, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_335975_1134022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335975 ⟨1134022, by decide⟩ :=
  accepted_of_selected 12 335975 ⟨1134022, by decide⟩ ⟨12, 2, 0, 1134022, 335975, 1653, 65536⟩
    (by decide) selected_cut_41474

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
