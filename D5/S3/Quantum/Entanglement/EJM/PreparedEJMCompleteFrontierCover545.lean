/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover544
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_18065_1523236 : frontier 12 ⟨1523236, by decide⟩
    (prefixCache 9 18065) (prefixPartial 9 18065) = false := by
  decide +kernel

theorem node_context_9_18065_1523236 : EJMOriginalGlobalDAGData.nodes 12 ⟨1523236, by decide⟩ =
    .split (coordinate 9) (![⟨1523053, by decide⟩,⟨1468874, by decide⟩,⟨1523163, by decide⟩,⟨1523235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18065_1523236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18065 ⟨1523236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18065
    ⟨1523236, by decide⟩ (by decide) (![⟨1523053, by decide⟩,⟨1468874, by decide⟩,⟨1523163, by decide⟩,⟨1523235, by decide⟩]) unmarked_context_9_18065_1523236 node_context_9_18065_1523236
  intro a
  fin_cases a
  · exact context_10_72260_1523053
  · exact context_10_72261_1468874
  · exact context_10_72262_1523163
  · exact context_10_72263_1523235

theorem selected_cut_52323 : selected 12 ⟨1523323, by decide⟩
    (prefixPartial 9 18066) = some ⟨9, 2, 0, 1523323, 18066, 3825, 4194304⟩ := by
  decide +kernel

theorem context_9_18066_1523323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18066 ⟨1523323, by decide⟩ :=
  accepted_of_selected 9 18066 ⟨1523323, by decide⟩ ⟨9, 2, 0, 1523323, 18066, 3825, 4194304⟩
    (by decide) selected_cut_52323

theorem selected_cut_52324 : selected 12 ⟨1523391, by decide⟩
    (prefixPartial 9 18067) = some ⟨9, 2, 0, 1523391, 18067, 1973, 4194304⟩ := by
  decide +kernel

theorem context_9_18067_1523391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18067 ⟨1523391, by decide⟩ :=
  accepted_of_selected 9 18067 ⟨1523391, by decide⟩ ⟨9, 2, 0, 1523391, 18067, 1973, 4194304⟩
    (by decide) selected_cut_52324

theorem unmarked_context_8_4516_1523392 : frontier 13 ⟨1523392, by decide⟩
    (prefixCache 8 4516) (prefixPartial 8 4516) = false := by
  decide +kernel

theorem node_context_8_4516_1523392 : EJMOriginalGlobalDAGData.nodes 13 ⟨1523392, by decide⟩ =
    .split (coordinate 8) (![⟨1522979, by decide⟩,⟨1523236, by decide⟩,⟨1523323, by decide⟩,⟨1523391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4516_1523392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4516 ⟨1523392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4516
    ⟨1523392, by decide⟩ (by decide) (![⟨1522979, by decide⟩,⟨1523236, by decide⟩,⟨1523323, by decide⟩,⟨1523391, by decide⟩]) unmarked_context_8_4516_1523392 node_context_8_4516_1523392
  intro a
  fin_cases a
  · exact context_9_18064_1522979
  · exact context_9_18065_1523236
  · exact context_9_18066_1523323
  · exact context_9_18067_1523391

theorem selected_cut_52325 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72272) = some ⟨10, 1, 0, 1468246, 72272, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72272_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72272 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72272 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72272, 1, 1048576⟩
    (by decide) selected_cut_52325

theorem selected_cut_52326 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 289092) = some ⟨11, 1, 0, 815620, 289092, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289092_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289092 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 289092 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 289092, 1, 262144⟩
    (by decide) selected_cut_52326

theorem selected_cut_52327 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289093) = some ⟨11, 1, 0, 1468419, 289093, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289093_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289093 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289093 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289093, 1, 262144⟩
    (by decide) selected_cut_52327

theorem selected_cut_52328 : selected 10 ⟨1523458, by decide⟩
    (prefixPartial 11 289094) = some ⟨11, 2, 0, 1523458, 289094, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_289094_1523458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289094 ⟨1523458, by decide⟩ :=
  accepted_of_selected 11 289094 ⟨1523458, by decide⟩ ⟨11, 2, 0, 1523458, 289094, 2425, 262144⟩
    (by decide) selected_cut_52328

theorem selected_cut_52329 : selected 10 ⟨1523518, by decide⟩
    (prefixPartial 11 289095) = some ⟨11, 2, 0, 1523518, 289095, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_289095_1523518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289095 ⟨1523518, by decide⟩ :=
  accepted_of_selected 11 289095 ⟨1523518, by decide⟩ ⟨11, 2, 0, 1523518, 289095, 2361, 262144⟩
    (by decide) selected_cut_52329

theorem unmarked_context_10_72273_1523519 : frontier 11 ⟨1523519, by decide⟩
    (prefixCache 10 72273) (prefixPartial 10 72273) = false := by
  decide +kernel

theorem node_context_10_72273_1523519 : EJMOriginalGlobalDAGData.nodes 11 ⟨1523519, by decide⟩ =
    .split (coordinate 10) (![⟨815620, by decide⟩,⟨1468419, by decide⟩,⟨1523458, by decide⟩,⟨1523518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72273_1523519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72273 ⟨1523519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72273
    ⟨1523519, by decide⟩ (by decide) (![⟨815620, by decide⟩,⟨1468419, by decide⟩,⟨1523458, by decide⟩,⟨1523518, by decide⟩]) unmarked_context_10_72273_1523519 node_context_10_72273_1523519
  intro a
  fin_cases a
  · exact context_11_289092_815620
  · exact context_11_289093_1468419
  · exact context_11_289094_1523458
  · exact context_11_289095_1523518

theorem selected_cut_52330 : selected 11 ⟨1523613, by decide⟩
    (prefixPartial 10 72274) = some ⟨10, 2, 0, 1523613, 72274, 3629, 1048576⟩ := by
  decide +kernel

theorem context_10_72274_1523613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72274 ⟨1523613, by decide⟩ :=
  accepted_of_selected 10 72274 ⟨1523613, by decide⟩ ⟨10, 2, 0, 1523613, 72274, 3629, 1048576⟩
    (by decide) selected_cut_52330

theorem selected_cut_52331 : selected 10 ⟨1523666, by decide⟩
    (prefixPartial 11 289100) = some ⟨11, 2, 0, 1523666, 289100, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_289100_1523666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289100 ⟨1523666, by decide⟩ :=
  accepted_of_selected 11 289100 ⟨1523666, by decide⟩ ⟨11, 2, 0, 1523666, 289100, 2169, 262144⟩
    (by decide) selected_cut_52331

theorem selected_cut_52332 : selected 10 ⟨1523683, by decide⟩
    (prefixPartial 11 289101) = some ⟨11, 2, 0, 1523683, 289101, 757, 262144⟩ := by
  decide +kernel

theorem context_11_289101_1523683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289101 ⟨1523683, by decide⟩ :=
  accepted_of_selected 11 289101 ⟨1523683, by decide⟩ ⟨11, 2, 0, 1523683, 289101, 757, 262144⟩
    (by decide) selected_cut_52332

theorem selected_cut_52333 : selected 10 ⟨1523740, by decide⟩
    (prefixPartial 11 289102) = some ⟨11, 2, 0, 1523740, 289102, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_289102_1523740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289102 ⟨1523740, by decide⟩ :=
  accepted_of_selected 11 289102 ⟨1523740, by decide⟩ ⟨11, 2, 0, 1523740, 289102, 1985, 262144⟩
    (by decide) selected_cut_52333

theorem selected_cut_52334 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 289103) = some ⟨11, 1, 0, 1470044, 289103, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289103_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289103 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 289103 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 289103, 1, 262144⟩
    (by decide) selected_cut_52334

theorem unmarked_context_10_72275_1523741 : frontier 11 ⟨1523741, by decide⟩
    (prefixCache 10 72275) (prefixPartial 10 72275) = false := by
  decide +kernel

theorem node_context_10_72275_1523741 : EJMOriginalGlobalDAGData.nodes 11 ⟨1523741, by decide⟩ =
    .split (coordinate 10) (![⟨1523666, by decide⟩,⟨1523683, by decide⟩,⟨1523740, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72275_1523741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72275 ⟨1523741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72275
    ⟨1523741, by decide⟩ (by decide) (![⟨1523666, by decide⟩,⟨1523683, by decide⟩,⟨1523740, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_72275_1523741 node_context_10_72275_1523741
  intro a
  fin_cases a
  · exact context_11_289100_1523666
  · exact context_11_289101_1523683
  · exact context_11_289102_1523740
  · exact context_11_289103_1470044

theorem unmarked_context_9_18068_1523742 : frontier 12 ⟨1523742, by decide⟩
    (prefixCache 9 18068) (prefixPartial 9 18068) = false := by
  decide +kernel

theorem node_context_9_18068_1523742 : EJMOriginalGlobalDAGData.nodes 12 ⟨1523742, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1523519, by decide⟩,⟨1523613, by decide⟩,⟨1523741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18068_1523742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18068 ⟨1523742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18068
    ⟨1523742, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1523519, by decide⟩,⟨1523613, by decide⟩,⟨1523741, by decide⟩]) unmarked_context_9_18068_1523742 node_context_9_18068_1523742
  intro a
  fin_cases a
  · exact context_10_72272_1468246
  · exact context_10_72273_1523519
  · exact context_10_72274_1523613
  · exact context_10_72275_1523741

theorem selected_cut_52335 : selected 11 ⟨1523814, by decide⟩
    (prefixPartial 10 72276) = some ⟨10, 2, 0, 1523814, 72276, 2829, 1048576⟩ := by
  decide +kernel

theorem context_10_72276_1523814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72276 ⟨1523814, by decide⟩ :=
  accepted_of_selected 10 72276 ⟨1523814, by decide⟩ ⟨10, 2, 0, 1523814, 72276, 2829, 1048576⟩
    (by decide) selected_cut_52335

theorem selected_cut_52336 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72277) = some ⟨10, 1, 0, 1468874, 72277, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72277_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72277 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72277 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72277, 1, 1048576⟩
    (by decide) selected_cut_52336

theorem selected_cut_52337 : selected 10 ⟨1523865, by decide⟩
    (prefixPartial 11 289112) = some ⟨11, 2, 0, 1523865, 289112, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_289112_1523865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289112 ⟨1523865, by decide⟩ :=
  accepted_of_selected 11 289112 ⟨1523865, by decide⟩ ⟨11, 2, 0, 1523865, 289112, 1733, 262144⟩
    (by decide) selected_cut_52337

theorem selected_cut_52338 : selected 10 ⟨1523887, by decide⟩
    (prefixPartial 11 289113) = some ⟨11, 2, 0, 1523887, 289113, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_289113_1523887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289113 ⟨1523887, by decide⟩ :=
  accepted_of_selected 11 289113 ⟨1523887, by decide⟩ ⟨11, 2, 0, 1523887, 289113, 1129, 262144⟩
    (by decide) selected_cut_52338

theorem selected_cut_52339 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 289114) = some ⟨11, 1, 0, 1468743, 289114, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289114_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289114 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 289114 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 289114, 1, 262144⟩
    (by decide) selected_cut_52339

theorem selected_cut_52340 : selected 10 ⟨1523919, by decide⟩
    (prefixPartial 11 289115) = some ⟨11, 2, 0, 1523919, 289115, 1345, 262144⟩ := by
  decide +kernel

theorem context_11_289115_1523919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289115 ⟨1523919, by decide⟩ :=
  accepted_of_selected 11 289115 ⟨1523919, by decide⟩ ⟨11, 2, 0, 1523919, 289115, 1345, 262144⟩
    (by decide) selected_cut_52340

theorem unmarked_context_10_72278_1523920 : frontier 11 ⟨1523920, by decide⟩
    (prefixCache 10 72278) (prefixPartial 10 72278) = false := by
  decide +kernel

theorem node_context_10_72278_1523920 : EJMOriginalGlobalDAGData.nodes 11 ⟨1523920, by decide⟩ =
    .split (coordinate 10) (![⟨1523865, by decide⟩,⟨1523887, by decide⟩,⟨1468743, by decide⟩,⟨1523919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72278_1523920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72278 ⟨1523920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72278
    ⟨1523920, by decide⟩ (by decide) (![⟨1523865, by decide⟩,⟨1523887, by decide⟩,⟨1468743, by decide⟩,⟨1523919, by decide⟩]) unmarked_context_10_72278_1523920 node_context_10_72278_1523920
  intro a
  fin_cases a
  · exact context_11_289112_1523865
  · exact context_11_289113_1523887
  · exact context_11_289114_1468743
  · exact context_11_289115_1523919

theorem selected_cut_52341 : selected 11 ⟨1523983, by decide⟩
    (prefixPartial 10 72279) = some ⟨10, 2, 0, 1523983, 72279, 2773, 1048576⟩ := by
  decide +kernel

theorem context_10_72279_1523983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72279 ⟨1523983, by decide⟩ :=
  accepted_of_selected 10 72279 ⟨1523983, by decide⟩ ⟨10, 2, 0, 1523983, 72279, 2773, 1048576⟩
    (by decide) selected_cut_52341

theorem unmarked_context_9_18069_1523984 : frontier 12 ⟨1523984, by decide⟩
    (prefixCache 9 18069) (prefixPartial 9 18069) = false := by
  decide +kernel

theorem node_context_9_18069_1523984 : EJMOriginalGlobalDAGData.nodes 12 ⟨1523984, by decide⟩ =
    .split (coordinate 9) (![⟨1523814, by decide⟩,⟨1468874, by decide⟩,⟨1523920, by decide⟩,⟨1523983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18069_1523984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18069 ⟨1523984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18069
    ⟨1523984, by decide⟩ (by decide) (![⟨1523814, by decide⟩,⟨1468874, by decide⟩,⟨1523920, by decide⟩,⟨1523983, by decide⟩]) unmarked_context_9_18069_1523984 node_context_9_18069_1523984
  intro a
  fin_cases a
  · exact context_10_72276_1523814
  · exact context_10_72277_1468874
  · exact context_10_72278_1523920
  · exact context_10_72279_1523983

theorem selected_cut_52342 : selected 12 ⟨1524052, by decide⟩
    (prefixPartial 9 18070) = some ⟨9, 2, 0, 1524052, 18070, 3337, 4194304⟩ := by
  decide +kernel

theorem context_9_18070_1524052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18070 ⟨1524052, by decide⟩ :=
  accepted_of_selected 9 18070 ⟨1524052, by decide⟩ ⟨9, 2, 0, 1524052, 18070, 3337, 4194304⟩
    (by decide) selected_cut_52342

theorem selected_cut_52343 : selected 12 ⟨1524111, by decide⟩
    (prefixPartial 9 18071) = some ⟨9, 2, 0, 1524111, 18071, 1541, 4194304⟩ := by
  decide +kernel

theorem context_9_18071_1524111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18071 ⟨1524111, by decide⟩ :=
  accepted_of_selected 9 18071 ⟨1524111, by decide⟩ ⟨9, 2, 0, 1524111, 18071, 1541, 4194304⟩
    (by decide) selected_cut_52343

theorem unmarked_context_8_4517_1524112 : frontier 13 ⟨1524112, by decide⟩
    (prefixCache 8 4517) (prefixPartial 8 4517) = false := by
  decide +kernel

theorem node_context_8_4517_1524112 : EJMOriginalGlobalDAGData.nodes 13 ⟨1524112, by decide⟩ =
    .split (coordinate 8) (![⟨1523742, by decide⟩,⟨1523984, by decide⟩,⟨1524052, by decide⟩,⟨1524111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4517_1524112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4517 ⟨1524112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4517
    ⟨1524112, by decide⟩ (by decide) (![⟨1523742, by decide⟩,⟨1523984, by decide⟩,⟨1524052, by decide⟩,⟨1524111, by decide⟩]) unmarked_context_8_4517_1524112 node_context_8_4517_1524112
  intro a
  fin_cases a
  · exact context_9_18068_1523742
  · exact context_9_18069_1523984
  · exact context_9_18070_1524052
  · exact context_9_18071_1524111

theorem selected_cut_52344 : selected 13 ⟨1524113, by decide⟩
    (prefixPartial 8 4518) = some ⟨8, 1, 0, 1524113, 4518, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4518_1524113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4518 ⟨1524113, by decide⟩ :=
  accepted_of_selected 8 4518 ⟨1524113, by decide⟩ ⟨8, 1, 0, 1524113, 4518, 1, 16777216⟩
    (by decide) selected_cut_52344

theorem selected_cut_52345 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72304) = some ⟨10, 1, 0, 1468246, 72304, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72304_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72304 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72304 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72304, 1, 1048576⟩
    (by decide) selected_cut_52345

theorem selected_cut_52346 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 289220) = some ⟨11, 1, 0, 815620, 289220, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289220_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289220 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 289220 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 289220, 1, 262144⟩
    (by decide) selected_cut_52346

theorem selected_cut_52347 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289221) = some ⟨11, 1, 0, 1468419, 289221, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289221_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289221 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289221 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289221, 1, 262144⟩
    (by decide) selected_cut_52347

theorem selected_cut_52348 : selected 10 ⟨1524199, by decide⟩
    (prefixPartial 11 289222) = some ⟨11, 2, 0, 1524199, 289222, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_289222_1524199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289222 ⟨1524199, by decide⟩ :=
  accepted_of_selected 11 289222 ⟨1524199, by decide⟩ ⟨11, 2, 0, 1524199, 289222, 2845, 262144⟩
    (by decide) selected_cut_52348

theorem selected_cut_52349 : selected 10 ⟨1524241, by decide⟩
    (prefixPartial 11 289223) = some ⟨11, 2, 0, 1524241, 289223, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_289223_1524241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289223 ⟨1524241, by decide⟩ :=
  accepted_of_selected 11 289223 ⟨1524241, by decide⟩ ⟨11, 2, 0, 1524241, 289223, 1397, 262144⟩
    (by decide) selected_cut_52349

theorem unmarked_context_10_72305_1524242 : frontier 11 ⟨1524242, by decide⟩
    (prefixCache 10 72305) (prefixPartial 10 72305) = false := by
  decide +kernel

theorem node_context_10_72305_1524242 : EJMOriginalGlobalDAGData.nodes 11 ⟨1524242, by decide⟩ =
    .split (coordinate 10) (![⟨815620, by decide⟩,⟨1468419, by decide⟩,⟨1524199, by decide⟩,⟨1524241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72305_1524242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72305 ⟨1524242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72305
    ⟨1524242, by decide⟩ (by decide) (![⟨815620, by decide⟩,⟨1468419, by decide⟩,⟨1524199, by decide⟩,⟨1524241, by decide⟩]) unmarked_context_10_72305_1524242 node_context_10_72305_1524242
  intro a
  fin_cases a
  · exact context_11_289220_815620
  · exact context_11_289221_1468419
  · exact context_11_289222_1524199
  · exact context_11_289223_1524241

theorem selected_cut_52350 : selected 10 ⟨1524339, by decide⟩
    (prefixPartial 11 289224) = some ⟨11, 2, 0, 1524339, 289224, 3033, 262144⟩ := by
  decide +kernel

theorem context_11_289224_1524339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289224 ⟨1524339, by decide⟩ :=
  accepted_of_selected 11 289224 ⟨1524339, by decide⟩ ⟨11, 2, 0, 1524339, 289224, 3033, 262144⟩
    (by decide) selected_cut_52350

theorem selected_cut_52351 : selected 10 ⟨1524370, by decide⟩
    (prefixPartial 11 289225) = some ⟨11, 2, 0, 1524370, 289225, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_289225_1524370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289225 ⟨1524370, by decide⟩ :=
  accepted_of_selected 11 289225 ⟨1524370, by decide⟩ ⟨11, 2, 0, 1524370, 289225, 1069, 262144⟩
    (by decide) selected_cut_52351

theorem selected_cut_52352 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 289226) = some ⟨11, 1, 0, 1468743, 289226, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289226_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289226 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 289226 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 289226, 1, 262144⟩
    (by decide) selected_cut_52352

theorem selected_cut_52353 : selected 10 ⟨1524404, by decide⟩
    (prefixPartial 11 289227) = some ⟨11, 2, 0, 1524404, 289227, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_289227_1524404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289227 ⟨1524404, by decide⟩ :=
  accepted_of_selected 11 289227 ⟨1524404, by decide⟩ ⟨11, 2, 0, 1524404, 289227, 1277, 262144⟩
    (by decide) selected_cut_52353

theorem unmarked_context_10_72306_1524405 : frontier 11 ⟨1524405, by decide⟩
    (prefixCache 10 72306) (prefixPartial 10 72306) = false := by
  decide +kernel

theorem node_context_10_72306_1524405 : EJMOriginalGlobalDAGData.nodes 11 ⟨1524405, by decide⟩ =
    .split (coordinate 10) (![⟨1524339, by decide⟩,⟨1524370, by decide⟩,⟨1468743, by decide⟩,⟨1524404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72306_1524405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72306 ⟨1524405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72306
    ⟨1524405, by decide⟩ (by decide) (![⟨1524339, by decide⟩,⟨1524370, by decide⟩,⟨1468743, by decide⟩,⟨1524404, by decide⟩]) unmarked_context_10_72306_1524405 node_context_10_72306_1524405
  intro a
  fin_cases a
  · exact context_11_289224_1524339
  · exact context_11_289225_1524370
  · exact context_11_289226_1468743
  · exact context_11_289227_1524404

theorem selected_cut_52354 : selected 10 ⟨1524487, by decide⟩
    (prefixPartial 11 289228) = some ⟨11, 2, 0, 1524487, 289228, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_289228_1524487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289228 ⟨1524487, by decide⟩ :=
  accepted_of_selected 11 289228 ⟨1524487, by decide⟩ ⟨11, 2, 0, 1524487, 289228, 2309, 262144⟩
    (by decide) selected_cut_52354

theorem selected_cut_52355 : selected 10 ⟨1524511, by decide⟩
    (prefixPartial 11 289229) = some ⟨11, 2, 0, 1524511, 289229, 901, 262144⟩ := by
  decide +kernel

theorem context_11_289229_1524511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289229 ⟨1524511, by decide⟩ :=
  accepted_of_selected 11 289229 ⟨1524511, by decide⟩ ⟨11, 2, 0, 1524511, 289229, 901, 262144⟩
    (by decide) selected_cut_52355

theorem selected_cut_52356 : selected 10 ⟨1524556, by decide⟩
    (prefixPartial 11 289230) = some ⟨11, 2, 0, 1524556, 289230, 2045, 262144⟩ := by
  decide +kernel

theorem context_11_289230_1524556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289230 ⟨1524556, by decide⟩ :=
  accepted_of_selected 11 289230 ⟨1524556, by decide⟩ ⟨11, 2, 0, 1524556, 289230, 2045, 262144⟩
    (by decide) selected_cut_52356

theorem selected_cut_52357 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 289231) = some ⟨11, 1, 0, 1470044, 289231, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289231_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289231 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 289231 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 289231, 1, 262144⟩
    (by decide) selected_cut_52357

theorem unmarked_context_10_72307_1524557 : frontier 11 ⟨1524557, by decide⟩
    (prefixCache 10 72307) (prefixPartial 10 72307) = false := by
  decide +kernel

theorem node_context_10_72307_1524557 : EJMOriginalGlobalDAGData.nodes 11 ⟨1524557, by decide⟩ =
    .split (coordinate 10) (![⟨1524487, by decide⟩,⟨1524511, by decide⟩,⟨1524556, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72307_1524557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72307 ⟨1524557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72307
    ⟨1524557, by decide⟩ (by decide) (![⟨1524487, by decide⟩,⟨1524511, by decide⟩,⟨1524556, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_72307_1524557 node_context_10_72307_1524557
  intro a
  fin_cases a
  · exact context_11_289228_1524487
  · exact context_11_289229_1524511
  · exact context_11_289230_1524556
  · exact context_11_289231_1470044

theorem unmarked_context_9_18076_1524558 : frontier 12 ⟨1524558, by decide⟩
    (prefixCache 9 18076) (prefixPartial 9 18076) = false := by
  decide +kernel

theorem node_context_9_18076_1524558 : EJMOriginalGlobalDAGData.nodes 12 ⟨1524558, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1524242, by decide⟩,⟨1524405, by decide⟩,⟨1524557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18076_1524558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18076 ⟨1524558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18076
    ⟨1524558, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1524242, by decide⟩,⟨1524405, by decide⟩,⟨1524557, by decide⟩]) unmarked_context_9_18076_1524558 node_context_9_18076_1524558
  intro a
  fin_cases a
  · exact context_10_72304_1468246
  · exact context_10_72305_1524242
  · exact context_10_72306_1524405
  · exact context_10_72307_1524557

theorem selected_cut_52358 : selected 11 ⟨1524645, by decide⟩
    (prefixPartial 10 72308) = some ⟨10, 2, 0, 1524645, 72308, 3241, 1048576⟩ := by
  decide +kernel

theorem context_10_72308_1524645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72308 ⟨1524645, by decide⟩ :=
  accepted_of_selected 10 72308 ⟨1524645, by decide⟩ ⟨10, 2, 0, 1524645, 72308, 3241, 1048576⟩
    (by decide) selected_cut_52358

theorem selected_cut_52359 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72309) = some ⟨10, 1, 0, 1468874, 72309, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72309_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72309 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72309 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72309, 1, 1048576⟩
    (by decide) selected_cut_52359

theorem selected_cut_52360 : selected 11 ⟨1524822, by decide⟩
    (prefixPartial 10 72310) = some ⟨10, 2, 0, 1524822, 72310, 3981, 1048576⟩ := by
  decide +kernel

theorem context_10_72310_1524822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72310 ⟨1524822, by decide⟩ :=
  accepted_of_selected 10 72310 ⟨1524822, by decide⟩ ⟨10, 2, 0, 1524822, 72310, 3981, 1048576⟩
    (by decide) selected_cut_52360

theorem selected_cut_52361 : selected 11 ⟨1524910, by decide⟩
    (prefixPartial 10 72311) = some ⟨10, 2, 0, 1524910, 72311, 3501, 1048576⟩ := by
  decide +kernel

theorem context_10_72311_1524910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72311 ⟨1524910, by decide⟩ :=
  accepted_of_selected 10 72311 ⟨1524910, by decide⟩ ⟨10, 2, 0, 1524910, 72311, 3501, 1048576⟩
    (by decide) selected_cut_52361

theorem unmarked_context_9_18077_1524911 : frontier 12 ⟨1524911, by decide⟩
    (prefixCache 9 18077) (prefixPartial 9 18077) = false := by
  decide +kernel

theorem node_context_9_18077_1524911 : EJMOriginalGlobalDAGData.nodes 12 ⟨1524911, by decide⟩ =
    .split (coordinate 9) (![⟨1524645, by decide⟩,⟨1468874, by decide⟩,⟨1524822, by decide⟩,⟨1524910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18077_1524911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18077 ⟨1524911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18077
    ⟨1524911, by decide⟩ (by decide) (![⟨1524645, by decide⟩,⟨1468874, by decide⟩,⟨1524822, by decide⟩,⟨1524910, by decide⟩]) unmarked_context_9_18077_1524911 node_context_9_18077_1524911
  intro a
  fin_cases a
  · exact context_10_72308_1524645
  · exact context_10_72309_1468874
  · exact context_10_72310_1524822
  · exact context_10_72311_1524910

theorem selected_cut_52362 : selected 12 ⟨1524997, by decide⟩
    (prefixPartial 9 18078) = some ⟨9, 2, 0, 1524997, 18078, 3121, 4194304⟩ := by
  decide +kernel

theorem context_9_18078_1524997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18078 ⟨1524997, by decide⟩ :=
  accepted_of_selected 9 18078 ⟨1524997, by decide⟩ ⟨9, 2, 0, 1524997, 18078, 3121, 4194304⟩
    (by decide) selected_cut_52362

theorem selected_cut_52363 : selected 12 ⟨1525057, by decide⟩
    (prefixPartial 9 18079) = some ⟨9, 2, 0, 1525057, 18079, 1573, 4194304⟩ := by
  decide +kernel

theorem context_9_18079_1525057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18079 ⟨1525057, by decide⟩ :=
  accepted_of_selected 9 18079 ⟨1525057, by decide⟩ ⟨9, 2, 0, 1525057, 18079, 1573, 4194304⟩
    (by decide) selected_cut_52363

theorem unmarked_context_8_4519_1525058 : frontier 13 ⟨1525058, by decide⟩
    (prefixCache 8 4519) (prefixPartial 8 4519) = false := by
  decide +kernel

theorem node_context_8_4519_1525058 : EJMOriginalGlobalDAGData.nodes 13 ⟨1525058, by decide⟩ =
    .split (coordinate 8) (![⟨1524558, by decide⟩,⟨1524911, by decide⟩,⟨1524997, by decide⟩,⟨1525057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4519_1525058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4519 ⟨1525058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4519
    ⟨1525058, by decide⟩ (by decide) (![⟨1524558, by decide⟩,⟨1524911, by decide⟩,⟨1524997, by decide⟩,⟨1525057, by decide⟩]) unmarked_context_8_4519_1525058 node_context_8_4519_1525058
  intro a
  fin_cases a
  · exact context_9_18076_1524558
  · exact context_9_18077_1524911
  · exact context_9_18078_1524997
  · exact context_9_18079_1525057

theorem unmarked_context_7_1129_1525059 : frontier 14 ⟨1525059, by decide⟩
    (prefixCache 7 1129) (prefixPartial 7 1129) = false := by
  decide +kernel

theorem node_context_7_1129_1525059 : EJMOriginalGlobalDAGData.nodes 14 ⟨1525059, by decide⟩ =
    .split (coordinate 7) (![⟨1523392, by decide⟩,⟨1524112, by decide⟩,⟨1524113, by decide⟩,⟨1525058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1129_1525059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1129 ⟨1525059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1129
    ⟨1525059, by decide⟩ (by decide) (![⟨1523392, by decide⟩,⟨1524112, by decide⟩,⟨1524113, by decide⟩,⟨1525058, by decide⟩]) unmarked_context_7_1129_1525059 node_context_7_1129_1525059
  intro a
  fin_cases a
  · exact context_8_4516_1523392
  · exact context_8_4517_1524112
  · exact context_8_4518_1524113
  · exact context_8_4519_1525058

theorem selected_cut_52364 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72320) = some ⟨10, 1, 0, 1468246, 72320, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72320_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72320 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72320 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72320, 1, 1048576⟩
    (by decide) selected_cut_52364

theorem selected_cut_52365 : selected 10 ⟨1525106, by decide⟩
    (prefixPartial 11 289284) = some ⟨11, 2, 0, 1525106, 289284, 1209, 262144⟩ := by
  decide +kernel

theorem context_11_289284_1525106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289284 ⟨1525106, by decide⟩ :=
  accepted_of_selected 11 289284 ⟨1525106, by decide⟩ ⟨11, 2, 0, 1525106, 289284, 1209, 262144⟩
    (by decide) selected_cut_52365

theorem selected_cut_52366 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289285) = some ⟨11, 1, 0, 1468419, 289285, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289285_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289285 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289285 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289285, 1, 262144⟩
    (by decide) selected_cut_52366

theorem selected_cut_52367 : selected 10 ⟨1525213, by decide⟩
    (prefixPartial 11 289286) = some ⟨11, 2, 0, 1525213, 289286, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_289286_1525213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289286 ⟨1525213, by decide⟩ :=
  accepted_of_selected 11 289286 ⟨1525213, by decide⟩ ⟨11, 2, 0, 1525213, 289286, 1777, 262144⟩
    (by decide) selected_cut_52367

theorem selected_cut_52368 : selected 10 ⟨1525309, by decide⟩
    (prefixPartial 11 289287) = some ⟨11, 2, 0, 1525309, 289287, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_289287_1525309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289287 ⟨1525309, by decide⟩ :=
  accepted_of_selected 11 289287 ⟨1525309, by decide⟩ ⟨11, 2, 0, 1525309, 289287, 2253, 262144⟩
    (by decide) selected_cut_52368

theorem unmarked_context_10_72321_1525310 : frontier 11 ⟨1525310, by decide⟩
    (prefixCache 10 72321) (prefixPartial 10 72321) = false := by
  decide +kernel

theorem node_context_10_72321_1525310 : EJMOriginalGlobalDAGData.nodes 11 ⟨1525310, by decide⟩ =
    .split (coordinate 10) (![⟨1525106, by decide⟩,⟨1468419, by decide⟩,⟨1525213, by decide⟩,⟨1525309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72321_1525310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72321 ⟨1525310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72321
    ⟨1525310, by decide⟩ (by decide) (![⟨1525106, by decide⟩,⟨1468419, by decide⟩,⟨1525213, by decide⟩,⟨1525309, by decide⟩]) unmarked_context_10_72321_1525310 node_context_10_72321_1525310
  intro a
  fin_cases a
  · exact context_11_289284_1525106
  · exact context_11_289285_1468419
  · exact context_11_289286_1525213
  · exact context_11_289287_1525309

theorem selected_cut_52369 : selected 11 ⟨1525378, by decide⟩
    (prefixPartial 10 72322) = some ⟨10, 2, 0, 1525378, 72322, 1845, 1048576⟩ := by
  decide +kernel

theorem context_10_72322_1525378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72322 ⟨1525378, by decide⟩ :=
  accepted_of_selected 10 72322 ⟨1525378, by decide⟩ ⟨10, 2, 0, 1525378, 72322, 1845, 1048576⟩
    (by decide) selected_cut_52369

theorem selected_cut_52370 : selected 11 ⟨1525530, by decide⟩
    (prefixPartial 10 72323) = some ⟨10, 2, 0, 1525530, 72323, 3057, 1048576⟩ := by
  decide +kernel

theorem context_10_72323_1525530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72323 ⟨1525530, by decide⟩ :=
  accepted_of_selected 10 72323 ⟨1525530, by decide⟩ ⟨10, 2, 0, 1525530, 72323, 3057, 1048576⟩
    (by decide) selected_cut_52370

theorem unmarked_context_9_18080_1525531 : frontier 12 ⟨1525531, by decide⟩
    (prefixCache 9 18080) (prefixPartial 9 18080) = false := by
  decide +kernel

theorem node_context_9_18080_1525531 : EJMOriginalGlobalDAGData.nodes 12 ⟨1525531, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1525310, by decide⟩,⟨1525378, by decide⟩,⟨1525530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18080_1525531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18080 ⟨1525531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18080
    ⟨1525531, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1525310, by decide⟩,⟨1525378, by decide⟩,⟨1525530, by decide⟩]) unmarked_context_9_18080_1525531 node_context_9_18080_1525531
  intro a
  fin_cases a
  · exact context_10_72320_1468246
  · exact context_10_72321_1525310
  · exact context_10_72322_1525378
  · exact context_10_72323_1525530

theorem selected_cut_52371 : selected 12 ⟨1525743, by decide⟩
    (prefixPartial 9 18081) = some ⟨9, 2, 0, 1525743, 18081, 3981, 4194304⟩ := by
  decide +kernel

theorem context_9_18081_1525743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18081 ⟨1525743, by decide⟩ :=
  accepted_of_selected 9 18081 ⟨1525743, by decide⟩ ⟨9, 2, 0, 1525743, 18081, 3981, 4194304⟩
    (by decide) selected_cut_52371

theorem selected_cut_52372 : selected 12 ⟨1525837, by decide⟩
    (prefixPartial 9 18082) = some ⟨9, 2, 0, 1525837, 18082, 989, 4194304⟩ := by
  decide +kernel

theorem context_9_18082_1525837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18082 ⟨1525837, by decide⟩ :=
  accepted_of_selected 9 18082 ⟨1525837, by decide⟩ ⟨9, 2, 0, 1525837, 18082, 989, 4194304⟩
    (by decide) selected_cut_52372

theorem selected_cut_52373 : selected 12 ⟨1525860, by decide⟩
    (prefixPartial 9 18083) = some ⟨9, 2, 0, 1525860, 18083, 273, 4194304⟩ := by
  decide +kernel

theorem context_9_18083_1525860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18083 ⟨1525860, by decide⟩ :=
  accepted_of_selected 9 18083 ⟨1525860, by decide⟩ ⟨9, 2, 0, 1525860, 18083, 273, 4194304⟩
    (by decide) selected_cut_52373

theorem unmarked_context_8_4520_1525861 : frontier 13 ⟨1525861, by decide⟩
    (prefixCache 8 4520) (prefixPartial 8 4520) = false := by
  decide +kernel

theorem node_context_8_4520_1525861 : EJMOriginalGlobalDAGData.nodes 13 ⟨1525861, by decide⟩ =
    .split (coordinate 8) (![⟨1525531, by decide⟩,⟨1525743, by decide⟩,⟨1525837, by decide⟩,⟨1525860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4520_1525861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4520 ⟨1525861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4520
    ⟨1525861, by decide⟩ (by decide) (![⟨1525531, by decide⟩,⟨1525743, by decide⟩,⟨1525837, by decide⟩,⟨1525860, by decide⟩]) unmarked_context_8_4520_1525861 node_context_8_4520_1525861
  intro a
  fin_cases a
  · exact context_9_18080_1525531
  · exact context_9_18081_1525743
  · exact context_9_18082_1525837
  · exact context_9_18083_1525860

theorem selected_cut_52374 : selected 13 ⟨1502490, by decide⟩
    (prefixPartial 8 4521) = some ⟨8, 1, 0, 1502490, 4521, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4521_1502490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4521 ⟨1502490, by decide⟩ :=
  accepted_of_selected 8 4521 ⟨1502490, by decide⟩ ⟨8, 1, 0, 1502490, 4521, 1, 16777216⟩
    (by decide) selected_cut_52374

theorem selected_cut_52375 : selected 13 ⟨1502490, by decide⟩
    (prefixPartial 8 4522) = some ⟨8, 1, 0, 1502490, 4522, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4522_1502490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4522 ⟨1502490, by decide⟩ :=
  accepted_of_selected 8 4522 ⟨1502490, by decide⟩ ⟨8, 1, 0, 1502490, 4522, 1, 16777216⟩
    (by decide) selected_cut_52375

theorem selected_cut_52376 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72368) = some ⟨10, 1, 0, 1468246, 72368, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72368_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72368 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72368 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72368, 1, 1048576⟩
    (by decide) selected_cut_52376

theorem selected_cut_52377 : selected 10 ⟨1525948, by decide⟩
    (prefixPartial 11 289476) = some ⟨11, 2, 0, 1525948, 289476, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_289476_1525948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289476 ⟨1525948, by decide⟩ :=
  accepted_of_selected 11 289476 ⟨1525948, by decide⟩ ⟨11, 2, 0, 1525948, 289476, 2809, 262144⟩
    (by decide) selected_cut_52377

theorem selected_cut_52378 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289477) = some ⟨11, 1, 0, 1468419, 289477, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289477_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289477 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289477 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289477, 1, 262144⟩
    (by decide) selected_cut_52378

theorem selected_cut_52379 : selected 10 ⟨1526049, by decide⟩
    (prefixPartial 11 289478) = some ⟨11, 2, 0, 1526049, 289478, 2757, 262144⟩ := by
  decide +kernel

theorem context_11_289478_1526049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289478 ⟨1526049, by decide⟩ :=
  accepted_of_selected 11 289478 ⟨1526049, by decide⟩ ⟨11, 2, 0, 1526049, 289478, 2757, 262144⟩
    (by decide) selected_cut_52379

theorem selected_cut_52380 : selected 10 ⟨1526138, by decide⟩
    (prefixPartial 11 289479) = some ⟨11, 2, 0, 1526138, 289479, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_289479_1526138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289479 ⟨1526138, by decide⟩ :=
  accepted_of_selected 11 289479 ⟨1526138, by decide⟩ ⟨11, 2, 0, 1526138, 289479, 2461, 262144⟩
    (by decide) selected_cut_52380

theorem unmarked_context_10_72369_1526139 : frontier 11 ⟨1526139, by decide⟩
    (prefixCache 10 72369) (prefixPartial 10 72369) = false := by
  decide +kernel

theorem node_context_10_72369_1526139 : EJMOriginalGlobalDAGData.nodes 11 ⟨1526139, by decide⟩ =
    .split (coordinate 10) (![⟨1525948, by decide⟩,⟨1468419, by decide⟩,⟨1526049, by decide⟩,⟨1526138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72369_1526139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72369 ⟨1526139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72369
    ⟨1526139, by decide⟩ (by decide) (![⟨1525948, by decide⟩,⟨1468419, by decide⟩,⟨1526049, by decide⟩,⟨1526138, by decide⟩]) unmarked_context_10_72369_1526139 node_context_10_72369_1526139
  intro a
  fin_cases a
  · exact context_11_289476_1525948
  · exact context_11_289477_1468419
  · exact context_11_289478_1526049
  · exact context_11_289479_1526138

theorem selected_cut_52381 : selected 11 ⟨1526190, by decide⟩
    (prefixPartial 10 72370) = some ⟨10, 2, 0, 1526190, 72370, 1933, 1048576⟩ := by
  decide +kernel

theorem context_10_72370_1526190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72370 ⟨1526190, by decide⟩ :=
  accepted_of_selected 10 72370 ⟨1526190, by decide⟩ ⟨10, 2, 0, 1526190, 72370, 1933, 1048576⟩
    (by decide) selected_cut_52381

theorem selected_cut_52382 : selected 11 ⟨1526271, by decide⟩
    (prefixPartial 10 72371) = some ⟨10, 2, 0, 1526271, 72371, 3713, 1048576⟩ := by
  decide +kernel

theorem context_10_72371_1526271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72371 ⟨1526271, by decide⟩ :=
  accepted_of_selected 10 72371 ⟨1526271, by decide⟩ ⟨10, 2, 0, 1526271, 72371, 3713, 1048576⟩
    (by decide) selected_cut_52382

theorem unmarked_context_9_18092_1526272 : frontier 12 ⟨1526272, by decide⟩
    (prefixCache 9 18092) (prefixPartial 9 18092) = false := by
  decide +kernel

theorem node_context_9_18092_1526272 : EJMOriginalGlobalDAGData.nodes 12 ⟨1526272, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1526139, by decide⟩,⟨1526190, by decide⟩,⟨1526271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18092_1526272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18092 ⟨1526272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18092
    ⟨1526272, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1526139, by decide⟩,⟨1526190, by decide⟩,⟨1526271, by decide⟩]) unmarked_context_9_18092_1526272 node_context_9_18092_1526272
  intro a
  fin_cases a
  · exact context_10_72368_1468246
  · exact context_10_72369_1526139
  · exact context_10_72370_1526190
  · exact context_10_72371_1526271

theorem selected_cut_52383 : selected 11 ⟨1526363, by decide⟩
    (prefixPartial 10 72372) = some ⟨10, 2, 0, 1526363, 72372, 3469, 1048576⟩ := by
  decide +kernel

theorem context_10_72372_1526363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72372 ⟨1526363, by decide⟩ :=
  accepted_of_selected 10 72372 ⟨1526363, by decide⟩ ⟨10, 2, 0, 1526363, 72372, 3469, 1048576⟩
    (by decide) selected_cut_52383

theorem selected_cut_52384 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72373) = some ⟨10, 1, 0, 1468874, 72373, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72373_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72373 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72373 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72373, 1, 1048576⟩
    (by decide) selected_cut_52384

theorem selected_cut_52385 : selected 11 ⟨1526430, by decide⟩
    (prefixPartial 10 72374) = some ⟨10, 2, 0, 1526430, 72374, 2657, 1048576⟩ := by
  decide +kernel

theorem context_10_72374_1526430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72374 ⟨1526430, by decide⟩ :=
  accepted_of_selected 10 72374 ⟨1526430, by decide⟩ ⟨10, 2, 0, 1526430, 72374, 2657, 1048576⟩
    (by decide) selected_cut_52385

theorem selected_cut_52386 : selected 11 ⟨1526490, by decide⟩
    (prefixPartial 10 72375) = some ⟨10, 2, 0, 1526490, 72375, 2545, 1048576⟩ := by
  decide +kernel

theorem context_10_72375_1526490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72375 ⟨1526490, by decide⟩ :=
  accepted_of_selected 10 72375 ⟨1526490, by decide⟩ ⟨10, 2, 0, 1526490, 72375, 2545, 1048576⟩
    (by decide) selected_cut_52386

theorem unmarked_context_9_18093_1526491 : frontier 12 ⟨1526491, by decide⟩
    (prefixCache 9 18093) (prefixPartial 9 18093) = false := by
  decide +kernel

theorem node_context_9_18093_1526491 : EJMOriginalGlobalDAGData.nodes 12 ⟨1526491, by decide⟩ =
    .split (coordinate 9) (![⟨1526363, by decide⟩,⟨1468874, by decide⟩,⟨1526430, by decide⟩,⟨1526490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18093_1526491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18093 ⟨1526491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18093
    ⟨1526491, by decide⟩ (by decide) (![⟨1526363, by decide⟩,⟨1468874, by decide⟩,⟨1526430, by decide⟩,⟨1526490, by decide⟩]) unmarked_context_9_18093_1526491 node_context_9_18093_1526491
  intro a
  fin_cases a
  · exact context_10_72372_1526363
  · exact context_10_72373_1468874
  · exact context_10_72374_1526430
  · exact context_10_72375_1526490

theorem selected_cut_52387 : selected 12 ⟨1526610, by decide⟩
    (prefixPartial 9 18094) = some ⟨9, 2, 0, 1526610, 18094, 4001, 4194304⟩ := by
  decide +kernel

theorem context_9_18094_1526610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18094 ⟨1526610, by decide⟩ :=
  accepted_of_selected 9 18094 ⟨1526610, by decide⟩ ⟨9, 2, 0, 1526610, 18094, 4001, 4194304⟩
    (by decide) selected_cut_52387

theorem selected_cut_52388 : selected 12 ⟨1526684, by decide⟩
    (prefixPartial 9 18095) = some ⟨9, 2, 0, 1526684, 18095, 1841, 4194304⟩ := by
  decide +kernel

theorem context_9_18095_1526684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18095 ⟨1526684, by decide⟩ :=
  accepted_of_selected 9 18095 ⟨1526684, by decide⟩ ⟨9, 2, 0, 1526684, 18095, 1841, 4194304⟩
    (by decide) selected_cut_52388

theorem unmarked_context_8_4523_1526685 : frontier 13 ⟨1526685, by decide⟩
    (prefixCache 8 4523) (prefixPartial 8 4523) = false := by
  decide +kernel

theorem node_context_8_4523_1526685 : EJMOriginalGlobalDAGData.nodes 13 ⟨1526685, by decide⟩ =
    .split (coordinate 8) (![⟨1526272, by decide⟩,⟨1526491, by decide⟩,⟨1526610, by decide⟩,⟨1526684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4523_1526685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4523 ⟨1526685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4523
    ⟨1526685, by decide⟩ (by decide) (![⟨1526272, by decide⟩,⟨1526491, by decide⟩,⟨1526610, by decide⟩,⟨1526684, by decide⟩]) unmarked_context_8_4523_1526685 node_context_8_4523_1526685
  intro a
  fin_cases a
  · exact context_9_18092_1526272
  · exact context_9_18093_1526491
  · exact context_9_18094_1526610
  · exact context_9_18095_1526684

theorem unmarked_context_7_1130_1526686 : frontier 14 ⟨1526686, by decide⟩
    (prefixCache 7 1130) (prefixPartial 7 1130) = false := by
  decide +kernel

theorem node_context_7_1130_1526686 : EJMOriginalGlobalDAGData.nodes 14 ⟨1526686, by decide⟩ =
    .split (coordinate 7) (![⟨1525861, by decide⟩,⟨1502490, by decide⟩,⟨1502490, by decide⟩,⟨1526685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1130_1526686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1130 ⟨1526686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1130
    ⟨1526686, by decide⟩ (by decide) (![⟨1525861, by decide⟩,⟨1502490, by decide⟩,⟨1502490, by decide⟩,⟨1526685, by decide⟩]) unmarked_context_7_1130_1526686 node_context_7_1130_1526686
  intro a
  fin_cases a
  · exact context_8_4520_1525861
  · exact context_8_4521_1502490
  · exact context_8_4522_1502490
  · exact context_8_4523_1526685

theorem selected_cut_52389 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72384) = some ⟨10, 1, 0, 1468246, 72384, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72384_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72384 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72384 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72384, 1, 1048576⟩
    (by decide) selected_cut_52389

theorem selected_cut_52390 : selected 10 ⟨1526735, by decide⟩
    (prefixPartial 11 289540) = some ⟨11, 2, 0, 1526735, 289540, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_289540_1526735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289540 ⟨1526735, by decide⟩ :=
  accepted_of_selected 11 289540 ⟨1526735, by decide⟩ ⟨11, 2, 0, 1526735, 289540, 1289, 262144⟩
    (by decide) selected_cut_52390

theorem selected_cut_52391 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289541) = some ⟨11, 1, 0, 1468419, 289541, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289541_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289541 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289541 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289541, 1, 262144⟩
    (by decide) selected_cut_52391

theorem selected_cut_52392 : selected 10 ⟨1526830, by decide⟩
    (prefixPartial 11 289542) = some ⟨11, 2, 0, 1526830, 289542, 2553, 262144⟩ := by
  decide +kernel

theorem context_11_289542_1526830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289542 ⟨1526830, by decide⟩ :=
  accepted_of_selected 11 289542 ⟨1526830, by decide⟩ ⟨11, 2, 0, 1526830, 289542, 2553, 262144⟩
    (by decide) selected_cut_52392

theorem selected_cut_52393 : selected 10 ⟨1526862, by decide⟩
    (prefixPartial 11 289543) = some ⟨11, 2, 0, 1526862, 289543, 993, 262144⟩ := by
  decide +kernel

theorem context_11_289543_1526862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289543 ⟨1526862, by decide⟩ :=
  accepted_of_selected 11 289543 ⟨1526862, by decide⟩ ⟨11, 2, 0, 1526862, 289543, 993, 262144⟩
    (by decide) selected_cut_52393

theorem unmarked_context_10_72385_1526863 : frontier 11 ⟨1526863, by decide⟩
    (prefixCache 10 72385) (prefixPartial 10 72385) = false := by
  decide +kernel

theorem node_context_10_72385_1526863 : EJMOriginalGlobalDAGData.nodes 11 ⟨1526863, by decide⟩ =
    .split (coordinate 10) (![⟨1526735, by decide⟩,⟨1468419, by decide⟩,⟨1526830, by decide⟩,⟨1526862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72385_1526863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72385 ⟨1526863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72385
    ⟨1526863, by decide⟩ (by decide) (![⟨1526735, by decide⟩,⟨1468419, by decide⟩,⟨1526830, by decide⟩,⟨1526862, by decide⟩]) unmarked_context_10_72385_1526863 node_context_10_72385_1526863
  intro a
  fin_cases a
  · exact context_11_289540_1526735
  · exact context_11_289541_1468419
  · exact context_11_289542_1526830
  · exact context_11_289543_1526862

theorem selected_cut_52394 : selected 10 ⟨1526923, by decide⟩
    (prefixPartial 11 289544) = some ⟨11, 2, 0, 1526923, 289544, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_289544_1526923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289544 ⟨1526923, by decide⟩ :=
  accepted_of_selected 11 289544 ⟨1526923, by decide⟩ ⟨11, 2, 0, 1526923, 289544, 2209, 262144⟩
    (by decide) selected_cut_52394

theorem selected_cut_52395 : selected 10 ⟨1526951, by decide⟩
    (prefixPartial 11 289545) = some ⟨11, 2, 0, 1526951, 289545, 1029, 262144⟩ := by
  decide +kernel

theorem context_11_289545_1526951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289545 ⟨1526951, by decide⟩ :=
  accepted_of_selected 11 289545 ⟨1526951, by decide⟩ ⟨11, 2, 0, 1526951, 289545, 1029, 262144⟩
    (by decide) selected_cut_52395

theorem selected_cut_52396 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 289546) = some ⟨11, 1, 0, 1468743, 289546, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289546_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289546 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 289546 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 289546, 1, 262144⟩
    (by decide) selected_cut_52396

theorem selected_cut_52397 : selected 10 ⟨1526982, by decide⟩
    (prefixPartial 11 289547) = some ⟨11, 2, 0, 1526982, 289547, 965, 262144⟩ := by
  decide +kernel

theorem context_11_289547_1526982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289547 ⟨1526982, by decide⟩ :=
  accepted_of_selected 11 289547 ⟨1526982, by decide⟩ ⟨11, 2, 0, 1526982, 289547, 965, 262144⟩
    (by decide) selected_cut_52397

theorem unmarked_context_10_72386_1526983 : frontier 11 ⟨1526983, by decide⟩
    (prefixCache 10 72386) (prefixPartial 10 72386) = false := by
  decide +kernel

theorem node_context_10_72386_1526983 : EJMOriginalGlobalDAGData.nodes 11 ⟨1526983, by decide⟩ =
    .split (coordinate 10) (![⟨1526923, by decide⟩,⟨1526951, by decide⟩,⟨1468743, by decide⟩,⟨1526982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72386_1526983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72386 ⟨1526983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72386
    ⟨1526983, by decide⟩ (by decide) (![⟨1526923, by decide⟩,⟨1526951, by decide⟩,⟨1468743, by decide⟩,⟨1526982, by decide⟩]) unmarked_context_10_72386_1526983 node_context_10_72386_1526983
  intro a
  fin_cases a
  · exact context_11_289544_1526923
  · exact context_11_289545_1526951
  · exact context_11_289546_1468743
  · exact context_11_289547_1526982

theorem selected_cut_52398 : selected 11 ⟨1527044, by decide⟩
    (prefixPartial 10 72387) = some ⟨10, 2, 0, 1527044, 72387, 2489, 1048576⟩ := by
  decide +kernel

theorem context_10_72387_1527044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72387 ⟨1527044, by decide⟩ :=
  accepted_of_selected 10 72387 ⟨1527044, by decide⟩ ⟨10, 2, 0, 1527044, 72387, 2489, 1048576⟩
    (by decide) selected_cut_52398

theorem unmarked_context_9_18096_1527045 : frontier 12 ⟨1527045, by decide⟩
    (prefixCache 9 18096) (prefixPartial 9 18096) = false := by
  decide +kernel

theorem node_context_9_18096_1527045 : EJMOriginalGlobalDAGData.nodes 12 ⟨1527045, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1526863, by decide⟩,⟨1526983, by decide⟩,⟨1527044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18096_1527045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18096 ⟨1527045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18096
    ⟨1527045, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1526863, by decide⟩,⟨1526983, by decide⟩,⟨1527044, by decide⟩]) unmarked_context_9_18096_1527045 node_context_9_18096_1527045
  intro a
  fin_cases a
  · exact context_10_72384_1468246
  · exact context_10_72385_1526863
  · exact context_10_72386_1526983
  · exact context_10_72387_1527044

theorem selected_cut_52399 : selected 11 ⟨1527131, by decide⟩
    (prefixPartial 10 72388) = some ⟨10, 2, 0, 1527131, 72388, 2157, 1048576⟩ := by
  decide +kernel

theorem context_10_72388_1527131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72388 ⟨1527131, by decide⟩ :=
  accepted_of_selected 10 72388 ⟨1527131, by decide⟩ ⟨10, 2, 0, 1527131, 72388, 2157, 1048576⟩
    (by decide) selected_cut_52399

theorem selected_cut_52400 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72389) = some ⟨10, 1, 0, 1468874, 72389, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72389_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72389 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72389 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72389, 1, 1048576⟩
    (by decide) selected_cut_52400

theorem selected_cut_52401 : selected 11 ⟨1527217, by decide⟩
    (prefixPartial 10 72390) = some ⟨10, 2, 0, 1527217, 72390, 3249, 1048576⟩ := by
  decide +kernel

theorem context_10_72390_1527217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72390 ⟨1527217, by decide⟩ :=
  accepted_of_selected 10 72390 ⟨1527217, by decide⟩ ⟨10, 2, 0, 1527217, 72390, 3249, 1048576⟩
    (by decide) selected_cut_52401

theorem selected_cut_52402 : selected 11 ⟨1527252, by decide⟩
    (prefixPartial 10 72391) = some ⟨10, 2, 0, 1527252, 72391, 1697, 1048576⟩ := by
  decide +kernel

theorem context_10_72391_1527252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72391 ⟨1527252, by decide⟩ :=
  accepted_of_selected 10 72391 ⟨1527252, by decide⟩ ⟨10, 2, 0, 1527252, 72391, 1697, 1048576⟩
    (by decide) selected_cut_52402

theorem unmarked_context_9_18097_1527253 : frontier 12 ⟨1527253, by decide⟩
    (prefixCache 9 18097) (prefixPartial 9 18097) = false := by
  decide +kernel

theorem node_context_9_18097_1527253 : EJMOriginalGlobalDAGData.nodes 12 ⟨1527253, by decide⟩ =
    .split (coordinate 9) (![⟨1527131, by decide⟩,⟨1468874, by decide⟩,⟨1527217, by decide⟩,⟨1527252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18097_1527253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18097 ⟨1527253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18097
    ⟨1527253, by decide⟩ (by decide) (![⟨1527131, by decide⟩,⟨1468874, by decide⟩,⟨1527217, by decide⟩,⟨1527252, by decide⟩]) unmarked_context_9_18097_1527253 node_context_9_18097_1527253
  intro a
  fin_cases a
  · exact context_10_72388_1527131
  · exact context_10_72389_1468874
  · exact context_10_72390_1527217
  · exact context_10_72391_1527252

theorem selected_cut_52403 : selected 12 ⟨1527370, by decide⟩
    (prefixPartial 9 18098) = some ⟨9, 2, 0, 1527370, 18098, 3725, 4194304⟩ := by
  decide +kernel

theorem context_9_18098_1527370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18098 ⟨1527370, by decide⟩ :=
  accepted_of_selected 9 18098 ⟨1527370, by decide⟩ ⟨9, 2, 0, 1527370, 18098, 3725, 4194304⟩
    (by decide) selected_cut_52403

theorem selected_cut_52404 : selected 12 ⟨1527427, by decide⟩
    (prefixPartial 9 18099) = some ⟨9, 2, 0, 1527427, 18099, 1317, 4194304⟩ := by
  decide +kernel

theorem context_9_18099_1527427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18099 ⟨1527427, by decide⟩ :=
  accepted_of_selected 9 18099 ⟨1527427, by decide⟩ ⟨9, 2, 0, 1527427, 18099, 1317, 4194304⟩
    (by decide) selected_cut_52404

theorem unmarked_context_8_4524_1527428 : frontier 13 ⟨1527428, by decide⟩
    (prefixCache 8 4524) (prefixPartial 8 4524) = false := by
  decide +kernel

theorem node_context_8_4524_1527428 : EJMOriginalGlobalDAGData.nodes 13 ⟨1527428, by decide⟩ =
    .split (coordinate 8) (![⟨1527045, by decide⟩,⟨1527253, by decide⟩,⟨1527370, by decide⟩,⟨1527427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4524_1527428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4524 ⟨1527428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4524
    ⟨1527428, by decide⟩ (by decide) (![⟨1527045, by decide⟩,⟨1527253, by decide⟩,⟨1527370, by decide⟩,⟨1527427, by decide⟩]) unmarked_context_8_4524_1527428 node_context_8_4524_1527428
  intro a
  fin_cases a
  · exact context_9_18096_1527045
  · exact context_9_18097_1527253
  · exact context_9_18098_1527370
  · exact context_9_18099_1527427

theorem selected_cut_52405 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72400) = some ⟨10, 1, 0, 1468246, 72400, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72400_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72400 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72400 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72400, 1, 1048576⟩
    (by decide) selected_cut_52405

theorem selected_cut_52406 : selected 10 ⟨1527464, by decide⟩
    (prefixPartial 11 289604) = some ⟨11, 2, 0, 1527464, 289604, 1285, 262144⟩ := by
  decide +kernel

theorem context_11_289604_1527464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289604 ⟨1527464, by decide⟩ :=
  accepted_of_selected 11 289604 ⟨1527464, by decide⟩ ⟨11, 2, 0, 1527464, 289604, 1285, 262144⟩
    (by decide) selected_cut_52406

theorem selected_cut_52407 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289605) = some ⟨11, 1, 0, 1468419, 289605, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289605_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289605 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289605 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289605, 1, 262144⟩
    (by decide) selected_cut_52407

theorem selected_cut_52408 : selected 10 ⟨1527537, by decide⟩
    (prefixPartial 11 289606) = some ⟨11, 2, 0, 1527537, 289606, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_289606_1527537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289606 ⟨1527537, by decide⟩ :=
  accepted_of_selected 11 289606 ⟨1527537, by decide⟩ ⟨11, 2, 0, 1527537, 289606, 2401, 262144⟩
    (by decide) selected_cut_52408

theorem selected_cut_52409 : selected 10 ⟨1527560, by decide⟩
    (prefixPartial 11 289607) = some ⟨11, 2, 0, 1527560, 289607, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_289607_1527560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289607 ⟨1527560, by decide⟩ :=
  accepted_of_selected 11 289607 ⟨1527560, by decide⟩ ⟨11, 2, 0, 1527560, 289607, 1069, 262144⟩
    (by decide) selected_cut_52409

theorem unmarked_context_10_72401_1527561 : frontier 11 ⟨1527561, by decide⟩
    (prefixCache 10 72401) (prefixPartial 10 72401) = false := by
  decide +kernel

theorem node_context_10_72401_1527561 : EJMOriginalGlobalDAGData.nodes 11 ⟨1527561, by decide⟩ =
    .split (coordinate 10) (![⟨1527464, by decide⟩,⟨1468419, by decide⟩,⟨1527537, by decide⟩,⟨1527560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72401_1527561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72401 ⟨1527561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72401
    ⟨1527561, by decide⟩ (by decide) (![⟨1527464, by decide⟩,⟨1468419, by decide⟩,⟨1527537, by decide⟩,⟨1527560, by decide⟩]) unmarked_context_10_72401_1527561 node_context_10_72401_1527561
  intro a
  fin_cases a
  · exact context_11_289604_1527464
  · exact context_11_289605_1468419
  · exact context_11_289606_1527537
  · exact context_11_289607_1527560

theorem selected_cut_52410 : selected 11 ⟨1527685, by decide⟩
    (prefixPartial 10 72402) = some ⟨10, 2, 0, 1527685, 72402, 3889, 1048576⟩ := by
  decide +kernel

theorem context_10_72402_1527685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72402 ⟨1527685, by decide⟩ :=
  accepted_of_selected 10 72402 ⟨1527685, by decide⟩ ⟨10, 2, 0, 1527685, 72402, 3889, 1048576⟩
    (by decide) selected_cut_52410

theorem selected_cut_52411 : selected 11 ⟨1527733, by decide⟩
    (prefixPartial 10 72403) = some ⟨10, 2, 0, 1527733, 72403, 1485, 1048576⟩ := by
  decide +kernel

theorem context_10_72403_1527733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72403 ⟨1527733, by decide⟩ :=
  accepted_of_selected 10 72403 ⟨1527733, by decide⟩ ⟨10, 2, 0, 1527733, 72403, 1485, 1048576⟩
    (by decide) selected_cut_52411

theorem unmarked_context_9_18100_1527734 : frontier 12 ⟨1527734, by decide⟩
    (prefixCache 9 18100) (prefixPartial 9 18100) = false := by
  decide +kernel

theorem node_context_9_18100_1527734 : EJMOriginalGlobalDAGData.nodes 12 ⟨1527734, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1527561, by decide⟩,⟨1527685, by decide⟩,⟨1527733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18100_1527734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18100 ⟨1527734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18100
    ⟨1527734, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1527561, by decide⟩,⟨1527685, by decide⟩,⟨1527733, by decide⟩]) unmarked_context_9_18100_1527734 node_context_9_18100_1527734
  intro a
  fin_cases a
  · exact context_10_72400_1468246
  · exact context_10_72401_1527561
  · exact context_10_72402_1527685
  · exact context_10_72403_1527733

theorem selected_cut_52412 : selected 11 ⟨1527804, by decide⟩
    (prefixPartial 10 72404) = some ⟨10, 2, 0, 1527804, 72404, 2369, 1048576⟩ := by
  decide +kernel

theorem context_10_72404_1527804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72404 ⟨1527804, by decide⟩ :=
  accepted_of_selected 10 72404 ⟨1527804, by decide⟩ ⟨10, 2, 0, 1527804, 72404, 2369, 1048576⟩
    (by decide) selected_cut_52412

theorem selected_cut_52413 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72405) = some ⟨10, 1, 0, 1468874, 72405, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72405_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72405 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72405 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72405, 1, 1048576⟩
    (by decide) selected_cut_52413

theorem selected_cut_52414 : selected 11 ⟨1527927, by decide⟩
    (prefixPartial 10 72406) = some ⟨10, 2, 0, 1527927, 72406, 3645, 1048576⟩ := by
  decide +kernel

theorem context_10_72406_1527927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72406 ⟨1527927, by decide⟩ :=
  accepted_of_selected 10 72406 ⟨1527927, by decide⟩ ⟨10, 2, 0, 1527927, 72406, 3645, 1048576⟩
    (by decide) selected_cut_52414

theorem selected_cut_52415 : selected 11 ⟨1527978, by decide⟩
    (prefixPartial 10 72407) = some ⟨10, 2, 0, 1527978, 72407, 1881, 1048576⟩ := by
  decide +kernel

theorem context_10_72407_1527978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72407 ⟨1527978, by decide⟩ :=
  accepted_of_selected 10 72407 ⟨1527978, by decide⟩ ⟨10, 2, 0, 1527978, 72407, 1881, 1048576⟩
    (by decide) selected_cut_52415

theorem unmarked_context_9_18101_1527979 : frontier 12 ⟨1527979, by decide⟩
    (prefixCache 9 18101) (prefixPartial 9 18101) = false := by
  decide +kernel

theorem node_context_9_18101_1527979 : EJMOriginalGlobalDAGData.nodes 12 ⟨1527979, by decide⟩ =
    .split (coordinate 9) (![⟨1527804, by decide⟩,⟨1468874, by decide⟩,⟨1527927, by decide⟩,⟨1527978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18101_1527979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18101 ⟨1527979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18101
    ⟨1527979, by decide⟩ (by decide) (![⟨1527804, by decide⟩,⟨1468874, by decide⟩,⟨1527927, by decide⟩,⟨1527978, by decide⟩]) unmarked_context_9_18101_1527979 node_context_9_18101_1527979
  intro a
  fin_cases a
  · exact context_10_72404_1527804
  · exact context_10_72405_1468874
  · exact context_10_72406_1527927
  · exact context_10_72407_1527978

theorem selected_cut_52416 : selected 12 ⟨1528073, by decide⟩
    (prefixPartial 9 18102) = some ⟨9, 2, 0, 1528073, 18102, 2413, 4194304⟩ := by
  decide +kernel

theorem context_9_18102_1528073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18102 ⟨1528073, by decide⟩ :=
  accepted_of_selected 9 18102 ⟨1528073, by decide⟩ ⟨9, 2, 0, 1528073, 18102, 2413, 4194304⟩
    (by decide) selected_cut_52416

theorem selected_cut_52417 : selected 12 ⟨1528132, by decide⟩
    (prefixPartial 9 18103) = some ⟨9, 2, 0, 1528132, 18103, 1133, 4194304⟩ := by
  decide +kernel

theorem context_9_18103_1528132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18103 ⟨1528132, by decide⟩ :=
  accepted_of_selected 9 18103 ⟨1528132, by decide⟩ ⟨9, 2, 0, 1528132, 18103, 1133, 4194304⟩
    (by decide) selected_cut_52417

theorem unmarked_context_8_4525_1528133 : frontier 13 ⟨1528133, by decide⟩
    (prefixCache 8 4525) (prefixPartial 8 4525) = false := by
  decide +kernel

theorem node_context_8_4525_1528133 : EJMOriginalGlobalDAGData.nodes 13 ⟨1528133, by decide⟩ =
    .split (coordinate 8) (![⟨1527734, by decide⟩,⟨1527979, by decide⟩,⟨1528073, by decide⟩,⟨1528132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4525_1528133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4525 ⟨1528133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4525
    ⟨1528133, by decide⟩ (by decide) (![⟨1527734, by decide⟩,⟨1527979, by decide⟩,⟨1528073, by decide⟩,⟨1528132, by decide⟩]) unmarked_context_8_4525_1528133 node_context_8_4525_1528133
  intro a
  fin_cases a
  · exact context_9_18100_1527734
  · exact context_9_18101_1527979
  · exact context_9_18102_1528073
  · exact context_9_18103_1528132

theorem selected_cut_52418 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72416) = some ⟨10, 1, 0, 1468246, 72416, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72416_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72416 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72416 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72416, 1, 1048576⟩
    (by decide) selected_cut_52418

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
